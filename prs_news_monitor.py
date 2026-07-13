#!/usr/bin/env python3
"""
NRLA PRS news — daily email digest generator
=============================================
Reads the same prs_news.db the dashboard uses, selects the stories first seen
since the last digest, ranks them editorially, and renders an Outlook-safe HTML
email. Optionally uploads the HTML (and a small JSON sidecar with the subject /
preheader) to SharePoint via the Microsoft Graph API, where a Power Automate
flow can pick it up and send it.
 
Design notes
------------
* Push surface, not a database mirror: the job is to make the 2-3 stories that
  matter impossible to miss. A ranked "Top stories" block does that; the rest is
  grouped by region (Wales pulled out) so a reader can jump to their patch.
* Daily cadence: selection is "new since last digest" via a `last_emailed`
  marker in the meta table, so nothing is sent twice and a missed run catches up.
* Degrades by volume: a busy day gets the full grouped layout; a quiet day
  (<= SIMPLE_LAYOUT_MAX) collapses to a simple ranked list. Zero new stories =>
  no email at all.
* Bulletproof HTML: 600px role=presentation tables, all CSS inline, web-safe
  fonts, no layout-critical images, explicit light backgrounds.
 
Delivery is intentionally decoupled: this script only renders + uploads a file.
Sending (recipients, subject, etc.) is handled by the Power Automate flow.
 
No third-party dependencies — standard library only (urllib for Graph).
"""
 
import os
import re
import json
import html
import sqlite3
import urllib.parse
import urllib.request
from datetime import datetime, timezone, date, timedelta
 
# --------------------------------------------------------------------------- #
# CONFIG                                                                       #
# --------------------------------------------------------------------------- #
 
DB_PATH        = os.environ.get("PRS_DB_PATH", "prs_news.db")
OUTPUT_HTML    = os.environ.get("PRS_DIGEST_HTML", "digest.html")
OUTPUT_META    = os.environ.get("PRS_DIGEST_META", "digest.json")
DASHBOARD_URL  = os.environ.get("PRS_DASHBOARD_URL",
                                "https://jhc220199.github.io/PRS-News-Aggregator/")
 
# Layout / selection tuning
SIMPLE_LAYOUT_MAX = int(os.environ.get("PRS_DIGEST_SIMPLE_MAX", "5"))
TOP_STORIES       = int(os.environ.get("PRS_DIGEST_TOP", "5"))
PER_REGION_CAP    = int(os.environ.get("PRS_DIGEST_REGION_CAP", "4"))
WALES_CAP         = int(os.environ.get("PRS_DIGEST_WALES_CAP", "6"))
NATIONAL_CAP      = int(os.environ.get("PRS_DIGEST_NATIONAL_CAP", "4"))
 
# Test/preview only: cap the number of selected stories (0 = off).
DEMO_LIMIT     = int(os.environ.get("PRS_DIGEST_DEMO_LIMIT", "0"))
# When set, build the file but never upload or advance the marker.
DRY_RUN        = os.environ.get("PRS_DIGEST_DRY_RUN", "0") == "1"
 
# SharePoint / Graph (set as GitHub secrets). Upload is skipped if any missing.
GRAPH_TENANT   = os.environ.get("PRS_GRAPH_TENANT_ID", "")
GRAPH_CLIENT   = os.environ.get("PRS_GRAPH_CLIENT_ID", "")
GRAPH_SECRET   = os.environ.get("PRS_GRAPH_CLIENT_SECRET", "")
SP_HOST        = os.environ.get("PRS_SP_HOST", "rlateam.sharepoint.com")
SP_SITE_PATH   = os.environ.get("PRS_SP_SITE_PATH", "")          # e.g. /sites/Policy
SP_LIBRARY     = os.environ.get("PRS_SP_LIBRARY", "Campaigns & Policy")
SP_FOLDER      = os.environ.get("PRS_SP_FOLDER", "PRS-news-digest")
 
# --- NRLA palette ----------------------------------------------------------
BLUE, ORANGE, INK = "#113B54", "#E96C19", "#0F2636"
MUTED, LINE = "#5C6B75", "#E2E6E9"
PAGE_BG, CARD, BLUE_TINT = "#F2F4F5", "#FFFFFF", "#E7EEF2"
FONT = "Arial, Helvetica, sans-serif"
 
# --- Editorial ranking -----------------------------------------------------
CATEGORY_WEIGHT = {
    "Selective licensing": 10,
    "Enforcement & penalties": 9,
    "Rent Smart Wales": 9,
    "HMO / additional licensing": 9,
    "Article 4 / planning": 8,
    "Renters' Rights & reform": 8,
    "Landlord licensing (other)": 6,
    "Possession & eviction": 5,
    "Energy & standards": 5,
    "Council tax & empty homes": 4,
    "Other PRS news": 2,
}
# Categories with a publishing window — flagged "time-sensitive" in the email.
TIME_SENSITIVE_CATS = {
    "Selective licensing", "HMO / additional licensing", "Article 4 / planning",
    "Rent Smart Wales", "Enforcement & penalties", "Landlord licensing (other)",
}
 
ENGLISH_REGIONS = ["North East", "North West", "Yorkshire and The Humber",
                   "East Midlands", "West Midlands", "East of England",
                   "London", "South East", "South West"]
WELSH_REGIONS = ["North Wales", "Mid Wales", "South West Wales",
                 "South East Wales", "Wales (national)"]
 
MONTHS = ["January", "February", "March", "April", "May", "June", "July",
          "August", "September", "October", "November", "December"]
 
 
# --------------------------------------------------------------------------- #
# HELPERS                                                                      #
# --------------------------------------------------------------------------- #
 
def ordinal(n: int) -> str:
    suf = "th" if 10 <= n % 100 <= 20 else {1: "st", 2: "nd", 3: "rd"}.get(n % 10, "th")
    return f"{n}{suf}"
 
 
def fmt_date(iso: str) -> str:
    try:
        d = date.fromisoformat(iso)
        return f"{ordinal(d.day)} {MONTHS[d.month - 1]} {d.year}"
    except Exception:
        return iso or ""
 
 
def esc(s: str) -> str:
    return html.escape(s or "", quote=True)
 
 
def is_consultation(r) -> bool:
    return "consultation" in (r["title"] + " " + (r["summary"] or "")).lower()
 
 
def editorial_score(r) -> float:
    s = CATEGORY_WEIGHT.get(r["category"], 2)
    if r["primary_la"]:
        s += 4                      # local stories are the whole point
    if is_consultation(r):
        s += 3
    s += min(r["score"] or 0, 6) * 0.5
    # Recency nudge (tie-breaker): published within the last few days.
    try:
        age = (date.today() - date.fromisoformat(r["published"])).days
        s += max(0, 3 - age) * 0.4
    except Exception:
        pass
    return s
 
 
def time_sensitive(r) -> bool:
    return r["category"] in TIME_SENSITIVE_CATS or is_consultation(r)
 
 
def loc_label(r) -> str:
    if r["primary_la"]:
        return r["primary_la"]
    reg = r["region"]
    if reg.startswith("National"):
        return "National"
    if reg == "Wales (national)":
        return "Wales-wide"
    return reg
 
 
def meta_line(r) -> str:
    bits = []
    if r["primary_la"]:
        bits.append(esc(r["primary_la"]))
        if r["region"] and r["region"] != r["primary_la"]:
            bits.append(esc(r["region"]))
    else:
        bits.append(esc(loc_label(r)))
    if r["source"]:
        bits.append(esc(r["source"]))
    if r["published"]:
        bits.append(esc(fmt_date(r["published"])))
    return " &middot; ".join(bits)
 
 
# --------------------------------------------------------------------------- #
# SELECTION                                                                    #
# --------------------------------------------------------------------------- #
 
def ensure_emailed_column(con):
    """Add the per-story 'emailed' flag if this database predates it. Rows
    already covered by the old date marker are marked as sent so the upgrade
    doesn't re-email the whole 30-day window once."""
    cols = [r[1] for r in con.execute("PRAGMA table_info(articles)")]
    if "emailed" not in cols:
        con.execute("ALTER TABLE articles ADD COLUMN emailed INTEGER DEFAULT 0")
        row = con.execute(
            "SELECT value FROM meta WHERE key='last_emailed'").fetchone()
        if row:
            con.execute("UPDATE articles SET emailed=1 WHERE first_seen <= ?",
                        (row[0],))
        con.commit()
 
 
def select_new(con):
    """Stories not yet included in any digest, editorial-rank first. Selection
    is a per-story flag rather than a date marker so any cadence works —
    including two runs on the same day (a date marker would make the afternoon
    digest always empty, since first_seen is only date-granular)."""
    ensure_emailed_column(con)
    cur = con.execute(
        """SELECT guid,title,url,source,published,first_seen,summary,nation,
                  region,primary_la,category,score
           FROM articles WHERE emailed=0 ORDER BY published DESC""")
    cols = [c[0] for c in cur.description]
    rows = [dict(zip(cols, v)) for v in cur.fetchall()]
    rows.sort(key=editorial_score, reverse=True)
    if DEMO_LIMIT:
        rows = rows[:DEMO_LIMIT]
    return rows
 
 
# --------------------------------------------------------------------------- #
# HTML BUILDING (Outlook-safe: tables, inline CSS, web-safe fonts)             #
# --------------------------------------------------------------------------- #
 
def region_link(region):
    return DASHBOARD_URL + "#r=" + urllib.parse.quote(region)
 
 
def story_block(r, lead=False):
    """One story as a bulletproof two-column table (orange accent + content)."""
    tag = esc(r["category"])
    ts = ('<span style="color:%s;font-weight:bold;font-size:11px;'
          'letter-spacing:.04em;text-transform:uppercase;">&#9679; Time-sensitive'
          '</span><span style="color:%s;"> &middot; </span>' % (ORANGE, LINE)) \
        if time_sensitive(r) else ""
    tag_html = ('%s<span style="color:%s;font-weight:bold;font-size:11px;'
                'letter-spacing:.04em;text-transform:uppercase;">%s</span>'
                % (ts, BLUE, tag))
    headline_size = "17px" if lead else "15px"
    accent = ORANGE if lead else LINE
    content = (
        '<div style="margin-bottom:5px;">%s</div>'
        '<a href="%s" style="color:%s;font-size:%s;font-weight:bold;'
        'text-decoration:none;line-height:1.35;">%s</a>'
        '<div style="color:%s;font-size:12px;margin-top:5px;">%s</div>'
        % (tag_html, esc(r["url"]), INK, headline_size, esc(r["title"]),
           MUTED, meta_line(r)))
    return (
        '<table role="presentation" cellpadding="0" cellspacing="0" border="0" '
        'width="100%%" style="border-collapse:collapse;margin:0 0 10px 0;">'
        '<tr>'
        '<td width="4" bgcolor="%s" style="background:%s;font-size:0;line-height:0;">&nbsp;</td>'
        '<td style="background:%s;border:1px solid %s;border-left:0;padding:13px 15px;">%s</td>'
        '</tr></table>' % (accent, accent, CARD, LINE, content))
 
 
def section_header(label, count):
    return ('<tr><td style="padding:20px 0 8px 0;">'
            '<span style="font-size:13px;font-weight:bold;text-transform:uppercase;'
            'letter-spacing:.06em;color:%s;">%s</span>'
            '<span style="color:%s;font-size:13px;font-weight:normal;"> &nbsp;(%d)</span>'
            '</td></tr>' % (BLUE, esc(label), MUTED, count))
 
 
def more_link(region, n):
    return ('<tr><td style="padding:2px 0 4px 0;">'
            '<a href="%s" style="color:%s;font-size:12px;font-weight:bold;'
            'text-decoration:none;">+ %d more &middot; view all &rarr;</a>'
            '</td></tr>' % (region_link(region), ORANGE, n))
 
 
def rows_to_cells(rows, lead=False):
    return "".join('<tr><td>%s</td></tr>' % story_block(r, lead) for r in rows)
 
 
def build_summary(rows):
    areas = len({r["primary_la"] for r in rows if r["primary_la"]})
    eng = sum(1 for r in rows if r["nation"] == "England")
    wal = sum(1 for r in rows if r["nation"] == "Wales")
    nat = len(rows) - eng - wal
    cats = {}
    for r in rows:
        cats[r["category"]] = cats.get(r["category"], 0) + 1
    top_cats = sorted(cats.items(), key=lambda x: -x[1])[:4]
    nation_bits = []
    if eng: nation_bits.append(f"England {eng}")
    if wal: nation_bits.append(f"Wales {wal}")
    if nat: nation_bits.append(f"national {nat}")
    cat_bits = " &middot; ".join(f"{esc(k)} {v}" for k, v in top_cats)
    line1 = f"{len(rows)} new {'story' if len(rows)==1 else 'stories'} &middot; {areas} {'area' if areas==1 else 'areas'}"
    return (
        '<tr><td style="padding:4px 0 0 0;color:%s;font-size:13px;line-height:1.6;">'
        '<span style="color:%s;font-weight:bold;">%s</span><br>%s<br>'
        '<span style="color:%s;">%s</span></td></tr>'
        % (INK, INK, line1, " &middot; ".join(nation_bits), MUTED, cat_bits))
 
 
def build_body(rows):
    """Return inner HTML rows for the digest, branching on volume."""
    if len(rows) <= SIMPLE_LAYOUT_MAX:
        # Quiet day: one simple ranked list, no scaffolding.
        return ('<tr><td style="padding:14px 0 2px 0;font-size:13px;font-weight:bold;'
                'text-transform:uppercase;letter-spacing:.06em;color:%s;">'
                'Today\'s stories</td></tr>%s' % (BLUE, rows_to_cells(rows)))
 
    out = []
    top = rows[:TOP_STORIES]
    top_urls = {r["url"] for r in top}
    rest = [r for r in rows if r["url"] not in top_urls]
 
    out.append('<tr><td style="padding:18px 0 8px 0;"><span style="font-size:14px;'
               'font-weight:bold;text-transform:uppercase;letter-spacing:.06em;'
               'color:%s;">Top stories</span></td></tr>' % ORANGE)
    out.append(rows_to_cells(top, lead=True))
 
    # Wales block (its own section, given how central it is)
    wales = [r for r in rest if r["region"] in WELSH_REGIONS]
    if wales:
        out.append(section_header("Wales", len(wales)))
        out.append(rows_to_cells(wales[:WALES_CAP]))
        if len(wales) > WALES_CAP:
            out.append(more_link("Wales (national)", len(wales) - WALES_CAP))
 
    # England, grouped by region
    eng_rest = [r for r in rest if r["region"] in ENGLISH_REGIONS]
    if eng_rest:
        out.append('<tr><td style="padding:20px 0 0 0;"><span style="font-size:13px;'
                   'font-weight:bold;text-transform:uppercase;letter-spacing:.06em;'
                   'color:%s;">England &mdash; by region</span></td></tr>' % BLUE)
        for reg in ENGLISH_REGIONS:
            grp = [r for r in eng_rest if r["region"] == reg]
            if not grp:
                continue
            out.append('<tr><td style="padding:12px 0 6px 0;color:%s;font-size:13px;'
                       'font-weight:bold;">%s <span style="color:%s;font-weight:normal;">'
                       '(%d)</span></td></tr>' % (INK, esc(reg), MUTED, len(grp)))
            out.append(rows_to_cells(grp[:PER_REGION_CAP]))
            if len(grp) > PER_REGION_CAP:
                out.append(more_link(reg, len(grp) - PER_REGION_CAP))
 
    # National / cross-cutting
    nat = [r for r in rest if r["region"] not in WELSH_REGIONS
           and r["region"] not in ENGLISH_REGIONS]
    if nat:
        out.append(section_header("National / cross-cutting", len(nat)))
        out.append(rows_to_cells(nat[:NATIONAL_CAP]))
        if len(nat) > NATIONAL_CAP:
            out.append(more_link("National / cross-cutting", len(nat) - NATIONAL_CAP))
 
    return "".join(out)
 
 
def make_subject_preheader(rows):
    n = len(rows)
    schemes = sum(1 for r in rows if r["category"] in
                  ("Selective licensing", "HMO / additional licensing",
                   "Landlord licensing (other)"))
    enf = sum(1 for r in rows if r["category"] == "Enforcement & penalties")
    extra = ""
    if schemes >= 1:
        extra = f", incl. {schemes} licensing {'item' if schemes==1 else 'items'}"
    elif enf >= 1:
        extra = f", incl. {enf} enforcement {'action' if enf==1 else 'actions'}"
    subject = f"PRS news \u00b7 {n} new {'story' if n==1 else 'stories'}{extra}"
 
    # Preheader: the essence of the top few stories.
    pre_bits = []
    for r in rows[:3]:
        loc = loc_label(r)
        pre_bits.append(f"{loc}: {r['category']}" if r["primary_la"] else r["category"])
    preheader = "; ".join(pre_bits)
    return subject, preheader
 
 
def render_email(rows, subject, preheader):
    today = date.today()
    datestr = f"{ordinal(today.day)} {MONTHS[today.month-1]} {today.year}"
    body = build_body(rows)
    return f"""<!DOCTYPE html>
<html lang="en-GB" xmlns:v="urn:schemas-microsoft-com:vml" xmlns:o="urn:schemas-microsoft-com:office:office">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<meta name="color-scheme" content="light only">
<meta name="supported-color-schemes" content="light only">
<title>{esc(subject)}</title>
</head>
<body style="margin:0;padding:0;background:{PAGE_BG};">
<div style="display:none;max-height:0;overflow:hidden;mso-hide:all;font-size:1px;line-height:1px;color:{PAGE_BG};">{esc(preheader)}&nbsp;&zwnj;&nbsp;&zwnj;&nbsp;&zwnj;&nbsp;&zwnj;&nbsp;&zwnj;&nbsp;&zwnj;</div>
<table role="presentation" cellpadding="0" cellspacing="0" border="0" width="100%" bgcolor="{PAGE_BG}" style="background:{PAGE_BG};">
<tr><td align="center" style="padding:18px 12px;">
  <table role="presentation" cellpadding="0" cellspacing="0" border="0" width="600" style="width:600px;max-width:600px;font-family:{FONT};">
 
    <!-- Masthead -->
    <tr><td bgcolor="{BLUE}" style="background:{BLUE};padding:18px 20px;border-radius:8px 8px 0 0;">
      <table role="presentation" cellpadding="0" cellspacing="0" border="0" width="100%">
        <tr>
          <td style="font-family:{FONT};font-size:18px;font-weight:bold;color:#FFFFFF;">
            <span style="color:{ORANGE};">NRLA</span> PRS news digest
          </td>
          <td align="right" style="font-family:{FONT};font-size:12px;color:#AFC2CC;">{datestr}</td>
        </tr>
      </table>
    </td></tr>
 
    <!-- Body -->
    <tr><td bgcolor="{CARD}" style="background:{CARD};padding:6px 20px 20px 20px;border:1px solid {LINE};border-top:0;border-radius:0 0 8px 8px;">
      <table role="presentation" cellpadding="0" cellspacing="0" border="0" width="100%">
        {build_summary(rows)}
        {body}
      </table>
    </td></tr>
 
    <!-- Footer -->
    <tr><td style="padding:16px 20px;font-family:{FONT};font-size:11px;color:{MUTED};line-height:1.6;">
      Auto-generated from the PRS local news monitor &mdash; always verify against the
      original source before publishing.<br>
      <a href="{DASHBOARD_URL}" style="color:{BLUE};font-weight:bold;text-decoration:none;">Open the full dashboard &rarr;</a>
    </td></tr>
 
  </table>
</td></tr>
</table>
</body>
</html>"""
 
 
# --------------------------------------------------------------------------- #
# GRAPH / SHAREPOINT UPLOAD                                                     #
# --------------------------------------------------------------------------- #
 
def graph_configured() -> bool:
    return all([GRAPH_TENANT, GRAPH_CLIENT, GRAPH_SECRET, SP_SITE_PATH])
 
 
def graph_token() -> str:
    data = urllib.parse.urlencode({
        "client_id": GRAPH_CLIENT, "client_secret": GRAPH_SECRET,
        "scope": "https://graph.microsoft.com/.default",
        "grant_type": "client_credentials",
    }).encode()
    url = f"https://login.microsoftonline.com/{GRAPH_TENANT}/oauth2/v2.0/token"
    with urllib.request.urlopen(urllib.request.Request(url, data=data), timeout=30) as resp:
        return json.load(resp)["access_token"]
 
 
def graph_get(url, token):
    req = urllib.request.Request(url, headers={"Authorization": "Bearer " + token})
    with urllib.request.urlopen(req, timeout=30) as resp:
        return json.load(resp)
 
 
def graph_upload(token, site_id, drive_id, name, content_bytes, content_type):
    path = urllib.parse.quote(f"{SP_FOLDER}/{name}")
    url = (f"https://graph.microsoft.com/v1.0/sites/{site_id}/drives/{drive_id}"
           f"/root:/{path}:/content")
    req = urllib.request.Request(url, data=content_bytes, method="PUT",
                                 headers={"Authorization": "Bearer " + token,
                                          "Content-Type": content_type})
    with urllib.request.urlopen(req, timeout=60) as resp:
        return json.load(resp).get("webUrl", "(uploaded)")
 
 
def upload_to_sharepoint(html_text, meta_obj) -> bool:
    token = graph_token()
    site = graph_get(
        f"https://graph.microsoft.com/v1.0/sites/{SP_HOST}:{SP_SITE_PATH}", token)
    site_id = site["id"]
    drives = graph_get(
        f"https://graph.microsoft.com/v1.0/sites/{site_id}/drives", token)["value"]
    drive = next((d for d in drives if d.get("name") == SP_LIBRARY), drives[0])
    drive_id = drive["id"]
    web = graph_upload(token, site_id, drive_id, OUTPUT_HTML,
                       html_text.encode("utf-8"), "text/html; charset=utf-8")
    graph_upload(token, site_id, drive_id, OUTPUT_META,
                 json.dumps(meta_obj).encode("utf-8"), "application/json")
    print(f"   uploaded to SharePoint: {web}")
    return True
 
 
# --------------------------------------------------------------------------- #
# MAIN                                                                         #
# --------------------------------------------------------------------------- #
 
def mark_emailed(con, rows):
    """Flag exactly the stories included in this digest as sent. The
    last_emailed date is kept in meta for information only."""
    con.executemany("UPDATE articles SET emailed=1 WHERE guid=?",
                    [(r["guid"],) for r in rows])
    con.execute("INSERT OR REPLACE INTO meta VALUES ('last_emailed', ?)",
                (date.today().isoformat(),))
    con.commit()
 
 
def main():
    con = sqlite3.connect(DB_PATH)
    rows = select_new(con)
    print(f"== PRS digest | not yet emailed: {len(rows)} stories "
          f"| dry_run={DRY_RUN} ==")
 
    if not rows:
        print("   nothing new to send — no email this run.")
        con.close()
        return
 
    subject, preheader = make_subject_preheader(rows)
    html_text = render_email(rows, subject, preheader)
    meta_obj = {
        "subject": subject, "preheader": preheader, "count": len(rows),
        "date": date.today().isoformat(),
        "areas": len({r["primary_la"] for r in rows if r["primary_la"]}),
    }
 
    with open(OUTPUT_HTML, "w", encoding="utf-8") as f:
        f.write(html_text)
    with open(OUTPUT_META, "w", encoding="utf-8") as f:
        json.dump(meta_obj, f, indent=2)
    print(f"   subject: {subject}")
    print(f"   wrote {OUTPUT_HTML} ({len(html_text)//1024} KB) and {OUTPUT_META}")
 
    delivered = False
    if DRY_RUN:
        print("   dry run — not uploading, stories left unmarked.")
    elif graph_configured():
        try:
            delivered = upload_to_sharepoint(html_text, meta_obj)
        except Exception as exc:  # noqa: BLE001
            print(f"   ! upload failed ({exc}); stories left unmarked, will retry.")
    else:
        print("   Graph not configured — wrote file locally, stories left unmarked.")
 
    if delivered and not DRY_RUN:
        mark_emailed(con, rows)
        print(f"   marked {len(rows)} stories as emailed.")
    con.close()
 
 
if __name__ == "__main__":
    main()
 
