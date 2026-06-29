#!/usr/bin/env python3
"""
NRLA PRS Local News Monitor
===========================
Aggregates private-rented-sector news from across England and Wales into a
SQLite database (prs_news.db) that powers a static read-only dashboard.
 
Coverage model (see README):
  1. National theme sweeps   - Google News RSS queries on PRS themes
  2. Geographic sweeps        - one Google News query per local authority
  3. Curated feeds            - trade press, gov.uk, local-government press
 
The database is a rolling 30-day window. Each record is geotagged to a local
authority/region and tagged with a theme category, then deduplicated.
 
No paid APIs are used. Relevance is rules-based (keyword) so the script is free
to run. Drop your refined PRS keyword list into the CONFIG block below.
"""
 
import os
import re
import json
import time
import html
import random
import sqlite3
import urllib.parse
import urllib.request
from datetime import datetime, timezone, date, timedelta
 
import feedparser
from rapidfuzz import fuzz
 
# --------------------------------------------------------------------------- #
# CONFIG                                                                       #
# --------------------------------------------------------------------------- #
 
DB_PATH            = os.environ.get("PRS_DB_PATH", "prs_news.db")
AUTHORITIES_PATH   = os.environ.get("PRS_AUTHORITIES", "local_authorities.json")
RETENTION_DAYS     = int(os.environ.get("PRS_RETENTION_DAYS", "30"))
WINDOW_CUTOFF      = (date.today() - timedelta(days=RETENTION_DAYS)).isoformat()
USER_AGENT         = "Mozilla/5.0 (compatible; NRLA-PRS-Monitor/1.0; +https://www.nrla.org.uk)"
 
# Politeness / robustness when hitting Google News
GNEWS_MIN_DELAY    = float(os.environ.get("PRS_GNEWS_MIN_DELAY", "1.0"))
GNEWS_MAX_DELAY    = float(os.environ.get("PRS_GNEWS_MAX_DELAY", "1.8"))
REQUEST_TIMEOUT    = 30
MAX_RETRIES        = 2
 
# For local testing only: cap how many authorities are swept (0 = all).
MAX_AUTHORITIES    = int(os.environ.get("PRS_MAX_AUTHORITIES", "0"))
 
# National theme sweeps – broad Google News queries (no area name).
THEME_QUERIES = [
    '"selective licensing" landlords',
    '"additional licensing" HMO',
    '"HMO licensing" scheme',
    '"landlord licensing" scheme consultation',
    '"Article 4 direction" HMO',
    '"licensing scheme" private rented',
    '"Rent Smart Wales"',
    '"rent repayment order" landlord',
    '"banning order" landlord',
    'council "civil penalty" landlord unlicensed',
    '"Renters\' Rights" landlord council',
    '"selective licensing" consultation Wales',
]
 
# The PRS term-set injected into every per-authority geographic query.
GEO_QUERY_TERMS = ('"selective licensing" OR "additional licensing" OR '
                   '"HMO licensing" OR "landlord licensing" OR "Article 4" OR '
                   '"private rented" OR HMO')
 
# Wales runs on a different regime (Rent Smart Wales, occupation contracts,
# Renting Homes (Wales) Act, Section 173), so Welsh authorities get their own
# term-set or the England vocabulary returns almost nothing for them.
GEO_QUERY_TERMS_WALES = ('"Rent Smart Wales" OR "occupation contract" OR '
                         '"Renting Homes" OR "Section 173" OR "HMO licensing" OR '
                         '"landlord licensing" OR "Article 4" OR "private rented" '
                         'OR HMO OR landlord')
 
# Curated feeds (name, url). All verified to return content.
# Add LandlordZONE / regional publisher feeds here once you confirm their URLs.
CURATED_FEEDS = [
    ("GOV.UK – MHCLG news",
     "https://www.gov.uk/search/news-and-communications.atom?organisations%5B%5D=ministry-of-housing-communities-local-government"),
    ("GOV.UK – MHCLG consultations & papers",
     "https://www.gov.uk/search/policy-papers-and-consultations.atom?organisations%5B%5D=ministry-of-housing-communities-local-government"),
    ("Property118", "https://www.property118.com/feed/"),
    ("Property Industry Eye", "https://propertyindustryeye.com/feed/"),
    ("LocalGov", "https://www.localgov.co.uk/rss"),
    ("Nation.Cymru", "https://nation.cymru/feed/"),
]
 
# --- Relevance filter -------------------------------------------------------
# Context terms confirm a story is actually about the PRS (guards against
# alcohol/taxi/premises licensing and unrelated planning appeals).
PRS_CONTEXT_TERMS = [
    "landlord", "landlords", "tenant", "tenants", "tenancy", "tenancies",
    "private rented", "private rental", "privately rented", "rented sector",
    "rental property", "rental properties", "rental home", "rental homes",
    "buy-to-let", "buy to let", "lettings", "letting agent",
    "hmo", "house in multiple occupation", "houses in multiple occupation",
    "selective licensing", "additional licensing", "landlord licensing",
    "rent smart wales", "article 4", "rent repayment", "banning order",
    "renters' rights", "renters rights", "renters reform", "section 21",
    "section 8", "section 173", "occupation contract", "possession",
    "eviction", "epc", "mees", "minimum energy efficiency", "decent homes",
    "awaab", "empty homes", "second homes",
]
 
# High-signal terms strongly indicate a target story; they boost the score and
# on their own qualify an item as relevant.
PRS_HIGH_SIGNAL_TERMS = [
    "selective licensing", "additional licensing", "hmo licensing",
    "landlord licensing", "licensing scheme", "licensing designation",
    "article 4", "rent smart wales", "rent repayment order", "banning order",
    "renters' rights", "renters rights",
]
 
# Theme categories, in priority order (first match becomes the primary tag).
CATEGORY_RULES = [
    ("Selective licensing",        ["selective licensing", "selective licence",
                                     "selective licence scheme"]),
    ("HMO / additional licensing", ["additional licensing", "additional licence",
                                     "hmo licensing", "hmo licence",
                                     "house in multiple occupation",
                                     "houses in multiple occupation", "hmo"]),
    ("Article 4 / planning",       ["article 4", "use class", "c3 to c4",
                                     "c4 use", "permitted development"]),
    ("Rent Smart Wales",           ["rent smart wales", "renting homes wales",
                                     "occupation contract"]),
    ("Renters' Rights & reform",   ["renters' rights", "renters rights",
                                     "renters reform", "section 21", "section 8",
                                     "section 173", "no-fault", "no fault"]),
    ("Enforcement & penalties",    ["rent repayment", "banning order",
                                     "civil penalty", "prosecut", "unlicensed",
                                     "rogue landlord"]),
    ("Possession & eviction",      ["possession", "eviction", "bailiff"]),
    ("Energy & standards",         ["epc", "mees", "energy efficiency", "awaab",
                                     "damp and mould", "decent homes", "hazard"]),
    ("Council tax & empty homes",  ["empty homes", "second homes",
                                     "council tax premium", "long-term empty"]),
    # Catch-all for licensing stories that didn't match a specific scheme above.
    ("Landlord licensing (other)", ["landlord licensing", "landlord licence",
                                     "licensing scheme", "licence scheme",
                                     "property licensing", "property licence",
                                     "licensing designation", "licensing consultation",
                                     "licensing", "licence"]),
]
DEFAULT_CATEGORY = "Other PRS news"
 
# --------------------------------------------------------------------------- #
# FETCHING                                                                     #
# --------------------------------------------------------------------------- #
 
def gnews_url(query: str) -> str:
    return ("https://news.google.com/rss/search?q="
            + urllib.parse.quote(query)
            + "&hl=en-GB&gl=GB&ceid=GB:en")
 
 
def fetch_feed(url: str):
    """Fetch + parse a feed with retries. Returns feedparser dict or None."""
    for attempt in range(MAX_RETRIES + 1):
        try:
            req = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
            raw = urllib.request.urlopen(req, timeout=REQUEST_TIMEOUT).read()
            return feedparser.parse(raw)
        except Exception as exc:  # noqa: BLE001
            if attempt < MAX_RETRIES:
                time.sleep(2 ** attempt)
            else:
                print(f"      ! feed failed ({exc}) -> {url[:90]}")
                return None
 
 
def polite_pause():
    time.sleep(random.uniform(GNEWS_MIN_DELAY, GNEWS_MAX_DELAY))
 
 
# --------------------------------------------------------------------------- #
# PARSING HELPERS                                                              #
# --------------------------------------------------------------------------- #
 
def clean_text(s: str) -> str:
    if not s:
        return ""
    s = re.sub(r"<[^>]+>", " ", s)          # strip HTML tags from summaries
    s = html.unescape(s)
    return re.sub(r"\s+", " ", s).strip()
 
 
def entry_source(entry, default_title: str, default_source: str = "") -> str:
    """Best-effort publication name."""
    src = entry.get("source")
    if src and getattr(src, "title", None):
        return src.title.strip()
    # Google News titles end with ' - Publication'
    if " - " in default_title:
        return default_title.rsplit(" - ", 1)[-1].strip()
    return default_source
 
 
def entry_date(entry) -> str:
    for key in ("published_parsed", "updated_parsed"):
        t = entry.get(key)
        if t:
            return datetime(*t[:6], tzinfo=timezone.utc).date().isoformat()
    return date.today().isoformat()
 
 
def tidy_summary(summary: str, title: str, source: str) -> str:
    """Google News / feed summaries often echo the title and source (in either
    order). Strip leading echoes so cards show real excerpt text, else nothing."""
    if not summary:
        return ""
    s = summary.strip()
    t = title.strip()
    for _ in range(4):  # peel title/source prefixes in whatever order they appear
        before = s
        if t and s.lower().startswith(t.lower()):
            s = s[len(t):].lstrip(" -–|:·")
        if source and s.lower().startswith(source.lower()):
            s = s[len(source):].lstrip(" -–|:·")
        if s == before:
            break
    s = s.strip()
    return s if len(s) >= 25 else ""
 
 
# --------------------------------------------------------------------------- #
# RELEVANCE, GEOTAGGING, CATEGORISATION                                        #
# --------------------------------------------------------------------------- #
 
_NORMALISE_MAP = str.maketrans({
    "\u2019": "'", "\u2018": "'", "\u201c": '"', "\u201d": '"',
    "\u2013": "-", "\u2014": "-",
})
 
 
def normalise(s: str) -> str:
    """Lowercase and flatten curly quotes/dashes so keyword matching is reliable
    (e.g. 'Renters' Rights' with a typographic apostrophe still matches)."""
    return (s or "").translate(_NORMALISE_MAP).lower()
 
 
# Nation-level signals — used only when a story names no specific authority, to
# separate Wales-wide and England-wide stories from genuinely UK-wide ones.
WALES_SIGNALS = [
    "wales", "welsh", "cymru", "rent smart wales", "renting homes",
    "occupation contract", "senedd", "welsh government", "section 173",
]
ENGLAND_SIGNALS = [
    "england", "english", "selective licensing", "additional licensing",
    "article 4", "renters' rights act", "renters rights act",
    "section 21", "section 8",
]
 
 
def nation_signal(text_lc: str):
    """Return 'Wales', 'England', or None for an un-geotagged story.
    A story signalling both nations (comparative) stays cross-cutting."""
    w = any(t in text_lc for t in WALES_SIGNALS)
    e = any(t in text_lc for t in ENGLAND_SIGNALS)
    if w and not e:
        return "Wales"
    if e and not w:
        return "England"
    return None
 
 
def score_relevance(text_lc: str):
    """Return (is_relevant, score). Score is for ranking only."""
    context_hits = {t for t in PRS_CONTEXT_TERMS if t in text_lc}
    high_hits = {t for t in PRS_HIGH_SIGNAL_TERMS if t in text_lc}
    score = len(high_hits) * 3 + len(context_hits)
    relevant = bool(high_hits) or len(context_hits) >= 2
    return relevant, score
 
 
def categorise(text_lc: str):
    matched = []
    for label, terms in CATEGORY_RULES:
        if any(t in text_lc for t in terms):
            matched.append(label)
    if not matched:
        matched = [DEFAULT_CATEGORY]
    return matched[0], matched
 
 
def build_geo_index(authorities):
    """Map each match-term -> authority record, longest terms first."""
    index = []
    for a in authorities:
        terms = [a["name"]] + a.get("aliases", [])
        for t in terms:
            if len(t) >= 3:
                index.append((normalise(t), a))
    index.sort(key=lambda x: len(x[0]), reverse=True)
    return index
 
 
def geotag(text, geo_index):
    """Return list of matched authority records (word-boundary matched)."""
    text_lc = normalise(text)
    matched, seen = [], set()
    for term_lc, a in geo_index:
        if a["code"] in seen:
            continue
        if re.search(r"\b" + re.escape(term_lc) + r"\b", text_lc):
            matched.append(a)
            seen.add(a["code"])
    return matched
 
 
# --------------------------------------------------------------------------- #
# DATABASE                                                                     #
# --------------------------------------------------------------------------- #
 
def open_db(path):
    con = sqlite3.connect(path)
    con.execute("""
        CREATE TABLE IF NOT EXISTS articles (
            id            INTEGER PRIMARY KEY AUTOINCREMENT,
            guid          TEXT UNIQUE,
            url           TEXT,
            title         TEXT,
            source        TEXT,
            published     TEXT,
            first_seen    TEXT,
            summary       TEXT,
            nation        TEXT,
            region        TEXT,
            primary_la    TEXT,
            all_las       TEXT,
            category      TEXT,
            all_categories TEXT,
            score         REAL,
            fetch_method  TEXT
        )""")
    con.execute("CREATE INDEX IF NOT EXISTS idx_pub    ON articles(published)")
    con.execute("CREATE INDEX IF NOT EXISTS idx_region ON articles(region)")
    con.execute("CREATE INDEX IF NOT EXISTS idx_nation ON articles(nation)")
    con.execute("CREATE INDEX IF NOT EXISTS idx_cat    ON articles(category)")
    con.execute("CREATE TABLE IF NOT EXISTS meta (key TEXT PRIMARY KEY, value TEXT)")
    con.commit()
    return con
 
 
def load_existing(con):
    guids = {r[0] for r in con.execute("SELECT guid FROM articles")}
    titles = [(r[0], r[1]) for r in con.execute(
        "SELECT title, source FROM articles WHERE first_seen >= ?",
        ((date.today() - timedelta(days=7)).isoformat(),))]
    return guids, titles
 
 
def is_fuzzy_dupe(title, source, recent_titles, threshold=90):
    for t, s in recent_titles:
        if fuzz.token_sort_ratio(title, t) >= threshold:
            return True
    return False
 
 
# --------------------------------------------------------------------------- #
# MAIN PIPELINE                                                                #
# --------------------------------------------------------------------------- #
 
def process_entries(entries, fetch_method, geo_index, seen_guids,
                     recent_titles, batch_titles, default_source=""):
    """Score, geotag, categorise. Return list of row dicts to insert."""
    rows = []
    for e in entries:
        title = clean_text(e.get("title", ""))
        if not title:
            continue
        guid = e.get("id") or e.get("link") or title
        if guid in seen_guids:
            continue
        summary = clean_text(e.get("summary", ""))
        source = entry_source(e, title, default_source)
        # Strip the ' - Publication' suffix Google News appends to titles.
        display_title = title
        if source and display_title.endswith(" - " + source):
            display_title = display_title[: -(len(source) + 3)].strip()
 
        # Rolling window: skip anything published before the cutoff so the
        # database stays a genuine last-N-days view (Google News will otherwise
        # backfill years of archive on the first run).
        published = entry_date(e)
        if published < WINDOW_CUTOFF:
            continue
 
        haystack = normalise(display_title + " " + summary)
        relevant, score = score_relevance(haystack)
        if not relevant:
            continue
 
        # Cross-source duplicate guard (syndicated stories).
        if (is_fuzzy_dupe(display_title, source, recent_titles)
                or is_fuzzy_dupe(display_title, source, batch_titles)):
            continue
 
        las = geotag(display_title + " " + summary, geo_index)
 
        # Curated feeds are national trade/gov sources. If an item doesn't map
        # to a specific authority, only keep it when it carries a high-signal
        # term, so genuine national developments come through but routine
        # national blog chatter doesn't swamp the local stories.
        if fetch_method == "feed" and not las:
            if not any(t in haystack for t in PRS_HIGH_SIGNAL_TERMS):
                continue
 
        if las:
            nations = sorted({a["nation"] for a in las})
            regions = sorted({a["region"] for a in las})
            nation = nations[0] if len(nations) == 1 else "England & Wales"
            region = regions[0] if len(regions) == 1 else "Multiple regions"
            primary_la = las[0]["name"]
            all_las = [a["name"] for a in las]
        else:
            if nation_signal(haystack) == "Wales":
                nation, region = "Wales", "Wales (national)"
            else:
                nation, region = "National / cross-cutting", "National / cross-cutting"
            primary_la, all_las = "", []
 
        category, all_cats = categorise(haystack)
        seen_guids.add(guid)
        batch_titles.append((display_title, source))
        rows.append({
            "guid": guid, "url": e.get("link", ""), "title": display_title,
            "source": source, "published": published,
            "first_seen": date.today().isoformat(),
            "summary": tidy_summary(summary, display_title, source),
            "nation": nation, "region": region, "primary_la": primary_la,
            "all_las": json.dumps(all_las), "category": category,
            "all_categories": json.dumps(all_cats), "score": score,
            "fetch_method": fetch_method,
        })
    return rows
 
 
def insert_rows(con, rows):
    con.executemany("""
        INSERT OR IGNORE INTO articles
        (guid,url,title,source,published,first_seen,summary,nation,region,
         primary_la,all_las,category,all_categories,score,fetch_method)
        VALUES
        (:guid,:url,:title,:source,:published,:first_seen,:summary,:nation,
         :region,:primary_la,:all_las,:category,:all_categories,:score,
         :fetch_method)""", rows)
    con.commit()
 
 
def prune(con):
    cutoff = (date.today() - timedelta(days=RETENTION_DAYS)).isoformat()
    cur = con.execute("DELETE FROM articles WHERE published < ?", (cutoff,))
    con.commit()
    return cur.rowcount
 
 
def main():
    spine = json.load(open(AUTHORITIES_PATH, encoding="utf-8"))
    authorities = spine["authorities"]
    if MAX_AUTHORITIES:
        authorities = authorities[:MAX_AUTHORITIES]
    geo_index = build_geo_index(spine["authorities"])
 
    con = open_db(DB_PATH)
    seen_guids, recent_titles = load_existing(con)
    batch_titles, all_new = [], []
 
    print(f"== NRLA PRS news monitor | {datetime.now().isoformat(timespec='seconds')} ==")
    print(f"   DB={DB_PATH}  retention={RETENTION_DAYS}d  authorities={len(authorities)}")
 
    # 1. National theme sweeps -------------------------------------------------
    print(f"\n[1/3] Theme sweeps ({len(THEME_QUERIES)})")
    for q in THEME_QUERIES:
        d = fetch_feed(gnews_url(q))
        if d:
            new = process_entries(d.entries, "theme", geo_index, seen_guids,
                                  recent_titles, batch_titles)
            all_new += new
            print(f"      • {q[:45]:<47} +{len(new)}")
        polite_pause()
 
    # 2. Geographic sweeps -----------------------------------------------------
    print(f"\n[2/3] Geographic sweeps ({len(authorities)} authorities)")
    failures = 0
    for i, a in enumerate(authorities, 1):
        names = [a["name"]] + [x for x in a.get("aliases", []) if len(x) > 3]
        name_clause = " OR ".join(f'"{n}"' for n in names[:4])
        terms = GEO_QUERY_TERMS_WALES if a["nation"] == "Wales" else GEO_QUERY_TERMS
        query = f'({terms}) ({name_clause})'
        d = fetch_feed(gnews_url(query))
        if d is None:
            failures += 1
        else:
            new = process_entries(d.entries, "geographic", geo_index,
                                  seen_guids, recent_titles, batch_titles)
            all_new += new
            if new:
                print(f"      • [{i}/{len(authorities)}] {a['name']:<32} +{len(new)}")
        polite_pause()
 
    # 3. Curated feeds ---------------------------------------------------------
    print(f"\n[3/3] Curated feeds ({len(CURATED_FEEDS)})")
    for name, url in CURATED_FEEDS:
        d = fetch_feed(url)
        if d:
            new = process_entries(d.entries, "feed", geo_index, seen_guids,
                                  recent_titles, batch_titles, default_source=name)
            all_new += new
            print(f"      • {name:<40} +{len(new)}")
 
    # Persist ------------------------------------------------------------------
    insert_rows(con, all_new)
    pruned = prune(con)
    total = con.execute("SELECT COUNT(*) FROM articles").fetchone()[0]
    con.execute("INSERT OR REPLACE INTO meta VALUES ('last_run', ?)",
                (datetime.now(timezone.utc).isoformat(timespec="seconds"),))
    con.execute("INSERT OR REPLACE INTO meta VALUES ('last_added', ?)",
                (str(len(all_new)),))
    con.commit()
    con.close()
 
    print(f"\n== Done. Added {len(all_new)} | pruned {pruned} | "
          f"DB total {total} | geo failures {failures} ==")
 
 
if __name__ == "__main__":
    main()
 
