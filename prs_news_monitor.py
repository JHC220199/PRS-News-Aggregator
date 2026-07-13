#!/usr/bin/env python3
"""
NRLA PRS news — daily email digest generator
=============================================
Reads the same prs_news.db the dashboard uses, selects the stories first seen
since the last digest, ran#!/usr/bin/env python3
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
 
# Sources whose entire output is PRS-relevant by definition (single-purpose
# regulators, not broad trade blogs) — exempted from the high-signal-only bar
# applied to other national feed items with no specific authority.
SINGLE_PURPOSE_PRS_SOURCES = {"Rent Smart Wales"}
# Sources that are inherently Welsh regardless of whether a story's own text
# happens to say "Wales" — used to tag un-geotagged items from that source.
WALES_ONLY_SOURCES = {"Rent Smart Wales"}
 
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
 
 
# --- Article-body geotag enrichment ------------------------------------------
# Some stories name their place only in the article body (e.g. a Yahoo News
# syndication of an Argus piece: title "New licensing rules to affect private
# landlords from October", empty RSS summary, Brighton only in paragraph one).
# For relevant stories that end up un-geotagged, we fetch the opening
# paragraphs of the article itself and geotag on those. Google News URLs are
# opaque redirects, so they're first decoded via Google's internal endpoint —
# a fragile-by-nature dependency, wrapped so failures degrade to the current
# behaviour (story stays national) rather than breaking the run.
 
BODY_FETCH_MAX = int(os.environ.get("PRS_BODY_FETCH_MAX", "20"))
 
 
def decode_gnews_url(url: str):
    """Resolve a news.google.com/rss/articles/ redirect to the publisher URL.
    Returns None if the URL isn't a GN redirect or decoding fails."""
    if "news.google.com" not in url or "/articles/" not in url:
        return url  # already a direct publisher link
    try:
        gid = url.split("/articles/")[1].split("?")[0]
        req = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
        page = urllib.request.urlopen(req, timeout=REQUEST_TIMEOUT).read().decode(
            "utf-8", "ignore")
        sg = re.search(r'data-n-a-sg="([^"]+)"', page)
        ts = re.search(r'data-n-a-ts="([^"]+)"', page)
        if not (sg and ts):
            return None
        inner = json.dumps([
            "garturlreq",
            [["en-GB", "GB", ["FINANCE_TOP_INDICES", "WEB_TEST_1_0_0"],
              None, None, 1, 1, "GB:en", None, 180, None, None, None, None,
              None, 0, None, None, [1608992183, 723341000]],
             "en-GB", "GB", 1, [2, 3, 4, 8], 1, 0, "655000234", 0, 0, None, 0],
            gid, int(ts.group(1)), sg.group(1)])
        freq = json.dumps([[["Fbv4je", inner, None, "generic"]]])
        data = urllib.parse.urlencode({"f.req": freq}).encode()
        req = urllib.request.Request(
            "https://news.google.com/_/DotsSplashUi/data/batchexecute",
            data=data,
            headers={"User-Agent": USER_AGENT,
                     "Content-Type": "application/x-www-form-urlencoded;charset=UTF-8"})
        resp = urllib.request.urlopen(req, timeout=REQUEST_TIMEOUT).read().decode(
            "utf-8", "ignore")
        candidates = [u for u in re.findall(r'https?://[^"\\\s]+', resp)
                      if "google" not in u and "gstatic" not in u]
        return candidates[0] if candidates else None
    except Exception:  # noqa: BLE001
        return None
 
 
def fetch_article_lead(url: str, max_chars: int = 1800):
    """Fetch an article page and return the opening of its actual article text.
    Tries, in order: JSON-LD articleBody (cleanest, most news sites embed it);
    paragraphs inside the <article> element; paragraphs after the <h1>. Plain
    whole-page <p> scraping is deliberately NOT used — it harvests nav menus
    (which contain words like 'Rugby' that collide with authority names).
    Returns '' on any failure."""
    try:
        req = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
        page = urllib.request.urlopen(req, timeout=REQUEST_TIMEOUT).read(500_000)
        page = page.decode("utf-8", "ignore")
    except Exception:  # noqa: BLE001
        return ""
 
    # 1) JSON-LD articleBody
    for m in re.finditer(
            r'<script[^>]+application/ld\+json[^>]*>(.*?)</script>', page, re.S):
        try:
            data = json.loads(m.group(1))
        except Exception:  # noqa: BLE001
            continue
        items = data if isinstance(data, list) else [data]
        for item in items:
            if isinstance(item, dict) and item.get("articleBody"):
                return clean_text(item["articleBody"])[:max_chars]
 
    def paras(fragment):
        out = []
        for pm in re.finditer(r"<p[^>]*>(.*?)</p>", fragment, re.S):
            text = clean_text(pm.group(1))
            if len(text) < 40:
                continue
            out.append(text)
            if sum(len(x) for x in out) >= max_chars:
                break
        return " ".join(out)[:max_chars]
 
    # 2) Inside the <article> element
    am = re.search(r"<article[^>]*>(.*?)</article>", page, re.S)
    if am:
        text = paras(am.group(1))
        if text:
            return text
 
    # 3) Paragraphs after the <h1> (skips header/nav that precede it)
    hm = re.search(r"</h1>", page)
    if hm:
        return paras(page[hm.end():])
    return ""
 
 
def enrich_geotag_from_body(con, geo_index):
    """For un-geotagged stories, fetch the article body and geotag on its
    opening paragraphs. Capped per run; each URL is attempted once (tracked via
    body_checked) so failures don't retry forever. A story is only tagged when
    the body names one or two authorities — three or more means it's a national
    round-up citing examples, which should stay national."""
    rows = con.execute(
        """SELECT id,url,title FROM articles
           WHERE primary_la='' AND body_checked=0 AND url!=''
           ORDER BY first_seen DESC, published DESC LIMIT ?""",
        (BODY_FETCH_MAX,)).fetchall()
    tagged = 0
    for rid, url, title in rows:
        real = decode_gnews_url(url)
        lead = fetch_article_lead(real) if real else ""
        con.execute("UPDATE articles SET body_checked=1 WHERE id=?", (rid,))
        if lead:
            las = geotag(lead, geo_index)
            if las and len(las) <= 2:
                a = las[0]
                con.execute(
                    """UPDATE articles SET nation=?, region=?, primary_la=?,
                       all_las=? WHERE id=?""",
                    (a["nation"], a["region"], a["name"],
                     json.dumps([x["name"] for x in las]), rid))
                tagged += 1
        time.sleep(random.uniform(0.5, 1.0))
    con.commit()
    return len(rows), tagged
 
 
class _FakeEntry(dict):
    """Minimal feedparser-entry-alike so scraped sources can flow through the
    same process_entries() pipeline as real feeds."""
    def get(self, key, default=None):
        return dict.get(self, key, default)
 
 
_RSW_ARTICLE_RE = re.compile(
    r'<h[23] class="article-item-title">\s*<a[^>]*href="(?P<href>/en/news/\d+/[^"]+)"'
    r'[^>]*>(?P<title>[^<]+)</a></h[23]>\s*'
    r'<span class="article-time">\s*(?P<date>\d{1,2} \w+ \d{4})</span>',
    re.S)
 
 
def fetch_rent_smart_wales_news():
    """Rent Smart Wales publishes PRS news but exposes no RSS/Atom feed, so this
    scrapes the news listing page directly and returns feedparser-alike entries.
    If the site's markup changes this degrades to zero entries rather than
    erroring the whole run (caught by the caller like any other feed failure)."""
    url = "https://rentsmart.gov.wales/en/news/"
    req = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
    raw = urllib.request.urlopen(req, timeout=REQUEST_TIMEOUT).read().decode(
        "utf-8", "ignore")
    entries = []
    for m in _RSW_ARTICLE_RE.finditer(raw):
        title = html.unescape(m.group("title")).strip()
        href = "https://rentsmart.gov.wales" + m.group("href")
        try:
            dt = datetime.strptime(m.group("date"), "%d %b %Y")
        except ValueError:
            continue
        entries.append(_FakeEntry(
            title=title, link=href,
            published_parsed=dt.replace(tzinfo=timezone.utc).timetuple(),
            summary="", id=href))
 
    class _FakeFeed:
        pass
    feed = _FakeFeed()
    feed.entries = entries
    return feed
 
 
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
    "\u2013": "-", "\u2014": "-", "&": " and ",
})
 
 
def normalise(s: str) -> str:
    """Lowercase, flatten curly quotes/dashes and expand '&' to 'and' so keyword
    and place-name matching is reliable (e.g. 'Renters' Rights' with a
    typographic apostrophe, or 'Brighton & Hove' vs 'Brighton and Hove')."""
    s = (s or "").translate(_NORMALISE_MAP).lower()
    return re.sub(r"\s+", " ", s)
 
 
def _signal_match(text_lc: str, terms) -> bool:
    """Match any term, using word boundaries for plain-word terms so short
    tokens like 'usa' don't match inside 'thousands' or 'crusade'. Terms with
    non-word characters ('$', 'u.s.', 'buy-to-let', 'new york') match as
    substrings, which is already safe."""
    for t in terms:
        if re.search(r"[^\w]", t):
            if t in text_lc:
                return True
        elif re.search(r"\b" + re.escape(t) + r"\b", text_lc):
            return True
    return False
 
 
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
    w = _signal_match(text_lc, WALES_SIGNALS)
    e = _signal_match(text_lc, ENGLAND_SIGNALS)
    if w and not e:
        return "Wales"
    if e and not w:
        return "England"
    return None
 
 
# Geographic scope guard — the tool covers England and Wales only. Generic
# theme/feed queries occasionally surface US, Scottish or Irish stories (e.g. a
# US "renter rights" piece). A story is dropped if it carries a clear
# out-of-scope signal and no countervailing UK signal.
FOREIGN_SIGNALS = [
    # United States
    "$", "us$", "u.s.", "usa", "united states", "america", "american",
    "california", "texas", "florida", "illinois", "new york", "new jersey",
    "massachusetts", "pennsylvania", "ohio", "michigan", "arizona", "colorado",
    "north carolina", "minnesota", "oregon", "nevada", "chicago", "los angeles",
    "san francisco", "houston", "philadelphia", "seattle", "las vegas", "miami",
    "atlanta", "denver", "phoenix", "dallas", "baltimore", "detroit",
    "brooklyn", "manhattan", "hud",
    # Other UK nations / Ireland (out of scope for this tool)
    "scotland", "scottish", "holyrood", "edinburgh", "glasgow", "aberdeen",
    "dundee", "northern ireland", "stormont", "belfast",
    "republic of ireland", "dublin",
    # Other
    "canada", "toronto", "vancouver", "australia", "sydney", "melbourne",
    "new zealand", "auckland",
]
# Distinctively UK/England-&-Wales terms that rescue an otherwise ambiguous item
# (these rarely appear in non-UK coverage).
UK_SIGNALS = [
    "uk", "u.k.", "united kingdom", "britain", "british", "england", "english",
    "wales", "welsh", "cymru", "senedd", "westminster", "whitehall", "gov.uk",
    "mhclg", "\u00a3", "rent smart wales", "renting homes", "selective licensing",
    "additional licensing", "hmo", "house in multiple occupation", "section 21",
    "section 173", "section 8", "renters' rights", "right to rent", "leasehold",
    "rent repayment order", "banning order", "article 4", "epc", "awaab",
    "rightmove", "zoopla", "london", "buy-to-let", "buy to let", "lettings",
    "letting agent", "tenancy deposit", "council tax",
]
 
 
def in_scope(text_lc: str, has_authority: bool = False) -> bool:
    """True unless the text clearly points outside England and Wales. A story
    that maps to a real E&W authority is always in scope."""
    if has_authority:
        return True
    if _signal_match(text_lc, FOREIGN_SIGNALS):
        return _signal_match(text_lc, UK_SIGNALS)
    return True
 
 
# Out-of-jurisdiction filter. The tool covers England and Wales only, but broad
# Google News theme queries occasionally return US ("renter rights"), Scottish,
# or other coverage. Country-level signals are always disqualifying; state/city
# signals only disqualify when the story hasn't anchored to an E&W authority
# (so we don't wrongly drop, say, a story that genuinely names an English town).
_FOREIGN_STRONG = re.compile(
    r"\b(united states|u\.?s\.?a\.?|u\.s\.|americans?|scotland|scottish|holyrood|"
    r"northern ireland|stormont|republic of ireland|australia|australian|"
    r"new zealand|canada|canadian)\b")
_FOREIGN_WEAK = re.compile(
    r"\b(illinois|california|texas|florida|massachusetts|pennsylvania|ohio|"
    r"michigan|minnesota|wisconsin|colorado|arizona|nevada|oregon|maryland|"
    r"virginia|tennessee|missouri|louisiana|kentucky|alabama|oklahoma|"
    r"connecticut|iowa|kansas|nebraska|utah|idaho|montana|wyoming|vermont|"
    r"indiana|delaware|arkansas|mississippi|new jersey|new york|new mexico|"
    r"north carolina|south carolina|north dakota|south dakota|west virginia|"
    r"rhode island|hawaii|alaska|chicago|los angeles|san francisco|brooklyn|"
    r"manhattan|seattle|denver|atlanta|dallas|houston|philadelphia|miami|"
    r"minneapolis|detroit|phoenix|las vegas|new orleans|"
    r"edinburgh|glasgow|aberdeen|dundee|belfast|dublin)\b")
 
 
def out_of_scope(text_lc: str, has_authority: bool) -> bool:
    if _FOREIGN_STRONG.search(text_lc):
        return True
    if not has_authority and _FOREIGN_WEAK.search(text_lc):
        return True
    return False
 
 
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
 
 
# --- Source-based geotag fallbacks ------------------------------------------
# Local outlets whose coverage is overwhelmingly about one home patch. Used
# ONLY as a last resort (no place in the story text) and ONLY when the story
# carries no national-scope signal. Keys are matched case-insensitively
# against the source name; values are canonical spine authority names.
# Extend freely as you spot more outlets.
OUTLET_HOME_PATCH = {
    "the argus": "Brighton and Hove",
    "brighton and hove news": "Brighton and Hove",
    "manchester evening news": "Manchester",
    "liverpool echo": "Liverpool",
    "birminghamlive": "Birmingham",
    "birmingham mail": "Birmingham",
    "chronicle live": "Newcastle upon Tyne",
    "chroniclelive": "Newcastle upon Tyne",
    "yorkshire evening post": "Leeds",
    "leeds live": "Leeds",
    "bristol post": "Bristol",
    "bristollive": "Bristol",
    "bristol live": "Bristol",
    "leicester mercury": "Leicester",
    "leicestershirelive": "Leicester",
    "nottingham post": "Nottingham",
    "nottinghamshirelive": "Nottingham",
    "hull live": "Kingston upon Hull",
    "hull daily mail": "Kingston upon Hull",
    "the northern echo": "County Durham",
    "oxford mail": "Oxford",
    "cambridge news": "Cambridge",
    "portsmouth news": "Portsmouth",
    "the news, portsmouth": "Portsmouth",
    "southern daily echo": "Southampton",
    "daily echo": "Southampton",
    "express and star": "Wolverhampton",
    "coventry telegraph": "Coventry",
    "coventrylive": "Coventry",
    "stokeontrentlive": "Stoke-on-Trent",
    "stoke sentinel": "Stoke-on-Trent",
    "the star, sheffield": "Sheffield",
    "sheffield star": "Sheffield",
    "teesside live": "Middlesbrough",
    "gazette live": "Middlesbrough",
    "lancashire telegraph": "Blackburn with Darwen",
    "the bolton news": "Bolton",
    "bolton news": "Bolton",
    "wigan today": "Wigan",
    "reading chronicle": "Reading",
    "swindon advertiser": "Swindon",
    "derby telegraph": "Derby",
    "derbyshire live": "Derby",
    "plymouth herald": "Plymouth",
    "plymouth live": "Plymouth",
    "norwich evening news": "Norwich",
    "ipswich star": "Ipswich",
    "south wales argus": "Newport",
    "south wales evening post": "Swansea",
    "wrexham leader": "Wrexham",
    "the leader, wrexham": "Wrexham",
    # Opaque council domains that don't contain the word "council" or a
    # matchable place name:
    "rbkc.gov.uk": "Kensington and Chelsea",
    "lbhf.gov.uk": "Hammersmith and Fulham",
}
 
# If a story carries any of these, it is plausibly national in scope, so the
# outlet fallback must NOT localise it (a local paper covering a national
# story keeps its national tag).
NATIONAL_STORY_SIGNALS = [
    "government", "minister", "ministers", "mps", "westminster", "whitehall",
    "chancellor", "prime minister", "downing street", "mhclg", "hmrc", "dwp",
    "ombudsman", "white paper", "consultation launched nationally", "bill",
    "royal assent", "national", "nationwide", "across england", "across wales",
    "across the country", "uk-wide", "england-wide",
]
 
 
def fallback_geotag(source, haystack, geo_index):
    """Geotag from the source when the story text names no place.
    Tier 1 — council sources (contain 'council' or end .gov.uk): councils only
    publish about their own area, so always safe.
    Tier 2 — known local outlets (OUTLET_HOME_PATCH): applied only when the
    story carries no national-scope signal."""
    if not source:
        return []
    src_lc = normalise(source)
    if "council" in src_lc or src_lc.strip().endswith(".gov.uk"):
        las = geotag(source, geo_index)
        if las:
            return las
        home = OUTLET_HOME_PATCH.get(src_lc.strip())
        return geotag(home, geo_index) if home else []
    home = OUTLET_HOME_PATCH.get(src_lc.strip())
    if home and not _signal_match(haystack, NATIONAL_STORY_SIGNALS):
        return geotag(home, geo_index)
    return []
 
 
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
            fetch_method  TEXT,
            body_checked  INTEGER DEFAULT 0
        )""")
    con.execute("CREATE INDEX IF NOT EXISTS idx_pub    ON articles(published)")
    con.execute("CREATE INDEX IF NOT EXISTS idx_region ON articles(region)")
    con.execute("CREATE INDEX IF NOT EXISTS idx_nation ON articles(nation)")
    con.execute("CREATE INDEX IF NOT EXISTS idx_cat    ON articles(category)")
    con.execute("CREATE TABLE IF NOT EXISTS meta (key TEXT PRIMARY KEY, value TEXT)")
    # Migration for databases created before body_checked existed.
    cols = [r[1] for r in con.execute("PRAGMA table_info(articles)")]
    if "body_checked" not in cols:
        con.execute("ALTER TABLE articles ADD COLUMN body_checked INTEGER DEFAULT 0")
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
 
        # Council newsrooms and local outlets often omit the place name from
        # headlines ("Council expands rental licensing scheme" — The Argus).
        # When the text yields no match, fall back to the source: councils
        # always map to their own area; known local outlets map to their home
        # patch only if the story carries no national-scope signal.
        if not las:
            las = fallback_geotag(source, haystack, geo_index)
 
        # Geographic scope: England and Wales only. Generic theme/feed queries
        # occasionally surface US/Scottish/Irish stories. A story that maps to an
        # actual E&W authority is in scope; otherwise drop it if it carries a
        # clear foreign signal and no UK signal. The source name often gives the
        # foreign story away (e.g. "Chicago Tribune"), so include it.
        scope_text = normalise(display_title + " " + summary + " " + source)
        if not in_scope(scope_text, bool(las)):
            continue
 
        # Curated feeds are national trade/gov sources. If an item doesn't map
        # to a specific authority, only keep it when it carries a high-signal
        # term, so genuine national developments come through but routine
        # national blog chatter doesn't swamp the local stories. Exempt
        # single-purpose PRS regulators (their whole output is on-topic, unlike
        # a broad trade blog) — the base relevance filter above already applies.
        if fetch_method == "feed" and not las and source not in SINGLE_PURPOSE_PRS_SOURCES:
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
            if nation_signal(haystack) == "Wales" or source in WALES_ONLY_SOURCES:
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
 
 
def purge_out_of_scope(con):
    """Retroactively remove rows that predate the geographic scope guard (e.g.
    US stories that slipped in before in_scope() existed). Only un-geotagged
    rows are re-checked — anything mapped to a real E&W authority is always
    kept, same rule as at ingest time. Cheap enough to run every day."""
    rows = con.execute(
        "SELECT id,title,summary,source FROM articles WHERE primary_la=''"
    ).fetchall()
    bad_ids = [
        rid for rid, t, s, src in rows
        if not in_scope(normalise(f"{t or ''} {s or ''} {src or ''}"), False)
    ]
    if bad_ids:
        con.executemany("DELETE FROM articles WHERE id=?", [(i,) for i in bad_ids])
        con.commit()
    return len(bad_ids)
 
 
def retag_from_council_source(con, geo_index):
    """Retroactively geotag rows stored before the source fallbacks existed:
    every un-geotagged row is re-run through fallback_geotag (council sources,
    .gov.uk domains, known local outlets with the national-signal guard) so
    e.g. an Argus licensing story stored as National moves to Brighton."""
    rows = con.execute(
        "SELECT id,title,summary,source FROM articles WHERE primary_la=''"
    ).fetchall()
    n = 0
    for rid, t, s, src in rows:
        haystack = normalise(f"{t or ''} {s or ''}")
        las = fallback_geotag(src or "", haystack, geo_index)
        if las:
            a = las[0]
            con.execute(
                """UPDATE articles SET nation=?, region=?, primary_la=?, all_las=?
                   WHERE id=?""",
                (a["nation"], a["region"], a["name"],
                 json.dumps([x["name"] for x in las]), rid))
            n += 1
    if n:
        con.commit()
    return n
 
 
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
    print(f"\n[3/3] Curated feeds ({len(CURATED_FEEDS)} feeds + Rent Smart Wales)")
    for name, url in CURATED_FEEDS:
        d = fetch_feed(url)
        if d:
            new = process_entries(d.entries, "feed", geo_index, seen_guids,
                                  recent_titles, batch_titles, default_source=name)
            all_new += new
            print(f"      • {name:<40} +{len(new)}")
 
    # Rent Smart Wales has no public RSS feed, so its news page is scraped
    # directly (see fetch_rent_smart_wales_news). Wrapped defensively so a
    # markup change on their site degrades to zero items, not a failed run.
    try:
        d = fetch_rent_smart_wales_news()
        new = process_entries(d.entries, "feed", geo_index, seen_guids,
                              recent_titles, batch_titles,
                              default_source="Rent Smart Wales")
        all_new += new
        print(f"      • {'Rent Smart Wales (scraped)':<40} +{len(new)}")
    except Exception as exc:  # noqa: BLE001
        print(f"      ! Rent Smart Wales scrape failed ({exc})")
 
    # Persist ------------------------------------------------------------------
    insert_rows(con, all_new)
    pruned = prune(con)
    purged = purge_out_of_scope(con)
    retagged = retag_from_council_source(con, geo_index)
    body_checked, body_tagged = enrich_geotag_from_body(con, geo_index)
    total = con.execute("SELECT COUNT(*) FROM articles").fetchone()[0]
    con.execute("INSERT OR REPLACE INTO meta VALUES ('last_run', ?)",
                (datetime.now(timezone.utc).isoformat(timespec="seconds"),))
    con.execute("INSERT OR REPLACE INTO meta VALUES ('last_added', ?)",
                (str(len(all_new)),))
    con.commit()
    con.close()
 
    print(f"\n== Done. Added {len(all_new)} | pruned {pruned} | "
          f"out-of-scope purged {purged} | council-retagged {retagged} | "
          f"body-checked {body_checked} (geotagged {body_tagged}) | "
          f"DB total {total} | geo failures {failures} ==")
 
 
if __name__ == "__main__":
    main()
 ks them editorially, and renders an Outlook-safe HTML
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
 
