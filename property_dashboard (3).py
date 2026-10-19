#!/usr/bin/env python3
"""
Property Dashboard for Rightmove + Zoopla
------------------------------------------
Builds a sortable/filterable local dashboard from your own saved
searches: real square footage, tenure, lease years, EPC, council tax
band, service charge, ground rent, and per-area peer-group averages
(price/sqft, sqft) so you can spot good value at a glance.

SETUP
1. pip install requests beautifulsoup4 lxml
2. On Rightmove/Zoopla, set your search normally: location or postcode,
   price, beds. For commute-based search, use Rightmove's "My Places"
   or Zoopla's travel-time search tool FIRST, then copy the resulting
   URL below — this script doesn't calculate commute itself.
3. Paste the search URL(s) into SEARCHES, one per area.
4. Run: python property_dashboard.py
5. Open dashboard.html in your browser.

NOTES
- Rightmove's terms of service prohibit scraping their content. This
  script is for light, personal, infrequent use only — not for
  redistribution or high-volume/commercial use.
- Zoopla uses stronger bot protection than Rightmove and may block
  requests outright regardless of headers used here. If Zoopla runs
  keep failing, that's the likely reason, not a bug in this script.
"""

import datetime
import html as htmllib
import json
import os
import re
import sqlite3
import sys
import time
from pathlib import Path
from urllib.parse import urlsplit, urlunsplit, parse_qsl, urlencode

import requests
from bs4 import BeautifulSoup

# ---------------------------------------------------------------------
# 1. PASTE YOUR SEARCH URLS HERE — one per area
# ---------------------------------------------------------------------
# Zoopla is dropped: it actively blocks non-browser requests (403 on
# every request, not intermittent), so it isn't included here.
# Rightmove only, for now.
SEARCHES = {
    "rightmove": {
        "Canary Wharf": "",
        "Greenwich": "",
        "Wembley": "",
        "West Hampstead": "",
    },
}

# Paste individual listing URLs here for ones you specifically want to
# keep tracking regardless of whether they're still in the search
# results' top 100 — e.g. a place you're seriously considering.
# These get rechecked every run no matter what.
WATCHLIST = [
    # "https://www.rightmove.co.uk/properties/123456789",
]

# ---- Cloud mode (GitHub Actions) ------------------------------------
# In the cloud, search URLs come from secrets so they aren't in the
# public repo. SEARCHES env: one "Area | URL" per line. WATCHLIST env:
# one listing URL per line. Locally these env vars are simply unset.
CLOUD_RUN = bool(os.environ.get("CLOUD_RUN"))
if os.environ.get("SEARCHES", "").strip():
    SEARCHES = {"rightmove": {}}
    for _line in os.environ["SEARCHES"].splitlines():
        if "|" in _line:
            _area, _url = _line.split("|", 1)
            if _area.strip() and _url.strip():
                SEARCHES["rightmove"][_area.strip()] = _url.strip()
if os.environ.get("WATCHLIST", "").strip():
    WATCHLIST = [u.strip() for u in os.environ["WATCHLIST"].split() if u.strip()]

MAX_LISTINGS_PER_SEARCH = 100    # paginates to reach this — see note below
REQUEST_DELAY_SECONDS = 2.5      # politeness delay between requests
MAX_PAGES_PER_SEARCH = 8         # hard safety cap on pagination
STALE_AFTER_DAYS = 7             # flag as "stale" if not re-seen within this many days
ARCHIVE_AFTER_DAYS = 21          # auto-remove from the dashboard after this long unseen
AGING_RECHECK_COUNT = 10         # each run, also directly recheck this many of the
                                 # oldest-unseen tracked listings that fell out of the
                                 # search results entirely — keeps long-tail listings'
                                 # prices from going stale forever without needing a
                                 # manual watchlist entry. Adds this many extra detail-
                                 # page fetches per run; set to 0 to disable.
DAILY_SEARCH_LIMIT = 4           # recommended max location searches per 24h
# Note: 4 areas x 1 site (Rightmove only), run once every few days.
# What's risky isn't the count, it's hammering the same search
# repeatedly in a short window — this script's delays already guard
# against that.
#
# On MAX_LISTINGS_PER_SEARCH: searches now sort "newest first"
# automatically (see set_query_param below), so raising this past 100
# mostly buys you *older* listings you're less likely to want, not
# newer ones — new listings are always captured first regardless of
# the cap. Raising it also multiplies request volume directly (each
# extra listing = one more detail-page fetch), so a jump to 250 means
# roughly 2.5x the requests and runtime per area. If you still want
# full coverage, raise this and MAX_PAGES_PER_SEARCH together, but
# expect a much longer run and higher block risk.

# ---------------------------------------------------------------------
# 2. KEYWORD RULES
# ---------------------------------------------------------------------
FIXER_UPPER_INCLUDE = [
    "needs updating", "needs modernising", "requires modernisation",
    "in need of refurbishment", "cosmetic", "no onward chain",
    "renovation project", "improvement", "dated throughout",
]
FIXER_UPPER_EXCLUDE = [
    "subsidence", "structural repair", "structural work required",
    "unmortgageable", "cash buyers only", "collapsed", "underpinning",
]
UNIQUE_KEYWORDS = [
    "warehouse", "converted", "loft", "barn conversion", "industrial",
    "mill", "unusual", "character property", "church conversion",
    "school conversion",
]
BIG_LIVING_KEYWORDS = [
    "bay window", "floor-to-ceiling", "open plan", "double aspect",
    "vaulted ceiling", "high ceiling", "exposed beams", "mezzanine",
]

HEADERS = {
    "User-Agent": (
        "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
        "(KHTML, like Gecko) Chrome/124.0 Safari/537.36"
    ),
    "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,image/webp,*/*;q=0.8",
    "Accept-Language": "en-GB,en;q=0.9",
    "Connection": "keep-alive",
    "Upgrade-Insecure-Requests": "1",
}

DATA_DIR = Path(os.environ.get("DATA_DIR") or Path(__file__).parent)
DATA_DIR.mkdir(parents=True, exist_ok=True)
DATA_FILE = DATA_DIR / "listings.json"
HTML_FILE = DATA_DIR / os.environ.get("HTML_NAME", "dashboard.html")
SEARCH_LOG_FILE = DATA_DIR / "search_log.json"
DB_FILE = DATA_DIR / "properties.db"
CHANGES_FILE = DATA_DIR / "changes.txt"


# ---------------------------------------------------------------------
# Daily limit tracking
# ---------------------------------------------------------------------
def check_daily_limit(num_searches_about_to_run, auto_mode=False):
    now = datetime.datetime.now()
    cutoff = now - datetime.timedelta(hours=24)

    log = []
    if SEARCH_LOG_FILE.exists():
        log = json.loads(SEARCH_LOG_FILE.read_text(encoding="utf-8"))

    recent = [t for t in log if datetime.datetime.fromisoformat(t) > cutoff]
    total_after = len(recent) + num_searches_about_to_run

    if total_after > DAILY_SEARCH_LIMIT:
        print(
            f"\n⚠️  You've run {len(recent)} location search(es) in the last "
            f"24 hours. This run adds {num_searches_about_to_run} more, for "
            f"{total_after} total — above the recommended limit of "
            f"{DAILY_SEARCH_LIMIT}.\n"
            "Running too many in one day raises the chance of getting "
            "rate-limited or temporarily blocked.\n"
        )
        if auto_mode:
            print("Running in auto mode — continuing without asking.\n")
            return True
        answer = input("Continue anyway? (y/n): ").strip().lower()
        if answer != "y":
            print("Stopped. Try again later.")
            return False

    return True


def log_search_run(num_searches):
    log = []
    if SEARCH_LOG_FILE.exists():
        log = json.loads(SEARCH_LOG_FILE.read_text(encoding="utf-8"))
    now = datetime.datetime.now()
    log.extend([now.isoformat()] * num_searches)
    cutoff = now - datetime.timedelta(days=7)
    log = [t for t in log if datetime.datetime.fromisoformat(t) > cutoff]
    SEARCH_LOG_FILE.write_text(json.dumps(log, indent=2), encoding="utf-8")


# ---------------------------------------------------------------------
# Database
# ---------------------------------------------------------------------
def init_db():
    conn = sqlite3.connect(DB_FILE)
    conn.execute("""
        CREATE TABLE IF NOT EXISTS listings (
            url TEXT PRIMARY KEY,
            source TEXT,
            area TEXT,
            title TEXT,
            price INTEGER,
            initial_price INTEGER,
            sqft INTEGER,
            price_per_sqft INTEGER,
            bedrooms INTEGER,
            bathrooms INTEGER,
            tenure TEXT,
            lease_years_remaining INTEGER,
            epc_rating TEXT,
            council_tax_band TEXT,
            service_charge_annual INTEGER,
            ground_rent_annual INTEGER,
            is_reduced INTEGER,
            is_sstc INTEGER,
            floorplan_url TEXT,
            added_date TEXT,
            is_watchlisted INTEGER,
            tags TEXT,
            first_seen TEXT,
            last_seen TEXT
        )
    """)
    existing_cols = {row[1] for row in conn.execute("PRAGMA table_info(listings)")}
    new_cols = [
        ("area", "TEXT"), ("bedrooms", "INTEGER"), ("bathrooms", "INTEGER"),
        ("tenure", "TEXT"), ("lease_years_remaining", "INTEGER"),
        ("epc_rating", "TEXT"), ("council_tax_band", "TEXT"),
        ("service_charge_annual", "INTEGER"), ("ground_rent_annual", "INTEGER"),
        ("is_reduced", "INTEGER"), ("is_sstc", "INTEGER"), ("floorplan_url", "TEXT"),
        ("added_date", "TEXT"), ("is_watchlisted", "INTEGER"),
    ]
    for col, coltype in new_cols:
        if col not in existing_cols:
            conn.execute(f"ALTER TABLE listings ADD COLUMN {col} {coltype}")
    conn.commit()
    return conn


UPSERT_FIELDS = [
    "source", "area", "title", "price", "sqft", "price_per_sqft",
    "bedrooms", "bathrooms", "tenure", "lease_years_remaining",
    "epc_rating", "council_tax_band", "service_charge_annual",
    "ground_rent_annual", "is_reduced", "is_sstc", "floorplan_url",
    "added_date", "is_watchlisted",
]


def upsert_listing(conn, record):
    """Insert if new, update tracked fields if already known.
    is_watchlisted is sticky: once true, a later run that finds this
    listing via a normal area search (which reports is_watchlisted as
    False by default) will NOT clear it — watch status only turns off
    if you remove the URL from WATCHLIST and manually clear it."""
    now = datetime.datetime.now().isoformat()
    existing = conn.execute(
        "SELECT initial_price, first_seen, is_watchlisted FROM listings WHERE url = ?",
        (record["url"],),
    ).fetchone()

    tags_json = json.dumps(record["tags"])

    if existing is None:
        cols = ["url", "initial_price", "tags", "first_seen", "last_seen"] + UPSERT_FIELDS
        placeholders = ", ".join("?" for _ in cols)
        values = [record["url"], record["price"], tags_json, now, now] + \
                 [record[f] for f in UPSERT_FIELDS]
        conn.execute(
            f"INSERT INTO listings ({', '.join(cols)}) VALUES ({placeholders})",
            values,
        )
        conn.commit()
        return True
    else:
        merged_watchlisted = bool(existing[2]) or bool(record.get("is_watchlisted", False))
        set_clause = ", ".join(f"{f} = ?" for f in UPSERT_FIELDS)
        values = [
            (merged_watchlisted if f == "is_watchlisted" else record[f])
            for f in UPSERT_FIELDS
        ] + [tags_json, now, record["url"]]
        conn.execute(
            f"UPDATE listings SET {set_clause}, tags = ?, last_seen = ? WHERE url = ?",
            values,
        )
        conn.commit()
        return False


def get_all_listings(conn):
    rows = conn.execute("SELECT * FROM listings").fetchall()
    cols = [d[0] for d in conn.execute("SELECT * FROM listings").description]
    today = datetime.datetime.now()
    out = []
    for row in rows:
        d = dict(zip(cols, row))
        d["tags"] = json.loads(d["tags"]) if d["tags"] else []
        first_seen_date = datetime.datetime.fromisoformat(d["first_seen"])
        last_seen_date = datetime.datetime.fromisoformat(d["last_seen"])
        d["days_tracked"] = (today - first_seen_date).days
        d["is_new"] = d["days_tracked"] == 0
        d["days_since_last_seen"] = (today - last_seen_date).days
        d["is_stale"] = d["days_since_last_seen"] > STALE_AFTER_DAYS
        if d["added_date"]:
            added = datetime.datetime.fromisoformat(d["added_date"])
            d["days_on_market"] = (today - added).days
        else:
            d["days_on_market"] = None
        d["price_dropped"] = (
            d["initial_price"] is not None
            and d["price"] is not None
            and d["price"] < d["initial_price"]
        )
        d["is_reduced"] = bool(d["is_reduced"])
        d["is_sstc"] = bool(d["is_sstc"])
        d["is_watchlisted"] = bool(d["is_watchlisted"])
        out.append(d)
    add_peer_group_stats(out)
    return out


def archive_stale_listings(conn):
    """Removes listings not seen in over ARCHIVE_AFTER_DAYS — by that
    point they're very likely sold or taken down. Keeps the database
    (and dashboard) from accumulating dead listings forever.
    Watchlisted listings are exempt — they should never silently
    disappear even if a fetch fails for a while."""
    cutoff = (datetime.datetime.now() - datetime.timedelta(days=ARCHIVE_AFTER_DAYS)).isoformat()
    cur = conn.execute(
        "DELETE FROM listings WHERE last_seen < ? AND (is_watchlisted IS NULL OR is_watchlisted = 0)",
        (cutoff,),
    )
    conn.commit()
    return cur.rowcount


def add_peer_group_stats(listings):
    by_area = {}
    for l in listings:
        by_area.setdefault(l["area"] or "Unknown", []).append(l)

    area_stats = {}
    for area, group in by_area.items():
        sqft_price_vals = [l["price_per_sqft"] for l in group if l["price_per_sqft"]]
        sqft_vals = [l["sqft"] for l in group if l["sqft"]]
        area_stats[area] = {
            "avg_price_per_sqft": round(sum(sqft_price_vals) / len(sqft_price_vals)) if sqft_price_vals else None,
            "avg_sqft": round(sum(sqft_vals) / len(sqft_vals)) if sqft_vals else None,
            "count": len(group),
        }

    for l in listings:
        stats = area_stats[l["area"] or "Unknown"]
        l["area_avg_price_per_sqft"] = stats["avg_price_per_sqft"]
        l["area_avg_sqft"] = stats["avg_sqft"]
        l["good_value"] = (
            l["price_per_sqft"] is not None
            and stats["avg_price_per_sqft"] is not None
            and l["price_per_sqft"] < stats["avg_price_per_sqft"]
        )


# ---------------------------------------------------------------------
# Fetching + pagination
# ---------------------------------------------------------------------
def fetch(url):
    try:
        resp = requests.get(url, headers=HEADERS, timeout=15)
        if resp.status_code in (403, 429):
            print(f"  [blocked] {url} -> HTTP {resp.status_code} "
                  f"(site is likely rate-limiting or bot-blocking this request)")
            return None
        resp.raise_for_status()
        return resp.text
    except requests.RequestException as e:
        print(f"  [error] {url}: {e}")
        return None


def set_query_param(url, key, value):
    parts = urlsplit(url)
    q = dict(parse_qsl(parts.query))
    q[key] = str(value)
    new_query = urlencode(q)
    return urlunsplit((parts.scheme, parts.netloc, parts.path, new_query, parts.fragment))


def parse_rightmove_search(html):
    soup = BeautifulSoup(html, "lxml")
    out = []
    for card in soup.select("div[class*='propertyCard']") or soup.select("div.l-searchResult"):
        link = card.select_one("a[href*='/properties/']")
        if not link:
            continue
        url = "https://www.rightmove.co.uk" + link["href"].split("?")[0]
        out.append(url)
    return list(dict.fromkeys(out))


def parse_zoopla_search(html):
    soup = BeautifulSoup(html, "lxml")
    out = []
    for a in soup.select("a[href*='/for-sale/details/']") or soup.select("a[href*='/to-rent/details/']"):
        href = a.get("href", "")
        if href:
            out.append("https://www.zoopla.co.uk" + href.split("?")[0])
    return list(dict.fromkeys(out))


def fetch_search_listing_urls(site, base_url, max_listings):
    """Fetches multiple result pages until max_listings is reached,
    a page returns nothing new, or MAX_PAGES_PER_SEARCH is hit.
    For Rightmove, forces "newest first" sorting (unless the URL
    already specifies a sortType) so that within a capped fetch, the
    freshest listings are always the ones captured."""
    parser = parse_rightmove_search if site == "rightmove" else parse_zoopla_search
    all_urls, seen = [], set()
    page = 0

    if site == "rightmove" and "sortType" not in base_url:
        base_url = set_query_param(base_url, "sortType", "6")  # 6 = newest first

    while len(all_urls) < max_listings and page < MAX_PAGES_PER_SEARCH:
        if page == 0:
            page_url = base_url
        elif site == "rightmove":
            page_url = set_query_param(base_url, "index", page * 24)
        else:
            page_url = set_query_param(base_url, "pn", page + 1)

        html = fetch(page_url)
        if not html:
            break
        page_urls = parser(html)
        new_urls = [u for u in page_urls if u not in seen]
        if not new_urls:
            break
        for u in new_urls:
            seen.add(u)
            all_urls.append(u)
        if len(page_urls) < 20:
            break  # fewer than a full page -> likely the last page
        page += 1
        time.sleep(REQUEST_DELAY_SECONDS)

    return all_urls[:max_listings]


# ---------------------------------------------------------------------
# Field extraction — tries embedded JSON first (more reliable, present
# on many Rightmove pages as hydration data), falls back to scanning
# the visible text if that's not found or doesn't have the field.
# ---------------------------------------------------------------------
def find_json_blobs(soup):
    blobs = []
    for script in soup.find_all("script"):
        content = script.string or script.get_text() or ""
        content = content.strip()
        if not content or len(content) > 3_000_000:
            continue
        idx = content.find("{")
        if idx == -1:
            continue
        candidate = content[idx:].rstrip().rstrip(";")
        try:
            blobs.append(json.loads(candidate))
        except (json.JSONDecodeError, ValueError):
            continue
    return blobs


def search_json_recursive(obj, key_substrings):
    if isinstance(obj, dict):
        for k, v in obj.items():
            kl = k.lower()
            if any(sub in kl for sub in key_substrings):
                if v not in (None, "", "N/A") and not isinstance(v, (dict, list)):
                    return v
        for v in obj.values():
            result = search_json_recursive(v, key_substrings)
            if result is not None:
                return result
    elif isinstance(obj, list):
        for item in obj:
            result = search_json_recursive(item, key_substrings)
            if result is not None:
                return result
    return None


def extract_sqft(text, json_blobs=None):
    if json_blobs:
        for blob in json_blobs:
            v = search_json_recursive(blob, ["sqft", "squarefeet", "areasqft"])
            if v:
                try:
                    return int(float(v))
                except (ValueError, TypeError):
                    pass
    m = re.search(r"([\d,]{3,6})\s*sq\s*ft", text, re.I)
    if m:
        return int(m.group(1).replace(",", ""))
    m = re.search(r"([\d,]{2,4})\s*sq\s*m", text, re.I)
    if m:
        return round(int(m.group(1).replace(",", "")) * 10.7639)
    return None


def extract_price(text):
    m = re.search(r"£\s?([\d,]{5,9})", text)
    if m:
        return int(m.group(1).replace(",", ""))
    return None


def extract_tenure(text, json_blobs=None):
    if json_blobs:
        for blob in json_blobs:
            v = search_json_recursive(blob, ["tenure"])
            if v:
                return str(v).title()
    m = re.search(r"tenure[:\s]{1,10}(freehold|leasehold|share of freehold)", text, re.I)
    if m:
        return m.group(1).title()
    if re.search(r"\bleasehold\b", text, re.I):
        return "Leasehold"
    if re.search(r"\bfreehold\b", text, re.I):
        return "Freehold"
    return None


def extract_lease_years(text, json_blobs=None):
    if json_blobs:
        for blob in json_blobs:
            v = search_json_recursive(blob, ["yearsremaining", "remaininglease", "leaseyears", "leaselength"])
            if v:
                try:
                    return int(float(v))
                except (ValueError, TypeError):
                    pass
    m = re.search(r"([\d,]{1,4})\s*years?\s*(?:remaining|left)(?:\s*on\s*(?:the\s*)?lease)?", text, re.I)
    if m:
        return int(m.group(1).replace(",", ""))
    m = re.search(r"lease(?:\s*length)?[:\s]{1,10}([\d,]{1,4})\s*years?", text, re.I)
    if m:
        return int(m.group(1).replace(",", ""))
    return None


def extract_epc_rating(text, json_blobs=None):
    if json_blobs:
        for blob in json_blobs:
            v = search_json_recursive(blob, ["epcrating", "energyrating", "epc"])
            if v and str(v).strip().upper() in list("ABCDEFG"):
                return str(v).strip().upper()
    m = re.search(r"epc\s*rating[:\s]{1,15}([A-G])\b", text, re.I)
    if m:
        return m.group(1).upper()
    # fallback: "Current energy rating C" / "Energy Efficiency Rating: C"
    m = re.search(r"energy\s*(?:efficiency\s*)?rating[:\s]{1,15}([A-G])\b", text, re.I)
    if m:
        return m.group(1).upper()
    return None


def extract_council_tax_band(text, json_blobs=None):
    if json_blobs:
        for blob in json_blobs:
            v = search_json_recursive(blob, ["counciltaxband", "taxband"])
            if v and str(v).strip().upper() in list("ABCDEFGH"):
                return str(v).strip().upper()
    m = re.search(r"council\s*tax\s*band[:\s]{1,15}([A-H])\b", text, re.I)
    if m:
        return m.group(1).upper()
    return None


def _money_to_int(raw):
    return int(round(float(raw.replace(",", ""))))


def extract_service_charge(text, json_blobs=None):
    if json_blobs:
        for blob in json_blobs:
            v = search_json_recursive(blob, ["servicecharge"])
            if v:
                try:
                    return int(round(float(v)))
                except (ValueError, TypeError):
                    pass
    m = re.search(
        r"service\s*charge[^£\n]{0,60}£\s?([\d,]{1,7}(?:\.\d{2})?)",
        text, re.I,
    )
    if not m:
        return None
    amount = _money_to_int(m.group(1))
    window = text[m.end():m.end() + 25].lower()
    if "per month" in window or "pcm" in window or "/month" in window or "monthly" in window:
        amount *= 12
    return amount


def extract_ground_rent(text, json_blobs=None):
    if json_blobs:
        for blob in json_blobs:
            v = search_json_recursive(blob, ["groundrent"])
            if v:
                try:
                    return int(round(float(v)))
                except (ValueError, TypeError):
                    pass
    m = re.search(
        r"ground\s*rent[^£\n]{0,60}£\s?([\d,]{1,7}(?:\.\d{2})?)",
        text, re.I,
    )
    if not m:
        return None
    amount = _money_to_int(m.group(1))
    window = text[m.end():m.end() + 25].lower()
    if "per month" in window or "pcm" in window or "/month" in window or "monthly" in window:
        amount *= 12
    return amount


def extract_bedrooms(text, json_blobs=None):
    if json_blobs:
        for blob in json_blobs:
            v = search_json_recursive(blob, ["bedrooms"])
            if v is not None:
                try:
                    return int(v)
                except (ValueError, TypeError):
                    pass
    m = re.search(r"(\d+)\s*bedroom", text, re.I)
    return int(m.group(1)) if m else None


def extract_bathrooms(text, json_blobs=None):
    if json_blobs:
        for blob in json_blobs:
            v = search_json_recursive(blob, ["bathrooms"])
            if v is not None:
                try:
                    return int(v)
                except (ValueError, TypeError):
                    pass
    m = re.search(r"(\d+)\s*bathroom", text, re.I)
    return int(m.group(1)) if m else None


def extract_status_flags(text):
    t = text.lower()
    return {
        "is_reduced": bool(re.search(r"\breduced\b", t)),
        "is_sstc": bool(re.search(r"sold\s*stc|under\s*offer", t)),
    }


def extract_added_date(text, json_blobs=None):
    """Rightmove's actual 'first listed' date, where available — gives
    real days-on-market rather than just how long we've tracked it."""
    today = datetime.date.today()

    if json_blobs:
        for blob in json_blobs:
            v = search_json_recursive(blob, ["firstvisibledate", "addedon", "addeddate", "onmarketdate", "listeddate"])
            if v:
                parsed = _parse_date_flexible(str(v))
                if parsed:
                    return parsed.isoformat()

    m = re.search(r"added\s+today", text, re.I)
    if m:
        return today.isoformat()
    m = re.search(r"added\s+yesterday", text, re.I)
    if m:
        return (today - datetime.timedelta(days=1)).isoformat()
    m = re.search(r"added\s*(?:on\s*)?(\d{1,2})[/.](\d{1,2})[/.](\d{2,4})", text, re.I)
    if m:
        day, month, year = m.groups()
        year = int(year)
        if year < 100:
            year += 2000
        try:
            return datetime.date(year, int(month), int(day)).isoformat()
        except ValueError:
            return None
    return None


def _parse_date_flexible(raw):
    """Tries a handful of common date formats/ISO timestamps."""
    raw = raw.strip()
    for fmt in ("%Y-%m-%d", "%Y-%m-%dT%H:%M:%S", "%d/%m/%Y", "%d-%m-%Y"):
        try:
            return datetime.datetime.strptime(raw[:len(fmt) + 8], fmt).date()
        except ValueError:
            continue
    return None


def extract_floorplan_url(soup, base_url):
    img = soup.find("img", src=re.compile(r"floorplan", re.I))
    if img and img.get("src"):
        src = img["src"]
        if src.startswith("http"):
            return src
        origin = "/".join(base_url.split("/")[:3])
        return origin + src
    return None


def tag_text(text):
    t = text.lower()
    tags = []
    has_fixer = any(k in t for k in FIXER_UPPER_INCLUDE)
    has_structural = any(k in t for k in FIXER_UPPER_EXCLUDE)
    if has_fixer and not has_structural:
        tags.append("fixer-upper")
    if any(k in t for k in UNIQUE_KEYWORDS):
        tags.append("warehouse/unique")
    if any(k in t for k in BIG_LIVING_KEYWORDS):
        tags.append("big-living/windows")
    return tags


def fetch_listing_detail(url, source, area):
    html = fetch(url)
    if not html:
        return None
    soup = BeautifulSoup(html, "lxml")
    text = soup.get_text(" ", strip=True)
    title_tag = soup.find("h1")
    title = title_tag.get_text(strip=True) if title_tag else url

    json_blobs = find_json_blobs(soup)
    status_flags = extract_status_flags(text)

    record = {
        "url": url,
        "source": source,
        "area": area,
        "title": title,
        "price": extract_price(text),
        "sqft": extract_sqft(text, json_blobs),
        "bedrooms": extract_bedrooms(text, json_blobs),
        "bathrooms": extract_bathrooms(text, json_blobs),
        "tenure": extract_tenure(text, json_blobs),
        "lease_years_remaining": extract_lease_years(text, json_blobs),
        "epc_rating": extract_epc_rating(text, json_blobs),
        "council_tax_band": extract_council_tax_band(text, json_blobs),
        "service_charge_annual": extract_service_charge(text, json_blobs),
        "ground_rent_annual": extract_ground_rent(text, json_blobs),
        "is_reduced": status_flags["is_reduced"],
        "is_sstc": status_flags["is_sstc"],
        "floorplan_url": extract_floorplan_url(soup, url),
        "added_date": extract_added_date(text, json_blobs),
        "is_watchlisted": False,
        "tags": tag_text(text),
    }
    if record["price"] and record["sqft"]:
        record["price_per_sqft"] = round(record["price"] / record["sqft"])
    else:
        record["price_per_sqft"] = None

    return record


def guess_source_from_url(url):
    if "rightmove.co.uk" in url:
        return "rightmove"
    if "zoopla.co.uk" in url:
        return "zoopla"
    return "unknown"


# ---------------------------------------------------------------------
# Main run
# ---------------------------------------------------------------------
def run(auto_mode=False):
    all_records = []

    total_searches = sum(1 for urls in SEARCHES.values() for url in urls.values() if url)
    if total_searches == 0 and not WATCHLIST:
        print("No search URLs or watchlist entries set — add some first.")
        return
    if total_searches and not CLOUD_RUN and not check_daily_limit(total_searches, auto_mode=auto_mode):
        return

    conn = init_db()
    searches_with_results = 0
    search_records = 0
    empty_areas = []

    for site, area_urls in SEARCHES.items():
        for area, search_url in area_urls.items():
            if not search_url:
                continue
            print(f"Searching {site} — {area}: {search_url}")
            try:
                listing_urls = fetch_search_listing_urls(site, search_url, MAX_LISTINGS_PER_SEARCH)
            except Exception as e:
                print(f"  [error] search failed for {site} — {area}: {e}")
                listing_urls = []

            if not listing_urls:
                empty_areas.append(area)
                continue
            searches_with_results += 1

            print(f"  found {len(listing_urls)} listings, fetching details...")
            time.sleep(REQUEST_DELAY_SECONDS)

            for i, listing_url in enumerate(listing_urls, 1):
                print(f"  [{i}/{len(listing_urls)}] {listing_url}")
                try:
                    record = fetch_listing_detail(listing_url, site, area)
                except Exception as e:
                    print(f"    [error] failed to parse listing: {e}")
                    record = None
                if record:
                    all_records.append(record)
                    search_records += 1
                time.sleep(REQUEST_DELAY_SECONDS)

    # Blocked-run guard: if every search came back empty (or no listing
    # page could be read), Rightmove is almost certainly refusing us.
    # Exit non-zero BEFORE saving anything so the old data isn't touched
    # and GitHub emails a failure.
    if total_searches and (searches_with_results == 0 or search_records == 0):
        conn.close()
        print("\nBLOCKED: no listings could be read from any search "
              "(Rightmove is probably refusing this connection). Nothing was saved.")
        sys.exit(2)
    if empty_areas:
        print(f"\n::warning::These searches returned nothing and may have been blocked: {', '.join(empty_areas)}")

    if WATCHLIST:
        print(f"\nChecking {len(WATCHLIST)} watchlisted listing(s)...")
        for url in WATCHLIST:
            existing = conn.execute("SELECT area FROM listings WHERE url = ?", (url,)).fetchone()
            area = existing[0] if existing and existing[0] else "Watchlist"
            source = guess_source_from_url(url)
            print(f"  {url}")
            try:
                record = fetch_listing_detail(url, source, area)
            except Exception as e:
                print(f"    [error] failed to parse watchlisted listing: {e}")
                record = None
            if record:
                record["is_watchlisted"] = True
                all_records.append(record)
            time.sleep(REQUEST_DELAY_SECONDS)

    if AGING_RECHECK_COUNT > 0:
        fetched_this_run = {r["url"] for r in all_records}
        candidates = conn.execute(
            """SELECT url, source, area FROM listings
               WHERE is_watchlisted = 0 OR is_watchlisted IS NULL
               ORDER BY last_seen ASC LIMIT ?""",
            (AGING_RECHECK_COUNT * 3,),  # overfetch, then skip ones already covered this run
        ).fetchall()
        to_recheck = [c for c in candidates if c[0] not in fetched_this_run][:AGING_RECHECK_COUNT]
        if to_recheck:
            print(f"\nRechecking {len(to_recheck)} older listing(s) that fell out of this run's search results...")
            for url, source, area in to_recheck:
                print(f"  {url}")
                try:
                    record = fetch_listing_detail(url, source, area)
                except Exception as e:
                    print(f"    [error] {e}")
                    record = None
                if record:
                    all_records.append(record)
                time.sleep(REQUEST_DELAY_SECONDS)

    if total_searches and not CLOUD_RUN:
        log_search_run(total_searches)

    new_count = 0
    new_titles = []
    price_drop_events = []
    newly_sstc = []
    for record in all_records:
        prior = conn.execute(
            "SELECT price, is_sstc FROM listings WHERE url = ?", (record["url"],)
        ).fetchone()
        is_new = upsert_listing(conn, record)
        if is_new:
            new_count += 1
            new_titles.append(f"{record['title']} ({record['area']})")
        elif prior:
            prior_price, prior_sstc = prior
            if prior_price is not None and record["price"] is not None and record["price"] < prior_price:
                price_drop_events.append((record["title"], prior_price, record["price"]))
            if not prior_sstc and record["is_sstc"]:
                newly_sstc.append(record["title"])
    print(f"\nThis run: {len(all_records)} listings checked, {new_count} new")

    archived = archive_stale_listings(conn)
    if archived:
        print(f"Removed {archived} listing(s) not seen in over {ARCHIVE_AFTER_DAYS} days (likely sold/removed)")

    all_listings = get_all_listings(conn)
    conn.close()

    changes_text = write_changes_summary(new_titles, price_drop_events, newly_sstc, archived)
    write_dashboard(all_listings, changes_text)
    print(f"Dashboard ready ({len(all_listings)} total tracked): open {HTML_FILE.name}")


def write_changes_summary(new_titles, price_drop_events, newly_sstc, archived):
    lines = [f"Run completed: {datetime.datetime.now().strftime('%Y-%m-%d %H:%M')}"]

    if new_titles:
        lines.append(f"\n{len(new_titles)} new listing(s):")
        lines += [f"  - {t}" for t in new_titles]
    else:
        lines.append("\nNo new listings this run.")

    if price_drop_events:
        lines.append(f"\n{len(price_drop_events)} price drop(s):")
        lines += [f"  - {title}: £{old:,} -> £{new:,}" for title, old, new in price_drop_events]

    if newly_sstc:
        lines.append(f"\n{len(newly_sstc)} newly sold/under offer:")
        lines += [f"  - {t}" for t in newly_sstc]

    if archived:
        lines.append(f"\n{archived} listing(s) archived (not seen in {ARCHIVE_AFTER_DAYS}+ days)")

    summary = "\n".join(lines)
    print("\n--- Changes this run ---")
    print(summary)
    CHANGES_FILE.write_text(summary, encoding="utf-8")
    return summary


# ---------------------------------------------------------------------
# Dashboard
# ---------------------------------------------------------------------
def write_dashboard(records, changes_text=""):
    # Safe to embed inside <script>: no raw <, > or & can appear.
    data_json = (json.dumps(records)
                 .replace("<", "\\u003c").replace(">", "\\u003e").replace("&", "\\u0026"))
    esc = lambda v: htmllib.escape(str(v), quote=True)
    updated = datetime.datetime.now(datetime.timezone.utc).strftime("%d %b %Y, %H:%M UTC")

    areas = {}
    for r in records:
        a = r["area"] or "Unknown"
        areas[a] = {
            "avg_price_per_sqft": r["area_avg_price_per_sqft"],
            "avg_sqft": r["area_avg_sqft"],
            "count": sum(1 for x in records if (x["area"] or "Unknown") == a),
        }

    max_psf = max([s["avg_price_per_sqft"] for s in areas.values() if s["avg_price_per_sqft"]], default=1)

    area_cards = "".join(
        f'''<div class="area-card" data-area="{esc(a)}">
              <div class="area-card-name">{esc(a)}</div>
              <div class="area-card-stat">{'£' + str(s['avg_price_per_sqft']) if s['avg_price_per_sqft'] else '—'}<span class="unit"> /sqft avg</span></div>
              <div class="area-card-bar"><div class="area-card-bar-fill" style="width:{round((s['avg_price_per_sqft'] or 0) / max_psf * 100)}%"></div></div>
              <div class="area-card-sub">{s['avg_sqft'] if s['avg_sqft'] else '—'} sqft avg &middot; {s['count']} tracked</div>
            </div>'''
        for a, s in sorted(areas.items())
    )

    area_options = "".join(f'<option value="{esc(a)}">{esc(a)}</option>' for a in sorted(areas.keys()))

    html_template = r"""<!DOCTYPE html>
<html lang="en-GB"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1, viewport-fit=cover">
<meta name="theme-color" content="#1F5F4E">
<meta name="robots" content="noindex,nofollow">
<title>Property Dashboard</title>
<link rel="preconnect" href="https://fonts.googleapis.com">
<link href="https://fonts.googleapis.com/css2?family=Fraunces:opsz,wght@9..144,500;9..144,600&family=Source+Sans+3:wght@400;500;600&family=IBM+Plex+Mono:wght@400;500&display=swap" rel="stylesheet">
<style>
  :root {
    --bg: #F5F6F4;
    --surface: #FFFFFF;
    --ink: #1C2321;
    --ink-soft: #5C6B66;
    --border: #E1E4E1;
    --brand: #1F5F4E;
    --brand-soft: #E6EFEC;
    --amber: #B5762C;
    --amber-soft: #F5EBDD;
    --brick: #A8412C;
    --brick-soft: #F5E4DF;
  }
  * { box-sizing: border-box; }
  body {
    font-family: "Source Sans 3", -apple-system, sans-serif;
    margin: 0; background: var(--bg); color: var(--ink);
  }
  .wrap { max-width: 1240px; margin: 0 auto; padding: 32px 28px 60px; }
  header { margin-bottom: 28px; }
  h1 {
    font-family: "Fraunces", serif; font-weight: 600; font-size: 30px;
    margin: 0 0 4px; letter-spacing: -0.01em;
  }
  .subhead { color: var(--ink-soft); font-size: 14px; }

  h2.section-label {
    font-family: "Source Sans 3", sans-serif; font-weight: 600; font-size: 12px;
    text-transform: uppercase; letter-spacing: 0.08em; color: var(--ink-soft);
    margin: 32px 0 12px;
  }

  .area-cards { display: grid; grid-template-columns: repeat(auto-fit, minmax(200px, 1fr)); gap: 12px; }
  .area-card {
    background: var(--surface); border: 1px solid var(--border); border-radius: 10px;
    padding: 16px 18px; cursor: pointer; transition: border-color 0.15s, transform 0.15s;
  }
  .area-card:hover { border-color: var(--brand); transform: translateY(-1px); }
  .area-card-name { font-weight: 600; font-size: 14px; margin-bottom: 6px; }
  .area-card-stat { font-family: "IBM Plex Mono", monospace; font-size: 20px; font-weight: 500; }
  .area-card-stat .unit { font-family: "Source Sans 3", sans-serif; font-size: 12px; color: var(--ink-soft); font-weight: 400; }
  .area-card-bar { height: 4px; background: var(--border); border-radius: 2px; margin: 10px 0 8px; overflow: hidden; }
  .area-card-bar-fill { height: 100%; background: var(--brand); border-radius: 2px; }
  .area-card-sub { font-size: 12px; color: var(--ink-soft); }

  .controls {
    display: flex; flex-wrap: wrap; align-items: center; gap: 10px 18px;
    background: var(--surface); border: 1px solid var(--border); border-radius: 10px;
    padding: 14px 18px; margin: 16px 0 20px; position: sticky; top: 12px; z-index: 5;
  }
  .controls select {
    font-family: inherit; font-size: 13px; padding: 6px 10px; border-radius: 6px;
    border: 1px solid var(--border); background: var(--bg); color: var(--ink);
  }
  .controls label {
    font-size: 13px; display: flex; align-items: center; gap: 6px; color: var(--ink-soft);
    cursor: pointer; user-select: none;
  }
  .controls input[type=checkbox] { accent-color: var(--brand); }
  #reset-filters {
    margin-left: auto; font-size: 12px; color: var(--brand); background: none;
    border: none; cursor: pointer; text-decoration: underline; padding: 0;
  }

  .table-scroll { overflow-x: auto; border: 1px solid var(--border); border-radius: 10px; }
  table { border-collapse: collapse; width: 100%; min-width: 1400px; background: var(--surface); }
  th, td { padding: 10px 12px; text-align: left; font-size: 13px; border-bottom: 1px solid var(--border); white-space: nowrap; }
  th {
    background: var(--ink); color: #fff; cursor: pointer; user-select: none;
    font-weight: 500; font-size: 11px; text-transform: uppercase; letter-spacing: 0.04em;
    position: sticky; top: 0;
  }
  th:hover { background: #313a37; }
  th.sorted::after { content: " ▾"; opacity: 0.7; }
  tbody tr:hover { background: var(--bg); }
  .num { font-family: "IBM Plex Mono", monospace; }
  a.listing-link { color: var(--brand); text-decoration: none; font-weight: 500; white-space: normal; }
  a.listing-link:hover { text-decoration: underline; }
  td:has(.listing-link) { white-space: normal; min-width: 220px; }

  .status-select {
    font-family: inherit; font-size: 12px; padding: 4px 6px; border-radius: 5px;
    border: 1px solid var(--border); background: var(--bg); color: var(--ink);
  }
  .notes-input {
    font-family: inherit; font-size: 12px; padding: 4px 6px; border-radius: 5px;
    border: 1px solid var(--border); background: var(--bg); color: var(--ink); width: 140px;
  }

  .badge { display: inline-block; border-radius: 4px; padding: 2px 7px; font-size: 11px; font-weight: 500; margin-left: 4px; }
  .badge-new { background: var(--brand-soft); color: var(--brand); }
  .badge-drop { background: var(--brick-soft); color: var(--brick); }
  .badge-value { background: var(--amber-soft); color: var(--amber); }
  .badge-sstc { background: var(--border); color: var(--ink-soft); }
  .badge-watch { background: #EAE6F5; color: #5B3FA0; }
  .tag { display: inline-block; background: var(--bg); border: 1px solid var(--border); border-radius: 4px;
    padding: 2px 7px; margin: 1px 3px 1px 0; font-size: 11px; color: var(--ink-soft); }
  .fp-link { font-size: 11px; }

  .whatsnew { margin-top: 8px; font-size: 13px; }
  .whatsnew summary { cursor: pointer; color: var(--brand); font-weight: 600; }
  .whatsnew pre { white-space: pre-wrap; font-family: "IBM Plex Mono", monospace; font-size: 12px;
    background: var(--surface); border: 1px solid var(--border); border-radius: 8px; padding: 10px 12px; margin: 8px 0 0; }
  #filter-toggle, #sort-select, #cards { display: none; }
  #filter-box { display: contents; }

  .card { background: var(--surface); border: 1px solid var(--border); border-radius: 12px; padding: 14px; margin-bottom: 12px; }
  .card-title { display: block; font-weight: 600; font-size: 15px; line-height: 1.3; color: var(--brand); text-decoration: none; margin-bottom: 6px; }
  .card-badges { margin-bottom: 8px; } .card-badges .badge { margin: 0 4px 4px 0; }
  .card-price { font-family: "IBM Plex Mono", monospace; font-size: 22px; font-weight: 500; }
  .card-grid { display: grid; grid-template-columns: repeat(3, 1fr); gap: 8px; margin: 10px 0; }
  .card-stat { background: var(--bg); border-radius: 8px; padding: 8px; }
  .card-stat b { display: block; font-family: "IBM Plex Mono", monospace; font-size: 14px; font-weight: 500; }
  .card-stat span { font-size: 11px; color: var(--ink-soft); }
  .card-meta { font-size: 12px; color: var(--ink-soft); line-height: 1.6; margin-bottom: 8px; }
  .card-actions { display: flex; gap: 8px; margin-top: 10px; }
  .card-actions .status-select, .card-actions .notes-input { font-size: 16px; padding: 8px; }
  .card-actions .notes-input { flex: 1; width: auto; min-width: 0; }

  @media (max-width: 760px) {
    .wrap { padding: 16px 14px 48px; }
    h1 { font-size: 24px; }
    .table-scroll { display: none; }
    #cards { display: block; }
    .area-cards { grid-template-columns: repeat(2, 1fr); gap: 8px; }
    .area-card { padding: 12px; }
    .area-card-stat { font-size: 17px; }
    .controls { position: static; padding: 12px; gap: 10px; }
    #area-select, #status-select, #sort-select { display: block; width: 100%; font-size: 16px; padding: 9px 10px; }
    #filter-toggle { display: block; width: 100%; font-size: 15px; padding: 9px; border-radius: 6px;
      border: 1px solid var(--border); background: var(--bg); color: var(--ink); }
    #filter-box { display: none; width: 100%; }
    #filter-box.open { display: grid; grid-template-columns: 1fr; gap: 12px; }
    #filter-box label { font-size: 15px; }
    #reset-filters { margin-left: 0; font-size: 14px; text-align: left; }
  }

  .note { font-size: 12px; color: var(--ink-soft); margin: 8px 0 0; }
  .empty { padding: 40px; text-align: center; color: var(--ink-soft); font-size: 14px; }
</style></head>
<body>
<div class="wrap">
<header>
  <h1>Property Dashboard</h1>
  <div class="subhead">Tracking __TOTAL_COUNT__ listings across __AREA_COUNT__ areas &middot; updated __UPDATED__</div>
  <details class="whatsnew"><summary>What's new this run</summary><pre>__CHANGES__</pre></details>
</header>

<h2 class="section-label">Areas at a glance</h2>
<div class="area-cards">
__AREA_CARDS__
</div>
<p class="note">Click an area to filter the table below and sort by best value (lowest £/sqft first).</p>

<h2 class="section-label">Listings</h2>
<div class="controls">
  <select id="area-select">
    <option value="">All areas</option>
    __AREA_OPTIONS__
  </select>
  <select id="status-select">
    <option value="">All statuses</option>
    <option value="interested">Interested</option>
    <option value="contacted">Contacted</option>
    <option value="viewed">Viewed</option>
    <option value="rejected">Rejected</option>
    <option value="none">Not set</option>
  </select>
  <select id="sort-select">
    <option value="first_seen|0">Newest first</option>
    <option value="price_per_sqft|1">Lowest £/sqft</option>
    <option value="price|1">Lowest price</option>
    <option value="sqft|0">Biggest first</option>
    <option value="days_on_market|1">Fewest days on market</option>
  </select>
  <button id="filter-toggle" type="button">Filters</button>
  <div id="filter-box">
  <label><input type="checkbox" id="f-fixer"> Fixer-upper</label>
  <label><input type="checkbox" id="f-warehouse"> Warehouse/unique</label>
  <label><input type="checkbox" id="f-living"> Big living/windows</label>
  <label><input type="checkbox" id="f-new"> New today</label>
  <label><input type="checkbox" id="f-dropped"> Price drops</label>
  <label><input type="checkbox" id="f-value"> Good value</label>
  <label><input type="checkbox" id="f-hide-sstc"> Hide sold/under offer</label>
  <label><input type="checkbox" id="f-hide-stale"> Hide stale (not re-seen in __STALE_DAYS__+ days)</label>
  <label><input type="checkbox" id="f-watchlist"> Watchlist only</label>
  <button id="reset-filters" onclick="resetFilters()">Reset</button>
  </div>
</div>

<div class="table-scroll">
<table id="tbl">
<thead><tr>
<th data-key="source">Source</th>
<th data-key="area">Area</th>
<th data-key="title">Listing</th>
<th data-key="price">Price</th>
<th data-key="sqft">Sq Ft</th>
<th data-key="price_per_sqft">Price / Sq Ft</th>
<th data-key="beds_baths">Beds/Baths</th>
<th data-key="tenure">Tenure</th>
<th data-key="lease_years_remaining">Lease Yrs</th>
<th data-key="service_charge_annual">Service Chg/yr</th>
<th data-key="ground_rent_annual">Ground Rent/yr</th>
<th data-key="epc_rating">EPC</th>
<th data-key="council_tax_band">Tax Band</th>
<th data-key="days_on_market">Days on Market</th>
<th data-key="days_tracked">Days Tracked</th>
<th data-key="tags">Tags</th>
<th data-key="status">Status</th>
<th>Notes</th>
</tr></thead>
<tbody id="tbody"></tbody>
</table>
</div>
<div id="cards"></div>
<div id="empty-state" class="empty" style="display:none;">No listings match these filters.</div>

<script>
const DATA = __DATA_JSON__;
DATA.forEach(r => { r.beds_baths = (r.bedrooms || 0) * 100 + (r.bathrooms || 0); });

// Personal notes/status — stored only in this browser, never sent
// anywhere, and not overwritten when the dashboard is regenerated on
// the next run (keyed by listing URL, loaded fresh from localStorage
// each time the page opens).
const NOTES_KEY = 'property_dashboard_notes_v1';
function loadNotes() {
  try { return JSON.parse(localStorage.getItem(NOTES_KEY) || '{}'); } catch (e) { return {}; }
}
function saveNotes(notes) {
  try { localStorage.setItem(NOTES_KEY, JSON.stringify(notes)); } catch (e) { /* storage unavailable, ignore */ }
}
let NOTES = loadNotes();
DATA.forEach(r => {
  const n = NOTES[r.url] || {};
  r.status = n.status || '';
  r.notes = n.notes || '';
});

function updateNote(url, field, value) {
  if (!NOTES[url]) NOTES[url] = {};
  NOTES[url][field] = value;
  saveNotes(NOTES);
  const row = DATA.find(r => r.url === url);
  if (row) row[field] = value;
}

function safeUrl(u) {
  u = String(u || '');
  return /^https?:\/\//i.test(u) ? escapeHtml(u) : '#';
}

function badgesHtml(r) {
  return (r.is_new ? '<span class="badge badge-new">NEW</span>' : '')
    + ((r.price_dropped || r.is_reduced) ? '<span class="badge badge-drop">PRICE DROP</span>' : '')
    + (r.good_value ? '<span class="badge badge-value">GOOD VALUE</span>' : '')
    + (r.is_sstc ? '<span class="badge badge-sstc">SOLD/UNDER OFFER</span>' : '')
    + (r.is_stale ? '<span class="badge badge-sstc">STALE</span>' : '')
    + (r.is_watchlisted ? '<span class="badge badge-watch">WATCHED</span>' : '');
}

function cardHtml(r) {
  const gbp = v => v ? '£' + v.toLocaleString() : '-';
  const opt = (v, label) => `<option value="${v}" ${r.status === v ? 'selected' : ''}>${label}</option>`;
  const meta = [
    r.tenure ? escapeHtml(r.tenure) : null,
    r.lease_years_remaining ? r.lease_years_remaining + ' yrs lease' : null,
    r.service_charge_annual ? 'Service ' + gbp(r.service_charge_annual) + '/yr' : null,
    r.ground_rent_annual ? 'Ground rent ' + gbp(r.ground_rent_annual) + '/yr' : null,
    r.epc_rating ? 'EPC ' + escapeHtml(r.epc_rating) : null,
    r.council_tax_band ? 'Tax band ' + escapeHtml(r.council_tax_band) : null,
    r.days_on_market != null ? r.days_on_market + ' days on market' : null,
  ].filter(Boolean).join(' &middot; ');
  return `<div class="card">
    <a class="card-title" href="${safeUrl(r.url)}" target="_blank" rel="noopener">${escapeHtml(r.title)}</a>
    <div class="card-badges">${badgesHtml(r)}</div>
    <div class="card-price">${gbp(r.price)}</div>
    <div class="card-grid">
      <div class="card-stat"><b>${r.sqft ? r.sqft.toLocaleString() : '-'}</b><span>sq ft</span></div>
      <div class="card-stat"><b>${r.price_per_sqft ? '£' + r.price_per_sqft : '-'}</b><span>Price / Sq Ft</span></div>
      <div class="card-stat"><b>${r.bedrooms || '-'}${r.bathrooms ? ' / ' + r.bathrooms : ''}</b><span>beds / baths</span></div>
    </div>
    <div class="card-meta">${escapeHtml(r.area || '-')}${meta ? ' &middot; ' + meta : ''}</div>
    <div class="card-meta">${r.tags.map(t => `<span class="tag">${escapeHtml(t)}</span>`).join('')}${r.floorplan_url ? ` <a class="tag fp-link" href="${safeUrl(r.floorplan_url)}" target="_blank" rel="noopener">floorplan</a>` : ''}</div>
    <div class="card-actions">
      <select class="status-select" data-url="${escapeHtml(r.url)}">
        <option value="" ${!r.status ? 'selected' : ''}>Status</option>
        ${opt('interested','Interested')}${opt('contacted','Contacted')}${opt('viewed','Viewed')}${opt('rejected','Rejected')}
      </select>
      <input type="text" class="notes-input" data-url="${escapeHtml(r.url)}" value="${escapeHtml(r.notes)}" placeholder="notes...">
    </div>
  </div>`;
}

function escapeHtml(str) {
  return String(str)
    .replace(/&/g, '&amp;')
    .replace(/"/g, '&quot;')
    .replace(/</g, '&lt;')
    .replace(/>/g, '&gt;');
}

function noteHandler(e) {
  if (e.target.classList.contains('status-select')) {
    updateNote(e.target.dataset.url, 'status', e.target.value);
  } else if (e.target.classList.contains('notes-input')) {
    updateNote(e.target.dataset.url, 'notes', e.target.value);
  }
}
document.getElementById('tbody').addEventListener('change', noteHandler);
document.getElementById('cards').addEventListener('change', noteHandler);

document.querySelector('.area-cards').addEventListener('click', (e) => {
  const c = e.target.closest('.area-card');
  if (c) filterToArea(c.dataset.area);
});
document.getElementById('filter-toggle').addEventListener('click', () => {
  document.getElementById('filter-box').classList.toggle('open');
});
document.getElementById('sort-select').addEventListener('change', (e) => {
  const [k, asc] = e.target.value.split('|');
  sortKey = k; sortAsc = asc === '1';
  render();
});

let sortKey = "first_seen", sortAsc = false;

function filterToArea(area) {
  document.getElementById('area-select').value = area;
  sortKey = "price_per_sqft";
  sortAsc = true;
  document.getElementById('sort-select').value = "price_per_sqft|1";
  render();
  const target = window.matchMedia('(max-width: 760px)').matches ? document.getElementById('cards') : document.getElementById('tbl');
  target.scrollIntoView({behavior: 'smooth', block: 'start'});
}

function resetFilters() {
  document.getElementById('area-select').value = "";
  document.getElementById('status-select').value = "";
  ['f-fixer','f-warehouse','f-living','f-new','f-dropped','f-value','f-hide-sstc','f-hide-stale','f-watchlist'].forEach(id => {
    document.getElementById(id).checked = false;
  });
  sortKey = "first_seen"; sortAsc = false;
  document.getElementById('sort-select').value = "first_seen|0";
  render();
}

function render() {
  const area = document.getElementById('area-select').value;
  const status = document.getElementById('status-select').value;
  const fFixer = document.getElementById('f-fixer').checked;
  const fWarehouse = document.getElementById('f-warehouse').checked;
  const fLiving = document.getElementById('f-living').checked;
  const fNew = document.getElementById('f-new').checked;
  const fDropped = document.getElementById('f-dropped').checked;
  const fValue = document.getElementById('f-value').checked;
  const fHideSstc = document.getElementById('f-hide-sstc').checked;
  const fHideStale = document.getElementById('f-hide-stale').checked;
  const fWatchlist = document.getElementById('f-watchlist').checked;

  let rows = DATA.filter(r => {
    if (area && r.area !== area) return false;
    if (status === 'none' && r.status) return false;
    if (status && status !== 'none' && r.status !== status) return false;
    if (fFixer && !r.tags.includes('fixer-upper')) return false;
    if (fWarehouse && !r.tags.includes('warehouse/unique')) return false;
    if (fLiving && !r.tags.includes('big-living/windows')) return false;
    if (fNew && !r.is_new) return false;
    if (fDropped && !(r.price_dropped || r.is_reduced)) return false;
    if (fValue && !r.good_value) return false;
    if (fHideSstc && r.is_sstc) return false;
    if (fHideStale && r.is_stale) return false;
    if (fWatchlist && !r.is_watchlisted) return false;
    return true;
  });

  rows.sort((a, b) => {
    let av = a[sortKey], bv = b[sortKey];
    if (av == null) return 1;
    if (bv == null) return -1;
    if (typeof av === 'string') return sortAsc ? av.localeCompare(bv) : bv.localeCompare(av);
    return sortAsc ? av - bv : bv - av;
  });

  document.querySelectorAll('th[data-key]').forEach(th => {
    th.classList.toggle('sorted', th.dataset.key === sortKey);
  });

  const tbody = document.getElementById('tbody');
  const emptyState = document.getElementById('empty-state');
  document.getElementById('tbl').style.display = rows.length ? '' : 'none';
  emptyState.style.display = rows.length ? 'none' : '';

  document.getElementById('cards').innerHTML = rows.map(cardHtml).join('');
  tbody.innerHTML = rows.map(r => `
    <tr>
      <td>${escapeHtml(r.source)}</td>
      <td>${escapeHtml(r.area || '-')}</td>
      <td><a class="listing-link" href="${safeUrl(r.url)}" target="_blank" rel="noopener">${escapeHtml(r.title)}</a>
        ${r.is_new ? '<span class="badge badge-new">NEW</span>' : ''}
        ${(r.price_dropped || r.is_reduced) ? '<span class="badge badge-drop">PRICE DROP</span>' : ''}
        ${r.good_value ? '<span class="badge badge-value">GOOD VALUE</span>' : ''}
        ${r.is_sstc ? '<span class="badge badge-sstc">SOLD/UNDER OFFER</span>' : ''}
        ${r.is_stale ? '<span class="badge badge-sstc">STALE</span>' : ''}
        ${r.is_watchlisted ? '<span class="badge badge-watch">WATCHED</span>' : ''}
        ${r.floorplan_url ? `<a class="tag fp-link" href="${safeUrl(r.floorplan_url)}" target="_blank" rel="noopener">floorplan</a>` : ''}
      </td>
      <td class="num">${r.price ? '£' + r.price.toLocaleString() : '-'}</td>
      <td class="num">${r.sqft ? r.sqft.toLocaleString() : '-'}</td>
      <td class="num">${r.price_per_sqft ? '£' + r.price_per_sqft : '-'}</td>
      <td class="num">${r.bedrooms || '-'}${r.bathrooms ? ' / ' + r.bathrooms : ''}</td>
      <td>${escapeHtml(r.tenure || '-')}</td>
      <td class="num">${r.lease_years_remaining || '-'}</td>
      <td class="num">${r.service_charge_annual ? '£' + r.service_charge_annual.toLocaleString() : '-'}</td>
      <td class="num">${r.ground_rent_annual ? '£' + r.ground_rent_annual.toLocaleString() : '-'}</td>
      <td>${escapeHtml(r.epc_rating || '-')}</td>
      <td>${escapeHtml(r.council_tax_band || '-')}</td>
      <td class="num">${r.days_on_market != null ? r.days_on_market : '-'}</td>
      <td class="num">${r.days_tracked}</td>
      <td>${r.tags.map(t => `<span class="tag">${escapeHtml(t)}</span>`).join('')}</td>
      <td>
        <select class="status-select" data-url="${escapeHtml(r.url)}">
          <option value="" ${!r.status ? 'selected' : ''}>-</option>
          <option value="interested" ${r.status === 'interested' ? 'selected' : ''}>Interested</option>
          <option value="contacted" ${r.status === 'contacted' ? 'selected' : ''}>Contacted</option>
          <option value="viewed" ${r.status === 'viewed' ? 'selected' : ''}>Viewed</option>
          <option value="rejected" ${r.status === 'rejected' ? 'selected' : ''}>Rejected</option>
        </select>
      </td>
      <td><input type="text" class="notes-input" data-url="${escapeHtml(r.url)}" value="${escapeHtml(r.notes)}" placeholder="notes..."></td>
    </tr>
  `).join('');
}

document.querySelectorAll('th[data-key]').forEach(th => {
  th.addEventListener('click', () => {
    const key = th.dataset.key;
    if (sortKey === key) sortAsc = !sortAsc; else { sortKey = key; sortAsc = true; }
    render();
  });
});
['area-select','status-select','f-fixer','f-warehouse','f-living','f-new','f-dropped','f-value','f-hide-sstc','f-hide-stale','f-watchlist'].forEach(id =>
  document.getElementById(id).addEventListener('change', render)
);

render();
</script>
</div>
</body></html>"""

    html_out = html_template
    html_out = html_out.replace("__AREA_CARDS__", area_cards)
    html_out = html_out.replace("__AREA_OPTIONS__", area_options)
    html_out = html_out.replace("__TOTAL_COUNT__", str(len(records)))
    html_out = html_out.replace("__AREA_COUNT__", str(len(areas)))
    html_out = html_out.replace("__UPDATED__", updated)
    html_out = html_out.replace("__CHANGES__", htmllib.escape(changes_text or "No change summary yet."))
    html_out = html_out.replace("__STALE_DAYS__", str(STALE_AFTER_DAYS))
    html_out = html_out.replace("__DATA_JSON__", data_json)
    HTML_FILE.write_text(html_out, encoding="utf-8")


if __name__ == "__main__":
    run(auto_mode="--auto" in sys.argv)
