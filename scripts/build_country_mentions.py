"""
build_country_mentions.py
=========================
Scans 30 credible US/UK/CA news sources via RSS for a 24-hour window,
counts how many articles mention each of 44 tracked countries,
compares against a rolling 7-day baseline, computes z-scores,
flags trending countries, and writes public/country_mentions.json.

JSON shape (Base44-friendly):
{
  "meta": { ... },
  "countries": [
    {
      "country":          "Russia",
      "iso2":             "RU",
      "mentions":         42,
      "baseline_mean":    31.4,
      "baseline_std":     6.2,
      "baseline_n":       14,
      "baseline_method":  method,
      "z_score":          1.71,
      "trend_status":     "trending",   // "trending" | "elevated" | "normal" | "low"
      "pct_change":       33.8,
      "history": [
        { "window_end": "2026-04-26T11:54:00Z", "mentions": 28 },
        ...
      ]
    },
    ...
  ]
}

trend_status logic:
  z >= 2.0  → "trending"
  z >= 1.0  → "elevated"
  z <= -1.0 → "low"
  else      → "normal"

Cold-start behaviour (< BASELINE_MIN_RUNS history points):
  Falls back to a hybrid score combining:
    (a) seed baseline (realistic long-term averages per country), AND
    (b) relative ranking within the current run's distribution.
  This means Iran at 183 mentions is correctly flagged "trending" on run #1.
"""

from __future__ import annotations

import json
import re
import time
import math
from datetime import datetime, timezone, timedelta
from pathlib import Path
from typing import Dict, List, Optional, Tuple
from urllib.parse import urlparse, parse_qs, urlencode, urlunparse

import feedparser
import requests
from dateutil import parser as dtparser


# ──────────────────────────────────────────────────────────
# CONFIG
# ──────────────────────────────────────────────────────────

WINDOW_HOURS      = 24
HISTORY_DAYS      = 90
BASELINE_MIN_RUNS = 360     # history points needed before full rolling baseline kicks in
                              # (~15 days of twice-daily runs)
BASELINE_DAYS     = 30     # how far back the baseline window looks
BASELINE_RECENCY_EXCLUDE_DAYS = 3   # exclude the most recent N days from baseline
                                    # so an ongoing event doesn't erase its own signal
TRENDING_Z        = 2.0
ELEVATED_Z        = 1.0
LOW_Z             = -1.0

TIMEOUT     = 20
MAX_RETRIES = 3
RETRY_SLEEP = 1.2

HEADERS = {
    "User-Agent": (
        "Mozilla/5.0 (Macintosh; Intel Mac OS 10_15_7) "
        "AppleWebKit/537.36 (KHTML, like Gecko) "
        "Chrome/120.0.0.0 Safari/537.36"
    ),
    "Accept": "application/rss+xml, application/xml, text/xml, */*;q=0.8",
    "Accept-Language": "en-US,en;q=0.9",
}

OUTPUT_DIR  = Path("public")
OUTPUT_FILE = OUTPUT_DIR / "country_mentions.json"

# ── Source-bias discount ───────────────────────────────────
# When a source mentions its OWN country, that mention is
# worth HOME_SOURCE_WEIGHT instead of 1.0 to dampen ambient
# domestic references (e.g. BBC constantly saying "London",
# CBC constantly saying "Canada").
# 0.25 = one home-source mention ≈ one-quarter of a foreign mention.
HOME_SOURCE_WEIGHT: float = 0.25

# Maps each source name → the country it is "home" to.
# Only UK and Canadian outlets need entries; US outlets cover
# the US itself which is not in our tracked-country list.
SOURCE_HOME_COUNTRY: Dict[str, str] = {
    # UK outlets  →  United Kingdom
    "BBC World":       "United Kingdom",
    "The Guardian":    "United Kingdom",
    "The Times UK":    "United Kingdom",
    "The Telegraph":   "United Kingdom",
    "The Independent": "United Kingdom",
    "Sky News":        "United Kingdom",
    "The Economist":   "United Kingdom",
    "Financial Times": "United Kingdom",
    # Canadian outlets  →  Canada
    "CBC World":       "Canada",
    "Globe and Mail":  "Canada",
    "National Post":   "Canada",
    "Toronto Star":    "Canada",
    "CTV News":        "Canada",
}


# ──────────────────────────────────────────────────────────
# SEED BASELINE
# ──────────────────────────────────────────────────────────
# Realistic "quiet news day" mean mention counts per country
# across ~500 articles from 30 sources in a 24h window.
# Used as the baseline on run #1 (cold start) so trending
# detection works immediately without waiting for history to build.
# Std is set to 40% of mean (reasonable for news counts).

# ── Seed baselines reflect city-expanded aliases ──────────
# Counts are expected weighted mentions per 24h window across ~500 articles.
# Values are higher than the pre-city baseline to account for major-city
# coverage that now rolls up to the country count.
# Seed baselines = expected mention counts on a QUIET news day.
# Calibrated against observed real RSS data (city-expanded aliases, ~500 articles/day).
# These stay active for the first 30 runs (~15 days); after that the
# rolling 30-day window takes over entirely.
#
# Key calibration anchors from observed data (today is an Iran/Israel spike day):
#   Russia ~26, Ukraine ~17, China ~19, UK ~12-26, France ~7-9,
#   Canada ~4-7, India ~8, Syria ~17 (currently elevated), Israel ~40-47 (spike)
# Quiet-day estimates set ~20-30% below current observed where war/conflict
# is clearly inflating counts right now.
SEED_BASELINE: Dict[str, float] = {
    "Russia":         25.0,   # Moscow + SPb; consistent war-adjacent coverage
    "China":          20.0,   # Beijing + Shanghai + cities; trade/geopolitics staple
    "Ukraine":        20.0,   # Kyiv + front-line cities; ongoing war baseline
    "Israel":         15.0,   # Jerusalem + Tel Aviv; quiet-day estimate (currently spiked)
    "Palestine":       8.0,   # Gaza + West Bank; currently quiet relative to Israel
    "Iran":           15.0,   # Tehran + cities; currently massively spiked, seed = quiet
    "United Kingdom": 15.0,   # London + cities; home-source weighted down
    "Germany":         8.0,   # Berlin + cities; observed ~1-6 today
    "France":          8.0,   # Paris + cities; observed ~6-9 today
    "India":           8.0,   # Observed consistently ~8; cities add little extra
    "Pakistan":        5.0,   # Karachi + Lahore; sporadically covered
    "North Korea":     5.0,   # Pyongyang; steady low-level coverage
    "South Korea":     6.0,   # Seoul + Busan; tech/politics coverage
    "Japan":           8.0,   # Tokyo + Osaka; consistent coverage
    "Taiwan":          6.0,   # Taipei; China-tension driven
    "Syria":           6.0,   # Damascus + Aleppo; quiet-day estimate (currently elevated)
    "Turkey":          6.0,   # Istanbul + Ankara; moderate steady coverage
    "Saudi Arabia":    5.0,   # Riyadh + Jeddah; observed ~1-2 today, seed more generous
    "UAE":             5.0,   # Dubai + Abu Dhabi; observed ~6-7 today
    "Yemen":           4.0,   # Sanaa + Aden; Houthi coverage, sporadic
    "Canada":          6.0,   # Ottawa + Toronto + Vancouver; home-source weighted
    "Mexico":          5.0,   # Mexico City + others; observed ~2-3 today
    "Brazil":          6.0,   # Sao Paulo + Rio; observed ~2-3 today, cities should help
    "Colombia":        6.0,   # Bogota + Medellin; observed 7-19 (possible spike today)
    "Venezuela":       4.0,   # Caracas; observed ~2-3
    "Cuba":            3.0,   # Havana; observed ~1
    "Argentina":       5.0,   # Buenos Aires; sporadic Milei/economy coverage
    "Chile":           4.0,   # Santiago; observed ~1-3
    "Peru":            3.0,   # Lima; low coverage
    "Panama":          3.0,   # Panama City/Canal; Trump rhetoric drives spikes
    "El Salvador":     3.0,   # San Salvador; Bukele coverage
    "Nigeria":         5.0,   # Lagos + Abuja; observed 0-18 (spike today)
    "Sudan":           4.0,   # Khartoum + Darfur; ongoing conflict, sporadic
    "Somalia":         3.0,   # Mogadishu; al-Shabaab coverage, sporadic
    "Libya":           3.0,   # Tripoli + Benghazi; low steady coverage
    "Egypt":           5.0,   # Cairo + Alexandria; regional hub coverage
    "Algeria":         3.0,   # Algiers; low coverage
    "Morocco":         4.0,   # Casablanca + Rabat; moderate coverage
    "Myanmar":         4.0,   # Yangon; civil war coverage, sporadic
    "Indonesia":       4.0,   # Jakarta; large country, underreported in Western press
    "Vietnam":         3.0,   # Ho Chi Minh + Hanoi; low Western coverage
    "Armenia":         3.0,   # Yerevan; post-Karabakh, sporadic
    "Azerbaijan":      3.0,   # Baku; post-Karabakh, sporadic
    "Denmark":         5.0,   # Copenhagen + Greenland; elevated due to Trump/Greenland
}

def _seed_std(mean: float) -> float:
    """Std = 40% of mean, floor of 1.0 to avoid division-by-zero."""
    return max(1.5, mean * 0.6)


# ──────────────────────────────────────────────────────────
# 30 CREDIBLE US / UK / CA NEWS SOURCES  (RSS)
# ──────────────────────────────────────────────────────────

RSS_SOURCES: Dict[str, str] = {
    # ── United States ──────────────────────────────────────
    "AP News":             "https://rsshub.app/apnews/topics/ap-top-news",
    "Reuters":             "https://feeds.reuters.com/reuters/topNews",
    "NPR World":           "https://www.npr.org/rss/rss.php?id=1004",
    "PBS NewsHour":        "https://www.pbs.org/newshour/feeds/rss/world",
    "ABC News":            "https://feeds.abcnews.com/abcnews/internationalheadlines",
    "CBS News":            "https://www.cbsnews.com/latest/rss/world",
    "NBC News":            "https://feeds.nbcnews.com/nbcnews/public/world",
    "CNN":                 "http://rss.cnn.com/rss/edition_world.rss",
    "Fox News":            "https://moxie.foxnews.com/google-publisher/world.xml",
    "New York Times":      "https://rss.nytimes.com/services/xml/rss/nyt/World.xml",
    "Washington Post":     "https://feeds.washingtonpost.com/rss/world",
    "Wall Street Journal": "https://feeds.a.dj.com/rss/RSSWorldNews.xml",
    "Politico":            "https://rss.politico.com/politics-news.xml",
    "The Hill":            "https://thehill.com/feed/",
    "Foreign Policy":      "https://foreignpolicy.com/feed/",
    "Defense One":         "https://www.defenseone.com/rss/all/",
    "Voice of America":    "https://www.voanews.com/api/zk_$egt",

    # ── United Kingdom ─────────────────────────────────────
    "BBC World":           "https://feeds.bbci.co.uk/news/world/rss.xml",
    "The Guardian":        "https://www.theguardian.com/world/rss",
    "The Times UK":        "https://www.thetimes.co.uk/rss/world.xml",
    "The Telegraph":       "https://www.telegraph.co.uk/rss.xml",
    "The Independent":     "https://www.independent.co.uk/news/world/rss",
    "Sky News":            "https://feeds.skynews.com/feeds/rss/world.xml",
    "The Economist":       "https://www.economist.com/international/rss.xml",
    "Financial Times":     "https://www.ft.com/world?format=rss",

    # ── Canada ─────────────────────────────────────────────
    "CBC World":           "https://rss.cbc.ca/lineup/world.xml",
    "Globe and Mail":      "https://www.theglobeandmail.com/arc/outboundfeeds/rss/category/world/",
    "National Post":       "https://nationalpost.com/feed/",
    "Toronto Star":        "https://www.thestar.com/content/thestar/feed.rss",
    "CTV News":            "https://www.ctvnews.ca/rss/ctvnews-ca-world-public-rss-1.822289",
}


# ──────────────────────────────────────────────────────────
# TRACKED COUNTRIES
# ──────────────────────────────────────────────────────────

COUNTRIES = [
    {"country": "Russia",         "iso2": "RU"},
    {"country": "India",          "iso2": "IN"},
    {"country": "Pakistan",       "iso2": "PK"},
    {"country": "China",          "iso2": "CN"},
    {"country": "United Kingdom", "iso2": "GB"},
    {"country": "Germany",        "iso2": "DE"},
    {"country": "UAE",            "iso2": "AE"},
    {"country": "Saudi Arabia",   "iso2": "SA"},
    {"country": "Israel",         "iso2": "IL"},
    {"country": "Palestine",      "iso2": "PS"},
    {"country": "Mexico",         "iso2": "MX"},
    {"country": "Brazil",         "iso2": "BR"},
    {"country": "Canada",         "iso2": "CA"},
    {"country": "Nigeria",        "iso2": "NG"},
    {"country": "Japan",          "iso2": "JP"},
    {"country": "Iran",           "iso2": "IR"},
    {"country": "Syria",          "iso2": "SY"},
    {"country": "France",         "iso2": "FR"},
    {"country": "Turkey",         "iso2": "TR"},
    {"country": "Venezuela",      "iso2": "VE"},
    {"country": "Vietnam",        "iso2": "VN"},
    {"country": "Taiwan",         "iso2": "TW"},
    {"country": "South Korea",    "iso2": "KR"},
    {"country": "North Korea",    "iso2": "KP"},
    {"country": "Indonesia",      "iso2": "ID"},
    {"country": "Myanmar",        "iso2": "MM"},
    {"country": "Armenia",        "iso2": "AM"},
    {"country": "Azerbaijan",     "iso2": "AZ"},
    {"country": "Morocco",        "iso2": "MA"},
    {"country": "Somalia",        "iso2": "SO"},
    {"country": "Yemen",          "iso2": "YE"},
    {"country": "Libya",          "iso2": "LY"},
    {"country": "Egypt",          "iso2": "EG"},
    {"country": "Algeria",        "iso2": "DZ"},
    {"country": "Argentina",      "iso2": "AR"},
    {"country": "Chile",          "iso2": "CL"},
    {"country": "Peru",           "iso2": "PE"},
    {"country": "Cuba",           "iso2": "CU"},
    {"country": "Colombia",       "iso2": "CO"},
    {"country": "Panama",         "iso2": "PA"},
    {"country": "El Salvador",    "iso2": "SV"},
    {"country": "Denmark",        "iso2": "DK"},
    {"country": "Sudan",          "iso2": "SD"},
    {"country": "Ukraine",        "iso2": "UA"},
]

COUNTRY_ALIASES: Dict[str, List[str]] = {
    # Aliases include: country name/demonyms, capital city, major cities (pop >1M),
    # and key political figures / organisations.
    "Russia":         ["russia", "russian", "russians", "moscow", "kremlin", "putin",
                       "saint petersburg", "st. petersburg", "novosibirsk", "yekaterinburg",
                       "nizhny novgorod", "kazan", "chelyabinsk", "omsk", "samara", "rostov"],
    "India":          ["india", "indian", "indians", "new delhi", "modi",
                       "mumbai", "delhi", "bangalore", "bengaluru", "hyderabad", "ahmedabad",
                       "chennai", "kolkata", "surat", "pune", "jaipur", "lucknow",
                       "kanpur", "nagpur", "patna", "indore", "vadodara", "bhopal"],
    "Pakistan":       ["pakistan", "pakistani", "pakistanis", "islamabad",
                       "karachi", "lahore", "faisalabad", "rawalpindi", "gujranwala",
                       "peshawar", "multan", "hyderabad sind", "quetta"],
    "China":          ["china", "chinese", "beijing", "xi jinping", "prc",
                       "shanghai", "guangzhou", "shenzhen", "chengdu", "chongqing",
                       "tianjin", "wuhan", "dongguan", "nanjing", "hangzhou",
                       "xi'an", "shenyang", "harbin", "qingdao", "zhengzhou",
                       "foshan", "dalian", "kunming", "changsha"],
    "United Kingdom": ["united kingdom", "britain", "british", "england", "english",
                       "london", "uk ", " uk,", "sunak", "starmer",
                       "birmingham", "manchester", "leeds", "glasgow", "liverpool",
                       "sheffield", "edinburgh", "bristol", "cardiff"],
    "Germany":        ["germany", "german", "germans", "berlin", "bundestag", "scholz",
                       "hamburg", "munich", "cologne", "frankfurt", "stuttgart",
                       "dusseldorf", "dortmund", "essen", "leipzig", "bremen"],
    "UAE":            ["uae", "united arab emirates", "abu dhabi", "dubai", "emirati",
                       "sharjah"],
    "Saudi Arabia":   ["saudi arabia", "saudi", "saudis", "riyadh", "mbs", "aramco",
                       "jeddah", "mecca", "medina"],
    "Israel":         ["israel", "israeli", "israelis", "jerusalem", "tel aviv",
                       "idf", "netanyahu", "haifa", "rishon lezion", "petah tikva",
                       "ashdod", "beersheba"],
    "Palestine":      ["palestine", "palestinian", "palestinians", "gaza", "west bank",
                       "hamas", "ramallah", "nablus", "jenin", "hebron"],
    "Mexico":         ["mexico", "mexican", "mexicans", "mexico city", "sheinbaum",
                       "guadalajara", "monterrey", "puebla", "tijuana", "leon",
                       "juarez", "ciudad juarez", "zapopan", "nezahualcoyotl"],
    "Brazil":         ["brazil", "brazilian", "brazilians", "brasilia", "lula",
                       "sao paulo", "são paulo", "rio de janeiro", "salvador",
                       "fortaleza", "belo horizonte", "manaus", "curitiba", "recife",
                       "porto alegre", "goiania", "belem", "guarulhos", "campinas"],
    "Canada":         ["canada", "canadian", "canadians", "ottawa", "trudeau", "carney",
                       "toronto", "montreal", "vancouver", "calgary", "edmonton",
                       "winnipeg", "quebec city"],
    "Nigeria":        ["nigeria", "nigerian", "nigerians", "abuja", "lagos",
                       "kano", "ibadan", "kaduna", "port harcourt", "benin city",
                       "maiduguri", "zaria", "aba", "jos", "ilorin"],
    "Japan":          ["japan", "japanese", "tokyo", "kishida", "ishiba",
                       "osaka", "nagoya", "sapporo", "fukuoka", "kobe", "kawasaki",
                       "kyoto", "saitama", "hiroshima"],
    "Iran":           ["iran", "iranian", "iranians", "tehran", "khamenei",
                       "irgc", "rouhani", "raisi", "pezeshkian", "hormuz",
                       "mashhad", "isfahan", "karaj", "tabriz", "shiraz",
                       "ahvaz", "qom", "kermanshah"],
    "Syria":          ["syria", "syrian", "syrians", "damascus", "al-sharaa", "hts",
                       "aleppo", "homs", "latakia", "hama", "deir ez-zor", "raqqa"],
    "France":         ["france", "french", "paris", "macron", "elysee",
                       "marseille", "lyon", "toulouse", "nice", "nantes",
                       "montpellier", "strasbourg", "bordeaux", "lille"],
    "Turkey":         ["turkey", "turkish", "ankara", "erdogan", "istanbul",
                       "izmir", "bursa", "adana", "gaziantep", "konya",
                       "mersin", "diyarbakir", "kayseri"],
    "Venezuela":      ["venezuela", "venezuelan", "venezuelans", "caracas", "maduro",
                       "maracaibo", "valencia", "barquisimeto", "maracay"],
    "Vietnam":        ["vietnam", "vietnamese", "hanoi",
                       "ho chi minh city", "saigon", "hai phong", "da nang", "bien hoa",
                       "can tho", "hue"],
    "Taiwan":         ["taiwan", "taiwanese", "taipei",
                       "kaohsiung", "taichung", "tainan", "taoyuan"],
    "South Korea":    ["south korea", "south korean", "seoul",
                       "busan", "incheon", "daegu", "daejeon", "gwangju", "suwon",
                       "ulsan"],
    "North Korea":    ["north korea", "north korean", "pyongyang", "kim jong"],
    "Indonesia":      ["indonesia", "indonesian", "jakarta", "prabowo",
                       "surabaya", "bandung", "medan", "bekasi", "tangerang",
                       "depok", "semarang", "palembang", "makassar", "south tangerang",
                       "batam", "pekanbaru", "bandar lampung", "malang"],
    "Myanmar":        ["myanmar", "burmese", "naypyidaw", "tatmadaw", "burma",
                       "yangon", "mandalay"],
    "Armenia":        ["armenia", "armenian", "armenians", "yerevan"],
    "Azerbaijan":     ["azerbaijan", "azerbaijani", "baku", "aliyev",
                       "ganja", "sumqayit"],
    "Morocco":        ["morocco", "moroccan", "moroccans", "rabat",
                       "casablanca", "fez", "marrakech", "tangier", "agadir",
                       "meknes", "oujda"],
    "Somalia":        ["somalia", "somali", "somalis", "mogadishu", "al-shabaab"],
    "Yemen":          ["yemen", "yemeni", "yemenis", "sanaa", "houthis", "houthi",
                       "aden", "taiz", "hodeidah"],
    "Libya":          ["libya", "libyan", "libyans", "tripoli", "benghazi",
                       "misrata", "tobruk"],
    "Egypt":          ["egypt", "egyptian", "egyptians", "cairo", "sisi",
                       "alexandria", "giza", "shubra el kheima", "port said",
                       "suez", "luxor", "aswan"],
    "Algeria":        ["algeria", "algerian", "algerians", "algiers",
                       "oran", "constantine", "annaba", "blida", "batna"],
    "Argentina":      ["argentina", "argentinian", "argentinians", "buenos aires", "milei",
                       "cordoba", "rosario", "mendoza", "la plata", "san miguel de tucuman",
                       "mar del plata", "quilmes", "salta"],
    "Chile":          ["chile", "chilean", "chileans", "santiago",
                       "valparaiso", "concepcion", "antofagasta"],
    "Peru":           ["peru", "peruvian", "peruvians", "lima",
                       "arequipa", "trujillo", "chiclayo", "callao", "iquitos"],
    "Cuba":           ["cuba", "cuban", "cubans", "havana",
                       "santiago de cuba", "camaguey", "holguin"],
    "Colombia":       ["colombia", "colombian", "colombians", "bogota", "petro",
                       "medellin", "cali", "barranquilla", "cartagena", "cucuta",
                       "bucaramanga", "pereira"],
    "Panama":         ["panama", "panamanian", "panamanians", "panama city", "panama canal",
                       "colon"],
    "El Salvador":    ["el salvador", "salvadoran", "salvadorans", "san salvador", "bukele"],
    "Denmark":        ["denmark", "danish", "danes", "copenhagen", "greenland",
                       "aarhus", "odense", "aalborg"],
    "Sudan":          ["sudan", "sudanese", "khartoum", "rsf", "darfur",
                       "omdurman", "port sudan", "kassala"],
    "Ukraine":        ["ukraine", "ukrainian", "ukrainians", "kyiv", "kiev",
                       "zelensky", "zelenskyy",
                       "kharkiv", "dnipro", "odessa", "odesa", "donetsk",
                       "zaporizhzhia", "lviv", "kryvyi rih", "mykolaiv", "mariupol"],
}


# ──────────────────────────────────────────────────────────
# HELPERS
# ──────────────────────────────────────────────────────────

def _norm(s: str) -> str:
    return " ".join((s or "").lower().split())

def fetch_text(url: str) -> Optional[str]:
    sess = requests.Session()
    sess.headers.update(HEADERS)
    for attempt in range(1, MAX_RETRIES + 1):
        try:
            r = sess.get(url, timeout=TIMEOUT, allow_redirects=True)
            if r.status_code == 200 and r.text:
                return r.text
        except requests.RequestException:
            pass
        time.sleep(RETRY_SLEEP * attempt)
    return None

def parse_dt(entry: dict) -> Optional[datetime]:
    for k in ("published_parsed", "updated_parsed", "created_parsed"):
        st = entry.get(k)
        if st:
            try:
                return datetime(*st[:6], tzinfo=timezone.utc)
            except Exception:
                pass
    for k in ("published", "updated", "created"):
        v = entry.get(k)
        if v:
            try:
                dt = dtparser.parse(v)
                if dt.tzinfo is None:
                    dt = dt.replace(tzinfo=timezone.utc)
                return dt.astimezone(timezone.utc)
            except Exception:
                continue
    return None

def canonicalize_url(url: str) -> str:
    try:
        u = urlparse(url)
        qs = parse_qs(u.query, keep_blank_values=True)
        drop = {"utm_source", "utm_medium", "utm_campaign", "utm_term", "utm_content",
                "fbclid", "gclid", "mc_cid", "mc_eid"}
        for p in list(qs.keys()):
            if p.lower() in drop:
                qs.pop(p, None)
        new_q = urlencode({k: v[0] for k, v in qs.items() if v})
        path = u.path or ""
        if path != "/" and path.endswith("/"):
            path = path[:-1]
        return urlunparse((u.scheme, u.netloc, path, u.params, new_q, ""))
    except Exception:
        return url

def _parse_iso(s: str) -> datetime:
    try:
        return dtparser.parse(s).astimezone(timezone.utc)
    except Exception:
        return datetime.min.replace(tzinfo=timezone.utc)


# ──────────────────────────────────────────────────────────
# RSS FETCHING
# ──────────────────────────────────────────────────────────

def fetch_articles(window_hours: int) -> Tuple[List[dict], int]:
    now    = datetime.now(timezone.utc)
    cutoff = now - timedelta(hours=window_hours)

    seen_urls: set = set()
    articles: List[dict] = []
    total_scanned = 0

    for source, feed_url in RSS_SOURCES.items():
        raw = fetch_text(feed_url)
        if not raw:
            print(f"  ⚠  Could not fetch: {source}")
            continue

        d = feedparser.parse(raw)
        entries = getattr(d, "entries", [])
        total_scanned += len(entries)

        for e in entries:
            title = (e.get("title") or "").strip()
            link  = canonicalize_url((e.get("link") or "").strip())
            if not title or not link:
                continue
            if link in seen_urls:
                continue

            dt = parse_dt(e)
            if dt and dt < cutoff:
                continue

            seen_urls.add(link)
            summary = re.sub(r"<[^>]+>", " ",
                             e.get("summary") or e.get("description") or "")
            combined = f"{title} {summary}"

            articles.append({
                "title":  title,
                "url":    link,
                "source": source,
                "text":   _norm(combined),
            })

    return articles, total_scanned


# ──────────────────────────────────────────────────────────
# MENTION COUNTING
# ──────────────────────────────────────────────────────────

def count_mentions(articles: List[dict]) -> Dict[str, float]:
    """
    Count weighted article mentions per country.

    A mention from a source that is 'home' to that country
    (e.g. BBC mentioning United Kingdom, CBC mentioning Canada)
    counts as HOME_SOURCE_WEIGHT (0.25) rather than 1.0 to
    reduce ambient domestic-coverage bias.  All other mentions
    count as 1.0.  Final counts are rounded to 2 decimal places
    so the JSON stays readable; downstream z-score math uses floats.
    """
    counts: Dict[str, float] = {c["country"]: 0.0 for c in COUNTRIES}
    for art in articles:
        text       = art["text"]
        source     = art.get("source", "")
        home_cntry = SOURCE_HOME_COUNTRY.get(source)   # None for US sources

        for c in COUNTRIES:
            name    = c["country"]
            aliases = COUNTRY_ALIASES.get(name, [name.lower()])
            for alias in aliases:
                if alias in text:
                    weight = HOME_SOURCE_WEIGHT if (home_cntry == name) else 1.0
                    counts[name] = round(counts[name] + weight, 2)
                    break

    return counts


# ──────────────────────────────────────────────────────────
# STATISTICAL ANALYSIS
# ──────────────────────────────────────────────────────────

def _mean_std(values: List[float]) -> Tuple[float, float]:
    if not values:
        return 0.0, 0.0
    n  = len(values)
    mu = sum(values) / n
    if n < 2:
        return mu, 0.0
    var = sum((x - mu) ** 2 for x in values) / (n - 1)
    return mu, math.sqrt(var)

def compute_trend_status(z: float) -> str:
    if z >= TRENDING_Z:
        return "trending"
    if z >= ELEVATED_Z:
        return "elevated"
    if z <= LOW_Z:
        return "low"
    return "normal"

def _cold_start_z(country: str, current: float,
                  all_counts: Dict[str, float]) -> Tuple[float, float, float, str]:
    """
    Hybrid z-score for when there is insufficient run history.

    Combines two signals:
      1. Seed baseline z — how far above the country's typical quiet-day level?
      2. Relative z     — how far above THIS run's mean across all countries?

    Takes the HIGHER of the two, so a country that is both way above its own
    typical level AND dominating the current cycle (e.g. Iran during a war)
    gets the full signal.

    Returns (z, baseline_mean, baseline_std, method_label)
    """
    # Signal 1: against per-country seed baseline
    seed_mean = SEED_BASELINE.get(country, 3.0)
    seed_std  = _seed_std(seed_mean)
    seed_z    = (current - seed_mean) / seed_std

    # Signal 2: relative within current run distribution
    run_values = [float(v) for v in all_counts.values()]
    run_mean, run_std = _mean_std(run_values)
    rel_z = (current - run_mean) / run_std if run_std > 0 else 0.0

    z = max(seed_z, rel_z)
    return z, seed_mean, seed_std, "cold_start_hybrid"


def analyze(current_counts: Dict[str, float],
            existing_data: dict,
            window_end: datetime) -> List[dict]:
    existing_map: Dict[str, dict] = {}
    for c in existing_data.get("countries", []):
        existing_map[c["country"]] = c

    results: List[dict] = []
    cutoff_history        = window_end - timedelta(days=HISTORY_DAYS)
    baseline_window_start = window_end - timedelta(days=BASELINE_DAYS)
    recency_cutoff        = window_end - timedelta(days=BASELINE_RECENCY_EXCLUDE_DAYS)

    for c in COUNTRIES:
        name    = c["country"]
        iso2    = c["iso2"]
        current = current_counts.get(name, 0)

        old     = existing_map.get(name, {})
        history = old.get("history", [])
        history = [h for h in history
                   if _parse_iso(h.get("window_end", "")) >= cutoff_history]

        # Baseline = runs from 30 days ago up to 3 days ago.
        # Excluding the most recent 3 days prevents an ongoing news event
        # from normalising itself into the baseline and collapsing its own z-score.
        baseline_values = [
            float(h["mentions"])
            for h in history
            if baseline_window_start
               <= _parse_iso(h.get("window_end", ""))
               < recency_cutoff
        ]

        mu, sigma  = _mean_std(baseline_values)
        baseline_n = len(baseline_values)
        method     = "rolling_30d_excl3"

        if baseline_n >= BASELINE_MIN_RUNS:
            if sigma > 0:
                z = (current - mu) / sigma
            else:
                # std=0 means all baseline values were identical.
                # Use a floor std of max(1.5, 20% of mean) so that small
                # integer wobbles on low-volume countries don't falsely trend.
                # e.g. Somalia 0→1 with mean=0: floor_std=1.5, z=0.67 (normal)
                #      Germany 1→6 with mean=1: floor_std=1.5, z=3.3 (trending - real)
                floor_std = max(1.5, mu * 0.20)
                z = (current - mu) / floor_std
        else:
            z, mu, sigma, method = _cold_start_z(name, current, current_counts)

        trend_status = compute_trend_status(z)
        pct_change   = (round((current - mu) / mu * 100, 1) if mu > 0 else None)

        history.append({
            "window_end": window_end.isoformat().replace("+00:00", "Z"),
            "mentions":   current,
        })

        results.append({
            "country":          name,
            "iso2":             iso2,
            "mentions":         round(current, 2),   # weighted (home-source bias corrected)
            "baseline_mean":    round(mu, 2),
            "baseline_std":     round(sigma, 2),
            "baseline_n":       baseline_n,
            "baseline_method":  method,
            "z_score":          round(z, 3),
            "trend_status":     trend_status,
            "pct_change":       pct_change,
            "history":          history,
        })

    results.sort(key=lambda x: x["mentions"], reverse=True)
    return results


# ──────────────────────────────────────────────────────────
# MAIN
# ──────────────────────────────────────────────────────────

def main():
    now          = datetime.now(timezone.utc)
    window_end   = now
    window_start = now - timedelta(hours=WINDOW_HOURS)

    print(f"🔍 Scanning {window_start.isoformat()} → {window_end.isoformat()}")

    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)
    existing_data: dict = {}
    if OUTPUT_FILE.exists():
        try:
            existing_data = json.loads(OUTPUT_FILE.read_text(encoding="utf-8"))
            n = len(existing_data.get("countries", []))
            print(f"📂 Loaded existing data ({n} countries in history)")
        except Exception as e:
            print(f"⚠  Could not parse existing JSON: {e}")

    print("📡 Fetching RSS feeds…")
    articles, total_scanned = fetch_articles(WINDOW_HOURS)
    print(f"   → {len(articles)} unique articles in window (scanned {total_scanned} entries)")

    print("🔢 Counting country mentions…")
    counts = count_mentions(articles)

    top = sorted(counts.items(), key=lambda x: x[1], reverse=True)[:10]
    for name, n in top:
        print(f"   {n:6.1f}  {name}")

    print("📊 Computing z-scores and trend status…")
    country_results = analyze(counts, existing_data, window_end)

    trending = [c for c in country_results if c["trend_status"] == "trending"]
    elevated = [c for c in country_results if c["trend_status"] == "elevated"]
    if trending:
        print(f"🔥 Trending:  {', '.join(c['country'] for c in trending)}")
    if elevated:
        print(f"📈 Elevated:  {', '.join(c['country'] for c in elevated)}")

    output = {
        "meta": {
            "generated_at":         window_end.isoformat().replace("+00:00", "Z"),
            "window_start":         window_start.isoformat().replace("+00:00", "Z"),
            "window_end":           window_end.isoformat().replace("+00:00", "Z"),
            "window_hours":         WINDOW_HOURS,
            "articles_scanned":     total_scanned,
            "articles_in_window":   len(articles),
            "sources_count":        len(RSS_SOURCES),
            "trending_threshold_z": TRENDING_Z,
            "elevated_threshold_z": ELEVATED_Z,
        },
        "countries": country_results,
    }

    OUTPUT_FILE.write_text(
        json.dumps(output, ensure_ascii=False, indent=2),
        encoding="utf-8",
    )
    print(f"✅ Wrote {len(country_results)} countries → {OUTPUT_FILE.resolve()}")


if __name__ == "__main__":
    main()
