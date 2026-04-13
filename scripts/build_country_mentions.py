"""
build_country_mentions.py
=========================
Scans 30 credible US/UK/CA news sources via RSS for a 24-hour window,
counts how many articles mention each tracked country,
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
BASELINE_MIN_RUNS = 100     # minimum baseline points to use rolling stats.
                              # The baseline window is 30d minus the 3-day recency
                              # exclusion = 27 usable days. At ~6-7 runs/day (observed
                              # cadence), 100 points ≈ 15 days of usable history,
                              # meaning rolling baseline kicks in ~18 days after a
                              # country is first tracked. Below this we fall back to
                              # cold_start_hybrid.
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
# Std is set to 40-60% of mean (reasonable for news counts).

SEED_BASELINE: Dict[str, float] = {
    # ── Original 44 ──────────────────────────────────────
    "Russia":         25.0,
    "China":          20.0,
    "Ukraine":        20.0,
    "Israel":         15.0,
    "Palestine":       8.0,
    "Iran":           15.0,
    "United Kingdom": 15.0,
    "Germany":         8.0,
    "France":          8.0,
    "India":           8.0,
    "Pakistan":        5.0,
    "North Korea":     5.0,
    "South Korea":     6.0,
    "Japan":           8.0,
    "Taiwan":          6.0,
    "Syria":           6.0,
    "Turkey":          6.0,
    "Saudi Arabia":    5.0,
    "UAE":             5.0,
    "Yemen":           4.0,
    "Canada":          6.0,
    "Mexico":          5.0,
    "Brazil":          6.0,
    "Colombia":        6.0,
    "Venezuela":       4.0,
    "Cuba":            3.0,
    "Argentina":       5.0,
    "Chile":           4.0,
    "Peru":            3.0,
    "Panama":          3.0,
    "El Salvador":     3.0,
    "Nigeria":         5.0,
    "Sudan":           4.0,
    "Somalia":         3.0,
    "Libya":           3.0,
    "Egypt":           5.0,
    "Algeria":         3.0,
    "Morocco":         4.0,
    "Myanmar":         4.0,
    "Indonesia":       4.0,
    "Vietnam":         3.0,
    "Armenia":         3.0,
    "Azerbaijan":      3.0,
    "Denmark":         5.0,

    # ── New additions ─────────────────────────────────────
    # Anglosphere / Western Europe majors
    "Australia":      10.0,
    "New Zealand":     4.0,
    "Spain":           6.0,
    "Italy":           6.0,
    "Poland":          6.0,
    "Netherlands":     5.0,
    "Belgium":         4.0,
    "Portugal":        3.0,
    "Czech Republic":  3.0,
    "Norway":          3.0,
    "Romania":         3.0,
    "Sweden":          4.0,
    "Finland":         3.0,
    "Switzerland":     4.0,
    "Austria":         3.0,
    "Hungary":         3.0,
    "Ireland":         3.0,
    "Greece":          3.0,
    "Luxembourg":      2.0,
    "Iceland":         2.0,
    "Malta":           1.5,
    "Cyprus":          2.0,

    # Eastern Europe / Balkans / FSU
    "Belarus":         4.0,
    "Serbia":          3.0,
    "Albania":         2.0,
    "Bulgaria":        2.0,
    "Moldova":         2.0,
    "Kosovo":          2.0,
    "North Macedonia": 1.5,
    "Bosnia":          2.0,
    "Montenegro":      1.5,
    "Croatia":         2.0,
    "Slovakia":        2.0,
    "Slovenia":        1.5,
    "Lithuania":       2.0,
    "Latvia":          2.0,
    "Estonia":         2.0,
    "Georgia":         2.5,
    "Kazakhstan":      3.0,
    "Uzbekistan":      2.5,
    "Turkmenistan":    1.5,
    "Kyrgyzstan":      1.5,
    "Tajikistan":      1.5,

    # Middle East / North Africa extras
    "Iraq":            5.0,
    "Afghanistan":     5.0,
    "Jordan":          3.0,
    "Lebanon":         4.0,
    "Kuwait":          2.5,
    "Bahrain":         2.0,
    "Oman":            2.5,
    "Qatar":           3.0,
    "Tunisia":         3.0,

    # Asia-Pacific extras
    "Singapore":       4.0,
    "Philippines":     4.0,
    "Malaysia":        3.0,
    "Thailand":        3.0,
    "Cambodia":        2.0,
    "Laos":            1.5,
    "Bangladesh":      3.0,
    "Nepal":           2.0,
    "Sri Lanka":       2.5,
    "Mongolia":        1.5,
    "Brunei":          1.0,
    "Timor-Leste":     1.0,
    "Maldives":        1.5,
    "Bhutan":          1.0,
    "Papua New Guinea":1.5,
    "Hong Kong":       5.0,

    # Africa extras
    "South Africa":    5.0,
    "Kenya":           4.0,
    "Ethiopia":        4.0,
    "Ghana":           3.0,
    "Ivory Coast":     2.5,
    "Senegal":         2.5,
    "Rwanda":          2.5,
    "Uganda":          2.5,
    "Zimbabwe":        2.5,
    "Zambia":          2.0,
    "Cameroon":        2.5,
    "Mozambique":      2.0,
    "Burkina Faso":    2.5,
    "Niger":           2.5,
    "Chad":            2.5,
    "Guinea":          2.0,
    "Angola":          2.5,
    "DRC":             3.5,
    "South Sudan":     3.0,
    "Eritrea":         2.0,
    "Djibouti":        1.5,
    "Mauritania":      1.5,
    "Liberia":         1.5,
    "Sierra Leone":    1.5,
    "Gabon":           1.5,
    "Congo":           2.0,
    "Namibia":         1.5,
    "Eswatini":        1.0,
    "Lesotho":         1.0,
    "Malawi":          1.5,
    "Tanzania":        2.0,
    "Madagascar":      1.5,
    "Botswana":        1.5,
    "Mali":            2.5,

    # Americas extras
    "Bolivia":         2.5,
    "Ecuador":         2.5,
    "Paraguay":        2.0,
    "Uruguay":         2.0,
    "Guyana":          2.0,
    "Dominican Republic": 2.0,
    "Haiti":           3.0,
    "Guatemala":       2.5,
    "Honduras":        2.0,
    "Nicaragua":       2.0,
    "Costa Rica":      2.0,
    "Bahamas":        1.5,
    "Trinidad and Tobago": 1.5,
    "Jamaica":         2.0,
}

def _seed_std(mean: float) -> float:
    """Std = 60% of mean, floor of 1.0 to avoid division-by-zero."""
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
    # ── Original 44 ──────────────────────────────────────
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

    # ── New additions ─────────────────────────────────────
    # Anglosphere / Western Europe majors
    {"country": "Australia",      "iso2": "AU"},
    {"country": "New Zealand",    "iso2": "NZ"},
    {"country": "Spain",          "iso2": "ES"},
    {"country": "Italy",          "iso2": "IT"},
    {"country": "Poland",         "iso2": "PL"},
    {"country": "Netherlands",    "iso2": "NL"},
    {"country": "Belgium",        "iso2": "BE"},
    {"country": "Portugal",       "iso2": "PT"},
    {"country": "Czech Republic", "iso2": "CZ"},
    {"country": "Norway",         "iso2": "NO"},
    {"country": "Romania",        "iso2": "RO"},
    {"country": "Sweden",         "iso2": "SE"},
    {"country": "Finland",        "iso2": "FI"},
    {"country": "Switzerland",    "iso2": "CH"},
    {"country": "Austria",        "iso2": "AT"},
    {"country": "Hungary",        "iso2": "HU"},
    {"country": "Ireland",        "iso2": "IE"},
    {"country": "Greece",         "iso2": "GR"},
    {"country": "Luxembourg",     "iso2": "LU"},
    {"country": "Iceland",        "iso2": "IS"},
    {"country": "Malta",          "iso2": "MT"},
    {"country": "Cyprus",         "iso2": "CY"},

    # Eastern Europe / Balkans / FSU
    {"country": "Belarus",        "iso2": "BY"},
    {"country": "Serbia",         "iso2": "RS"},
    {"country": "Albania",        "iso2": "AL"},
    {"country": "Bulgaria",       "iso2": "BG"},
    {"country": "Moldova",        "iso2": "MD"},
    {"country": "Kosovo",         "iso2": "XK"},
    {"country": "North Macedonia","iso2": "MK"},
    {"country": "Bosnia",         "iso2": "BA"},
    {"country": "Montenegro",     "iso2": "ME"},
    {"country": "Croatia",        "iso2": "HR"},
    {"country": "Slovakia",       "iso2": "SK"},
    {"country": "Slovenia",       "iso2": "SI"},
    {"country": "Lithuania",      "iso2": "LT"},
    {"country": "Latvia",         "iso2": "LV"},
    {"country": "Estonia",        "iso2": "EE"},
    {"country": "Georgia",        "iso2": "GE"},
    {"country": "Kazakhstan",     "iso2": "KZ"},
    {"country": "Uzbekistan",     "iso2": "UZ"},
    {"country": "Turkmenistan",   "iso2": "TM"},
    {"country": "Kyrgyzstan",     "iso2": "KG"},
    {"country": "Tajikistan",     "iso2": "TJ"},

    # Middle East / North Africa extras
    {"country": "Iraq",           "iso2": "IQ"},
    {"country": "Afghanistan",    "iso2": "AF"},
    {"country": "Jordan",         "iso2": "JO"},
    {"country": "Lebanon",        "iso2": "LB"},
    {"country": "Kuwait",         "iso2": "KW"},
    {"country": "Bahrain",        "iso2": "BH"},
    {"country": "Oman",           "iso2": "OM"},
    {"country": "Qatar",          "iso2": "QA"},
    {"country": "Tunisia",        "iso2": "TN"},

    # Asia-Pacific extras
    {"country": "Singapore",      "iso2": "SG"},
    {"country": "Philippines",    "iso2": "PH"},
    {"country": "Malaysia",       "iso2": "MY"},
    {"country": "Thailand",       "iso2": "TH"},
    {"country": "Cambodia",       "iso2": "KH"},
    {"country": "Laos",           "iso2": "LA"},
    {"country": "Bangladesh",     "iso2": "BD"},
    {"country": "Nepal",          "iso2": "NP"},
    {"country": "Sri Lanka",      "iso2": "LK"},
    {"country": "Mongolia",       "iso2": "MN"},
    {"country": "Brunei",         "iso2": "BN"},
    {"country": "Timor-Leste",    "iso2": "TL"},
    {"country": "Maldives",       "iso2": "MV"},
    {"country": "Bhutan",         "iso2": "BT"},
    {"country": "Papua New Guinea","iso2": "PG"},
    {"country": "Hong Kong",      "iso2": "HK"},

    # Africa extras
    {"country": "South Africa",   "iso2": "ZA"},
    {"country": "Kenya",          "iso2": "KE"},
    {"country": "Ethiopia",       "iso2": "ET"},
    {"country": "Ghana",          "iso2": "GH"},
    {"country": "Ivory Coast",    "iso2": "CI"},
    {"country": "Senegal",        "iso2": "SN"},
    {"country": "Rwanda",         "iso2": "RW"},
    {"country": "Uganda",         "iso2": "UG"},
    {"country": "Zimbabwe",       "iso2": "ZW"},
    {"country": "Zambia",         "iso2": "ZM"},
    {"country": "Cameroon",       "iso2": "CM"},
    {"country": "Mozambique",     "iso2": "MZ"},
    {"country": "Burkina Faso",   "iso2": "BF"},
    {"country": "Niger",          "iso2": "NE"},
    {"country": "Chad",           "iso2": "TD"},
    {"country": "Guinea",         "iso2": "GN"},
    {"country": "Angola",         "iso2": "AO"},
    {"country": "DRC",            "iso2": "CD"},
    {"country": "South Sudan",    "iso2": "SS"},
    {"country": "Eritrea",        "iso2": "ER"},
    {"country": "Djibouti",       "iso2": "DJ"},
    {"country": "Mauritania",     "iso2": "MR"},
    {"country": "Liberia",        "iso2": "LR"},
    {"country": "Sierra Leone",   "iso2": "SL"},
    {"country": "Gabon",          "iso2": "GA"},
    {"country": "Congo",          "iso2": "CG"},
    {"country": "Namibia",        "iso2": "NA"},
    {"country": "Eswatini",       "iso2": "SZ"},
    {"country": "Lesotho",        "iso2": "LS"},
    {"country": "Malawi",         "iso2": "MW"},
    {"country": "Tanzania",       "iso2": "TZ"},
    {"country": "Madagascar",     "iso2": "MG"},
    {"country": "Botswana",       "iso2": "BW"},
    {"country": "Mali",           "iso2": "ML"},

    # Americas extras
    {"country": "Bolivia",        "iso2": "BO"},
    {"country": "Ecuador",        "iso2": "EC"},
    {"country": "Paraguay",       "iso2": "PY"},
    {"country": "Uruguay",        "iso2": "UY"},
    {"country": "Guyana",         "iso2": "GY"},
    {"country": "Dominican Republic", "iso2": "DO"},
    {"country": "Haiti",          "iso2": "HT"},
    {"country": "Guatemala",      "iso2": "GT"},
    {"country": "Honduras",       "iso2": "HN"},
    {"country": "Nicaragua",      "iso2": "NI"},
    {"country": "Costa Rica",     "iso2": "CR"},
    {"country": "Trinidad and Tobago", "iso2": "TT"},
    {"country": "Jamaica",        "iso2": "JM"},
    {"country": "Bahamas",        "iso2": "BS"},
]


# ──────────────────────────────────────────────────────────
# COUNTRY ALIASES
# ──────────────────────────────────────────────────────────

COUNTRY_ALIASES: Dict[str, List[str]] = {
    # ── Original 44 ──────────────────────────────────────
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

    # ── New additions ─────────────────────────────────────
    # Anglosphere / Western Europe majors
    "Australia":      ["australia", "australian", "australians", "canberra", "albanese",
                       "sydney", "melbourne", "brisbane", "perth", "adelaide",
                       "gold coast", "newcastle nsw", "canberra", "wollongong",
                       "hobart", "darwin"],
    "New Zealand":    ["new zealand", "new zealander", "new zealanders", "wellington",
                       "auckland", "christchurch", "hamilton", "tauranga", "dunedin"],
    "Spain":          ["spain", "spanish", "spaniards", "madrid", "sanchez",
                       "barcelona", "valencia", "seville", "zaragoza", "malaga",
                       "murcia", "palma", "bilbao", "alicante", "cordoba"],
    "Italy":          ["italy", "italian", "italians", "rome", "meloni",
                       "milan", "naples", "turin", "palermo", "genoa",
                       "bologna", "florence", "bari", "catania", "venice"],
    "Poland":         ["poland", "polish", "poles", "warsaw", "tusk",
                       "krakow", "lodz", "wroclaw", "poznan", "gdansk",
                       "szczecin", "bydgoszcz", "lublin", "katowice"],
    "Netherlands":    ["netherlands", "dutch", "amsterdam", "rutte", "schoof",
                       "rotterdam", "the hague", "utrecht", "eindhoven",
                       "tilburg", "groningen", "almere", "breda"],
    "Belgium":        ["belgium", "belgian", "belgians", "brussels", "de croo",
                       "antwerp", "ghent", "charleroi", "liege", "bruges"],
    "Portugal":       ["portugal", "portuguese", "lisbon", "porto",
                       "braga", "setubal", "coimbra", "funchal"],
    "Czech Republic": ["czech republic", "czechia", "czech", "czechs", "prague",
                       "brno", "ostrava", "pilsen", "liberec"],
    "Norway":         ["norway", "norwegian", "norwegians", "oslo",
                       "bergen", "trondheim", "stavanger", "tromsø", "tromso"],
    "Romania":        ["romania", "romanian", "romanians", "bucharest",
                       "cluj-napoca", "timisoara", "iasi", "constanta", "craiova"],
    "Sweden":         ["sweden", "swedish", "swedes", "stockholm",
                       "gothenburg", "malmo", "uppsala", "vasteras", "orebro"],
    "Finland":        ["finland", "finnish", "finns", "helsinki",
                       "espoo", "tampere", "vantaa", "oulu", "turku"],
    "Switzerland":    ["switzerland", "swiss", "bern", "zurich",
                       "geneva", "basel", "lausanne", "winterthur"],
    "Austria":        ["austria", "austrian", "austrians", "vienna",
                       "graz", "linz", "salzburg", "innsbruck"],
    "Hungary":        ["hungary", "hungarian", "hungarians", "budapest", "orban",
                       "debrecen", "miskolc", "pecs", "gyor"],
    "Ireland":        ["ireland", "irish", "dublin", "varadkar", "harris",
                       "cork", "limerick", "galway", "waterford"],
    "Greece":         ["greece", "greek", "greeks", "athens", "mitsotakis",
                       "thessaloniki", "patras", "heraklion", "larissa"],
    "Luxembourg":     ["luxembourg", "luxembourgish", "luxembourg city"],
    "Iceland":        ["iceland", "icelandic", "icelanders", "reykjavik"],
    "Malta":          ["malta", "maltese", "valletta"],
    "Cyprus":         ["cyprus", "cypriot", "cypriots", "nicosia", "limassol"],

    # Eastern Europe / Balkans / FSU
    "Belarus":        ["belarus", "belarusian", "belarusians", "minsk", "lukashenko",
                       "brest", "grodno", "gomel", "mogilev", "vitebsk"],
    "Serbia":         ["serbia", "serbian", "serbians", "belgrade", "vucic",
                       "novi sad", "nis", "kragujevac", "subotica"],
    "Albania":        ["albania", "albanian", "albanians", "tirana",
                       "durres", "shkoder", "vlore", "elbasan"],
    "Bulgaria":       ["bulgaria", "bulgarian", "bulgarians", "sofia",
                       "plovdiv", "varna", "burgas", "stara zagora"],
    "Moldova":        ["moldova", "moldovan", "moldovans", "chisinau",
                       "tiraspol", "balti"],
    "Kosovo":         ["kosovo", "kosovar", "kosovars", "pristina"],
    "North Macedonia": ["north macedonia", "macedonian", "macedonians", "skopje",
                        "bitola", "kumanovo", "tetovo"],
    "Bosnia":         ["bosnia", "bosnian", "bosnians", "bosnia and herzegovina",
                       "sarajevo", "banja luka", "mostar", "tuzla"],
    "Montenegro":     ["montenegro", "montenegrin", "podgorica"],
    "Croatia":        ["croatia", "croatian", "croatians", "zagreb",
                       "split", "rijeka", "osijek", "zadar", "dubrovnik"],
    "Slovakia":       ["slovakia", "slovak", "slovaks", "bratislava",
                       "kosice", "presov", "zilina", "nitra"],
    "Slovenia":       ["slovenia", "slovenian", "slovenians", "ljubljana",
                       "maribor", "celje", "kranj"],
    "Lithuania":      ["lithuania", "lithuanian", "lithuanians", "vilnius",
                       "kaunas", "klaipeda", "siauliai", "panevezys"],
    "Latvia":         ["latvia", "latvian", "latvians", "riga",
                       "daugavpils", "liepaja", "jelgava"],
    "Estonia":        ["estonia", "estonian", "estonians", "tallinn",
                       "tartu", "narva", "parnu"],
    "Georgia":        ["georgia country", "georgian", "georgians", "tbilisi",
                       "kutaisi", "batumi", "rustavi"],
    "Kazakhstan":     ["kazakhstan", "kazakh", "kazakhs", "nur-sultan", "astana",
                       "almaty", "shymkent", "karaganda", "aktobe"],
    "Uzbekistan":     ["uzbekistan", "uzbek", "uzbeks", "tashkent",
                       "samarkand", "namangan", "andijan", "bukhara"],
    "Turkmenistan":   ["turkmenistan", "turkmen", "ashgabat"],
    "Kyrgyzstan":     ["kyrgyzstan", "kyrgyz", "bishkek", "osh"],
    "Tajikistan":     ["tajikistan", "tajik", "tajiks", "dushanbe",
                       "khujand", "kulob"],

    # Middle East / North Africa extras
    "Iraq":           ["iraq", "iraqi", "iraqis", "baghdad",
                       "basra", "mosul", "erbil", "najaf", "karbala", "kirkuk"],
    "Afghanistan":    ["afghanistan", "afghan", "afghans", "kabul", "taliban",
                       "kandahar", "herat", "mazar-i-sharif", "jalalabad"],
    "Jordan":         ["jordan", "jordanian", "jordanians", "amman",
                       "zarqa", "irbid", "aqaba"],
    "Lebanon":        ["lebanon", "lebanese", "beirut", "hezbollah",
                       "tripoli lebanon", "sidon", "tyre"],
    "Kuwait":         ["kuwait", "kuwaiti", "kuwaitis", "kuwait city"],
    "Bahrain":        ["bahrain", "bahraini", "bahrainis", "manama"],
    "Oman":           ["oman", "omani", "omanis", "muscat",
                       "salalah", "sohar", "nizwa"],
    "Qatar":          ["qatar", "qatari", "qataris", "doha"],
    "Tunisia":        ["tunisia", "tunisian", "tunisians", "tunis",
                       "sfax", "sousse", "kairouan", "bizerte"],

    # Asia-Pacific extras
    "Singapore":      ["singapore", "singaporean", "singaporeans"],
    "Philippines":    ["philippines", "philippine", "filipino", "filipinos",
                       "manila", "quezon city", "caloocan", "davao", "cebu",
                       "zamboanga", "antipolo", "pasig", "taguig", "marcos",
                       "duterte"],
    "Malaysia":       ["malaysia", "malaysian", "malaysians", "kuala lumpur",
                       "george town", "johor bahru", "ipoh", "shah alam",
                       "petaling jaya", "kota kinabalu"],
    "Thailand":       ["thailand", "thai", "thais", "bangkok",
                       "chiang mai", "pattaya", "nonthaburi", "hat yai",
                       "udon thani", "phuket"],
    "Cambodia":       ["cambodia", "cambodian", "cambodians", "phnom penh",
                       "siem reap", "sihanoukville"],
    "Laos":           ["laos", "laotian", "laotians", "lao pdr", "vientiane",
                       "luang prabang", "pakse"],
    "Bangladesh":     ["bangladesh", "bangladeshi", "bangladeshis", "dhaka",
                       "chittagong", "sylhet", "rajshahi", "khulna", "mymensingh"],
    "Nepal":          ["nepal", "nepali", "nepalese", "kathmandu",
                       "pokhara", "patan", "biratnagar"],
    "Sri Lanka":      ["sri lanka", "sri lankan", "colombo", "kandy",
                       "galle", "jaffna", "batticaloa"],
    "Mongolia":       ["mongolia", "mongolian", "mongolians", "ulaanbaatar",
                       "erdenet", "darkhan"],
    "Brunei":         ["brunei", "bruneian", "bandar seri begawan"],
    "Timor-Leste":    ["timor-leste", "east timor", "timorese", "dili"],
    "Maldives":       ["maldives", "maldivian", "male"],
    "Bhutan":         ["bhutan", "bhutanese", "thimphu", "phuntsholing"],
    "Papua New Guinea": ["papua new guinea", "papua", "port moresby",
                         "lae", "mount hagen"],
    "Hong Kong":      ["hong kong", "hongkonger", "hongkongers"],

    # Africa extras
    "South Africa":   ["south africa", "south african", "south africans",
                       "pretoria", "johannesburg", "cape town", "durban",
                       "soweto", "east london", "port elizabeth", "gqeberha",
                       "ramaphosa", "anc"],
    "Kenya":          ["kenya", "kenyan", "kenyans", "nairobi",
                       "mombasa", "kisumu", "nakuru", "eldoret", "ruto"],
    "Ethiopia":       ["ethiopia", "ethiopian", "ethiopians", "addis ababa",
                       "dire dawa", "gondar", "mekele", "bahir dar", "abiy"],
    "Ghana":          ["ghana", "ghanaian", "ghanaians", "accra",
                       "kumasi", "tamale", "sekondi", "takoradi"],
    "Ivory Coast":    ["ivory coast", "ivorian", "ivorians", "cote d'ivoire",
                       "cote divoire", "abidjan", "yamoussoukro", "bouake"],
    "Senegal":        ["senegal", "senegalese", "dakar", "touba", "thies"],
    "Rwanda":         ["rwanda", "rwandan", "rwandans", "kigali",
                       "butare", "gitarama"],
    "Uganda":         ["uganda", "ugandan", "ugandans", "kampala",
                       "gulu", "lira", "mbarara", "jinja", "museveni"],
    "Zimbabwe":       ["zimbabwe", "zimbabwean", "zimbabweans", "harare",
                       "bulawayo", "chitungwiza", "mutare", "mnangagwa"],
    "Zambia":         ["zambia", "zambian", "zambians", "lusaka",
                       "kitwe", "ndola", "kabwe", "chingola"],
    "Cameroon":       ["cameroon", "cameroonian", "cameroonians", "yaounde",
                       "douala", "garoua", "bamenda", "maroua"],
    "Mozambique":     ["mozambique", "mozambican", "mozambicans", "maputo",
                       "matola", "nampula", "beira", "nacala"],
    "Burkina Faso":   ["burkina faso", "burkinabe", "ouagadougou",
                       "bobo-dioulasso", "koudougou", "traore"],
    "Niger":          ["niger", "nigerien", "niamey", "zinder", "maradi",
                       "agadez"],
    "Chad":           ["chad", "chadian", "chadians", "n'djamena",
                       "moundou", "sarh", "abeche"],
    "Guinea":         ["guinea conakry", "republic of guinea", "guinean", "guineans", "conakry",
                       "nzerekore", "kindia", "kankan"],
    "Angola":         ["angola", "angolan", "angolans", "luanda",
                       "huambo", "lobito", "benguela", "malanje"],
    "DRC":            ["drc", "democratic republic of the congo", "congo kinshasa",
                       "kinshasa", "lubumbashi", "mbuji-mayi", "goma", "bukavu",
                       "m23", "eastern congo"],
    "South Sudan":    ["south sudan", "south sudanese", "juba",
                       "wau", "malakal", "yei"],
    "Eritrea":        ["eritrea", "eritrean", "eritreans", "asmara"],
    "Djibouti":       ["djibouti", "djiboutian"],
    "Mauritania":     ["mauritania", "mauritanian", "mauritanians", "nouakchott",
                       "nouadhibou"],
    "Liberia":        ["liberia", "liberian", "liberians", "monrovia"],
    "Sierra Leone":   ["sierra leone", "sierra leonean", "freetown",
                       "kenema", "makeni"],
    "Gabon":          ["gabon", "gabonese", "libreville", "port-gentil"],
    "Congo":          ["republic of the congo", "congo brazzaville",
                       "brazzaville", "pointe-noire"],
    "Namibia":        ["namibia", "namibian", "namibians", "windhoek",
                       "rundu", "walvis bay"],
    "Eswatini":       ["eswatini", "swazi", "swazis", "mbabane", "manzini"],
    "Lesotho":        ["lesotho", "basotho", "maseru"],
    "Malawi":         ["malawi", "malawian", "malawians", "lilongwe",
                       "blantyre", "mzuzu"],
    "Tanzania":       ["tanzania", "tanzanian", "tanzanians", "dodoma",
                       "dar es salaam", "mwanza", "arusha", "zanzibar"],
    "Madagascar":     ["madagascar", "malagasy", "antananarivo",
                       "toamasina", "antsirabe", "fianarantsoa"],
    "Botswana":       ["botswana", "batswana", "gaborone",
                       "francistown", "molepolole"],
    "Mali":           ["mali", "malian", "malians", "bamako",
                       "sikasso", "mopti", "koutiala", "ségou", "segou"],

    # Americas extras
    "Bolivia":        ["bolivia", "bolivian", "bolivians", "sucre", "la paz",
                       "santa cruz de la sierra", "cochabamba", "el alto"],
    "Ecuador":        ["ecuador", "ecuadorian", "ecuadorians", "quito",
                       "guayaquil", "cuenca", "santo domingo", "noboa"],
    "Paraguay":       ["paraguay", "paraguayan", "paraguayans", "asuncion",
                       "ciudad del este", "san lorenzo"],
    "Uruguay":        ["uruguay", "uruguayan", "uruguayans", "montevideo",
                       "salto", "ciudad de la costa"],
    "Guyana":         ["guyana", "guyanese", "georgetown guyana",
                       "linden", "new amsterdam"],
    "Dominican Republic": ["dominican republic", "dominican", "dominicans",
                           "santo domingo", "santiago dominican"],
    "Haiti":          ["haiti", "haitian", "haitians", "port-au-prince",
                       "cap-haïtien", "cap haitien", "gonaives"],
    "Guatemala":      ["guatemala", "guatemalan", "guatemalans", "guatemala city",
                       "mixco", "villa nueva", "quetzaltenango"],
    "Honduras":       ["honduras", "honduran", "hondurans", "tegucigalpa",
                       "san pedro sula", "choloma"],
    "Nicaragua":      ["nicaragua", "nicaraguan", "nicaraguans", "managua",
                       "leon nicaragua", "masaya", "ortega"],
    "Costa Rica":     ["costa rica", "costa rican", "costa ricans", "san jose costa rica",
                       "alajuela", "cartago"],
    "Trinidad and Tobago": ["trinidad and tobago", "trinidadian", "trinidadians",
                            "tobagonian", "port of spain", "san fernando"],
    "Jamaica":        ["jamaica", "jamaican", "jamaicans", "kingston jamaica",
                       "montego bay", "portmore"],
    "Bahamas":        ["bahamas", "bahamian", "bahamians", "nassau bahamas",
                       "freeport bahamas"],
}


# Aliases that are short or common enough to produce false positives if matched as
# plain substrings.  These get word-boundary matching instead.
# Any alias ≤ 4 chars, or a known ambiguous word, should be listed here.
_WORD_BOUNDARY_ALIASES: set = {
    # Laos — "lao pdr" is used now but keep "lao" here as safety for any future re-add
    "lao",
    # DRC abbreviation — could appear inside other acronyms
    "drc",
    # M23 rebel group — could match e.g. "m230"
    "m23",
    # "niger" is a strict substring of "nigeria" / "nigerian" — must use word boundary
    # so Nigerian articles don't inflate Niger's count
    "niger",
    # "mali" is inside "somalia" / "somali"
    "mali",
    # "chad" is a common English first name
    "chad",
    # "uk" — already padded in aliases ("uk ", " uk,") but keep here as guard
    "uk",
}


def _alias_matches(alias: str, text: str) -> bool:
    """
    Return True if alias appears in text.

    Short / ambiguous aliases use word-boundary matching via regex so that
    e.g. "bo" doesn't match inside "about" or "robot", and "niger" doesn't
    match inside "nigeria" / "nigerian".
    """
    if alias in _WORD_BOUNDARY_ALIASES:
        # \b is a word boundary — zero-width assertion between \w and \W
        return bool(re.search(r'\b' + re.escape(alias) + r'\b', text))
    return alias in text



# ──────────────────────────────────────────────────────────
# HELPERS
# ──────────────────────────────────────────────────────────

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
                if _alias_matches(alias, text):
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
