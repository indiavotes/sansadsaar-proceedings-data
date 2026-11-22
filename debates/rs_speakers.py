"""Find who spoke under which item of business in a Rajya Sabha sitting's text.

Rajya Sabha debate records are one text per sitting (floor version). Items of business are
headed by lines in capitals ("PAPERS LAID ON THE TABLE", "STATUTORY RESOLUTIONS"); speakers by
"SHRI X:" or "SHRI X (State):", ministers by "THE MINISTER OF ... (SHRI X):". speakers(text) returns
[(item heading, member name as written)], one per member per item, skipping presiding officers."""
import re

TITLES = (r"(?:SHRI|SHRIMATI|SMT\.|DR\.|MS\.|PROF\.|KUMARI|LT\.|SARDAR|CH\.|CHAUDHARY|SUSHRI|"
          r"SHRIMATHI|MOHD\.|SWAMI|SANT|CAPT\.|MAULANA|JUSTICE)")
SPEAKER = re.compile(r"^\s*((?:" + TITLES + r"\s[A-Z .'\-]{2,70}?)|(?:THE\s(?:PRIME\s)?MINISTER[A-Z ,'&\-]{0,160}?))"
                     r"\s*(\((?:" + TITLES + r")[^)]{2,80}\))?\s*(?:\([^)]{2,40}\))?\s*:", re.M)
PRESIDING = re.compile(r"CHAIRMAN|CHAIRPERSON|VICE-?CHAIRMAN|SPEAKER|SECRETARY.GENERAL", re.I)
HEADING = re.compile(r"^\s*([A-Z][A-Z0-9 ,'&()/\-.]{9,140})\s*$", re.M)
NOT_HEADING = re.compile(r"RAJYA SABHA|PARLIAMENTARY DEBATES|OFFICIAL REPORT|SECRETARIAT|UNCORRECTED|^\[|^\(.*\)$|"
                         r"MINIST|^(?:OF|AND|IN|TO|FOR|THE|ON|BY|WITH|NEW DELHI)\b|^[A-Z]+DAY,|\d{4}/|"
                         r"\([^)]*$|^[^(]*\)|HRS\.?$|^[A-Z .]{1,12}$|\d|^TOTAL\b|^\S+$")


# Printed written answers are not floor debate: a member named there asked a question, and each
# question there has its own subject heading. Written-answer mode lasts until a heading names a kind
# of floor business.
SKIP_ITEM = re.compile(r"^Written answers", re.I)
FLOOR_ITEM = re.compile(r"PAPERS? LAID|MATTERS? RAISED|BILL|SHORT DURATION|SPECIAL MENTION|STATEMENT|MESSAGE|"
                        r"REPORT|EVIDENCE|OBITUAR|REFERENCE|FELICITATION|CALLING ATTENTION|PRIVATE MEMBER|"
                        r"RESOLUTION|MOTION|DISCUSSION|BUDGET|APPROPRIATION|^RE\b|ANNOUNCEMENT|OATH|ELECTION|"
                        r"LEAVE OF ABSENCE|VALEDICTORY|RULING|OBSERVATION|SUBMISSION|BUSINESS|ALLOTMENT|"
                        r"NATIONAL SONG|ORAL ANSWERS|SHORT NOTICE|HALF-AN-HOUR|ADDRESS|DEMANDS FOR GRANTS", re.I)


def _plausible_heading(h: str) -> bool:
    """Reject table labels and broken text: a repeated word, or mostly fragments under 3 letters."""
    words = re.findall(r"[A-Za-z]+", h)
    if len(words) < 2:
        return False
    low = [w.lower() for w in words]
    if max(low.count(w) for w in set(low)) >= 3:
        return False
    return sum(len(w) for w in words) / len(words) >= 3.5


def _clean(name: str) -> str:
    return re.sub(r"\s+", " ", name).strip(" .,:")


def speakers(text: str) -> list[tuple[str, str]]:
    marks = []
    for m in HEADING.finditer(text):
        h = _clean(m.group(1))
        if not NOT_HEADING.search(h) and not re.match(TITLES + r"\s|THE (?:PRIME )?MINISTER", h) and _plausible_heading(h):
            marks.append((m.start(), "h", h))
    for m in SPEAKER.finditer(text):
        label, bracket = _clean(m.group(1)), m.group(2)
        if PRESIDING.search(label):
            continue
        if label.startswith("THE ") and not bracket:
            continue  # a minister named only by office: no name to attribute
        name = _clean(bracket.strip("()")) if bracket and label.startswith("THE ") else label
        marks.append((m.start(), "s", name))
    marks.sort()
    out, seen, item, written = [], set(), "Rajya Sabha sitting", False
    for _, kind, val in marks:
        if kind == "h":
            if SKIP_ITEM.match(val):
                written = True
            elif written and FLOOR_ITEM.search(val):
                written = False
            item = val.capitalize() if val.isupper() else val
        elif written:
            continue
        elif (item, val) not in seen:
            seen.add((item, val))
            out.append((item, val))
    return out
