"""Parse Rajya Sabha question lists into questions.

Rajya Sabha question records are one PDF per sitting day and type (starred, unstarred), with no
per-question metadata. parse(text) returns, for each question in the list, its number, the asking
members as written, the ministry and the subject line, plus the list's stated total. Tested on lists
from 2001 to 2026: 858 of 870 stated questions found (22 Nov 2026)."""
import re
TITLES = r"(?:SHRI|SHRIMATI|SMT|DR|KUMARI|KUM|MS|MR|MRS|PROF|SUSHRI|SANT|SWAMI|MOHD|LT|GEN|CAPT|MAJ|JUSTICE|CH|CHAUDHARY|SARDAR|SARDARNI|DIWAN|NAWAB|PANDIT|ACHARYA|MAULANA|AIR\s+CHIEF|MAHARAJA|RAJA|RANI|THIRU|SHRIMATHI|SHRIMANT)\.?"
# "<no>. <member>[: <member>...]: Will the Minister of <ministry> be pleased" or "... Will the PRIME MINISTER be pleased".
Q = re.compile(r"(?<![\w.])[†‡#*\s]*(\d{1,5})\s*\.?\s*[#*†‡]?\s*"
               r"((?:" + TITLES + r"[\s(.][^:?]{2,200}?\s*:\s*)+)"
               r"Will\s+the\s+(?:(Prime\s+Minister)|Minister(?:\s+of|\s+for)?\s+(.{2,140}?))\s+be\s+pleased", re.I)
SPLIT_NAMES = re.compile(r"\s*(?:,|:|\band\b)\s*(?=" + TITLES + r"[\s(.])", re.I)
NOISE = re.compile(r"†?Original notice of the question (?:was )?received in Hindi\.?|ws-\S+|\S*\\\S+|[\x80-\x9f]", re.I)
TOTAL = re.compile(r"Total\s+number\s+of\s+questions\s*[—–\-\x97]*\s*(\d+)", re.I)

def flat(t: str) -> str:
    return re.sub(r"\s+", " ", t.replace("\xa0", " ").replace("\x97", "—"))

def parse(text: str) -> tuple[list[dict], int | None]:
    t = flat(text)
    total = TOTAL.search(t)
    out, prev_end = [], (total.end() if total else 0)
    for m in Q.finditer(t):
        no, names = m.group(1), m.group(2).rstrip(": ")
        ministry = "Prime Minister" if m.group(3) else m.group(4)
        pre = NOISE.sub(" ", t[prev_end:m.start()])
        # The subject is the text after the previous question's last '?' or ';' and before the number.
        subj = re.split(r"[?]\s|\bstate:\s|\(\w\)\s", pre)[-1].strip(" .;:-—")
        subj = re.sub(r"^\d+\s+|\b\d+\s*$", "", re.sub(r"\s+", " ", subj)).strip(" .;:-—")
        members = [re.sub(r"\s+", " ", x).strip(" ,.") for x in SPLIT_NAMES.split(names) if x.strip(" ,.")]
        out.append({"question_no": int(no), "members": members,
                    "ministry": re.sub(r"\s+", " ", ministry).strip(), "subject": subj if 3 <= len(subj) <= 160 else None})
        prev_end = m.end()
    return out, int(total.group(1)) if total else None
