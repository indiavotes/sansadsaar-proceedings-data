#!/usr/bin/env python3
"""Extend a Netas database to every candidate in the IndiaVotes results.

Reads a base netas.sqlite (persons + LS contests for about 7,200 people),
copies it to out/candidates.sqlite and only ADDS rows:

  * every remaining IV Lok Sabha candidacy (vn_candidate_master) and every
    IV assembly candidacy (vn_ac_candidate_master) becomes a contest row;
  * each candidacy is owned by exactly one person.

Ownership, in priority order (each candidacy claimed once):

  1. TCPD link. Find the candidacy's TCPD row by (house, year, state,
     constituency number, position), confirmed by equal votes or by the
     name-score helpers of build_electoral_iv.py; fall back to the
     constituency name when the number does not line up. That gives a
     TCPD pid.
       1a  tcpd-attach  the pid belongs to exactly one existing person;
       1b  tcpd-mint    otherwise mint one person per TCPD pid
                        (identity_source 'tcpd_only', confidence 0.8).
     A pid that the base database already spreads over two persons, or
     that sits on a person carrying a different TCPD pid, is conflicted:
     its candidacies are skipped and reported.
  2. Name link, for candidacies with no TCPD row. Attach to a person only
     when the normalised full name is equal, the state is the same, the
     seat matches one the person contested (cons_match), the party is one
     the person contested for, the person passes the age guard, and
     exactly one person qualifies (name-attach). Otherwise mint a person
     (identity_source 'fallback', confidence 0.4; name-mint).

Assembly candidate ids share a number space with Lok Sabha ids in the IV
mirror, and contests.iv_candidate_id is UNIQUE, so assembly rows store
iv_candidate_id = AC_IV_ID_OFFSET + ac candidate_id.

Run:
    python build_candidates.py
    python build_candidates.py --base-db /path/to/netas.sqlite
"""
from __future__ import annotations

import argparse
import csv
import gzip
import json
import random
import re
import sqlite3
import sys
import time
from collections import Counter, defaultdict
from pathlib import Path

from build_electoral_iv import (
    COMMON_NAME_TOKENS,
    HONORIFIC_TOKENS,
    _apply_tcpd_pid_split,
    cons_match,
    name_score,
    name_tokens,
    norm_cons,
    norm_name,
    norm_party,
    norm_state,
    slug_of,
    state_display,
)

REPO = Path(__file__).resolve().parent
HOME = Path.home()
DEFAULT_OUT = REPO / "out"
DEFAULT_BASE_FALLBACK = HOME / "Code/indiavotes/netas/data/netas.sqlite"
DEFAULT_IV = HOME / "Code/indiavotes/site/data/.cache/iv-mirror.sqlite"
TCPD_DIR = HOME / "Code/indiavotes/site/data/external/tcpd"
DEFAULT_TCPD_GE = TCPD_DIR / "TCPD_GE_All_States_2026-5-13.csv.gz"
DEFAULT_TCPD_AE = TCPD_DIR / "TCPD_AE_All_States_2026-5-13.csv.gz"
PID_ASSIGNMENTS = REPO / "person_pid_assignments.json"

AC_IV_ID_OFFSET = 1_000_000_000
MIN_AGE = 25
SEED = 20261120

# Extra state grouping on top of build_electoral_iv.STATE_ALIASES. Both
# sources record the state as it was named at the election; these pairs
# are the same territory under an old and a new name. Constituency number,
# position and the name/vote check still gate every TCPD match.
STATE_GROUPS = {
    "madras": "tamil nadu",
    "mysore": "karnataka",
    "laccadive minicoy and amindivi islands": "lakshadweep",
}


def state_key(s: str) -> str:
    n = norm_state(s)
    return STATE_GROUPS.get(n, n)


def name_key(s: str) -> str:
    """Order-sensitive name key: honorifics dropped, initials pulled to the front.

    'A. Raja' and 'Raja A' give the same key; 'Oommen Chandy' and 'Chandy
    Oommen' (father and son) do not, unlike norm_name's sorted tokens.
    """
    if not s:
        return ""
    s = re.sub(r"[.,;:()\[\]'\"|]", " ", s.lower())
    toks = [t for t in s.split() if t and t not in HONORIFIC_TOKENS]
    initials = sorted(t for t in toks if len(t) == 1)
    rest = [t for t in toks if len(t) > 1]
    if not rest:
        return ""
    return " ".join(initials) + "|" + " ".join(rest)


def rare(tokens: frozenset) -> frozenset:
    return frozenset(t for t in tokens if t not in COMMON_NAME_TOKENS)


def to_int(v):
    try:
        return int(float(v))
    except (TypeError, ValueError):
        return None


def to_float(v):
    try:
        return float(v)
    except (TypeError, ValueError):
        return None


# ── IV loaders ───────────────────────────────────────────────────────────


def load_iv(iv: sqlite3.Connection) -> list[dict]:
    """Every IV general-election candidacy, LS and AC, one dict each."""
    states = {sid: name for sid, name in iv.execute(
        "SELECT state_id, state_name FROM vn_state_master")}
    parties = {pid: abbr for pid, abbr in iv.execute(
        "SELECT party_id, party_abbr FROM vn_party_master")}
    rows: list[dict] = []

    # Lok Sabha — same joins as build_electoral_iv.load_iv_rows
    # (pc_master by pc_id + year), but one result row per candidate.
    pcm = {}
    for pc_id, year, state_id, pc_name, pc_no in iv.execute(
            "SELECT pc_id, year, state_id, pc_name, pc_election_no FROM vn_pc_master"):
        pcm[(pc_id, year)] = (state_id, pc_name, pc_no)
    pres = defaultdict(list)
    for cid, pc_id, pos, votes, pct in iv.execute(
            "SELECT candidate_id, pc_id, pc_candidate_position, pc_candiadate_votes, "
            "pc_candidate_percentage_votes FROM vn_pc_candidate_results"):
        pres[cid].append((pc_id, pos, votes, pct))
    for cid, name, year, pc_id, party_id, dob, age, gender in iv.execute(
            "SELECT candidate_id, candidate_name, year, pc_id, party_id, candidate_dob, "
            "candidate_age, candidate_gender FROM vn_candidate_master"):
        m = pcm.get((pc_id, year))
        res = [r for r in pres.get(cid, []) if r[0] == pc_id] or pres.get(cid, [])[:1]
        pos, votes, pct = (res[0][1], res[0][2], res[0][3]) if res else (None, None, None)
        state = states.get(m[0]) if m else None
        rows.append(_iv_row("ls", cid, cid, name, year, None, state,
                            m[1] if m else None, m[2] if m else None,
                            parties.get(party_id), pos, votes, pct, bool(res), bool(m)))

    # Assembly — candidate → ac_master by (ac_id, ac_election_master_id);
    # results by candidate_id, keeping the row whose (ac_id, master) agrees.
    acm = {}
    for ac_id, em, state_id, ac_name, year, ac_no in iv.execute(
            "SELECT ac_id, ac_election_master_id, state_id, ac_name, year, ac_election_no "
            "FROM vn_ac_master"):
        acm[(ac_id, em)] = (state_id, ac_name, ac_no, year)
    months = {em: to_int(mo) for em, mo in iv.execute(
        "SELECT ac_election_master_id, ac_election_month FROM vn_ac_election_master")}
    ares = defaultdict(list)
    for cid, ac_id, em, pos, votes, pct in iv.execute(
            "SELECT candidate_id, ac_id, ac_election_master_id, candidate_results_position, "
            "candidate_results_votes, candidate_results_percentage FROM vn_ac_candidate_results"):
        ares[cid].append((ac_id, em, pos, votes, pct))
    for cid, name, year, ac_id, em, party_id, state_id in iv.execute(
            "SELECT candidate_id, candidate_name, year, ac_id, ac_election_master_id, "
            "party_id, state_id FROM vn_ac_candidate_master"):
        m = acm.get((ac_id, em))
        res = [r for r in ares.get(cid, []) if (r[0], r[1]) == (ac_id, em)]
        pos, votes, pct = (res[0][2], res[0][3], res[0][4]) if res else (None, None, None)
        state = states.get(m[0] if m else state_id)
        row = _iv_row("ac", cid, AC_IV_ID_OFFSET + cid, name, year, months.get(em), state,
                      m[1] if m else None, m[2] if m else None,
                      parties.get(party_id), pos, votes, pct, bool(res), bool(m))
        row["election_key"] = em
        rows.append(row)
    return rows


def _iv_row(house, raw_id, stored_id, name, year, month, state, cons, cons_no,
            party, pos, votes, pct, has_result, has_seat):
    toks = name_tokens(name)
    return {
        "house": house, "raw_id": raw_id, "iv_id": stored_id,
        "name": (name or "").strip(), "tokens": toks, "nname": norm_name(name),
        "year": year, "month": month,
        "state": state_display(state), "skey": state_key(state or ""),
        "cons": cons or "", "cnorm": norm_cons(cons), "cons_no": to_int(cons_no),
        "party": norm_party(party), "position": to_int(pos),
        "won": 1 if to_int(pos) == 1 else 0,
        "votes": to_int(votes),
        "vote_share": (pct / 100.0) if isinstance(pct, (int, float)) else None,
        "has_result": has_result, "has_seat": has_seat,
        "election_key": year,
    }


# ── TCPD loader ──────────────────────────────────────────────────────────


def load_tcpd(path: Path, house: str):
    """General-election rows (Poll_No 0) with a pid, indexed by seat number and seat name.

    TCPD ranks NOTA as a candidate (with an empty pid, so it is dropped here)
    and IV does not, so positions differ below NOTA; matching inside a seat
    therefore keys on votes, not position.
    """
    by_no = defaultdict(list)
    by_name = defaultdict(list)
    n = 0
    with gzip.open(path, "rt") as f:
        for r in csv.DictReader(f):
            pid = (r.get("pid") or "").strip()
            if not pid or (r.get("Poll_No") or "0") != "0":
                continue
            year = to_int(r["Year"])
            sk = state_key(r["State_Name"])
            cn = norm_cons(r["Constituency_Name"])
            party = norm_party(r["Party"])
            tup = (year, norm_state(r["State_Name"]), cn, party)
            eff = _apply_tcpd_pid_split(tup, pid)
            sex = (r.get("Sex") or "").strip().upper()[:1]
            row = {
                "pid": eff, "name": r["Candidate"], "tokens": name_tokens(r["Candidate"]),
                "nname": norm_name(r["Candidate"]),
                "year": year, "month": to_int(r.get("month")), "skey": sk,
                "cons_no": to_int(r["Constituency_No"]), "cnorm": cn,
                "position": to_int(r["Position"]), "votes": to_int(r["Votes"]),
                "party": party, "sex": sex if sex in ("M", "F") else None,
                "last_party": norm_party(r.get("Last_Party")),
                "age": to_int(r.get("Age")),
                "district": norm_cons(r.get("District_Name")),
            }
            by_no[(house, year, sk, row["cons_no"])].append(row)
            by_name[(house, year, sk, cn)].append(row)
            n += 1
    return by_no, by_name, n


def names_agree(iv_row, t) -> bool:
    if iv_row["nname"] and iv_row["nname"] == t["nname"]:
        return True
    return name_score(iv_row["tokens"], t["tokens"]) >= 0.6


def match_in_seat(r, seat_rows):
    """Return (tcpd_row, how), ("AMBIG", None) or None for one IV candidacy."""
    if not seat_rows:
        return None
    months = {t["month"] for t in seat_rows}
    if len(months) > 1 and r["month"] in months:          # two polls in one year (Bihar 2005)
        seat_rows = [t for t in seat_rows if t["month"] == r["month"]]
    if r["votes"]:
        eq = [t for t in seat_rows if t["votes"] == r["votes"]]
        agree = [t for t in eq if names_agree(r, t)]
        if agree:
            if len({t["pid"] for t in agree}) == 1:
                return agree[0], "votes+name"
            return "AMBIG", None
        if len(eq) == 1 and r["votes"] >= 100:
            return eq[0], "votes-only"
        if eq:
            return "AMBIG", None
    # Votes missing or revised: the name must be unique in the seat and the
    # position equal (or one lower in TCPD, where NOTA ranks above).
    named = [t for t in seat_rows if names_agree(r, t)]
    if len({t["pid"] for t in named}) == 1 and r["position"] is not None:
        t = named[0]
        if t["position"] in (r["position"], r["position"] + 1):
            return t, "name+position"
    return None


def link_tcpd(iv_rows, tcpd_by_no, tcpd_by_name):
    """Set r['tcpd'] on each IV row whose TCPD row is found. Returns a Counter."""
    out = Counter()
    tcpd_sy = {k[:3] for k in tcpd_by_no}
    tcpd_hy = {k[:2] for k in tcpd_by_no}
    iv_sy = {(r["house"], r["year"], r["skey"]) for r in iv_rows}
    year_map = {}
    for sy in iv_sy:
        h, y, sk = sy
        if sy in tcpd_sy:
            year_map[sy] = y
            continue
        # IV and TCPD sometimes date one election a year apart (Jharkhand
        # Dec 2019 is 2020 in IV). Shift only when the neighbouring
        # state-year exists in TCPD and not in IV.
        for dy in (-1, 1):
            if (h, y + dy, sk) in tcpd_sy and (h, y + dy, sk) not in iv_sy:
                year_map[sy] = y + dy
                break
    shifted = Counter()
    for r in iv_rows:
        r["tcpd"] = None
        ty = year_map.get((r["house"], r["year"], r["skey"]))
        if ty is None:
            out["no TCPD rows for this state and year" if (r["house"], r["year"]) in tcpd_hy
                else "no TCPD coverage for this year"] += 1
            continue
        res = match_in_seat(r, tcpd_by_no.get((r["house"], ty, r["skey"], r["cons_no"]), []))
        via = "seat number"
        if res is None or res[0] == "AMBIG":
            res2 = match_in_seat(r, tcpd_by_name.get((r["house"], ty, r["skey"], r["cnorm"]), []))
            if res2 is not None and res2[0] != "AMBIG":
                res, via = res2, "seat name"
        if res is None:
            out["unmatched in TCPD"] += 1
            continue
        if res[0] == "AMBIG":
            out["ambiguous in TCPD (tied votes or names)"] += 1
            continue
        t, how = res
        r["tcpd"] = t
        if ty != r["year"]:
            shifted[(r["house"], r["year"], r["skey"], ty)] += 1
        if via == "seat number" and t["cnorm"] != r["cnorm"] and not cons_match(t["cnorm"], r["cnorm"]):
            out["matched, seat names differ (spelling or rename)"] += 1
        out[f"matched by {via}, {how}"] += 1
    for (h, y, sk, ty), n in sorted(shifted.items()):
        out[f"year shift {h} {sk} IV {y} = TCPD {ty}"] = n
    return out


# ── Geography: which seats are near each other ───────────────────────────

# States carved out of one another; a seat in one may be "near" a seat in
# the other, so across these pairs nearness is unknown, never far.
REORG_GROUPS = [
    {"madhya pradesh", "chhattisgarh", "madhya bharat", "vindhya pradesh", "bhopal"},
    {"bihar", "jharkhand"}, {"uttar pradesh", "uttarakhand"},
    {"andhra pradesh", "telangana", "hyderabad"},
    {"punjab", "haryana", "himachal pradesh", "patiala and east punj", "chandigarh"},
    {"assam", "meghalaya", "mizoram", "arunachal pradesh", "nagaland"},
    {"bombay", "gujarat", "maharashtra", "saurashtra", "kutch"},
    {"goa daman and diu", "goa", "daman and diu"}, {"jammu and kashmir", "ladakh"},
    {"travancore cochin", "kerala", "tamil nadu"}, {"karnataka", "coorg"},
]
REORG = {s: i for i, g in enumerate(REORG_GROUPS) for s in g}


class Geo:
    def __init__(self, iv, tcpd_rows):
        st = {sid: state_key(n) for sid, n in iv.execute("SELECT state_id, state_name FROM vn_state_master")}
        self.pcs_of_ac = defaultdict(set)
        self.dist_of_ac = defaultdict(set)
        pcname = {(pc_id, em): norm_cons(n) for pc_id, em, n in iv.execute(
            "SELECT pc_id, pc_election_master_id, pc_name FROM vn_pc_master")}
        for sid, pc_id, em, ac in iv.execute(
                "SELECT state_id, pc_id, pc_election_master_id, ac_name FROM vn_pc_ac_details"):
            pc = pcname.get((pc_id, em))
            if pc and ac:
                self.pcs_of_ac[(st.get(sid), norm_cons(ac))].add(pc)
        for sid, ac, pc in iv.execute("SELECT state_id, ac_alias, pc_alias FROM iv_ac_pc_map"):
            if ac and pc:
                self.pcs_of_ac[(st.get(sid), norm_cons(ac))].add(norm_cons(pc))
        for sid, ac, d in iv.execute("SELECT state_id, ac_name, district_name FROM vn_ac_master "
                                     "WHERE district_name IS NOT NULL AND district_name != ''"):
            self.dist_of_ac[(st.get(sid), norm_cons(ac))].add(norm_cons(d))
        for sid, ac, d in iv.execute("SELECT state_id, ac_alias, district_alias FROM iv_ac_district_map"):
            if ac and d:
                self.dist_of_ac[(st.get(sid), norm_cons(ac))].add(norm_cons(d))
        for t in tcpd_rows:
            if t.get("district"):
                self.dist_of_ac[(t["skey"], t["cnorm"])].add(t["district"])
        # PCs that shared an AC in any delimitation are neighbours; one hop of
        # this graph stands in for adjacency, which the sources do not give.
        self.pc_nbr = defaultdict(set)
        for (sk, ac), pcs in self.pcs_of_ac.items():
            for pc in pcs:
                self.pc_nbr[(sk, pc)] |= pcs
        self.dist_of_pc = defaultdict(set)
        for (sk, ac), pcs in self.pcs_of_ac.items():
            for pc in pcs:
                self.dist_of_pc[(sk, pc)] |= self.dist_of_ac.get((sk, ac), set())

    def regions(self, c):
        k = (c["skey"], c["cnorm"])
        if c["house"] == "ls":
            return {c["cnorm"]}, self.dist_of_pc.get(k, set())
        return self.pcs_of_ac.get(k, set()), self.dist_of_ac.get(k, set())

    def near(self, a, b):
        """True (same seat or region), False (known far apart) or None (unknown)."""
        if cons_match(a["cnorm"], b["cnorm"]) and (a["skey"] == b["skey"] or
                                                    REORG.get(a["skey"], -1) == REORG.get(b["skey"], -2)):
            return True
        if a["skey"] != b["skey"]:
            return None if REORG.get(a["skey"], -1) == REORG.get(b["skey"], -2) else False
        pa, da = self.regions(a)
        pb, db = self.regions(b)
        if any(cons_match(x, y) for x in pa for y in pb) or (da & db):
            return True
        sk = a["skey"]
        na = set(pa).union(*(self.pc_nbr.get((sk, x), set()) for x in pa)) if pa else set()
        if any(cons_match(x, y) for x in na for y in pb):
            return None         # neighbouring seats: not provably far
        if pa and pb:
            return False
        if da and db:
            return False
        return None


# ── Person model ─────────────────────────────────────────────────────────


def mk_contest(r, base=False):
    t = r.get("tcpd") or {}
    return {"house": r["house"], "year": r["year"], "skey": r["skey"], "cnorm": r["cnorm"],
            "cons_no": r["cons_no"], "party": r["party"], "share": r["vote_share"],
            "won": r["won"], "name": r["name"], "nkey": name_key(r["name"]), "base": base,
            "row": r, "ekey": r["election_key"], "last_party": t.get("last_party") or "",
            "tcpd_age": t.get("age"), "iv_id": r["iv_id"]}


AGE_GAP_BLOCK = 6   # years between TCPD-implied birth year and base dob that block a far link
AGE_GAP_HARD = 12   # years that block the link outright


class People:
    def __init__(self, conn, iv_by_id):
        self.persons = {}
        self.contests = defaultdict(list)
        for pid, name, dob, tp, src in conn.execute(
                "SELECT pid, canonical_name, dob, tcpd_pid, identity_source FROM persons"):
            self.persons[pid] = {"pid": pid, "name": name, "dob": dob, "tcpd_pid": tp,
                                 "source": src, "base": True,
                                 "names": {name_key(name)} - {""}}
        self.base_tcpd = defaultdict(set)
        for pid, ctype, year, state, cons, party, ivid, tp, share, won in conn.execute(
                "SELECT pid, contest_type, year, state, constituency, party_short, "
                "iv_candidate_id, tcpd_pid, vote_share, won FROM contests"):
            r = iv_by_id.get(("ls" if ctype == "ls" else "ac", ivid))
            name = r["name"] if r else ""
            self.contests[pid].append({
                "house": ctype, "year": year, "skey": state_key(state or ""), "cnorm": norm_cons(cons),
                "cons_no": r["cons_no"] if r else None, "party": norm_party(party), "share": share,
                "won": won, "name": name, "nkey": name_key(name), "base": True, "row": r,
                "ekey": year, "last_party": "", "tcpd_age": None, "iv_id": ivid})
            if name:
                self.persons[pid]["names"].add(name_key(name))
            if tp:
                self.base_tcpd[tp].add(pid)
        self.iv_owner = {c["iv_id"]: pid for pid, cs in self.contests.items() for c in cs if c["iv_id"]}

    def tcpd_map(self):
        owners = defaultdict(set)
        for pid, p in self.persons.items():
            if p["tcpd_pid"]:
                owners[p["tcpd_pid"]].add(pid)
        for tp, pids in self.base_tcpd.items():
            owners[tp] |= pids
        mapping, conflicts = {}, {}
        for tp, pids in owners.items():
            if len(pids) > 1:
                conflicts[tp] = f"on {len(pids)} existing persons: {', '.join(sorted(pids))}"
                continue
            pid = next(iter(pids))
            own = self.persons[pid]["tcpd_pid"]
            if own and own != tp:
                conflicts[tp] = f"contest pid on {pid}, whose own tcpd_pid is {own}"
                continue
            mapping[tp] = pid
        return mapping, conflicts

    def dob_year(self, pid):
        dob = self.persons[pid].get("dob")
        return int(dob[:4]) if dob and re.match(r"\d{4}", dob) else None

    def age_ok(self, pid, year):
        by = self.dob_year(pid)
        return by is None or MIN_AGE <= year - by <= MAX_AGE

    def has_same_contest(self, pid, c):
        return any((x["house"], x["year"], x["cnorm"], x["ekey"]) ==
                   (c["house"], c["year"], c["cnorm"], c["ekey"]) for x in self.contests[pid])

    def add(self, pid, c):
        self.contests[pid].append(c)
        if c["nkey"]:
            self.persons[pid]["names"].add(c["nkey"])

    def new_person(self, pid, name, source, tcpd_pid, anchor, confidence, gender=None):
        self.persons[pid] = {"pid": pid, "name": name, "dob": None, "tcpd_pid": tcpd_pid,
                             "source": source, "base": False, "names": set(),
                             "anchor": anchor, "confidence": confidence, "gender": gender}


MAX_AGE = 90


# ── Consistency checks on one TCPD pid's rows (review rule 1) ────────────


def names_consistent(a, b) -> bool:
    if a["nkey"] and a["nkey"] == b["nkey"]:
        return True
    ra, rb = rare(name_tokens(a["name"])), rare(name_tokens(b["name"]))
    if ra and rb and (ra <= rb or rb <= ra):
        return True
    return name_score(name_tokens(a["name"]), name_tokens(b["name"])) == 1.0


def quarantine_cluster(cs, geo, dob_year):
    """cs: contests of one TCPD pid (base ones are fixed). Returns {iv_id: rule}."""
    q = {}

    def live():
        return [c for c in cs if c["base"] or c["iv_id"] not in q]

    # Age: known date of birth (base person only). TCPD's self-reported ages
    # are too noisy to judge single rows (they flagged Akbaruddin Owaisi).
    for c in cs:
        if not c["base"] and dob_year and not (MIN_AGE <= c["year"] - dob_year <= MAX_AGE):
            q[c["iv_id"]] = "age outside 25-90 by the person's date of birth"
    if len(cs) < 2:
        return q

    def support(c, others):
        return sum(1 for o in others if geo.near(c, o) or (o["party"] == c["party"] and c["party"] != "IND"))

    # Same year, different state or far-apart seat, and party or name disagree.
    changed = True
    while changed:
        changed = False
        L = live()
        for i in range(len(L)):
            for j in range(i + 1, len(L)):
                a, b = L[i], L[j]
                if a["year"] != b["year"] or (a["base"] and b["base"]):
                    continue
                if a["iv_id"] in q or b["iv_id"] in q:
                    continue
                nr = geo.near(a, b)
                if a["skey"] != b["skey"] and not cons_match(a["cnorm"], b["cnorm"]):
                    nr = False      # one year, two states: two separate elections
                if nr is not False:
                    continue
                if a["party"] == b["party"] and a["party"] != "IND" and names_consistent(a, b):
                    continue            # one person contesting two seats for one party
                rest = [o for o in L if o is not a and o is not b]
                sa, sb = support(a, rest), support(b, rest)
                if a["base"]:
                    loser = b
                elif b["base"]:
                    loser = a
                elif sa != sb:
                    loser = a if sa < sb else b
                else:
                    loser = a if (a["share"] or 0) < (b["share"] or 0) else b
                q[loser["iv_id"]] = "same year as another row, far seat or other state, party or name differs"
                changed = True
                break
            if changed:
                break

    # Collapse: a winner or major-party candidate elsewhere, under 1% in a far seat.
    L = live()
    for c in L:
        if c["base"] or (c["share"] is None) or c["share"] >= 0.01:
            continue
        others = [o for o in L if o is not c]
        strong = any(o["won"] or (o["party"] != "IND" and (o["share"] or 0) >= 0.10) for o in others)
        if strong and others and all(geo.near(c, o) is False for o in others):
            q[c["iv_id"]] = "under 1% in a far seat after a win or major-party run"

    # Region jump: against a career of 2+ other rows, a row far from all of
    # them, alone in its house, under a party the career never used, and either in no shared state or 15+ years
    # from the nearest other row. With only two rows neither is the outlier.
    L = live()
    for c in L:
        if c["base"]:
            continue
        others = [o for o in L if o is not c]
        if len(others) < 2 or any(o["house"] == c["house"] for o in others):
            continue
        if any(o["party"] == c["party"] for o in others):
            continue            # same party as the career: a move, not a different person
        if all(geo.near(c, o) is False for o in others):
            gap = min(abs(o["year"] - c["year"]) for o in others)
            if all(o["skey"] != c["skey"] for o in others) or gap >= 15:
                q[c["iv_id"]] = "career jumps to a far seat in the other house under another party"
    return q


# ── Same-name candidates in one race (review rule 2) ─────────────────────


def fit(c, cluster):
    """How well candidacy c fits the other rows of a TCPD pid: party + vote level."""
    if not cluster:
        return 0
    score = 0
    if c["party"] != "IND" and any(o["party"] == c["party"] for o in cluster):
        score += 1
    shares = sorted(o["share"] for o in cluster if o["share"])
    if shares and c["share"]:
        import math
        if abs(math.log10(c["share"]) - math.log10(shares[len(shares) // 2])) < 1:
            score += 1
    return score


def tie_break_same_names(iv_rows, base_contests_by_tcpd):
    """Swap TCPD rows between same-name candidates in one race when party and
    vote level fit the other pid's career better. Returns list of swaps."""
    by_pid = defaultdict(list)
    for r in iv_rows:
        if r.get("tcpd"):
            by_pid[r["tcpd"]["pid"]].append(r)
    races = defaultdict(list)
    for r in iv_rows:
        if r.get("tcpd"):
            races[(r["house"], r["year"], r["election_key"], r["skey"], r["cnorm"], name_key(r["name"]))].append(r)
    swaps = []
    for key, rs in races.items():
        if len(rs) != 2 or not key[-1]:
            continue
        a, b = rs
        pa, pb = a["tcpd"]["pid"], b["tcpd"]["pid"]
        ca, cb = mk_contest(a), mk_contest(b)

        def cluster(pid, excl):
            return [mk_contest(x) for x in by_pid[pid] if x not in excl] + base_contests_by_tcpd.get(pid, [])
        if pa == pb:
            cl = cluster(pa, rs)
            fa, fb = fit(ca, cl), fit(cb, cl)
            if fa != fb:
                loser = a if fa < fb else b
                loser["tcpd_dropped"] = loser["tcpd"]
                loser["tcpd"] = None
                swaps.append((key, "same pid on both; kept the better fit", loser["raw_id"]))
            continue
        cla, clb = cluster(pa, rs), cluster(pb, rs)
        now = fit(ca, cla) + fit(cb, clb)
        swapped = fit(cb, cla) + fit(ca, clb)
        if swapped > now:
            a["tcpd"], b["tcpd"] = b["tcpd"], a["tcpd"]
            swaps.append((key, f"swapped {pa} and {pb}", a["raw_id"]))
    return swaps


# ── Pid assignments ──────────────────────────────────────────────────────


class Assigner:
    def __init__(self, path: Path, base_next: int, seed_path: Path | None = None):
        self.path = path
        src = path if path.exists() else seed_path
        data = json.loads(src.read_text()) if src and src.exists() else {}
        self.by_key = dict(data.get("by_merge_key", {}))
        used = [int(v[2:]) for v in self.by_key.values()]
        self.next_id = max([data.get("next_id", base_next), base_next] + [u + 1 for u in used])

    def get(self, key):
        if key not in self.by_key:
            self.by_key[key] = f"n-{self.next_id}"
            self.next_id += 1
        return self.by_key[key]

    def save(self):
        self.path.write_text(json.dumps({"next_id": self.next_id, "by_merge_key": self.by_key},
                                        indent=1, ensure_ascii=False) + "\n")


# ── Attribution ──────────────────────────────────────────────────────────


def lev1(a: str, b: str) -> bool:
    """True when a and b differ by at most one insert, delete or substitution."""
    if a == b:
        return True
    if abs(len(a) - len(b)) > 1:
        return False
    if len(a) > len(b):
        a, b = b, a
    i = j = 0
    edits = 0
    while i < len(a) and j < len(b):
        if a[i] == b[j]:
            i += 1
            j += 1
            continue
        edits += 1
        if edits > 1:
            return False
        if len(a) == len(b):
            i += 1
        j += 1
    return edits + (len(b) - j) + (len(a) - i) <= 1


def squeeze(s: str) -> str:
    return re.sub(r"(.)\1+", r"\1", s.replace("h", ""))


def names_close(k1: str, k2: str) -> bool:
    """Small spelling difference between two name keys (same initials and token count)."""
    if not k1 or not k2 or k1 == k2:
        return k1 == k2 and bool(k1)
    i1, r1 = k1.split("|")
    i2, r2 = k2.split("|")
    if i1 != i2 or len(r1.split()) != len(r2.split()) or min(len(r1), len(r2)) < 6:
        return False
    return squeeze(r1) == squeeze(r2) or lev1(r1, r2)


def seat_same(c, r):
    """Same seat for the spelling-tolerant name pass."""
    if c["skey"] != r["skey"]:
        return False
    if cons_match(c["cnorm"], r["cnorm"]):
        return True
    if c["house"] == r["house"] and c["cons_no"] and c["cons_no"] == r["cons_no"] \
            and (c["year"] >= 2008) == (r["year"] >= 2008):
        return True
    return len(c["cnorm"]) >= 6 and (squeeze(c["cnorm"]) == squeeze(r["cnorm"]) or lev1(c["cnorm"], r["cnorm"]))


def attribute(iv_rows, people: People, assigner: Assigner, geo: Geo, R):
    """R collects stats and lists for the report. Returns out list (pid, contest, method)."""
    tmap, conflicts = people.tcpd_map()
    iv_rows.sort(key=lambda r: (r["house"], r["year"] or 0, r["skey"], r["cons_no"] or 0,
                                r["position"] or 99, r["raw_id"]))

    def skip(r, why):
        R["skips"][why] += 1
        r["skip"] = why

    work = []
    for r in iv_rows:
        if r["house"] == "ls" and r["iv_id"] in people.iv_owner:
            skip(r, "already in base contests")
        elif not r["has_seat"]:
            skip(r, "no seat row in IV master table")
        elif not r["has_result"]:
            skip(r, "no result row in IV results table")
        else:
            work.append(r)

    base_by_tcpd = {tp: people.contests[pid] for tp, pid in tmap.items()}
    R["swaps"] = tie_break_same_names(work, base_by_tcpd)

    # Group TCPD-linked rows by pid.
    clusters = defaultdict(list)
    pending = []
    for r in work:
        if r.get("tcpd"):
            clusters[r["tcpd"]["pid"]].append(r)
        else:
            pending.append(r)

    out = []
    quarantined = []
    for tp in sorted(clusters):
        rows = clusters[tp]
        if tp in conflicts:
            R["conflicts"][tp] = conflicts[tp]
            for r in rows:
                skip(r, "TCPD pid conflicted in base database")
            continue
        target = tmap.get(tp)
        new_cs = [mk_contest(r) for r in rows]
        blocked = None
        if target:
            base_cs = people.contests[target]
            by = people.dob_year(target)
            ages = sorted(c["year"] - c["tcpd_age"] for c in new_cs
                          if c["tcpd_age"] and 18 <= c["tcpd_age"] <= 110)
            near_base = any(geo.near(n, b) for n in new_cs for b in base_cs)
            gap = abs(ages[len(ages) // 2] - by) if by and ages else 0
            # TCPD ages are self-reported and drift by a few years, so a gap
            # alone blocks only when large; a moderate gap blocks when no TCPD
            # row is near the base person's seats either.
            if gap > AGE_GAP_HARD or (gap > AGE_GAP_BLOCK and not near_base):
                blocked = (f"TCPD ages put birth near {ages[len(ages) // 2]}, "
                           f"base dob is {people.persons[target]['dob']}"
                           + ("" if near_base else ", and no TCPD row is near the base seats"))
            elif base_cs and not any(geo.near(n, b) or n["skey"] == b["skey"]
                                     or REORG.get(n["skey"], -1) == REORG.get(b["skey"], -2)
                                     for n in new_cs for b in base_cs):
                blocked = "no TCPD row shares a state or region with the base contests"
            if blocked:
                R["blocked_base"].append((target, people.persons[target]["name"], tp, blocked, len(rows)))
                target = None
            cs_all = new_cs + ([] if blocked else base_cs)
            q = quarantine_cluster(cs_all, geo, None if blocked else by)
        else:
            q = quarantine_cluster(new_cs, geo, None)
        keep = [c for c in new_cs if c["iv_id"] not in q]
        for c in new_cs:
            if c["iv_id"] in q:
                quarantined.append((c, tp, q[c["iv_id"]]))
        if not keep:
            continue
        if target:
            pid, method = target, "tcpd-attach"
        else:
            if blocked:
                pid = assigner.get(f"tcpd-blocked:{tp}")
                people.new_person(pid, "", "fallback", None, f"tcpd_blocked:{tp}", 0.5)
            else:
                pid = assigner.get(f"tcpd:{tp}")
                people.new_person(pid, "", "tcpd_only", tp, "tcpd_pid", 0.8)
            latest = max(keep, key=lambda c: (c["year"], c["iv_id"]))
            people.persons[pid]["name"] = latest["name"]
            people.persons[pid]["gender"] = next((r["tcpd"]["sex"] for r in rows if r["tcpd"]["sex"]), None)
            method = "tcpd-mint"
        for c in keep:
            if people.has_same_contest(pid, c):
                skip(c["row"], "same person already has this seat in this election")
                continue
            c["tcpd_pid"] = tp
            people.add(pid, c)
            out.append([pid, c, method])
            R["stats"][(c["house"], method)] += 1

    for c, tp, rule in quarantined:
        pid = assigner.get(f"quarantine:{c['house']}:{c['row']['raw_id']}")
        people.new_person(pid, c["name"], "fallback", None, f"quarantine:{tp}", 0.3)
        c["tcpd_pid"] = None
        people.add(pid, c)
        out.append([pid, c, "quarantine"])
        R["stats"][(c["house"], "quarantine")] += 1
        R["quarantine"].append((rule, pid, c, tp))
        people.persons[pid]["quarantined"] = True

    # Name pass for rows without a TCPD row.
    idx = defaultdict(set)
    at_seat = defaultdict(set)       # (skey, cnorm) -> pids
    at_no = defaultdict(set)         # (skey, house, cons_no, post-2008) -> pids
    state_seats = defaultdict(set)
    for pid, p in people.persons.items():
        if not p["base"] and (p["source"] == "fallback"):
            continue
        for c in people.contests[pid]:
            for nk in p["names"]:
                idx[(nk, c["skey"])].add(pid)
            at_seat[(c["skey"], c["cnorm"])].add(pid)
            state_seats[c["skey"]].add(c["cnorm"])
            if c["cons_no"]:
                at_no[(c["skey"], c["house"], c["cons_no"], c["year"] >= 2008)].add(pid)
    for r in pending:
        c = mk_contest(r)
        c["tcpd_pid"] = None
        cands = []
        if c["nkey"]:
            for pid in idx.get((c["nkey"], c["skey"]), ()):
                cs = [x for x in people.contests[pid] if x["skey"] == c["skey"]]
                if any(cons_match(x["cnorm"], c["cnorm"]) for x in cs) \
                        and c["party"] and any(x["party"] == c["party"] for x in people.contests[pid]) \
                        and people.age_ok(pid, c["year"]) and not people.has_same_contest(pid, c):
                    cands.append(pid)
        method = "name-attach"
        if not cands and c["nkey"] and c["party"] != "IND":
            near_pids = set(at_no.get((c["skey"], c["house"], c["cons_no"], c["year"] >= 2008), ()))
            for sn in state_seats.get(c["skey"], ()):
                if cons_match(sn, c["cnorm"]) or (len(sn) >= 6 and (
                        squeeze(sn) == squeeze(c["cnorm"]) or lev1(sn, c["cnorm"]))):
                    near_pids |= at_seat[(c["skey"], sn)]
            for pid in sorted(near_pids):
                p = people.persons[pid]
                if not any(names_close(c["nkey"], nk) for nk in p["names"]):
                    continue
                if any(seat_same(x, c) and x["party"] == c["party"] for x in people.contests[pid]) \
                        and people.age_ok(pid, c["year"]) and not people.has_same_contest(pid, c):
                    cands.append(pid)
            method = "name-attach-spelling"
        if len(cands) == 1:
            people.add(cands[0], c)
            out.append([cands[0], c, method])
            R["stats"][(c["house"], method)] += 1
            continue
        if len(cands) > 1:
            R["stats"][(c["house"], "name-ambiguous->mint")] += 1
        pid = assigner.get(f"iv:{c['house']}:{r['raw_id']}")
        people.new_person(pid, c["name"], "fallback", None, "name", 0.4)
        people.add(pid, c)
        out.append([pid, c, "name-mint"])
        R["stats"][(c["house"], "name-mint")] += 1
    return out


# ── Split-merge pass (review rule 4) ─────────────────────────────────────


def split_merge(people: People, out, iv_rows, R):
    """Merge persons with the same order-kept name at the same seat in
    consecutive elections, same non-IND party (or a TCPD-recorded switch),
    and no two contests in one year. Base persons are never absorbed."""
    seat_years = defaultdict(set)
    for r in iv_rows:
        seat_years[(r["house"], r["skey"], r["cnorm"])].add(r["year"])
    seat_years = {k: sorted(v) for k, v in seat_years.items()}

    by_seat = defaultdict(list)       # (house, skey, cnorm, nkey) -> [(pid, contest)]
    for pid, cs in people.contests.items():
        for c in cs:
            if c["nkey"]:
                by_seat[(c["house"], c["skey"], c["cnorm"], c["nkey"])].append((pid, c))

    parent = {}

    def find(x):
        while parent.get(x, x) != x:
            x = parent[x]
        return x

    members = {}

    def group(x):
        return members.setdefault(find(x), {x})

    def years(g):
        return [c["year"] for p in g for c in people.contests[p]]

    candidates = []
    for key, items in sorted(by_seat.items()):
        pids = sorted({p for p, _ in items})
        if len(pids) < 2:
            continue
        ys = seat_years.get(key[:3], [])
        pos = {y: i for i, y in enumerate(ys)}
        for i in range(len(items)):
            for j in range(len(items)):
                (pa, a), (pb, b) = items[i], items[j]
                if pa == pb or a["year"] >= b["year"]:
                    continue
                if a["year"] not in pos or b["year"] not in pos or pos[b["year"]] - pos[a["year"]] != 1:
                    continue
                party_ok = (a["party"] == b["party"] and a["party"] != "IND") or \
                           (b["last_party"] and b["last_party"] == a["party"] and a["party"] != "IND")
                if party_ok:
                    candidates.append((key, pa, pb, a, b))
    merges = []
    for key, pa, pb, a, b in candidates:
        ga, gb = find(pa), find(pb)
        if ga == gb:
            continue
        A, B = group(ga), group(gb)
        base_a = [p for p in A if people.persons[p]["base"]]
        base_b = [p for p in B if people.persons[p]["base"]]
        if base_a and base_b:
            R["base_dupes"].add(tuple(sorted((base_a[0], base_b[0]))))
            continue
        ya, yb = years(A), years(B)
        if set(ya) & set(yb):
            continue
        dobs = {people.dob_year(p) for p in A | B} - {None}
        if len(dobs) > 1:
            continue
        if dobs:
            by = dobs.pop()
            if not all(MIN_AGE <= y - by <= MAX_AGE for y in ya + yb):
                continue
        root = base_a[0] if base_a else (base_b[0] if base_b else None)
        if root is None:
            def first(g):
                return min((min(c["year"] for c in people.contests[p]), int(p[2:]), p) for p in g)
            root = min(first(A), first(B))[2]
        old_ra, old_rb = find(ga), find(gb)
        for r in (old_ra, old_rb):
            parent[r] = root
        parent[root] = root
        members[root] = A | B
        for r in (old_ra, old_rb):
            if r != root:
                members.pop(r, None)
        merges.append((pa, pb, a, b, key))

    # Apply: move contests of absorbed persons to the group root.
    moved = {}
    for root, g in members.items():
        for p in g:
            if p != root:
                moved[p] = root
    R["moved_rows"] = {}
    for row in out:
        if row[0] in moved:
            R["moved_rows"][row[1]["iv_id"]] = row[0]
            row[0] = moved[row[0]]
            row[2] = "split-merge"
            R["stats"][(row[1]["house"], "split-merge")] += 1
    for p, root in moved.items():
        people.contests[root].extend(people.contests.pop(p, []))
        people.persons[p]["absorbed_into"] = root
    R["merges"] = [(moved.get(pa, pa), pa, pb, a, b, k) for pa, pb, a, b, k in merges]
    R["moved"] = moved
    return moved


# ── Writing ──────────────────────────────────────────────────────────────


def write(conn, people: People, out, moved):
    persons = [p for pid, p in people.persons.items() if not p["base"] and pid not in moved]
    conn.executemany(
        """INSERT INTO persons (pid, canonical_name, slug, dob, gender, image_url,
           identity_source, tcpd_pid, rs_tcpd_id, sansad_dob_hash, anchor_signal, confidence)
           VALUES (?,?,?,?,?,?,?,?,?,?,?,?)""",
        [(p["pid"], p["name"] or "Unknown", slug_of(p["name"]), None, p.get("gender"), None,
          p["source"], p["tcpd_pid"], None, None,
          p["anchor"] + (";split-merged" if any(m == p["pid"] for m in moved.values()) else ""),
          p["confidence"]) for p in persons])
    seen = {tuple(r) for r in conn.execute(
        "SELECT tcpd_pid, year, state, constituency, party_short FROM contests WHERE tcpd_pid IS NOT NULL")}
    nulled = 0
    rows = []
    for pid, c, method in out:
        r = c["row"]
        tp = c.get("tcpd_pid")
        if tp:
            k = (tp, r["year"], r["state"], r["cons"], r["party"])
            if k in seen:
                tp = None
                nulled += 1
            else:
                seen.add(k)
        rows.append((pid, r["house"], r["year"], r["state"], r["cons"], r["party"], r["votes"],
                     r["vote_share"], r["position"], r["won"], r["iv_id"], tp))
    conn.executemany(
        """INSERT INTO contests (pid, contest_type, year, state, constituency, party_short,
           votes, vote_share, position, won, iv_candidate_id, tcpd_pid)
           VALUES (?,?,?,?,?,?,?,?,?,?,?,?)""", rows)
    return nulled


# ── Reports ──────────────────────────────────────────────────────────────

SELF_CHECK_NAMES = [
    ["Mamata Banerjee"], ["Sharad Pawar"], ["Akhilesh Yadav"], ["Nitish Kumar"],
    ["Shivraj Singh Chouhan", "Shivraj Singh Chauhan"], ["Siddaramaiah"],
    ["Ashok Gehlot", "Ashok Gahlot"], ["Mayawati"], ["Mulayam Singh Yadav"],
    ["Lalu Prasad", "Lalu Prasad Yadav"], ["Naveen Patnaik"], ["Jyoti Basu"],
    ["Karunanidhi"], ["Jayalalitha", "Jayalalithaa"], ["Chandrababu Naidu", "Chandra Babu Naidu"],
    ["Parkash Singh Badal", "Prakash Singh Badal"], ["Bhupinder Singh Hooda"], ["Digvijay Singh"],
    ["Kamal Nath"], ["Ghulam Nabi Azad"], ["Devendra Fadnavis"],
    ["Raman Singh", "Dr. Raman"], ["Oommen Chandy"], ["Achuthanandan"], ["Arvind Kejriwal"],
    ["Yogi Adityanath"], ["Narendra Modi"], ["Vasundhara Raje", "Vasundhra Raje"], ["Farooq Abdullah"],
    ["Hemant Soren"],
    ["Rajasekhar Reddy", "Rajasekhara Reddy"], ["Haribhai Patel", "Harilal Madhavjibhai Patel"],
    ["Narayanaswamy", "Narayana Swamy"], ["Ajay Rai"], ["Dotasara", "Dotasra"],
    ["Mahendra Singh Chouhan", "Mahendra Singh Keshar Singh Chouhan"],
]


def person_contests(conn, pid):
    return conn.execute(
        "SELECT year, contest_type, state, constituency, party_short, votes, position "
        "FROM contests WHERE pid=? ORDER BY year, contest_type, constituency", (pid,)).fetchall()


def self_check(conn):
    names = conn.execute("SELECT pid, canonical_name, identity_source FROM persons").fetchall()
    rare_names = [(pid, n, src, rare(name_tokens(n))) for pid, n, src in names]
    lines = []
    for alts in SELF_CHECK_NAMES:
        wants = [rare(name_tokens(a)) for a in alts]
        rows = []
        for pid, n, src, rt in rare_names:
            if any(w and w <= rt for w in wants):
                cs = person_contests(conn, pid)
                if cs:
                    rows.append((len(cs), pid, n, src, cs))
        rows.sort(key=lambda x: (-x[0], x[1]))
        parts = [f"{pid} '{n}' {src}: {k} contests {cs[0][0]}-{cs[-1][0]}, "
                 f"{'+'.join(sorted({c[1] for c in cs}))}, {len({c[2] for c in cs})} state(s)"
                 for k, pid, n, src, cs in rows[:3]]
        lines.append(f"- {alts[0]}: {len(rows)} person(s) with contests. "
                     + ("; ".join(parts) if parts else "None") + ".")
    return lines


def case_checks(conn):
    """Named cases from the 2026-11-20 review."""
    def who(where, *args):
        return conn.execute(
            "SELECT c.pid, p.canonical_name, c.year, c.contest_type, c.constituency, c.party_short, "
            "c.votes, c.position, (SELECT COUNT(*) FROM contests x WHERE x.pid=c.pid) "
            "FROM contests c JOIN persons p USING(pid) WHERE " + where, args).fetchall()

    def fmt(rows):
        return "; ".join(f"{r[2]} {r[4]} {r[5]} {r[6]} votes on {r[0]} '{r[1]}' ({r[8]} contests)" for r in rows)

    def plist(pid):
        cs = person_contests(conn, pid)
        return f"{pid}: " + ", ".join(f"{c[0]} {c[1]} {c[3]} {c[4]}" for c in cs)
    L = [
        "- YSR, Pulivendla: " + fmt(who("lower(c.constituency) LIKE 'pulivend%' AND c.position=1 "
                                        "AND lower(p.canonical_name) LIKE '%rajasekhar%'")),
        "- Haribhai Patel " + plist("n-305") + ". Harilal Patel " + plist("n-1748") + ".",
        "- Dhoraji 2012 and 2017 BJP rows: " + fmt(who("lower(c.constituency)='dhoraji' AND "
                                                      "c.year IN (2012, 2017) AND c.party_short='BJP'")),
        "- Kanti 2020 Ajit Kumar rows: " + fmt(who("lower(c.constituency)='kanti' AND c.year=2020 "
                                                   "AND lower(p.canonical_name) LIKE '%ajit%'")),
        "- M. Narayanaswamy " + plist("n-4322") + ".",
        "- Kolasla 1996 winner: " + fmt(who("lower(c.constituency)='kolasla' AND c.year=1996 AND c.position=1"))
        + ". Ajay Rai " + plist("n-190161") + ".",
        "- Raman Singh, Rajnandgaon wins: " + fmt(who("lower(c.constituency) LIKE 'rajnandgaon%' "
                                                      "AND c.position=1 AND lower(p.canonical_name) LIKE '%raman%'")),
        "- Dotasra, Lachhmangarh: " + fmt(who("lower(p.canonical_name) LIKE '%dotas%'")),
        "- Mahendra Singh Chouhan, Bhainsdehi BJP: " + fmt(who("lower(c.constituency) LIKE 'bhainsdehi%' "
                                                               "AND c.party_short='BJP' AND lower(p.canonical_name) LIKE '%mahendra%'")),
        "- Shivraj Singh Chouhan " + plist("n-91") + ".",
        "- Naveen Patnaik: " + fmt(who("lower(p.canonical_name) LIKE '%naveen patnaik%'")),
        "- Alakesh Das (base, unchanged) " + plist("n-1612") + ".",
    ]
    return L


def write_sample(conn, path: Path, method_of_row, merged_into, base_pids, merges, seed):
    rnd = random.Random(seed)
    multi = [pid for (pid,) in conn.execute(
        "SELECT pid FROM contests GROUP BY pid HAVING COUNT(*) >= 2 ORDER BY pid")]
    rows_by_pid = defaultdict(set)
    for (pid, ivid) in conn.execute("SELECT pid, iv_candidate_id FROM contests"):
        rows_by_pid[pid].add(method_of_row.get(ivid, "base"))
    merged = sorted(pid for pid in multi
                    if rows_by_pid[pid] & {"name-attach", "name-attach-spelling"}
                    or (pid in base_pids and "tcpd-attach" in rows_by_pid[pid]))
    minted3 = sorted(pid for (pid,) in conn.execute(
        "SELECT p.pid FROM persons p JOIN contests c USING(pid) WHERE p.identity_source='tcpd_only' "
        "GROUP BY p.pid HAVING COUNT(*) >= 3") if pid not in base_pids)
    a = rnd.sample(merged, min(200, len(merged)))
    b = rnd.sample(minted3, min(50, len(minted3)))
    roots = sorted({m[0] for m in merges})
    c = rnd.sample(roots, min(50, len(roots)))
    out = [f"# Candidate merge sample, v2 (seed {seed})", "",
           f"Part A: {len(a)} of {len(merged)} persons with 2+ contests and at least one contest "
           "linked by name, or by TCPD to a person already in the base database.",
           f"Part B: {len(b)} of {len(minted3)} TCPD-minted persons with 3+ contests.",
           f"Part C: {len(c)} of {len(roots)} persons formed by the split-merge pass.",
           "Contest columns: year, house, state, seat, party, votes, position. The tag shows how this "
           "run linked the row; 'base' means the row was already there.", ""]
    for title, pids in (("Part A", a), ("Part B", b), ("Part C", c)):
        out += [f"## {title}", ""]
        for pid in pids:
            name, src, tp, anchor = conn.execute(
                "SELECT canonical_name, identity_source, tcpd_pid, anchor_signal FROM persons WHERE pid=?",
                (pid,)).fetchone()
            out.append(f"### {name} ({pid}, {src}, tcpd {tp or '-'}, anchor {anchor})")
            for row in conn.execute(
                    "SELECT year, contest_type, state, constituency, party_short, votes, position, "
                    "iv_candidate_id, tcpd_pid FROM contests WHERE pid=? ORDER BY year, contest_type", (pid,)):
                m = method_of_row.get(row[7], "base")
                extra = f", from {merged_into.get(row[7])}" if row[7] in merged_into else ""
                out.append(f"- {row[0]} {row[1]} {row[2]} / {row[3]} / {row[4]} / {row[5]} votes / "
                           f"pos {row[6]} [{m}{extra}; tcpd {row[8] or '-'}]")
            out.append("")
    path.write_text("\n".join(out) + "\n")
    return len(a), len(b), len(c)


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--base-db", type=Path, default=None)
    ap.add_argument("--iv", type=Path, default=DEFAULT_IV)
    ap.add_argument("--tcpd-ge", type=Path, default=DEFAULT_TCPD_GE)
    ap.add_argument("--tcpd-ae", type=Path, default=DEFAULT_TCPD_AE)
    ap.add_argument("--out", type=Path, default=DEFAULT_OUT)
    ap.add_argument("--suffix", default="-v2", help="output file suffix")
    args = ap.parse_args()
    t0 = time.time()
    sfx = args.suffix
    args.out.mkdir(parents=True, exist_ok=True)
    base = args.base_db or (args.out / "netas.sqlite" if (args.out / "netas.sqlite").exists()
                            else DEFAULT_BASE_FALLBACK)
    dst = args.out / f"candidates{sfx}.sqlite"
    for suffix in ("", "-wal", "-shm", "-journal"):
        Path(str(dst) + suffix).unlink(missing_ok=True)
    src = sqlite3.connect(f"file:{base}?mode=ro", uri=True)
    conn = sqlite3.connect(dst)
    src.backup(conn)
    src.close()
    conn.execute("PRAGMA journal_mode = DELETE")

    before_persons = conn.execute("SELECT COUNT(*) FROM persons").fetchone()[0]
    before_contests = conn.execute("SELECT COUNT(*) FROM contests").fetchone()[0]
    base_max_id = conn.execute("SELECT COALESCE(MAX(id), 0) FROM contests").fetchone()[0]
    sig_sql = ("SELECT COUNT(*), TOTAL(id * 7 + COALESCE(iv_candidate_id, 0) + LENGTH(pid)) "
               "FROM contests WHERE id <= ?")
    base_sig = conn.execute(sig_sql, (base_max_id,)).fetchone()
    psig_sql = ("SELECT COUNT(*), TOTAL(LENGTH(pid || canonical_name || identity_source || "
                "COALESCE(tcpd_pid, '') || COALESCE(dob, ''))) FROM persons")
    base_psig = conn.execute(psig_sql).fetchone()
    base_max = conn.execute("SELECT MAX(CAST(SUBSTR(pid,3) AS INTEGER)) FROM persons").fetchone()[0]
    file_next = json.loads(PID_ASSIGNMENTS.read_text())["next_id"]

    iv = sqlite3.connect(f"file:{args.iv}?mode=ro", uri=True)
    iv_rows = load_iv(iv)
    ge_no, ge_name, n_ge = load_tcpd(args.tcpd_ge, "ls")
    ae_no, ae_name, n_ae = load_tcpd(args.tcpd_ae, "ac")
    by_no = {**ge_no, **ae_no}
    by_name = {**ge_name, **ae_name}
    geo = Geo(iv, (t for rows in ae_no.values() for t in rows))
    iv.close()
    link_stats = link_tcpd(iv_rows, by_no, by_name)
    iv_by_id = {(r["house"], r["iv_id"]): r for r in iv_rows}

    people = People(conn, iv_by_id)
    base_pids = set(people.persons)
    assigner = Assigner(args.out / f"candidate_pid_assignments{sfx}.json", max(file_next, base_max + 1),
                        seed_path=args.out / "candidate_pid_assignments.json")
    R = {"stats": Counter(), "skips": Counter(), "conflicts": {}, "blocked_base": [],
         "quarantine": [], "base_dupes": set(), "swaps": [], "merges": []}
    out = attribute(iv_rows, people, assigner, geo, R)
    moved = split_merge(people, out, iv_rows, R)
    nulled = write(conn, people, out, moved)
    conn.execute("INSERT OR REPLACE INTO build_meta(key, value) VALUES ('candidates_built_at', ?)",
                 (time.strftime("%Y-%m-%dT%H:%M:%S%z"),))
    conn.commit()
    assigner.save()

    # Base persons with an internal same-year conflict (left unchanged).
    base_conflicts = []
    for pid in sorted(base_pids):
        cs = [c for c in people.contests[pid] if c["base"]]
        for i in range(len(cs)):
            for j in range(i + 1, len(cs)):
                a, b = cs[i], cs[j]
                if a["year"] == b["year"] and geo.near(a, b) is False and a["party"] != b["party"]:
                    base_conflicts.append((pid, people.persons[pid]["name"], a, b))

    # Integrity checks.
    q1 = lambda sql, *a: conn.execute(sql, a).fetchone()[0]  # noqa: E731
    dup_iv = q1("SELECT COUNT(*) FROM (SELECT iv_candidate_id FROM contests WHERE iv_candidate_id "
                "IS NOT NULL GROUP BY 1 HAVING COUNT(*)>1)")
    tp_on_persons = q1("SELECT COUNT(*) FROM (SELECT tcpd_pid FROM persons WHERE tcpd_pid IS NOT NULL "
                       "GROUP BY 1 HAVING COUNT(*)>1)")
    tp_split = q1("SELECT COUNT(*) FROM (SELECT tcpd_pid FROM contests WHERE tcpd_pid IS NOT NULL AND id > ? "
                  "GROUP BY 1 HAVING COUNT(DISTINCT pid)>1)", base_max_id)
    fk_bad = q1("SELECT COUNT(*) FROM contests c LEFT JOIN persons p USING(pid) WHERE p.pid IS NULL")
    empty = q1("SELECT COUNT(*) FROM persons p WHERE NOT EXISTS (SELECT 1 FROM contests c WHERE c.pid=p.pid) "
               "AND p.pid NOT IN (%s)" % ",".join("?" * len(base_pids)), *sorted(base_pids))
    same_year_new = q1("SELECT COUNT(*) FROM (SELECT pid, year, contest_type FROM contests WHERE id > ? "
                       "GROUP BY 1,2,3 HAVING COUNT(DISTINCT state) > 1)", base_max_id)
    base_ok = tuple(conn.execute(sig_sql, (base_max_id,)).fetchone()) == tuple(base_sig)
    persons_ok = tuple(conn.execute(psig_sql + " WHERE pid IN (%s)" % ",".join("?" * len(base_pids)),
                                    sorted(base_pids)).fetchone()) == tuple(base_psig)

    method_of_row = {c["iv_id"]: m for pid, c, m in out}
    merged_into = R.get("moved_rows", {})
    n_a, n_b, n_c = write_sample(conn, args.out / f"candidates-sample{sfx}.md", method_of_row,
                                 merged_into, base_pids, R["merges"], SEED)

    after_persons = q1("SELECT COUNT(*) FROM persons")
    after_contests = q1("SELECT COUNT(*) FROM contests")
    winners = q1("SELECT COUNT(DISTINCT pid) FROM contests WHERE won=1")
    multi = q1("SELECT COUNT(*) FROM (SELECT pid FROM contests GROUP BY pid HAVING COUNT(*)>=2)")
    either = q1("SELECT COUNT(*) FROM (SELECT pid FROM contests GROUP BY pid HAVING COUNT(*)>=2 OR MAX(won)=1)")
    by_src = conn.execute("SELECT identity_source, COUNT(*) FROM persons GROUP BY 1 ORDER BY 1").fetchall()
    check = self_check(conn)
    cases = case_checks(conn)
    conn.close()

    # Detail files.
    with open(args.out / f"candidates-quarantine{sfx}.csv", "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["rule", "new_pid", "tcpd_pid", "house", "year", "state", "seat", "name", "party",
                    "votes", "vote_share", "position"])
        for rule, pid, c, tp in sorted(R["quarantine"], key=lambda x: (x[0], x[3], x[2]["year"])):
            r = c["row"]
            w.writerow([rule, pid, tp, r["house"], r["year"], r["state"], r["cons"], r["name"], r["party"],
                        r["votes"], r["vote_share"], r["position"]])
    with open(args.out / f"candidates-split-merges{sfx}.csv", "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["kept_pid", "pid_a", "pid_b", "house", "state", "seat", "name_a", "year_a",
                    "party_a", "name_b", "year_b", "party_b"])
        for root, pa, pb, a, b, k in R["merges"]:
            w.writerow([root, pa, pb, k[0], a["row"]["state"] if a["row"] else k[1], k[2],
                        a["name"], a["year"], a["party"], b["name"], b["year"], b["party"]])
    with open(args.out / f"candidates-skipped{sfx}.csv", "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["reason", "house", "iv_candidate_id", "year", "state", "seat", "name", "party",
                    "votes", "position", "tcpd_pid"])
        for r in iv_rows:
            if r.get("skip") and r["skip"] != "already in base contests":
                w.writerow([r["skip"], r["house"], r["raw_id"], r["year"], r["state"], r["cons"], r["name"],
                            r["party"], r["votes"], r["position"], r["tcpd"]["pid"] if r.get("tcpd") else ""])

    runtime = time.time() - t0
    houses = {"ls": "Lok Sabha", "ac": "Assembly"}
    methods = ["tcpd-attach", "tcpd-mint", "name-attach", "name-attach-spelling", "name-mint",
               "quarantine", "split-merge"]
    st = R["stats"]
    qrules = Counter(x[0] for x in R["quarantine"])
    L = ["# Candidate extension report, v2", "",
         f"Base database: `{base}` (May 2026 copy; the published tarball carries no sqlite). "
         f"Output: `{dst}`. Runtime {runtime:.0f} s. New pids start at n-{max(file_next, base_max + 1)}, "
         f"because the base database already uses pids up to n-{base_max}.", "",
         "## Counts", "",
         f"- Persons: {before_persons} before, {after_persons} after ({after_persons - before_persons} added).",
         f"- Contests: {before_contests} before, {after_contests} after ({after_contests - before_contests} added).",
         f"- Persons with a win: {winners}. Persons with 2+ contests: {multi}. Either: {either}.",
         "- Persons by identity_source: " + ", ".join(f"{s} {n}" for s, n in by_src) + ".", "",
         "Contests added, by house and the method that placed them. Split-merge rows were first placed "
         "by another method and then moved; they are counted under split-merge only.", ""]
    for h in ("ls", "ac"):
        tot = Counter()
        for pid, c, m in out:
            if c["house"] == h:
                tot[m] += 1
        L.append(f"- {houses[h]}: " + ", ".join(f"{m} {tot[m]}" for m in methods)
                 + f" ({st[(h, 'name-ambiguous->mint')]} name-mints had 2+ qualifying persons).")
    L += ["", "## TCPD row matching", "",
          "Each IV candidacy finds its TCPD seat by house, year, state and seat number (seat name as "
          "fallback) and takes the row with equal votes and an agreeing name.", ""]
    keep_keys = [k for k in sorted(link_stats) if not k.startswith("year shift")]
    for k in keep_keys:
        L.append(f"- {k}: {link_stats[k]}")
    L.append("- Year shifts applied: " + "; ".join(k[len('year shift '):] for k in sorted(link_stats)
                                                   if k.startswith("year shift")) + ".")
    L += ["", "## Same-name candidates in one race (review rule 2)", "",
          f"{len(R['swaps'])} races had two same-name candidates whose TCPD pids I swapped or split by "
          "party and vote level. Examples: " + "; ".join(f"{k[1]} {k[4]} ({how})" for k, how, _ in R["swaps"][:5])
          + ".", "",
          "## Quarantined rows (review rule 1)", "",
          f"{len(R['quarantine'])} TCPD-linked rows became their own person (identity_source 'fallback', "
          "anchor 'quarantine:<tcpd pid>', confidence 0.3, contest tcpd_pid NULL). Full list in "
          f"candidates-quarantine{sfx}.csv.", ""]
    for rule, n in qrules.most_common():
        ex = [x for x in R["quarantine"] if x[0] == rule][:2]
        L.append(f"- {rule}: {n}. For example " + "; ".join(
            f"{c['name']} {c['year']} {c['row']['cons']} {c['party']} (pid {tp})" for _, _, c, tp in ex) + ".")
    L += ["", "## Base persons whose TCPD pid disagrees with their record (review rule 3)", "",
          f"{len(R['blocked_base'])} base persons keep their rows unchanged, but this run did not attach "
          "their TCPD pid's rows to them; those rows form one separate person each (anchor 'tcpd_blocked').", ""]
    for pid, name, tp, why, n in R["blocked_base"][:12]:
        L.append(f"- {pid} {name}, {tp}, {n} rows: {why}.")
    if len(R["blocked_base"]) > 12:
        L.append(f"- and {len(R['blocked_base']) - 12} more.")
    L += ["", f"Base persons with two contests in one year at far seats for different parties "
          f"(base data, unchanged): {len(base_conflicts)}. "
          + "; ".join(f"{pid} {n} ({a['year']} {a['cnorm']} {a['party']} / {b['cnorm']} {b['party']})"
                      for pid, n, a, b in base_conflicts[:6]) + ".",
          f"Pairs of base persons that the split-merge rules would join (base duplicates, unchanged): "
          f"{len(R['base_dupes'])}. " + ", ".join("/".join(p) for p in sorted(R["base_dupes"])[:10]) + ".", "",
          "## Split-merges (review rule 4)", "",
          f"{len(R['merges'])} merges joined {len(moved)} absorbed persons into {len({m[0] for m in R['merges']})} "
          f"kept persons, moving {sum(st[(h, 'split-merge')] for h in houses)} contests. Rule: same "
          "order-kept name at the same seat in consecutive elections, same non-IND party or a TCPD-recorded "
          "switch, no two contests in one year, dates of birth consistent; base persons are never absorbed. "
          f"Every merge is listed in candidates-split-merges{sfx}.csv; Part C of the sample shows 50.", ""]
    for root, pa, pb, a, b, k in R["merges"][:8]:
        L.append(f"- {root}: {a['name']} {a['year']} {a['party']} + {b['year']} {b['party']}, {k[2]} ({k[0]}).")
    L += ["", "## Candidacies skipped", ""]
    for k, v in R["skips"].most_common():
        L.append(f"- {k}: {v}")
    L += [f"- Contests stored with tcpd_pid NULL because UNIQUE(tcpd_pid, year, state, constituency, "
          f"party_short) already held the key (two polls in one year): {nulled}.",
          f"- TCPD pids not used because the base database puts them on two persons: {len(R['conflicts'])}.", "",
          "## Integrity checks (run on the output)", "",
          f"- IV candidate ids on more than one contest row: {dup_iv}.",
          f"- TCPD pids on more than one person row (all from the base database): {tp_on_persons}.",
          f"- TCPD pids on new contest rows of more than one person: {tp_split}.",
          f"- New contest rows whose pid has no person row: {fk_bad}. New persons with no contest: {empty}.",
          f"- Persons with new contests in two states in one year and house: {same_year_new}.",
          f"- Base contest rows unchanged: {'yes' if base_ok else 'NO'}. Base person rows unchanged: "
          f"{'yes' if persons_ok else 'NO'}.",
          f"- Sample: {n_a} Part A, {n_b} Part B, {n_c} Part C in candidates-sample{sfx}.md.", "",
          "## Review cases", ""]
    L += cases
    L += ["", "## Self-check: long-career politicians", "",
          "Persons whose rare name tokens contain one spelling of the target's; top three by contests.", ""]
    L += check
    (args.out / f"candidates-report{sfx}.md").write_text("\n".join(L) + "\n")
    print("\n".join(L[:22]))
    return 0


if __name__ == "__main__":
    sys.exit(main())
