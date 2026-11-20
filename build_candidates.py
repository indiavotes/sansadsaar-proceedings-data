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
    s = re.sub(r"[.,;:()\[\]'\"]", " ", s.lower())
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


# ── Person model ─────────────────────────────────────────────────────────


class People:
    def __init__(self, conn):
        self.persons = {}           # pid -> dict
        self.contests = defaultdict(list)   # pid -> list of contest summaries
        for pid, name, dob, tp, src in conn.execute(
                "SELECT pid, canonical_name, dob, tcpd_pid, identity_source FROM persons"):
            self.persons[pid] = {"pid": pid, "name": name, "dob": dob, "tcpd_pid": tp,
                                 "source": src, "base": True,
                                 "names": {name_key(name)} - {""}}
        for pid, ctype, year, state, cons, party, ivid, tp in conn.execute(
                "SELECT pid, contest_type, year, state, constituency, party_short, "
                "iv_candidate_id, tcpd_pid FROM contests"):
            self.contests[pid].append({"house": ctype, "year": year, "skey": state_key(state or ""),
                                       "cnorm": norm_cons(cons), "party": norm_party(party),
                                       "ekey": year, "tcpd": tp, "iv_id": ivid})
        self.iv_owner = {c["iv_id"]: pid for pid, cs in self.contests.items() for c in cs if c["iv_id"]}
        self.existing_iv_ids = set(self.iv_owner)

    def tcpd_map(self):
        """tcpd pid -> person pid, plus the set of conflicted tcpd pids."""
        owners = defaultdict(set)
        for pid, p in self.persons.items():
            if p["tcpd_pid"]:
                owners[p["tcpd_pid"]].add(pid)
        for pid, cs in self.contests.items():
            for c in cs:
                if c["tcpd"]:
                    owners[c["tcpd"]].add(pid)
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

    def age_ok(self, pid, year):
        dob = self.persons[pid].get("dob")
        if not dob or not re.match(r"\d{4}", dob):
            return True
        return year - int(dob[:4]) >= MIN_AGE

    def has_same_contest(self, pid, r):
        for c in self.contests[pid]:
            if (c["house"], c["year"], c["cnorm"]) == (r["house"], r["year"], r["cnorm"]) \
                    and c["ekey"] == r["election_key"]:
                return True
        return False

    def add_names(self, pid, *names):
        for n in names:
            k = name_key(n)
            if k:
                self.persons[pid]["names"].add(k)

    def add_contest(self, pid, r, tcpd_pid):
        self.contests[pid].append({"house": r["house"], "year": r["year"], "skey": r["skey"],
                                   "cnorm": r["cnorm"], "party": r["party"],
                                   "ekey": r["election_key"], "tcpd": tcpd_pid,
                                   "iv_id": r["iv_id"]})
        self.add_names(pid, r["name"], r["tcpd"]["name"] if r.get("tcpd") else "")


# ── Pid assignments ──────────────────────────────────────────────────────


class Assigner:
    def __init__(self, path: Path, base_next: int):
        self.path = path
        data = json.loads(path.read_text()) if path.exists() else {}
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


# ── Main attribution ─────────────────────────────────────────────────────


def attribute(iv_rows, people: People, assigner: Assigner, stats, skips, conflicts_seen):
    tmap, conflicts = people.tcpd_map()
    minted_tcpd = {}            # tcpd pid -> new person pid
    new_persons = {}            # pid -> person insert dict
    out = []                    # (pid, iv_row, tcpd_pid, method)

    # Stable order: house, year, seat, position, id.
    iv_rows.sort(key=lambda r: (r["house"], r["year"] or 0, r["skey"], r["cons_no"] or 0,
                                r["position"] or 99, r["raw_id"]))

    def skip(r, why):
        skips[why] += 1
        r["skip"] = why

    # Pass 1: TCPD-linked candidacies.
    pending_name = []
    for r in iv_rows:
        if r["house"] == "ls" and r["iv_id"] in people.existing_iv_ids:
            people.add_names(people.iv_owner[r["iv_id"]], r["name"])
            skip(r, "already in base contests")
            continue
        if not r["has_seat"]:
            skip(r, "no seat row in IV master table")
            continue
        if not r["has_result"]:
            skip(r, "no result row in IV results table")
            continue
        t = r.get("tcpd")
        if not t:
            pending_name.append(r)
            continue
        tp = t["pid"]
        if tp in conflicts:
            conflicts_seen[tp] = conflicts[tp]
            skip(r, "TCPD pid conflicted in base database")
            continue
        if tp in tmap:
            pid = tmap[tp]
            if not people.age_ok(pid, r["year"]):
                skip(r, "TCPD link to existing person fails age guard")
                conflicts_seen[tp] = f"age guard: {pid} born {people.persons[pid]['dob']}, contest {r['year']}"
                continue
            method = "tcpd-attach"
        else:
            pid = minted_tcpd.get(tp)
            if pid is None:
                pid = assigner.get(f"tcpd:{tp}")
                minted_tcpd[tp] = pid
                people.persons[pid] = {"pid": pid, "name": r["name"], "dob": None,
                                       "tcpd_pid": tp, "source": "tcpd_only", "base": False,
                                       "names": set()}
                new_persons[pid] = {"pid": pid, "tcpd_pid": tp, "gender": t["sex"],
                                    "identity_source": "tcpd_only", "anchor_signal": "tcpd_pid",
                                    "confidence": 0.8, "name_row": r}
            method = "tcpd-mint"
        if people.has_same_contest(pid, r):
            skip(r, "same person already has this seat in this election")
            continue
        people.add_contest(pid, r, tp)
        np = new_persons.get(pid)
        if np and (r["year"], r["raw_id"]) >= (np["name_row"]["year"], np["name_row"]["raw_id"]):
            np["name_row"] = r          # canonical name = latest candidacy's IV name
        out.append((pid, r, tp, method))
        stats[(r["house"], method)] += 1

    # Pass 2: name link for candidacies without a TCPD row.
    idx = defaultdict(set)      # (name_key, skey) -> pids eligible as anchors
    for pid, p in people.persons.items():
        if p["source"] == "fallback" and not p["base"]:
            continue
        states = {c["skey"] for c in people.contests[pid]}
        for nn in p["names"]:
            for sk in states:
                idx[(nn, sk)].add(pid)
    for r in pending_name:
        cands = []
        key = name_key(r["name"])
        if key:
            for pid in idx.get((key, r["skey"]), ()):
                cs = [c for c in people.contests[pid] if c["skey"] == r["skey"]]
                seat_ok = any(cons_match(c["cnorm"], r["cnorm"]) for c in cs)
                party_ok = r["party"] and any(c["party"] == r["party"] for c in people.contests[pid])
                if seat_ok and party_ok and people.age_ok(pid, r["year"]) \
                        and not people.has_same_contest(pid, r):
                    cands.append(pid)
        if len(cands) == 1:
            pid = cands[0]
            people.add_contest(pid, r, None)
            out.append((pid, r, None, "name-attach"))
            stats[(r["house"], "name-attach")] += 1
            continue
        if len(cands) > 1:
            stats[(r["house"], "name-ambiguous->mint")] += 1
        pid = assigner.get(f"iv:{r['house']}:{r['raw_id']}")
        people.persons[pid] = {"pid": pid, "name": r["name"], "dob": None, "tcpd_pid": None,
                               "source": "fallback", "base": False, "names": set()}
        new_persons[pid] = {"pid": pid, "tcpd_pid": None, "gender": None,
                            "identity_source": "fallback", "anchor_signal": "name",
                            "confidence": 0.4, "name_row": r}
        people.add_contest(pid, r, None)
        out.append((pid, r, None, "name-mint"))
        stats[(r["house"], "name-mint")] += 1
    return out, new_persons


def write(conn, out, new_persons):
    conn.executemany(
        """INSERT INTO persons (pid, canonical_name, slug, dob, gender, image_url,
           identity_source, tcpd_pid, rs_tcpd_id, sansad_dob_hash, anchor_signal, confidence)
           VALUES (?,?,?,?,?,?,?,?,?,?,?,?)""",
        [(p["pid"], p["name_row"]["name"] or "Unknown", slug_of(p["name_row"]["name"]), None,
          p["gender"], None, p["identity_source"], p["tcpd_pid"], None, None,
          p["anchor_signal"], p["confidence"]) for p in new_persons.values()])
    seen_unique = {tuple(r) for r in conn.execute(
        "SELECT tcpd_pid, year, state, constituency, party_short FROM contests WHERE tcpd_pid IS NOT NULL")}
    nulled = 0
    rows = []
    for pid, r, tp, method in out:
        if tp:
            k = (tp, r["year"], r["state"], r["cons"], r["party"])
            if k in seen_unique:
                tp = None       # second poll in the same year/seat (e.g. Bihar 2005 Feb + Oct)
                nulled += 1
            else:
                seen_unique.add(k)
        rows.append((pid, r["house"], r["year"], r["state"], r["cons"], r["party"],
                     r["votes"], r["vote_share"], r["position"], r["won"], r["iv_id"], tp))
    conn.executemany(
        """INSERT INTO contests (pid, contest_type, year, state, constituency, party_short,
           votes, vote_share, position, won, iv_candidate_id, tcpd_pid)
           VALUES (?,?,?,?,?,?,?,?,?,?,?,?)""", rows)
    return nulled


# ── Reports ──────────────────────────────────────────────────────────────

SELF_CHECK_NAMES = [
    ["Mamata Banerjee"], ["Sharad Pawar"], ["Akhilesh Yadav"], ["Nitish Kumar"],
    ["Shivraj Singh Chouhan", "Shivraj Singh Chauhan"], ["Siddaramaiah", "Siddaramaiah S"],
    ["Ashok Gehlot", "Ashok Gahlot"], ["Mayawati"], ["Mulayam Singh Yadav"],
    ["Lalu Prasad", "Lalu Prasad Yadav"], ["Naveen Patnaik"], ["Jyoti Basu"],
    ["Karunanidhi"], ["Jayalalitha", "Jayalalithaa"], ["Chandrababu Naidu", "Chandra Babu Naidu"],
    ["Parkash Singh Badal", "Prakash Singh Badal"], ["Bhupinder Singh Hooda"], ["Digvijay Singh"],
    ["Kamal Nath"], ["Ghulam Nabi Azad"], ["Devendra Fadnavis", "Devendra Fadanvis"],
    ["Raman Singh"], ["Oommen Chandy"], ["Achuthanandan"], ["Arvind Kejriwal"],
    ["Yogi Adityanath"], ["Narendra Modi"], ["Vasundhara Raje"], ["Farooq Abdullah"],
    ["Hemant Soren"],
]


def person_contests(conn, pid):
    return conn.execute(
        "SELECT year, contest_type, state, constituency, party_short, votes, position "
        "FROM contests WHERE pid=? ORDER BY year, contest_type, constituency", (pid,)).fetchall()


def self_check(conn):
    """Persons whose rare name tokens contain one spelling of the target's."""
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


def possible_splits(conn):
    """Pairs of TCPD-anchored persons with the same name key and state that also
    share a seat and a party. The rules forbid merging two TCPD pids, so these
    stay separate; the count measures how much TCPD's own pid split leaves behind."""
    people = defaultdict(list)
    for pid, n, tp in conn.execute("SELECT pid, canonical_name, tcpd_pid FROM persons "
                                   "WHERE tcpd_pid IS NOT NULL"):
        people[pid] = [name_key(n), tp, []]
    for pid, ctype, state, cons, party in conn.execute(
            "SELECT pid, contest_type, state, constituency, party_short FROM contests"):
        if pid in people:
            people[pid][2].append((ctype, state_key(state or ""), norm_cons(cons), party))
    groups = defaultdict(list)
    for pid, (k, tp, cs) in people.items():
        for sk in {c[1] for c in cs}:
            if k:
                groups[(k, sk)].append(pid)
    cross, same = 0, 0
    examples = []
    for (k, sk), pids in groups.items():
        for i in range(len(pids)):
            for j in range(i + 1, len(pids)):
                a, b = people[pids[i]][2], people[pids[j]][2]
                if not ({c[3] for c in a} & {c[3] for c in b}) - {"IND"}:
                    continue
                houses_a, houses_b = {c[0] for c in a}, {c[0] for c in b}
                shared_seat = any(cons_match(x[2], y[2]) for x in a for y in b)
                if houses_a != houses_b and len(houses_a) == 1 and len(houses_b) == 1:
                    cross += 1
                    if len(examples) < 4:
                        examples.append(f"{pids[i]}/{pids[j]} ({k.split('|')[1]}, {sk})")
                elif shared_seat:
                    same += 1
    return cross, same, examples


def write_sample(conn, path: Path, methods_by_pid, base_pids):
    rnd = random.Random(SEED)
    multi = [pid for (pid,) in conn.execute(
        "SELECT pid FROM contests GROUP BY pid HAVING COUNT(*) >= 2 ORDER BY pid")]
    merged = sorted(pid for pid in multi
                    if methods_by_pid.get(pid, set()) & {"name-attach"}
                    or (pid in base_pids and "tcpd-attach" in methods_by_pid.get(pid, set())))
    minted3 = sorted(pid for (pid,) in conn.execute(
        "SELECT p.pid FROM persons p JOIN contests c USING(pid) WHERE p.identity_source='tcpd_only' "
        "GROUP BY p.pid HAVING COUNT(*) >= 3") if pid not in base_pids)
    a = rnd.sample(merged, min(200, len(merged)))
    b = rnd.sample(minted3, min(50, len(minted3)))
    out = [f"# Candidate merge sample (seed {SEED})", "",
           f"Part A: {len(a)} of {len(merged)} persons with 2+ contests and at least one contest "
           "linked by name, or by TCPD to a person already in the base database.",
           f"Part B: {len(b)} of {len(minted3)} TCPD-minted persons with 3+ contests.",
           "Contest columns: year, house, state, seat, party, votes, position. "
           "Method shows how this run linked the row; 'base' means the row was already there.", ""]
    for title, pids in (("Part A", a), ("Part B", b)):
        out.append(f"## {title}")
        out.append("")
        for pid in pids:
            name, src, tp = conn.execute(
                "SELECT canonical_name, identity_source, tcpd_pid FROM persons WHERE pid=?", (pid,)).fetchone()
            out.append(f"### {name} ({pid}, {src}, tcpd {tp or '-'})")
            for c in conn.execute(
                    "SELECT year, contest_type, state, constituency, party_short, votes, position, "
                    "iv_candidate_id FROM contests WHERE pid=? ORDER BY year, contest_type", (pid,)):
                m = methods_by_pid.get(("row", c[7]), "base")
                out.append(f"- {c[0]} {c[1]} {c[2]} / {c[3]} / {c[4]} / {c[5]} votes / pos {c[6]} [{m}]")
            out.append("")
    path.write_text("\n".join(out) + "\n")
    return len(a), len(b)


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--base-db", type=Path, default=None,
                    help="base netas.sqlite (default: out/netas.sqlite if present, else the May copy)")
    ap.add_argument("--iv", type=Path, default=DEFAULT_IV)
    ap.add_argument("--tcpd-ge", type=Path, default=DEFAULT_TCPD_GE)
    ap.add_argument("--tcpd-ae", type=Path, default=DEFAULT_TCPD_AE)
    ap.add_argument("--out", type=Path, default=DEFAULT_OUT)
    args = ap.parse_args()
    t0 = time.time()
    args.out.mkdir(parents=True, exist_ok=True)
    base = args.base_db or (args.out / "netas.sqlite" if (args.out / "netas.sqlite").exists()
                            else DEFAULT_BASE_FALLBACK)
    dst = args.out / "candidates.sqlite"
    for suffix in ("", "-wal", "-shm"):
        Path(str(dst) + suffix).unlink(missing_ok=True)
    src = sqlite3.connect(f"file:{base}?mode=ro", uri=True)
    conn = sqlite3.connect(dst)
    src.backup(conn)
    src.close()
    conn.execute("PRAGMA journal_mode = DELETE")
    print(f"base {base} -> {dst}")

    before_persons = conn.execute("SELECT COUNT(*) FROM persons").fetchone()[0]
    before_contests = conn.execute("SELECT COUNT(*) FROM contests").fetchone()[0]
    base_max_id = conn.execute("SELECT COALESCE(MAX(id), 0) FROM contests").fetchone()[0]
    base_sig = conn.execute(
        "SELECT COUNT(*), TOTAL(id * 7 + COALESCE(iv_candidate_id, 0) + LENGTH(pid)) FROM contests "
        "WHERE id <= ?", (base_max_id,)).fetchone()
    base_persons_sig = conn.execute("SELECT COUNT(*), TOTAL(LENGTH(pid || canonical_name || "
                                    "identity_source || COALESCE(tcpd_pid, ''))) FROM persons").fetchone()
    base_max = conn.execute("SELECT MAX(CAST(SUBSTR(pid,3) AS INTEGER)) FROM persons").fetchone()[0]
    file_next = json.loads(PID_ASSIGNMENTS.read_text())["next_id"]
    people = People(conn)
    base_pids = set(people.persons)

    iv = sqlite3.connect(f"file:{args.iv}?mode=ro", uri=True)
    iv_rows = load_iv(iv)
    iv.close()
    print(f"IV candidacies: {len(iv_rows)}")

    ge_no, ge_name, n_ge = load_tcpd(args.tcpd_ge, "ls")
    ae_no, ae_name, n_ae = load_tcpd(args.tcpd_ae, "ac")
    by_no = {**ge_no, **ae_no}
    by_name = {**ge_name, **ae_name}
    print(f"TCPD rows: GE {n_ge}, AE {n_ae}")
    link_stats = link_tcpd(iv_rows, by_no, by_name)

    assigner = Assigner(args.out / "candidate_pid_assignments.json", max(file_next, base_max + 1))
    stats, skips, conflicts_seen = Counter(), Counter(), {}
    out, new_persons = attribute(iv_rows, people, assigner, stats, skips, conflicts_seen)
    nulled = write(conn, out, new_persons)
    with open(args.out / "candidates-skipped.csv", "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["reason", "house", "iv_candidate_id", "year", "state", "seat", "name", "party",
                    "votes", "position", "tcpd_pid"])
        for r in iv_rows:
            if r.get("skip") and r["skip"] != "already in base contests":
                w.writerow([r["skip"], r["house"], r["raw_id"], r["year"], r["state"], r["cons"],
                            r["name"], r["party"], r["votes"], r["position"],
                            r["tcpd"]["pid"] if r.get("tcpd") else ""])
    conn.execute("INSERT OR REPLACE INTO build_meta(key, value) VALUES ('candidates_built_at', ?)",
                 (time.strftime("%Y-%m-%dT%H:%M:%S%z"),))
    conn.commit()
    assigner.save()

    # Integrity checks.
    dup_iv = conn.execute("SELECT COUNT(*) FROM (SELECT iv_candidate_id FROM contests WHERE "
                          "iv_candidate_id IS NOT NULL GROUP BY 1 HAVING COUNT(*)>1)").fetchone()[0]
    multi_tcpd_person = conn.execute(
        "SELECT COUNT(*) FROM (SELECT tcpd_pid FROM persons WHERE tcpd_pid IS NOT NULL "
        "GROUP BY 1 HAVING COUNT(*)>1)").fetchone()[0]
    new_rows_pid_tcpd = defaultdict(set)
    for pid, r, tp, m in out:
        if tp:
            new_rows_pid_tcpd[pid].add(tp)
    two_pids_new = sum(1 for v in new_rows_pid_tcpd.values() if len(v) > 1)
    tp_persons = defaultdict(set)
    for pid, r, tp, m in out:
        if tp:
            tp_persons[tp].add(pid)
    split_new = sum(1 for v in tp_persons.values() if len(v) > 1)
    fk_bad = conn.execute("SELECT COUNT(*) FROM contests c LEFT JOIN persons p USING(pid) "
                          "WHERE p.pid IS NULL").fetchone()[0]
    base_untouched = conn.execute(
        "SELECT COUNT(*), TOTAL(id * 7 + COALESCE(iv_candidate_id, 0) + LENGTH(pid)) FROM contests "
        "WHERE id <= ?", (base_max_id,)).fetchone()
    base_untouched = base_untouched[0] if tuple(base_untouched) == tuple(base_sig) else -1

    persons_same = "yes" if tuple(conn.execute(
        "SELECT COUNT(*), TOTAL(LENGTH(pid || canonical_name || identity_source || "
        "COALESCE(tcpd_pid, ''))) FROM persons WHERE pid IN (%s)" % ",".join("?" * len(base_pids)),
        sorted(base_pids)).fetchone()) == tuple(base_persons_sig) else "NO"
    methods_by_pid = defaultdict(set)
    for pid, r, tp, m in out:
        methods_by_pid[pid].add(m)
        methods_by_pid[("row", r["iv_id"])] = m
    n_a, n_b = write_sample(conn, args.out / "candidates-sample.md", methods_by_pid, base_pids)

    after_persons = conn.execute("SELECT COUNT(*) FROM persons").fetchone()[0]
    after_contests = conn.execute("SELECT COUNT(*) FROM contests").fetchone()[0]
    winners = conn.execute("SELECT COUNT(DISTINCT pid) FROM contests WHERE won=1").fetchone()[0]
    multi = conn.execute("SELECT COUNT(*) FROM (SELECT pid FROM contests GROUP BY pid "
                         "HAVING COUNT(*)>=2)").fetchone()[0]
    either = conn.execute("SELECT COUNT(*) FROM (SELECT pid FROM contests GROUP BY pid "
                          "HAVING COUNT(*)>=2 OR MAX(won)=1)").fetchone()[0]
    by_src = conn.execute("SELECT identity_source, COUNT(*) FROM persons GROUP BY 1 ORDER BY 1").fetchall()
    ind_attach = sum(1 for pid, r, tp, m in out if m == "name-attach" and r["party"] == "IND")
    splits = possible_splits(conn)
    runtime = time.time() - t0
    check = self_check(conn)
    conn.close()

    houses = {"ls": "Lok Sabha", "ac": "Assembly"}
    methods = ["tcpd-attach", "tcpd-mint", "name-attach", "name-mint"]
    L = ["# Candidate extension report", "",
         f"Base database: `{base}`. Output: `{dst}`. Runtime {runtime:.0f} s.",
         f"Pids start at n-{max(file_next, base_max + 1)}: person_pid_assignments.json says next_id "
         f"{file_next}, and the base database already uses pids up to n-{base_max}.", "",
         "## Counts", "",
         f"- Persons: {before_persons} before, {after_persons} after ({after_persons - before_persons} added).",
         f"- Contests: {before_contests} before, {after_contests} after ({after_contests - before_contests} added).",
         f"- Persons with at least one win: {winners}. Persons with 2+ contests: {multi}. "
         f"Persons with either: {either}.",
         "- Persons by identity_source: " + ", ".join(f"{s} {n}" for s, n in by_src) + ".", "",
         "Contests added, by house and method:", ""]
    for h in ("ls", "ac"):
        L.append(f"- {houses[h]}: " + ", ".join(f"{m} {stats[(h, m)]}" for m in methods)
                 + f" (of the name-mints, {stats[(h, 'name-ambiguous->mint')]} had 2+ qualifying persons).")
    L += ["", "## TCPD row matching", "",
          "Each IV candidacy looks up its TCPD seat by house, year, state and seat number, with the "
          "seat name as fallback, then picks the row with equal votes whose name agrees "
          "(votes+name). 'votes-only' is a unique equal vote count of 100 or more with a differently "
          "spelled name; 'name+position' is used when votes differ and the name is unique in the seat.", ""]
    for k, v in sorted(link_stats.items()):
        L.append(f"- {k}: {v}")
    L += ["", "## Candidacies skipped", ""]
    for k, v in skips.most_common():
        L.append(f"- {k}: {v}")
    L += [f"- Contests stored with tcpd_pid NULL because the schema's UNIQUE(tcpd_pid, year, state, "
          f"constituency, party_short) already held that key (two polls in one year): {nulled}.", "",
          "## TCPD pid conflicts", "",
          f"{len(conflicts_seen)} TCPD pids were not used because the base database is inconsistent "
          "about them, or the age guard failed. Their candidacies are skipped, not minted.", ""]
    for tp, why in sorted(conflicts_seen.items())[:10]:
        L.append(f"- {tp}: {why}")
    if len(conflicts_seen) > 10:
        L.append(f"- and {len(conflicts_seen) - 10} more (all in candidates-skipped.csv).")
    L += ["", "## Integrity checks (run on the output)", "",
          f"- IV candidate ids on more than one contest row: {dup_iv}.",
          f"- TCPD pids on more than one person row (all from the base database): {multi_tcpd_person}.",
          f"- Persons given two different TCPD pids by this run: {two_pids_new}.",
          f"- TCPD pids split across two persons by this run: {split_new}.",
          f"- Contest rows whose pid has no person row: {fk_bad}.",
          f"- Base contest rows unchanged (count and checksum): {base_untouched} of {before_contests} "
          "(-1 would mean a change).",
          f"- Base person rows unchanged (checksum over pid, name, source, tcpd_pid): {persons_same}.",
          f"- Sample written: {n_a} merge cases and {n_b} TCPD-minted persons in candidates-sample.md.", "",
          "## Possible splits left in place", "",
          f"The rules forbid merging two TCPD pids, so people whom TCPD gives two pids stay two persons. "
          f"Pairs of TCPD-anchored persons with the same name and state and a shared non-IND party: "
          f"{splits[0]} pairs where one person has only Lok Sabha contests and the other only assembly "
          f"contests (for example {', '.join(splits[2])}), and {splits[1]} further pairs that share a seat.",
          f"Name-attaches where the shared party is IND (independent), the weakest party evidence: {ind_attach}.", "",
          "## Self-check: long-career politicians", "",
          "A person is listed when their rare name tokens contain one spelling of the target's "
          "name; the top three by contest count are shown.", ""]
    L += check
    (args.out / "candidates-report.md").write_text("\n".join(L) + "\n")
    print("\n".join(L[:20]))
    return 0


if __name__ == "__main__":
    sys.exit(main())
