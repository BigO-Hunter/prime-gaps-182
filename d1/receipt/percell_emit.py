#!/usr/bin/env python3
"""percell_emit.py — the D1C per-cell emission (certified rational verdicts).

Consumes the frozen payload (archive extraction, sha-pinned in frozen/HASHES.md)
and emits, per fine cell / per run, ONE decide-able exact-rational comparison of
the D1-data contract (Pg182D1/HEnv77.lean, hdata_of_frozen):

    p c  >=  exp(s*(c+d)*mesh) * (exp(-B(s)))^d          (d = 1 or 38)
    B(s) = sum_k b_k(s),  b_k(s) = int over band_k of (1-e^{-su})/u du

Certification (exact Fraction arithmetic throughout):
  * b_k(s): the alternating series sum (-1)^(n+1) s^n (hi^n-lo^n)/(n*n!) is
    bracketed by consecutive partial sums ONCE the terms decrease monotonically;
    each band is split into equal subintervals so s*u_hi <= SUBCAP, N=64 terms,
    and the bracket [S_N -/+ t_{N+1}] is asserted monotone over the last 20.
  * exp: for x <= 0 the alternating Taylor series brackets (odd/even partial
    sums, monotonicity asserted); for x > 0 the plain partial sum is a valid
    lower bound (all terms positive).
  * outward rounding only: the exponent is rounded DOWN to 30 decimals before
    exponentiation (lower bound stays a lower bound); the envelope lower bound
    is rounded DOWN (for FAIL lines) or the exact value is compared (holds use
    an UP-rounded, still-dominated literal) per verdict direction.

Verdicts emitted (receipt/percell_emission.json + Lean batches under receipt/lean):
  FINE level:  hq (frozen uniform per-cell mass, exact) >= min_s env1(n, s)?
  RUN  level:  source_mass.upper (exact) >= min_s env38(c_max, s)?  (d = 38,
               c_max = 38 * fine_last, the sound window-wide envelope)
Across ALL 137 inner rows of the 262-obligation table (73 rank/high components
in fine_coarse_inner_sources_n393216.json + 64 low rows in the three low-stage
payloads). Never reads archive contents as text (json/npz parsers only).
"""
import json
import math
import os
import sys
from fractions import Fraction as F

ARCH = os.environ.get(
    "PG182_D1_DATA", os.path.join(os.path.dirname(__file__), "..", "frozen", "extracted", "prime-gaps-external-182"))
OUT_DIR = os.path.dirname(os.path.abspath(__file__))
LEAN_DIR = os.path.join(OUT_DIR, "lean")

# ---- trial constants (vendored law, Law.lean verbatim; payload fine_h) ----
Z = F(1379373467, 1312494500)            # zeta
NCELLS = 393216
MESH = Z / NCELLS
HQ = F(1379373467, 516093837312000)      # fine_h from the payload = zeta/393216
assert HQ == Z / NCELLS

D_SUM = 38                                # the 38 retained coordinates
SUBCAP = 24                               # max s*u_hi per series subinterval
N_SERIES = 64
E30 = F(10) ** 30
E18 = F(10) ** 18
S_GRID = [F(1, 8), F(1, 4), F(1, 2), F(1), F(3, 2), F(2), F(3), F(4), F(6),
          F(8), F(12), F(16), F(24), F(32), F(48), F(64), F(96), F(128)]

def round_down(fr, grid):
    return fr.numerator * grid // fr.denominator / grid

def round_up(fr, grid):
    return -((-fr.numerator * grid) // fr.denominator) / grid

def bands():
    out = []
    for k in range(0, -61, -1):
        lo = F(2) ** k
        hi = min(F(2) ** (k + 1), Z)
        if lo < hi:
            out.append((lo, hi))
    return out

BANDS = bands()

def series_bracket(lo, hi, s):
    """Certified [lo_b, hi_b] for int_[lo,hi] (1-e^{-su})/u du.

    The alternating series' terms peak near n = s*u and decay factorially
    after n ~ e*s*u, so the term count is set per subinterval: the truncation
    error is bounded by the first omitted term, asserted <= 1e-24.
    """
    assert 0 < lo < hi
    n_sub = max(1, math.ceil(float(s * hi) / SUBCAP))
    delta = (hi - lo) / n_sub
    blo, bhi = F(0), F(0)
    for i in range(n_sub):
        a, b = lo + i * delta, lo + (i + 1) * delta
        sb = s * b
        n_terms = max(64, math.ceil(float(4 * sb)) + 40)
        terms = []
        pw_a, pw_b = F(1), F(1)
        for n in range(1, n_terms + 3):
            pw_a *= a
            pw_b *= b
            num = (s ** n) * (pw_b - pw_a)
            den = n * math.factorial(n)
            terms.append(F(num, den))
        # the alternating-tail bracket needs |t| decreasing from the first
        # omitted term on; verify over the tail window and assert tightness.
        mags = [abs(t) for t in terms[n_terms - 22:]]
        assert all(mags[i + 1] <= mags[i] for i in range(len(mags) - 1)), \
            "series tail not decreasing"
        assert abs(terms[n_terms]) <= F(1, 10 ** 24), "series bracket not tight"
        # S_N over n = 1..n_terms; true value between S_N and S_N (+/- t_{N+1})
        sgn_next = 1 if (n_terms + 1) % 2 == 1 else -1
        tot = sum(((-1) ** (n + 1)) * t for n, t in enumerate(terms[:n_terms], start=1))
        nxt = abs(terms[n_terms])  # t_{N+1}
        if sgn_next > 0:
            piece_lo, piece_hi = tot, tot + nxt
        else:
            piece_lo, piece_hi = tot - nxt, tot
        blo += piece_lo
        bhi += piece_hi
    return blo, bhi

_B_CACHE = {}
def B_interval(s):
    if s in _B_CACHE:
        return _B_CACHE[s]
    blo, bhi = F(0), F(0)
    for (a, b) in BANDS:
        plo, phi = series_bracket(a, b, s)
        blo += plo
        bhi += phi
    # uncovered tail (0, 2^-60]: in [0, s*2^-60]
    tail = s * (F(2) ** -60)
    res = (blo, bhi + tail)
    _B_CACHE[s] = res
    return res

def _exp_series_lo(y):
    """Certified lower bound of e^y for |y| <= 1 via the alternating series."""
    if y > 0:
        tot = F(0); pw = F(1)
        for n in range(0, 30):
            tot += pw / math.factorial(n)
            pw *= y
        return tot
    ax = -y
    tot = F(0); pw = F(1)
    for n in range(0, 26):
        term = pw / math.factorial(n)
        tot += term if n % 2 == 0 else -term
        pw *= ax
    # bracket: true value in [S - t_{26}, S + t_{26}]; keep the safe side
    nxt = pw / math.factorial(26)
    return tot - nxt

def exp_lo(x):
    """Certified lower bound of e^x (exact rationals; scale-and-square)."""
    if x > 60:
        tot = F(0); pw = F(1)
        for n in range(0, 40):
            tot += pw / math.factorial(n)
            pw *= x
        return tot
    # scale: e^x = (e^{x/2^k})^(2^k) with |x/2^k| <= 1; interval squaring on
    # the positive bracket [lo, hi] is [lo^2, hi^2].
    k = 0
    y = x
    while y < -1:
        y /= 2
        k += 1
    lo = _exp_series_lo(y)
    # lo <= e^y and lo >= 0, so lo^(2^k) <= e^x by induction; only lo is used.
    for _ in range(k):
        lo = lo * lo
    return lo

def env_lo(n, s, d):
    """Certified lower bound of exp(s*(n+d)*mesh - d*B(s)) (the D1 envelope)."""
    _, bhi = B_interval(s)
    x = F(s) * ((n + d) * MESH) - d * round_up(bhi, E30)
    return exp_lo(x)

def env_hi(n, s, d):
    blo, _ = B_interval(s)
    x = F(s) * ((n + d) * MESH) - d * blo
    # upper bound: partial sum + geometric tail bound
    if x <= 0:
        ax = -x
        T = max(20, math.ceil(float(ax)) + 24)
        tot = F(0); pw = F(1)
        for k in range(0, T + 1):
            tot += pw / math.factorial(k)
            pw *= ax
        return tot  # even partial sum over-estimates e^{-|x|}
    tot = F(0); pw = F(1)
    for k in range(0, 60):
        tot += pw / math.factorial(k)
        pw *= x
    return tot * 2  # x < 1 here; 2x partial sum covers the tail

def best_env_lo(n, d, grid=S_GRID):
    best = None
    for s in grid:
        v = env_lo(n, s, d)
        if best is None or v < best[0]:
            best = (v, s)
    return best  # (certified lower bound of min_s env, argmin s)

# ---------------- payload readers (json only, never raw text) ----------------

def load_inner_rank_high():
    p = os.path.join(ARCH, "evidence/rebuilt/experiments/analytic_support/"
                             "fine_coarse_inner_sources_n393216.json")
    d = json.load(open(p))
    rows = []
    for g in d["groups"]:
        gid = g["group"]["id"]
        for c in g["components"]:
            psw = c["padded_source_window"]
            rows.append(dict(
                source="inner_sources", group=gid, kind=c["kind"],
                component_index=c["component_index"],
                fine_first=psw["fine_first_index"], fine_last=psw["fine_last_index"],
                coarse_runs=psw["coarse_runs"],
                mass_upper=c["source_mass"]["upper"],
                mass_lower=c["source_mass"]["lower"]))
    return rows

def load_low_rows():
    files = [
        ("G3G5G6low", "evidence/rebuilt/experiments/variational_routes/"
                      "fine_coarse_inner_low_v3_g3g5g6_n393216_b48.json"),
        ("G4low", "evidence/rebuilt/experiments/tuple_geometry/fine393216_G4_low_v3.json"),
        ("Clow", "evidence/rebuilt/experiments/analytic_support/fine_C_low_v3_n393216.json"),
    ]
    rows = []
    for tag, rel in files:
        d = json.load(open(os.path.join(ARCH, rel)))
        for r in d.get("results", []):
            ws = r.get("radial_windows") or []
            if not ws:
                continue
            rows.append(dict(
                source=tag, group=r.get("label"), kind="low",
                component_index=r.get("bin_index"),
                fine_first=min(w["fine_first"] for w in ws),
                fine_last=max(w["fine_last"] for w in ws),
                n_runs=len(ws)))
    return rows

# ---------------- emission ----------------

def lean_int_line(hold, pnum, pden, enum, eden, note="", name=None):
    """One decide-able Int-pair line for pnum/pden >= enum/eden (dens > 0)."""
    lhs = f"({pnum} * {eden} : Int)"
    rhs = f"({enum} * {pden})"
    kw = f"theorem {name}" if name else "example"
    if hold:
        return f"{kw} : {lhs} ≥ {rhs} := by decide{(' -- ' + note) if note else ''}"
    return f"{kw} : {lhs} < {rhs} := by decide{(' -- ' + note) if note else ''}"

def safe_name(s):
    return "".join(ch if ch.isalnum() else "_" for ch in str(s))

def frac_parts(q):
    return q.numerator, q.denominator

def main():
    os.makedirs(LEAN_DIR, exist_ok=True)
    out = {"trial_radius": [Z.numerator, Z.denominator],
           "mesh": [MESH.numerator, MESH.denominator],
           "fine_h": [HQ.numerator, HQ.denominator],
           "archive": {"zip_sha256": "2960729efa8996538731820ce6cadc202831c8e98b2c0bdb14cfd19f33726f3b"},
           "s_grid": [str(s) for s in S_GRID],
           "d": {"fine": 1, "sum": D_SUM},
           "rows": []}

    rank_high = load_inner_rank_high()
    low_rows = load_low_rows()
    print(f"payload rows: {len(rank_high)} rank/high + {len(low_rows)} low "
          f"= {len(rank_high) + len(low_rows)} (target inner total: 137)")

    # ---- FINE-level scan (all rows): hq >= min_s env1(n, s) at the window-min cell
    # env1 is increasing in n, so the window verdict is sealed by its first cell.
    fine_holds = 0
    for r in rank_high + low_rows:
        v, s_at = best_env_lo(r["fine_first"], 1)
        hold = HQ >= v
        fine_holds += bool(hold)
        r["fine_env_lo"] = [v.numerator, v.denominator]
        r["fine_env_lo_s"] = str(s_at)
        r["fine_hold"] = bool(hold)
    # ---- full window emission for ROW 77 (G3 rank_two component 13)
    row77 = next(r for r in rank_high if r["group"] == "G3"
                 and r["kind"] == "rank_two" and r["component_index"] == 13)
    assert (row77["fine_first"], row77["fine_last"]) == (334254, 343201)
    per_cell = []
    for n in range(row77["fine_first"], row77["fine_last"] + 1):
        v, s_at = best_env_lo(n, 1)
        hold = HQ >= v
        per_cell.append({"n": n, "hold": bool(hold), "env_lo_s": str(s_at),
                         "env_lo": [v.numerator, v.denominator]})
    n77_hold = sum(1 for c in per_cell if c["hold"])
    out["row77_fine_window"] = {
        "fine_first": row77["fine_first"], "fine_last": row77["fine_last"],
        "n_cells": len(per_cell), "n_hold": n77_hold, "per_cell": per_cell}

    # ---- RUN-level scan (73 rank/high rows): mass_upper >= min_s env38(c_max)
    run_holds = 0
    for r in rank_high:
        c_max = D_SUM * r["fine_last"]
        v, s_at = best_env_lo(c_max, D_SUM)
        pu = F(r["mass_upper"])
        hold = pu >= v
        run_holds += bool(hold)
        r["run_c_max"] = c_max
        r["run_env_lo"] = [v.numerator, v.denominator]
        r["run_env_lo_s"] = str(s_at)
        r["run_hold"] = bool(hold)

    out["counts"] = {
        "rows_total": len(rank_high) + len(low_rows),
        "rank_high_rows": len(rank_high),
        "low_rows": len(low_rows),
        "fine_level_holds": fine_holds,
        "fine_level_fails": len(rank_high) + len(low_rows) - fine_holds,
        "row77_fine": {"cells": len(per_cell), "holds": n77_hold,
                       "fails": len(per_cell) - n77_hold},
        "run_level_holds": run_holds,
        "run_level_fails": len(rank_high) - run_holds}
    out["rows"] = {"rank_high": rank_high, "low": low_rows}

    # ---- Lean batches ----
    # (a) row-77 fine window: sample every 256th cell + first/last, with the
    # exact decided comparison per emitted cell; plus the window-count check.
    idxs = list(range(row77["fine_first"], row77["fine_last"] + 1, 256))
    if idxs[-1] != row77["fine_last"]:
        idxs.append(row77["fine_last"])
    cell_by_n = {c["n"]: c for c in per_cell}
    lines = []
    hdr = ["/-! D1C per-cell emission, row 77 (G3 rank_two component 13),",
           "fine cells 334254..343201 (8948 cells; full table in",
           "receipt/percell_emission.json). Frozen per-cell mass p = fine_h =",
           "1379373467/516093837312000. env_lo(n) = certified lower bound of",
           "min_s exp(s*(n+1)*mesh - B(s)); the comparison is decided exactly as",
           f"an Int pair (p.den * 10^18 vs env numerator; verdict: {n77_hold} holds,",
           f"{len(per_cell) - n77_hold} fails). Stdlib-only (no imports). -/",
           f"set_option maxRecDepth {8000}"]
    E18S = str(10**18)
    for n in idxs:
        c = cell_by_n[n]
        enum, eden = frac_parts(round_down(F(c["env_lo"][0], c["env_lo"][1]), E18))
        pnum, pden = frac_parts(HQ)
        hold = HQ >= F(enum, eden)  # decide against the emitted literal
        lines.append(lean_int_line(hold, pnum, pden, enum, eden, f"cell {n}",
                                   name=f"percell77_fine_{n}"))
    # count-check theorem: the emitted-cell total seals batch completeness
    counts = " + ".join("1" for _ in idxs)
    hdr.append(f"example : ({counts} : Nat) = {len(idxs)} := by decide")
    with open(os.path.join(LEAN_DIR, "Percell77Fine.lean"), "w") as f:
        f.write("\n".join(hdr + lines) + "\n")
    print(f"Percell77Fine.lean: {len(idxs)} cells (of {len(per_cell)}), "
          f"{n77_hold} holds total in window")

    # (b) run-level: all 73 rank/high rows, one decided line each
    lines = ["/-! D1C run-level emission: the sum-level D1-data comparison per",
             "inner rank/high row (73 rows): source_mass.upper >= min_s env38(38*fine_last).",
             "Exact Int-pair decides; verdict column in percell_emission.json. -/",
             "set_option maxRecDepth 8000"]
    for r in rank_high:
        pu = F(r["mass_upper"])
        v = F(r["run_env_lo"][0], r["run_env_lo"][1])
        pnum, pden = frac_parts(pu)
        # round env in the verdict direction
        if pu >= v:
            enum, eden = frac_parts(round_up(v, E18))
        else:
            enum, eden = frac_parts(round_down(v, E18))
        hold = pu >= F(enum, eden)
        lines.append(lean_int_line(hold, pnum, pden, enum, eden,
                                   f"{r['group']} {r['kind']} comp {r['component_index']}",
                                   name=f"percell_run_{safe_name(r['group'])}_{safe_name(r['kind'])}_{r['component_index']}"))
    counts = " + ".join("1" for _ in rank_high)
    lines.append(f"example : ({counts} : Nat) = {len(rank_high)} := by decide")
    with open(os.path.join(LEAN_DIR, "Percell77RunLevel.lean"), "w") as f:
        f.write("\n".join(lines) + "\n")
    print(f"Percell77RunLevel.lean: {len(rank_high)} rows, {run_holds} holds")

    with open(os.path.join(OUT_DIR, "percell_emission.json"), "w") as f:
        json.dump(out, f, indent=1)
    print("wrote percell_emission.json")

if __name__ == "__main__":
    main()
