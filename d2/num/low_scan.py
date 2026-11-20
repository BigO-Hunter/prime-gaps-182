"""D2b: the 64 low rows + the 73 rank/high rows -- window coordinates, slope, tilt range.

Binary discipline: JSON parse only. Prints aggregates, not raw payload text.
"""
import json
from fractions import Fraction as Q
from pathlib import Path

BASE = Path.home() / "bigo-campaign/pg182-d1/frozen/extracted/prime-gaps-external-182/snapshot/prime_gaps_20260903/experiments"
LOW = {
    "g3g5g6": BASE / "variational_routes/fine_coarse_inner_low_v3_g3g5g6_n393216_b48.json",
    "g4": BASE / "tuple_geometry/fine393216_G4_low_v3.json",
    "c": BASE / "analytic_support/fine_C_low_v3_n393216.json",
}
HI = BASE / "analytic_support/fine_coarse_inner_sources_n393216.json"

ZETA = Q(1379373467, 1312494500)
HQ = ZETA / 393216
print(f"zeta={float(ZETA):.10f}  hq={float(HQ):.6e}")

# ---------- rank/high: source_mass == log(upper/lower)? ----------
import math
d = json.loads(HI.read_text())
n_ok = n_tot = 0
worst = 0.0
masses = []
for g in d["groups"]:
    for c in g["components"]:
        p = c["parameters"]
        if "q_low" not in p:
            continue
        lo, hi = Q(p["q_low"]), Q(p["q_high"])
        pred = math.log(float(hi) / float(lo))
        got = float(Q(c["source_mass"]["approximate_midpoint"]))
        rel = abs(pred - got) / max(got, 1e-300)
        worst = max(worst, rel)
        n_tot += 1
        n_ok += rel < 1e-12
        masses.append(got)
print(f"\n[RANK/HIGH] source_mass == log(q_high/q_low): {n_ok}/{n_tot} (worst rel err {worst:.2e})")
print(f"[RANK/HIGH] source_mass range: {min(masses):.6e} .. {max(masses):.6e}  "
      f"(spread {max(masses)/min(masses):.1f}x)  count={len(masses)}")

# per-group spread (the D2 '400x inside one group' claim)
for g in d["groups"]:
    ms = [float(Q(c["source_mass"]["approximate_midpoint"])) for c in g["components"]]
    print(f"  group {g['group']['id']}: n={len(ms)} span {min(ms):.3e}..{max(ms):.3e} = {max(ms)/min(ms):.1f}x")

# ---------- low rows: window coordinates ----------
print("\n[LOW] per-file aggregate")
tot_rows = 0
inside = 0
for tag, p in LOW.items():
    D = json.loads(p.read_text())
    rows = D["results"]
    tot_rows += len(rows)
    lo_all, hi_all, slopes, maxexp = [], [], [], -1e9
    for r in rows:
        ki = r["kernel_inputs"]
        lo_i, hi_i = int(ki["low_index"]), int(ki["high_index"])
        lo_all.append(lo_i * HQ)
        hi_all.append(hi_i * HQ)
        slopes.append(Q(r["parameters"].get("positive_tilt") or r["parameters"]["slope"]))
        for w in r["radial_windows"]:
            maxexp = max(maxexp, float(Q(w["exponent_upper"])))
    inside += sum(1 for h in hi_all if h <= ZETA)
    print(f"  {tag}: rows={len(rows)} slope={sorted(set(float(s) for s in slopes))[:3]}... "
          f"mass-window=[{float(min(lo_all)):.4e},{float(max(hi_all)):.4e}] "
          f"all<=zeta={all(h <= ZETA for h in hi_all)} max_exponent={maxexp:.4f}")
print(f"\n[LOW] total rows={tot_rows}; rows with high·hq <= zeta: {inside}/{tot_rows}")
