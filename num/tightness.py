#!/usr/bin/env python3
"""tightness.py — the measured tightness table for TIGHTNESS.md."""
import numpy as np
from scipy.special import sici
from fractions import Fraction as F
import core, verify

Z, MESH, G = core.Zf, core.MESHf, core.EULER
EULER = G
A_true = np.exp(-EULER) / Z            # exact density on (0, zeta)
A_norm = 1.0 / Z                       # the provable bound A <= 1/zeta
hq = MESH

def f38(m):
    return verify.f_d(m, 38)

print("=== 1. the truth at the windows ===")
print(f"  f_1 on (0,zeta) = {A_true:.6f}   [= e^-gamma/zeta; bound 1/zeta = {A_norm:.6f}]")
print(f"  check by inversion: f_1(0.5)={verify.f_d(0.5,1):.6f} f_1(0.9)={verify.f_d(0.9,1):.6f} "
      f"f_1(1.2)={verify.f_d(1.2,1):.6f}  (constant to 1.2, then drops)")
for m in (34.4, 34.8, 35.5):
    print(f"  f_38({m}) = {f38(m):.6f}   (row-77 sum window is m in [33.95, 34.87])")

print("\n=== 2. envelope classes at the windows (units of hq = mesh) ===")
rows = []
def rec(name, env_over_hq, note=""):
    rows.append((name, env_over_hq, note))
    print(f"  {name:34s} {env_over_hq:12.6f} hq   {note}")

# (a) D1 Chernoff, fine
best = min((np.exp(s * (334255 * MESH) - core.Ein(s * Z)), s)
           for s in np.linspace(1e-4, 2, 40000))
rec("D1 Chernoff fine (cell 334254)", best[0] / hq, "D1c: 0.977 -> VOID (no mesh factor)")
# (b) D1 Chernoff, sum
best38 = min((np.exp(s * (38 * 343201 * MESH) - 38 * core.Ein(s * Z)), s)
             for s in np.linspace(1e-4, 4, 40000))
rec("D1 Chernoff sum  (c=38*fine_last)", best38[0] / hq, "D1c: 0.52 -> VOID")
# (c) D2 route 1: delay identity, fine
rec("D2-R1 fine  (delay identity)", (MESH / Z) / hq, "PROVED; truth ratio 1.781 = e^gamma")
# (d) D2 route 4: Fejer with exact |phi|^d, sum
b38, th38, _ = core.fejer_bound(MESH, 38)
rec("D2-R4 sum   (Fejer, exact |phi|^38)", b38 / hq, f"theta*={th38:.3f}; vs truth f_38={f38(34.8):.4f}")
# (e) rational certificate
rec("D2-R4 sum   (rational certificate)", 0.29586259, "receipt.py: all-transcendental-free")
# (f) the vacuous d=1 Fejer (the log-divergence wall)
b1, th1, _ = core.fejer_bound(MESH, 1)
rec("D2-R4 fine  (Fejer, |phi|^1)", b1 / hq, f"LOG-DIVERGENT: {b1/hq:.2f}x truth -> cannot reach hq")

print("\n=== 3. margin vs the frozen p (D1c ledger) ===")
print(f"  fine: need env <= hq ; have env = {MESH/Z/hq:.6f} hq -> margin {hq/(MESH/Z):.4f}x")
print(f"  sum : need env <= p/mesh ; smallest frozen p = 2.8224e-05 = {2.8224e-05/MESH:.2f} hq")
print(f"        have env = 0.2959 hq -> margin {2.8224e-05/(0.29586259*MESH):.1f}x")
print("\n=== 4. the wide-window reading (the caveat) ===")
print(f"  row-77 window at the sum level spans mass [33.95, 34.87] (width 0.917);")
print(f"  true P = {0.917*f38(34.8):.5f}  vs frozen source_mass 0.0308 (G3 comp0) / 7.9e-05 (comp13)")
print("  => the two components of ONE group claim window masses 400x apart, so the")
print("     frozen per-row value is NOT a window probability; a density bound of the")
print("     whole-window kind is not the right object there (caveat, not a D2 failure).")
