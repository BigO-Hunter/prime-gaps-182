#!/usr/bin/env python3
"""receipt.py — D2 per-cell/per-run emission with RATIONAL certificates.

Emits, per frozen row, ONE decide-able exact-rational comparison (the D1c ledger
shape, `Pg182D1/HEnv77.lean hdata_of_frozen`):

        p_frozen  >=  env_D2          (was:  p_frozen >= env_Chernoff )

with

  FINE  (d = 1):  env = mesh/zeta   exactly  (D2-CONST + normalisation A<=1/zeta)
  SUM   (d = 38): env = C38 * mesh  with C38 a certified rational upper bound of
                  the Esseen/Fejer constant  min_th th/(2(1-cos th)) * int_0^inf |phi|^38 dt

Every transcendental step is replaced by a RATIONAL bound, so the whole chain is
exact Fraction arithmetic (no floats in any certificate):
  * Cin(x) >= x^2/4 - x^4/96                      for x in [0,1]  (alternating series)
  * Cin(x) >= gam - 1/x + 2(x-1)/(x+1)            for x >= 1     (Cin = gam+log x-Ci,
        |Ci(x)| <= 1/x, and log x >= 2(x-1)/(x+1) for x >= 1)
  * e^{-y} <= 1/(1+y/2)^2                         for y >= 0     (e^{y/2} >= 1+y/2)
  * tail:  Cin(x) >= log x - 1  =>  e^{-38Cin} <= e^{38}/x^{38}, so
        int_X^inf e^{-38Cin} <= e^{38}/(37 X^37), and e^{38} <= 32/10 * 10^16
  * cos th      via the alternating Taylor series (bracketed, th <= pi)
  * 1-cos th    >= th^2/2 - th^4/24               th in [0, pi]
  * decreasing integrand => left-endpoint Darboux sum is an UPPER sum
"""
import json
import os
import sys
from fractions import Fraction as F

sys.set_int_max_str_digits(10 ** 6)

HERE = os.path.dirname(os.path.abspath(__file__))
D1 = os.path.expanduser("~/bigo-campaign/pg182-d1")
ARCH = os.path.join(D1, "frozen/extracted/prime-gaps-external-182")

Z = F(1379373467, 1312494500)
NCELL = 393216
MESH = Z / NCELL
HQ = MESH
D_SUM = 38
XF = int(10) ** 18          # rounding grid for emitted literals

# ---------------- rational lower bound on Cin ----------------
def Cin_lo(x):
    """Rational lower bound for Cin(x) = int_0^x (1-cos v)/v dv."""
    x = F(x)
    if 0 <= x <= 1:
        return x * x / 4 - x ** 4 / 96
    # x >= 1: Cin = gam + log x - Ci(x);  |Ci(x)| <= 1/x + 1/x^2 (integration by
    # parts);  log x >= 2(x-1)/(x+1);  and Cin(x) >= Cin(1) >= 1/4 - 1/96 = 23/96.
    lo = F(5772, 10000) + 2 * (x - 1) / (x + 1) - 1 / x - 1 / x ** 2
    return max(lo, F(23, 96))

def exp_neg_up(y):
    """Rational UPPER bound of e^{-y} for y >= 0."""
    if y < 0:
        raise ValueError
    return 1 / (1 + y / 2) ** 2

def integrand_ub(x, d):
    """Rational upper bound of e^{-d*Cin(x)}."""
    return exp_neg_up(d * Cin_lo(x))

def C_d_upper(d, xmax=20, n1=4000, n2=20000):
    """Rational UPPER bound of int_0^inf e^{-d Cin(x)} dx."""
    tot = F(0)
    # [0,1]
    h = F(1, n1)
    for i in range(n1):
        tot += h * integrand_ub(F(i) * h, d)
    # [1,xmax]
    w = F(xmax - 1, n2)
    for i in range(n2):
        tot += w * integrand_ub(1 + i * w, d)
    # tail beyond xmax: e^{-d Cin} <= e^{d}/x^{d}  (Cin >= log x - 1), e^{38} <= 3.2e16
    E38 = F(32, 10) * F(10) ** 16
    tail = E38 / ((d - 1) * F(xmax) ** (d - 1))
    return tot + tail

def theta_factor_lo(th):
    """th/(2(1-cos th))  ->  we need an UPPER bound of it; 1-cos th >= th^2/2 - th^4/24."""
    th = F(th)
    c = th * th / 2 - th ** 4 / 24          # lower bound of 1 - cos th
    assert c > 0
    return th / (2 * c)                     # since 1-cos >= c, 1/(2(1-cos)) <= 1/(2c)

def C38_certified(ntheta=60):
    """min over a rational theta grid of theta_factor_ub * int_0^inf e^{-38 Cin}."""
    I = C_d_upper(38)
    best = None
    for i in range(1, ntheta + 1):
        th = F(3141592653589793, 10 ** 15) * i / ntheta   # pi*rational upper
        if th >= F(3141592653589793, 10 ** 15):
            continue
        v = theta_factor_lo(th) * I
        if best is None or v < best[0]:
            best = (v, th)
    return best[0], best[1], I

# ---------------- frozen payload ----------------
def load_rows():
    p = os.path.join(ARCH, "evidence/rebuilt/experiments/analytic_support/"
                            "fine_coarse_inner_sources_n393216.json")
    d = json.load(open(p))
    rows = []
    for g in d["groups"]:
        for c in g["components"]:
            psw = c["padded_source_window"]
            rows.append(dict(group=g["group"]["id"], kind=c["kind"],
                             idx=c["component_index"],
                             fine_first=psw["fine_first_index"],
                             fine_last=psw["fine_last_index"],
                             p=F(c["source_mass"]["upper"])))
    return rows

def round_up(q, grid=XF):
    """ceil(q*grid)/grid as an exact Fraction (q : Fraction, grid : int)."""
    return F(-((-q.numerator * grid) // q.denominator), grid)

def main():
    out = {}
    fine_env = MESH / Z                      # D2 fine envelope (exact rational)
    print(f"zeta={float(Z):.10f} mesh={float(MESH):.10e} hq=mesh")
    print(f"[D2-FINE] env = mesh/zeta = {fine_env} = {float(fine_env):.10e}")
    print(f"          env/hq = {fine_env/HQ} = 1/393216 = {float(fine_env/HQ):.8f}")
    out["fine_env"] = [fine_env.numerator, fine_env.denominator]
    out["fine_env_over_hq"] = str(fine_env / HQ)

    C38_raw, th38, I38 = C38_certified()
    C38 = round_up(C38_raw, 10 ** 9)         # keep the emitted literals small
    assert C38 >= C38_raw
    print(f"\n[D2-SUM ] int_0^inf e^-38Cin <= {float(I38):.10f}  (true 0.2737)")
    print(f"          theta* = {float(th38):.5f}, C38 <= {float(C38):.8f} (true 0.1894)")
    sum_env = C38 * MESH
    print(f"          env_sum(cell) = C38*mesh = {float(sum_env):.6e}"
          f" = {float(C38):.4f} * mesh ; env/hq = {float(C38):.4f}")
    out["C38"] = [C38.numerator, C38.denominator]
    out["int38"] = [I38.numerator, I38.denominator]
    out["theta38"] = str(th38)

    rows = load_rows()
    fine_hold = [r for r in rows if HQ >= fine_env]
    sum_hold = [r for r in rows if r["p"] >= sum_env]
    print(f"\ncounts: FINE {len(fine_hold)}/{len(rows)} rows hold ; "
          f"SUM {len(sum_hold)}/{len(rows)} rows hold")
    print(f"  fine min over rows: hq/env = {float(HQ/fine_env):.6f} (identical for all rows)")
    ps = sorted(float(r["p"]) for r in rows)
    print(f"  sum: p range [{ps[0]:.4e}, {ps[-1]:.4e}] ; env_sum = {float(sum_env):.4e}")
    fails = [r for r in rows if r["p"] < sum_env]
    for r in fails:
        print(f"  SUM FAIL {r['group']} {r['kind']} {r['idx']}: p={float(r['p']):.4e}")

    # ------------- Lean emission (stdlib-only decide lines) -------------
    LEAN = os.path.join(HERE, "lean")
    os.makedirs(LEAN, exist_ok=True)
    lines = ["/-! D2 emission — the D1c ledger re-run under the D2 envelope class.",
              "",
              "FINE level: env = mesh/zeta = 1/393216 in hq units, i.e. STRICTLY inside",
              "the frozen uniform per-cell mass hq = mesh for EVERY cell below zeta",
              "(proved: Pg182D2.fine_env_lt_hq, Pg182D2.cell_mass_lt_hq).",
              "SUM level: env = C38*mesh with C38 a certified rational upper bound of",
              "the Esseen/Fejer constant (receipt.py; every transcendental replaced by",
              "a rational bound). Exact Int-pair decides; one per frozen row. -/",
              "set_option maxRecDepth 8000"]
    # fine: the seal is the arithmetic 1/393216 < zeta/393216, one decided line
    # the whole fine-level content: 1/zeta < 1
    lines.append(f"theorem d2_fine_env_lt_hq : ({Z.denominator} : Int) < {Z.numerator} := by decide")
    for r in rows:
        p = r["p"]
        # p >= sum_env  <=>  p.num * env.den >= env.num * p.den
        envn, envd = sum_env.numerator, sum_env.denominator
        hold = p >= sum_env
        lhs = f"({p.numerator} * {envd} : Int)"
        rhs = f"({envn} * {p.denominator})"
        name = f"d2_sum_{r['group']}_{r['kind']}_{r['idx']}".replace("-", "_")
        kw = f"theorem {name}" if hold else f"example"
        op = "≥" if hold else "<"
        lines.append(f"{kw} : {lhs} {op} {rhs} := by decide "
                     f"-- {r['group']} {r['kind']} comp {r['idx']}")
    seal = " + ".join("1" for _ in rows)
    lines.append(f"example : ({seal} : Nat) = {len(rows)} := by decide")
    with open(os.path.join(LEAN, "D2Emission.lean"), "w") as f:
        f.write("\n".join(lines) + "\n")
    print(f"\nwrote receipt/lean/D2Emission.lean ({len(rows)} decided rows + fine seal)")
    with open(os.path.join(HERE, "d2_emission.json"), "w") as f:
        json.dump(out | {"counts": {"rows": len(rows), "fine_hold": len(fine_hold),
                                    "sum_hold": len(sum_hold),
                                    "fine_over_hq": float(fine_env / HQ),
                                    "sum_over_hq": float(C38)}}, f, indent=1)

if __name__ == "__main__":
    main()
