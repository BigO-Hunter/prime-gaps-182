#!/usr/bin/env python3
"""core.py — exact-char-fn numerics for the D2 lane (vectorised, fast).

phi(t) = exp(-Cin(t zeta) - i Si(t zeta))   EXACT for the fragment law
|phi(t)|^d = exp(-d Cin(t zeta)),  Cin(x) = gamma + log x - Ci(x)
Laplace:  E[e^{-l M}] = exp(-Ein(l zeta)),  Ein(x) = gamma + log x + E1(x)
"""
import numpy as np
from scipy.special import sici, exp1
from fractions import Fraction as F

Z = F(1379373467, 1312494500)
NCELL = 393216
MESH = Z / NCELL
Zf = float(Z)
MESHf = float(MESH)
EULER = 0.5772156649015328606

def Cin(x):
    x = np.asarray(x, dtype=float)
    _, ci = sici(x)
    with np.errstate(divide="ignore", invalid="ignore"):
        out = EULER + np.log(np.where(x > 0, x, 1.0)) - ci
    return np.where(x > 0, out, 0.0)

def Ein(x):
    x = np.asarray(x, dtype=float)
    with np.errstate(divide="ignore", invalid="ignore"):
        out = EULER + np.log(np.where(x > 0, x, 1.0)) + exp1(np.where(x > 0, x, 1.0))
    return np.where(x > 0, out, 0.0)

def absphi(t, d=1):
    return np.exp(-d * Cin(np.asarray(t, float) * Zf))

# ---------------- precomputed cumulative integrals on a log grid ----------------
_GRID = None
def _grid(d, xmax):
    """cumulative I(X)=int_0^X g, J(X)=int_0^X x g, g(x)=e^{-d Cin(x)}, on log grid."""
    global _GRID
    key = (d, xmax)
    if _GRID is not None and _GRID[0] == key:
        return _GRID[1]
    lo = np.log(1e-10); hi = np.log(xmax)
    xs = np.exp(np.linspace(lo, hi, 60000))
    g = np.exp(-d * Cin(xs))
    dx = np.diff(xs)
    I = np.concatenate([[0.0], np.cumsum(0.5 * (g[1:] + g[:-1]) * dx)])
    J = np.concatenate([[0.0], np.cumsum(0.5 * (xs[1:] * g[1:] + xs[:-1] * g[:-1]) * dx)])
    _GRID = (key, (xs, I, J))
    return _GRID[1]

def weighted_int(X, d):
    """int_0^X (1-x/X) e^{-d Cin(x)} dx = I(X) - J(X)/X."""
    xmax = max(X * 1.001, 10.0)
    xs, I, J = _grid(d, xmax)
    if X >= xs[-1]:
        raise ValueError("X beyond grid")
    iX = float(np.interp(X, xs, I)); jX = float(np.interp(X, xs, J))
    return iX - jX / X

def fejer_bound(h, d, ntheta=2000):
    """P(X in [a,a+h]) <= min_{th} th*h/(2(1-cos th)) * int_0^{T}(1-t/T)|phi(t)|^d dt,
       T = 2 th / h  (dt = dx/zeta).  Returns (value, th*, T*)."""
    th = np.pi * np.arange(1, ntheta + 1) / ntheta
    th = th[th > 1e-3]
    X = 2.0 * th * Zf / h          # = T*zeta
    pref = th * h / (2.0 * (1.0 - np.cos(th)))
    vals = np.array([weighted_int(x, d) / Zf for x in X])
    v = pref * vals
    k = int(np.argmin(v))
    return float(v[k]), float(th[k]), float(2 * th[k] / h)

if __name__ == "__main__":
    print(f"zeta={Zf:.10f}  mesh={MESHf:.8e}  1/zeta={1/Zf:.10f}  e^-g/zeta={np.exp(-EULER)/Zf:.10f}")
    print(f"Cin(1)={float(Cin(1.0)):.10f}  Ein(1)={float(Ein(1.0)):.10f} (expect 0.7965995993)")
    print("\n--- D1 Chernoff at the row-77 window (cross-check vs D1c: 0.9772) ---")
    ss = np.linspace(1e-4, 2.0, 20000)
    for n in (334254, 343201):
        m = (n + 1) * MESHf
        vals = np.exp(ss * m - Ein(ss * Zf))
        k = int(np.argmin(vals))
        print(f"  n={n} m={m:.6f}  chernoff_min={vals[k]:.6f} (s*={ss[k]:.5f})")
    print("\n--- D2S: Esseen/Fejer with exact |phi|^d ---")
    for d in (1, 38):
        for h, tag in ((MESHf, "cell"), (40 * MESHf, "run40")):
            b, th, T = fejer_bound(h, d)
            print(f"  d={d:2d} h={tag:6s}  bound={b:.6e} = {b/MESHf:11.6f} mesh  (th*={th:.4f})")
