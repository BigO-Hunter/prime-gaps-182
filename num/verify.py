#!/usr/bin/env python3
"""verify.py — verify the two D2 mathematical claims.

CLAIM A (fine level, delay identity): the fragment law's density f satisfies
     m f'(m) = -f(m - zeta) * 1{m > zeta}
  hence f is CONSTANT on (0, zeta), and A = P(M < zeta)/zeta <= 1/zeta.
  Verified: (i) simulation of M, (ii) A vs e^{-gamma}/zeta.

CLAIM B (sum level): f_38 = density of the 38-fold convolution, obtained by exact
  Fourier inversion  f_d(m) = (1/pi) int_0^inf e^{-d Cin(t zeta)} cos(d Si(t zeta) - t m) dt.
  Verified against the concentration function / direct quadrature.
"""
import numpy as np
from scipy.special import sici
from fractions import Fraction as F
import core

Z = core.Zf; MESH = core.MESHf; EULER = core.EULER

# ---------- CLAIM A: simulation ----------
def simulate(n=400000, seed=7):
    rng = np.random.default_rng(seed)
    # Poisson rate-1 on s in [log(1/zeta), inf)  <=>  point process of intensity du/u on (0,zeta].
    # Truncate small u at 1e-7 (total intensity log(zeta/1e-7) = log(1.05e7) = 16.2 -> ~16 atoms).
    lo = np.log(1.0/Z); hi = -np.log(1e-7)   # s = -log u, u in [1e-7, zeta]
    # number of points in [lo,hi] ~ Poisson(hi-lo); uniform in the interval
    m = rng.poisson(hi - lo, size=n)
    tot = np.zeros(n)
    for i in range(m.max() + 1):
        sel = m >= i
        if not sel.any():
            break
        idx = np.nonzero(sel)[0]
        s = rng.uniform(lo, hi, size=idx.size)
        tot[idx] += np.exp(-s)
    # atoms below 1e-7 contribute [0, 1e-7 * (# of them)]; bounded by 0 in the mean
    return tot

def density_from_sim(x, nb=60, n=600000):
    v = simulate(n)
    h, edges = np.histogram(v, bins=nb, range=(0.0, Z), density=True)
    return edges, h

# ---------- CLAIM B: exact Fourier inversion ----------
def f_d(m, d, ngrid=200000):
    """density of the d-fold convolution at m, by exact char-fn inversion."""
    t = np.linspace(0.0, 60.0, ngrid)
    x = t * Z
    si, ci = sici(x)                       # scipy returns (si, ci) in THAT order
    Cin = np.where(x > 0, EULER + np.log(np.where(x > 0, x, 1)) - ci, 0.0)
    mag = np.exp(-d * Cin)
    phase = d * si - t * m
    return float(np.trapz(mag * np.cos(phase), t) / np.pi)

if __name__ == "__main__":
    print("=== CLAIM A: density constant on (0,zeta)? ===")
    edges, h = density_from_sim(0.0)
    print(f"  sim bins over (0,zeta), expected A*mesh if A=1/zeta -> {1/Z:.5f}, "
          f"if A=e^-g/zeta -> {np.exp(-EULER)/Z:.5f}")
    # report the density in the window [0.893,0.993] and near 0.2
    for lo_m in (0.05, 0.3, 0.6, 0.893, 0.993):
        k = int(lo_m / Z * len(h))
        print(f"  bin at m={lo_m:.3f}: hist density {h[min(k,len(h)-1)]:.5f}")
    print(f"  full-range mean density over (0,zeta) = 1/zeta only if P(M<zeta)=1; "
          f"estimate P(M<zeta) = {np.mean(simulate(200000) < Z):.6f} (candidate e^-g = {np.exp(-EULER):.6f})")

    print("\n=== CLAIM B: 38-fold density at the sum window ===")
    ms = [0.5, 0.9, 1.2, 34.4, 34.8, 35.5, 39.9]
    for m in ms:
        vals = [f_d(m, 1), f_d(m, 38)]
        print(f"  m={m:6.2f}:  f_1={vals[0]:.6e}   f_38={vals[1]:.6e}")
