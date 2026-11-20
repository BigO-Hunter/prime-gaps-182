#!/usr/bin/env python3
"""truth.py — numerical ground truth for the pg182 D2 envelope lane.

Objects (all from the vendored Law.lean):
  zeta  = 1379373467/1312494500   (mean mass of the fragment law = top of intensity)
  mesh  = zeta/393216             (fine cell width)
  hq    = zeta/393216             (frozen uniform per-cell mass = mesh)

Fragment law: Poisson point process on (0,zeta] with intensity du/u; mass M = sum u_i.
  char fn  phi(t) = exp(-Cin(t*zeta) - i*Si(t*zeta))     [EXACT, elementary]
  Laplace  L(l)   = exp(-Ein(l*zeta))
  density  f(m)   = A on (0,zeta), A = P(M<zeta)/zeta     [delay identity: m f'(m) = -f(m-zeta)1_{m>zeta}]

Envelope classes measured:
  (D1)  Chernoff/Markov:  env = min_s exp(s*(n+1)*mesh - B(s))          [never < ~0.52]
  (D2F) delay-identity:   f <= 1/zeta on (0,zeta)  =>  P(cell) <= mesh/zeta
  (D2S) Esseen/Fejer with the EXACT char fn:  P(X in [a,a+h]) <= min_th [th h/(2(1-cos th))]
        * int_0^{2th/h} (1 - t/(2th/h)) |phi(t)|^d dt     (d = 1 fine, d = 38 sum)
"""
import math
from fractions import Fraction as F

Z = F(1379373467, 1312494500)
N = 393216
MESH = Z / N
Zf = float(Z); MESHf = float(MESH)
EULER = 0.5772156649015328606

def Cin(x):
    """int_0^x (1-cos v)/v dv  = gamma + log x - Ci(x), stable via series+asymptotic."""
    if x < 1e-8:
        return x * x / 4.0
    # series: Cin(x) = sum_{n>=1} (-1)^{n+1} x^{2n}/((2n)(2n)!)
    tot = 0.0
    term = x * x / 4.0
    n = 1
    while True:
        tot += term
        n += 1
        term = -term * x * x / ((2 * n) * (2 * n - 1))
        if abs(term) < 1e-18 * max(1.0, abs(tot)) or n > 200:
            break
    if abs(tot) < 1e15:
        return tot
    return tot

def Cin_big(x):
    """Cin for large x: gamma + log x - Ci(x); Ci(x) ~ sin x/x * (1/x series)."""
    if x < 30.0:
        return Cin(x)
    # Ci(x) = (sin x/x)(1 - 2!/x^2 + 4!/x^4 - ...) - (cos x/x^2)(1 - 3!/x^2 + ...)
    s, c = math.sin(x), math.cos(x)
    p = 0.0
    for n in range(12, 0, -1):
        p = (-1) ** n * p + ((2 * n)) # placeholder
    # do it properly with two asymptotic sums
    def ser(coef_start):
        acc, f_ = 0.0, 1.0
        k = 0
        while True:
            term = f_ / x ** (coef_start + 2 * k)
            acc += (-1) ** k * term
            if term < 1e-18:
                return acc
            f_ *= (coef_start + 2 * k + 1) * (coef_start + 2 * k + 2)
            k += 1
    Ci = s / x * ser(0) - c / (x * x) * ser(1)
    return EULER + math.log(x) - Ci

def absphi(t, d=1):
    """|phi(t)|^d = exp(-d*Cin(t*zeta))."""
    x = t * Zf
    return math.exp(-d * Cin(x))

def fejer_bound(h, d, return_parts=False):
    """P(X in [a,a+h]) <= min_{theta in (0,pi]} theta*h/(2(1-cos th)) * int_0^{T}(1-t/T)|phi(t)|^d dt,
    T = 2*theta/h. Returns the min over a theta grid (and the argmin)."""
    best = None
    for i in range(1, 400):
        th = math.pi * i / 400.0
        if th < 1e-3:
            continue
        T = 2.0 * th / h
        pref = th * h / (2.0 * (1.0 - math.cos(th)))
        # integrate (1 - t/T) exp(-d Cin(t zeta)) dt over [0,T]
        # substitute x = t*zeta -> (1/zeta) int_0^{T*zeta} (1 - x/(T zeta)) e^{-d Cin(x)} dx
        X = T * Zf
        # quadrature: the integrand decays like e^{-d gamma}/x^d for large x (d>=2 fast);
        # for d=1 use log-growth tail: integrate to X with substitution u = log(1+x)
        val = integrate_weighted(X, d)
        # the remaining tail beyond x=X: weight (1 - x/X) <= 1 (negative beyond X) -> drop
        v = pref * val / Zf
        if best is None or v < best[0]:
            best = (v, th, T)
    if return_parts:
        return best
    return best[0]

def integrate_weighted(X, d):
    """int_0^X (1 - x/X) e^{-d Cin(x)} dx  via nested Gauss on segments (x in half-logs)."""
    if X <= 0:
        return 0.0
    # break at doubling points so Cin's slow log growth is resolved
    pts = [0.0]
    x = 1e-6
    while x < X:
        pts.append(min(x, X))
        x *= 1.35
    if pts[-1] < X:
        pts.append(X)
    total = 0.0
    for a, b in zip(pts, pts[1:]):
        if b <= a:
            continue
        total += gauss(lambda x: (1.0 - x / X) * math.exp(-d * Cin_big(x)), a, b)
    return total

def gauss(f, a, b, n=64):
    """Composite Gauss-Legendre 12-point on [a,b], n panels."""
    gl_x = [-0.981560634246719, -0.904117256370475, -0.769902674194305,
            -0.587317954286617, -0.367831498998180, -0.125233408511469,
            0.125233408511469, 0.367831498998180, 0.587317954286617,
            0.769902674194305, 0.904117256370475, 0.981560634246719]
    gl_w = [0.047175336386512, 0.106939325995318, 0.160078328543346,
            0.203167426723066, 0.233492536538355, 0.249147045813403,
            0.249147045813403, 0.233492536538355, 0.203167426723066,
            0.160078328543346, 0.106939325995318, 0.047175336386512]
    tot = 0.0
    for i in range(n):
        lo = a + (b - a) * i / n
        hi = a + (b - a) * (i + 1) / n
        c = 0.5 * (lo + hi)
        r = 0.5 * (hi - lo)
        tot += r * sum(w * f(c + r * x) for x, w in zip(gl_x, gl_w))
    return tot

if __name__ == "__main__":
    print(f"zeta = {Zf:.10f}   mesh = {MESHf:.6e}   hq = mesh (F) {float(MESH):.6e}")
    print(f"1/zeta = {1/Zf:.10f}   e^-gamma/zeta = {math.exp(-EULER)/Zf:.10f}")
    print(f"e^-gamma = {math.exp(-EULER):.10f}")
    # ---- fine level, D2F envelope
    envF = MESHf / Zf
    print(f"\n[D2F] env_fine = mesh/zeta = {envF:.6e}  vs hq = {MESHf:.6e}  ratio {envF/MESHf:.6f}")
    print(f"      truth (A=1/zeta? or e^-gamma/zeta?) * mesh = {MESHf/Zf:.6e} .. {MESHf*math.exp(-EULER)/Zf:.6e}")
    # ---- fine level, D1 Chernoff at the window
    for n in (334254, 338000, 343201):
        m = (n + 1) * MESHf
        # B(s) = Ein(s*zeta); minimise s*m - B(s)
        def Ein(x):
            if x < 1e-10:
                return x
            return Cin(x) # wrong; Ein(x)=int_0^x (1-e^-v)/v ; use series
        def Ein_(x):
            tot, term = 0.0, 1.0
            k = 0
            # Ein(x) = sum_{n>=1} (-1)^{n+1} x^n/(n n!)
            n_ = 1
            while True:
                term = (-1) ** (n_ + 1) * x ** n_ / (n_ * math.factorial(n_))
                tot += term
                if abs(term) < 1e-20:
                    return tot
                n_ += 1
        best = min(((math.exp(s * m - Ein_(s * Zf)), s) for s in
                    [i / 2000 for i in range(1, 4000)]))
        print(f"[D1 ] n={n} m={m:.6f} chernoff_min={best[0]:.6f} (s*={best[1]:.5f}) vs need <=1")
    # ---- sum level
    h_run = 40 * MESHf
    for d in (1, 38):
        b_cell = fejer_bound(MESHf, d, return_parts=True)
        b_run = fejer_bound(h_run, d, return_parts=True)
        print(f"\n[D2S d={d}] cell bound {b_cell[0]:.6e} (theta*={b_cell[1]:.3f}) "
              f"= {b_cell[0]/MESHf:.6f} * mesh ; run(40 cells) {b_run[0]:.6e}"
              f" = {b_run[0]/MESHf:.4f} * mesh")
