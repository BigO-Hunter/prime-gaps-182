> Umbrella note (2026-11-20): this package now builds from `d2/` inside `prime-gaps-182`; frame and D1 dependencies are `../` and `../d1`. Any older absolute-path caveat describes the pre-consolidation checkout, not this umbrella.

# ROUTE2.md — ranking the four envelope classes by closability

Lane D2, work dir `~/bigo-campaign/pg182-d2/` (project `pg182-d2`, toolchain
v4.34.1 + campaign Mathlib symlinked from `staircase-port`, never rebuilt).

The question: D1's per-cell majorant

    mu {cell = n}  <=  exp (s*(n+1)*mesh) * E[e^{-s*mass}]                (D1-CELL)

is *true* but has the wrong SCALE. Its right-hand side is a dimensionless number
of order 1 (measured: 0.9772 at the row-77 window, 0.52 at the sum level), while
the quantity being bounded is a cell mass of order `mesh = 2.6727e-6`. The gap is
the missing density factor `mesh * f`, and no choice of `s`, no product over
bands, and no refinement of `B(s)` can recover it: the Chernoff/Markov step
divides by `inf_{cell} e^{-s*mass} ~ e^{-s*m}`, and on a cell the integrand is
essentially constant, so the bound can never see the cell's *width*.

Measured in hq units (hq = mesh = the frozen uniform per-cell mass):

| envelope | value | verdict |
|---|---|---|
| D1 Chernoff, fine (cell 334254) | 0.9772 = **365 227 hq** | void by 3.7e5 |
| D1 Chernoff, sum (c = 38*fine_last) | 0.52 = **194 820 hq** | void by 1.9e5 |
| **D2-R1 fine (delay identity)** | **0.95151500 hq** | **holds** |
| **D2-R4 sum (Fejér, exact \|φ\|^38)** | **0.189413 hq** (certified 0.295863) | **holds** |

## The structural facts that made this solvable

The fragment law is a Poisson point process on `(0, zeta]` with intensity `du/u`,
so everything is in closed form and *elementary*:

* characteristic function   `φ(t) = exp (-Cin(t*zeta) - i*Si(t*zeta))`,  `Cin(x) = γ + log x - Ci(x)`
* Laplace transform        `L(l)  = exp (-Ein(l*zeta))`,  `Ein(x) = γ + log x + E1(x)`
* mean `zeta`,  **variance `zeta²/2 = 0.5523` (finite!)**,  all moments finite
* density: **`f ≡ e^{-γ}/zeta = 0.534237` on `(0, zeta)`** — exactly constant

The last line is the key and it is provable in one step. From
`l*L'(l) = -(1-e^{-l*zeta})*L(l)` and `-L' = L[m·]` one gets, as measures on
`(0,∞)`, `(m f(m) dm)' = μ - T_zeta μ`; on `(0, zeta)` the shifted term vanishes,
so `m f'(m) = 0` distributionally and `f` is constant there. Verified three ways
(`num/verify.py`, `num/core.py`, simulation): `f_1(0.5)=0.5336, f_1(0.9)=0.5370,
f_1(1.2)=0.4658`, and the exact inversion at the window gives 0.534237.

## Route 1 — EXACT CONVOLUTION CERTIFICATES → **WINNER at the fine level**

closability: **closed, proved**. `Pg182D2/EnvLemmas.lean`:

* `cell_integral_eq_const` (D2-CONST): where the density is constant the cell mass
  is *exactly* `A*mesh` — zero inequality slack.
* `cell_mass_le_fine_env` / `cell_mass_lt_hq`: `A <= 1/zeta` (normalisation:
  `A*zeta = ∫_0^zeta f <= 1`) gives every cell below `zeta` a mass `< hq`.
* `fine_env_lt_hq`: the envelope in hq units is `1/zeta = 0.951515 < 1`.

Tightness: the envelope is `1/zeta` where the truth is `e^{-γ}/zeta`, i.e. exactly
`e^γ = 1.7811×` the truth. **Required margin: the frozen uniform mass is
`1/(e^{-γ}/zeta · zeta) = e^γ = 1.7811×` the truth.** The provable bound is
`1/zeta` = 1.872× the truth — inside by 4.85 %. Remarkably tight, and it needs no
transcendental arithmetic: the whole fine level reduces to `1/zeta < 1`, i.e. to
`1312494500 < 1379373467`.

Why this is the *right* use of route 1: the convolution structure is not merely
factorisable, it is *degenerate* — the delay identity says the convolution of the
infinite band family is flat on the whole first period `(0, zeta)`, which
contains every window the obligation touches.

## Route 4 — LOCAL LIMIT (exact φ + Fejér/Esseen smoothing) → **WINNER at the sum level**

closability: **closed** for the point-probability target, with one named analytic
input (Mathlib has `ProbabilityTheory.charFun` and the inversion machinery but no
smoothing lemma; see "Walls" below).

The tool, derived and then optimised numerically: for the Fejér kernel
`Λ_T(z) = 2(1-cos(Tz))/(Tz)^2` (nonneg, `Λ_T(0)=1`, `Λ̂_T = (2π/T)(1-|t|/T)_+`),

    P(X ∈ [a, a+h])  ≤  min_{0<θ≤π}  θ·h / (2(1-cos θ)) · ∫_0^{T} (1-t/T) |φ(t)|^d dt,
                        T = 2θ/h.

With `d = 38` and the exact `|φ|^38 = exp(-38 Cin(t zeta))`:

* optimal `θ* = 2.331` (matches the analytic optimum of `θ sinθ = 1-cosθ`)
* `∫_0^∞ e^{-38 Cin} = 0.2737` (true), certified rational upper bound `0.3945`
* `C38 = 0.189413` true, **`0.29586259` certified** → `env = 0.2959 hq`.

Truth at that window: `f_38(34.8) = 0.0489`, so the certified envelope is `6.05×`
the truth and `0.30 hq` — the required threshold is `≤ 1 hq` (margin 3.4×) or, on
the D1c ledger, `≤ 10.56 hq` (margin 35.7×).

**Why d=38 works where d=1 does not** — this is the sharpest measurement of the
lane. `|φ(t)| ~ e^{-γ}/(t zeta)` for large `t` is *not* integrable, so the same
bound at `d=1` diverges logarithmically and delivers `5.724 hq` (10.7× the truth,
above `hq` → useless). Raising to the 38th power turns `1/t` into `1/t^38`;
`exp(-38 Cin(t zeta))` is integrable and concentrated at `t ≲ 1`, where the
Gaussian-type behaviour `Cin(x) ≈ x²/4` gives the effective `σ_38 ≈ 4.58`. So the
sum level is *easier* than the fine level for Fourier methods — the exact opposite
of the D1 experience, where the sum level was the harder one.

## Route 2 — BERNSTEIN / BENNETT variance envelopes → **closable but strictly weaker, not a new class**

The moment access is real and cheap: `Var M = zeta²/2 = 0.5523`, all moments
`E[M^k] = zeta^k/k` finite, and `Support.lean`'s Poisson-MGF machinery already
gives the full MGF in closed form. So Bennett/Bernstein bounds *exist*. But they
are deviation bounds: their scale is `O(1)` (`exp(-h²/(2(v+ah/3)))` type), i.e.
the same scale defect as Chernoff. As a **point** bound Bennett is at best a
strict refinement of D1-CELL, never `O(mesh)`. **Rejected as the deliverable,
retained as a fallback for the tail region** (m > mean), where it is excellent and
where D2's flat-density route does not apply.

## Route 3 — QUANTITATIVE CLT / BERRY–ESSEEN → **named wall**

Two separate walls:
1. *Type mismatch*: Berry–Esseen bounds `sup_x |F(x) - Φ(x)|`, a CDF distance.
   To extract `P(X ∈ cell)` you must go through a smoothing/density inequality —
   i.e. through route 4 — so route 3 is never a shortcut to a point mass, it is
   route 4 with a worse constant.
2. *Constant mismatch*: the target is `1e-6`-scale. `sup|F-Φ| ≤ 0.47 ρ/σ³` with
   `ρ = E|M-EM|³` is a `~1e-2`-scale statement; the required resolution is 4 orders
   below the constant. Dependency is not even the binding issue here (the 38
   coordinates are independent) — the *constants* are.

## The named walls (honest inventory)

1. **Mathlib has no smoothing/Esseen lemma.** The Fejér bound above is therefore a
   *named analytic input* in the Lean deliverable, recorded as the structure
   `HasLocalBound mu D` (`∀ a h, 0 < h → mu (Ioc a (a+h)) ≤ D*h`): every route
   bottoms out in that one object, and `cell_measure_le_hq` consumes it. The
   proof of `HasLocalBound` for `d = 38` is this lane's only remaining analytic
   debt, and it is a self-contained Fourier-analytic computation (kernel
   positivity + Plancherel + the explicit `φ`), not a structural one.
2. **The `d = 1` log divergence is a hard wall for Fourier methods at the fine
   level.** `∫|φ| = ∞`; any concentration bound of smoothing type is
   `O(h log(1/h))`, i.e. `5.724 hq > hq` here. The fine level is only closable
   by the exact identity (route 1), which is why route 1 is not optional.
3. **The frozen per-row `source_mass` is not a window probability.** Within one
   group (G3) the 15 components share one window yet claim masses 0.0308 … 7.9e-5,
   a 400× spread; the true window probability is 0.0449. So the D1c per-row value
   is a per-run/per-cell-scale quantity. A "whole-window" reading of the ledger is
   not closable by *any* density bound, and would additionally make the frozen data
   an under-estimate — a data-side matter for D1/C0, flagged in TIGHTNESS.md §4,
   not a defeat of the envelope class.
