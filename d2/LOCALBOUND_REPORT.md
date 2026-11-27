# LOCALBOUND_REPORT — the Fejér smoothing lemma, and `HasLocalBound` at `d = 38`

Lane D3, repo dir `d2/`.  Deliverable: `Pg182D2/HasLocalBound.lean`
(pointer `HasLocalBound.lean`), axcheck `receipt/axcheck_haslocalbound.{lean,txt}`.

## 0. Verdict

| object | verdict |
|---|---|
| **the Fejér/Esseen smoothing lemma** (`hasLocalBound_of_charFun_bound`) | **PROVED** |
| `HasLocalBound ν (1/ζ)` from `B ≤ 4/(πζ)` (`hasLocalBound_one_div_zeta`) | **PROVED** |
| the payload, per-cell mass `≤ hq` (`cell_measure_le_hq_of_charFun`) | **PROVED** |
| the `d = 38` product structure (`charFun_convPow`), and the instance at the convolution power (`cell_measure_le_hq_convPow`) | **PROVED** |
| `HasLocalBound` for the exact `d = 38` fragment law | **exact-partial** — see §5: two *computational* inputs, no analytic wall |

All 23 theorems: `[propext, Classical.choice, Quot.sound]` only. No `sorryAx`, no
`native_decide`, no new axioms.

**Named analytic input count: 1 → 0.**  The item D2 named ("Mathlib has no smoothing lemma")
no longer exists.  What remains is not a wall but two computations (§5), each stated precisely.

## 1. Answer to the prior question: the C38 route already embodied the numbers

Yes, and exactly.  ROUTE2's certified constant is

    C38 = min_θ [ θ / (2(1-cos θ)) ] × [ certified upper bound of ∫_0^∞ e^{-38 Cin} ]

i.e. the *right-hand side of the smoothing inequality* with `B` = the integral.  The instance
`receipt/receipt.py` emits (`C38_certified`, θ-grid min): θ\* = 1.98968, θ-factor 0.750030,
`∫_0^∞ e^{-38 Cin} ≤ 0.39446770`, `C38 = 0.29586259`.  The *left* side — the bridge from that
integral to an actual ball mass — is precisely what was missing and is what this file supplies.
So the C38 computation was never a rival route; it is the numeric instance of this lemma.

## 2. The lemma

For a finite measure `ν` on `ℝ`, every `R > 0`, `c ∈ ℝ`, and `B` bounding every truncation:

    (∀ R, ∫_0^R ‖charFun ν t‖ dt ≤ B)   ⟹   ν.real (Ioc a (a+h)) ≤ (π/4)·B·h   for all a, h > 0

i.e. `HasLocalBound ν (π/4 · B)`, with the sharper `min_θ θ/(2(1-cos θ)) = 0.6900` available but
not needed.  The `θ = π` member is taken because it needs no trigonometric optimisation.

## 3. Proof map (5 pieces, one imported analytic fact)

1. `fejerKernel R x = R^2 (sinc (R x/2))^2 = 2(1-cos(Rx))/x²` (`x ≠ 0`), and
   `∫_0^R 2r sinc(rx) dr = K_R x` — proved by the explicit antiderivative
   `2(1-cos(rx))/x²`; `intervalIntegral.integral_eq_sub_of_hasDerivAt`.
2. `4R²/π² ≤ K_R z` on `|Rz| ≤ π` — Jordan's inequality in cos form,
   `Real.cos_le_one_sub_mul_cos_sq` (`cos x ≤ 1 - 2x²/π²`, `|x| ≤ π`).  **No sinc
   monotonicity is needed**, which is why the whole file avoids derivative-monotonicity work.
3. `|∫ sinc(r(x-c)) dν| ≤ (1/2r) ∫_{-r}^{r} ‖charFun ν‖` — Mathlib's
   `MeasureTheory.integral_charFun_Icc` (its real part), a shift of the measure
   (`charFun_map_add_const`), and `‖charFun‖` invariance under the shift.
4. `∫ K_R(x-c) dν = ∫_0^R 2r (∫ sinc(r(x-c)) dν) dr` — **one rectangle Fubini** over
   `(0,R] × ℝ` (bounded integrand, finite measure).  The Fejér *triangle* is never formed.
5. Bound the `r`-integrand pointwise by `∫_{-R}^{R}‖charFun ν‖ ≤ 2B` and integrate.  The
   `π/4` constant is `2R B / (4R²/π²) · (1/(Rh))` with `R = 2π/h`.

6. **The `d = 38` product structure, formalised** (`convPow`, `charFun_convPow`,
   `hasLocalBound_convPow`, `cell_measure_le_hq_convPow`): the sum coordinate is the sum of 38
   independent copies, i.e. the 38-fold convolution power, and
   `‖charFun (μ^{*d}) t‖ = ‖charFun μ t‖ ^ d`.  So the `|φ|^38` of ROUTE2 is a theorem about
   convolution powers, and the lemma's hypothesis becomes a statement about the **single band**.

Design note worth keeping: the standard Fejér proof derives the kernel identity by a *triangle*
Fubini over `{(r,t) : |t| ≤ r ≤ R}`.  That is avoided here — only an *upper bound* is needed, so
`|∫_{-r}^{r}| ≤ ∫_{-R}^{R}` gives the same conclusion with one rectangle Fubini.  This is why
the file is ~490 lines rather than a multi-thousand-line Fourier development.

## 4. Sharpness — the `d = 1` wall is now a theorem

The hypothesis is `∫_0^∞ ‖φ‖ < ∞`.  For the single-band fragment law
`‖φ_1(t)‖ = exp(-Cin(t ζ)) → e^{-γ}/(t ζ)`, so the hypothesis **fails**: the `d = 1` logarithmic
divergence measured at `5.724 hq` (ROUTE2.md, TIGHTNESS §2) is exactly the non-applicability of
this lemma, not a defect of the route.  For the sum level `‖φ_38‖ = ‖φ‖^38 = exp(-38 Cin)` the
hypothesis holds by four orders of magnitude.  The theorem thus reproduces D2's measured
fine/sum asymmetry as a statement about an integrability class.

## 5. What remains (precise, and neither is analytic)

(i) **`charFun` of the actual `d = 38` law.**  The law is defined in Lean
(`Pg182D1/Law.lean`: `fragmentLaw ζ : Measure (FiniteMeasure ℝ)`, so the mass law is the
pushforward under `fun c => (c.mass : ℝ)`, and the sum coordinate is its 38-fold convolution).
Mathlib already has `charFun_conv` (`charFun (μ ∗ ν) = charFun μ * charFun ν`).  What is needed
is `‖charFun ν t‖ = exp(-38 · Cin(t ζ))`, i.e. a **ℂ-valued** version of the vendored Poisson
MGF computation `lintegral_exp_neg_finitePoissonLaw` (`Pg182D1/Support.lean:220`), whose real
`EReal` form is already proved.  A computation on a vendored law, not a missing Mathlib theorem.

(ii) **The certified integral, transcribed.**  `∫_0^∞ e^{-38 Cin} ≤ 0.39446770` is exact rational
arithmetic in `receipt/receipt.py` (Darboux sums + `Cin` lower bounds + `e^{38}` tail).  It is not
yet a Lean theorem.  Feeding `B = 0.39446770` into `hasLocalBound_one_div_zeta` needs
`B ≤ 4/(πζ) = 1.21150648`: **margin 3.07×**, so a far cruder formalised bound would do.

With those two, `HasLocalBound ν (1/ζ)` is immediate (`hasLocalBound_convPow_one_div_zeta`, whose
hypothesis is about the single band's `φ` to the 38th power) and the D2 ledger's
`cell_measure_le_hq` fires unchanged.  Concretely: `D = (π/4)·B = 0.30981421` against the
required `D ≤ 1/ζ = 0.95151497`, and the hypothesis needs only `B ≤ 4/(πζ) = 1.21150648`.

Also unchanged by this lane: the **fine-level** (`d = 1`) input is not smoothing at all — it is
D2 route 1's density-constancy (`cell_integral_eq_const`'s `hconst : f = e^{-γ}/ζ` on `(0,ζ)`),
which this file neither uses nor discharges.

## 6. Reproduction

    LAKE_JOBS=1 LEAN_NUM_THREADS=1 lake build Pg182D2.HasLocalBound          # 8925 jobs
    LAKE_JOBS=1 LEAN_NUM_THREADS=1 lake env lean receipt/axcheck_haslocalbound.lean
    cd receipt && python3 -c "import receipt; print(receipt.C38_certified())"  # (0.29586…, θ*, I)
