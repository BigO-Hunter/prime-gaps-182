# N1N2_REPORT — the last two named inputs of the 182 data side

Lane N1N2, repo dir `d2/`, continuing D4.  Deliverables:
`Pg182D2/HeadTail.lean` (N2), `Pg182D2/CharFunBridge.lean` (N1), axchecks in `receipt/`.

## 0. Verdicts

| item | verdict |
|---|---|
| **(N2)** `∀ R, ∫_0^R e^{-38 Cin} ≤ 4/π` | **CLOSED — PROVED, unconditionally** (`integral_cinDecay_le_four_div_pi`, `integral_exp_neg_Cin_le_four_div_pi`) |
| **(N1)** `charFun (fragment mass law) t = exp (-(charExponent t ζ))` | **prefix PROVED + one named residual.**  The whole ℂ/Bochner Poisson machinery is now a theorem; the residual is the *band assembly* over `k : ℤ`, blocked on a real Mathlib gap (§2) |
| layer M at `d = 38` | **now needs N1 only**: `hasLocalBound_convPow_of_charFun`, `cell_measure_le_hq_of_charFun'` (N2's hypothesis discharged) |
| axcheck | 15 (N2) + 7 (N1) theorems, **`[propext, Classical.choice, Quot.sound]` only** |

Named-input count of the data side: **2 → 1**, and that one is not a gap in *our* proof but
in Mathlib's Bochner surface.

## 1. (N2) — the head/mid/tail assembly, proved

`Pg182D2/HeadTail.lean`.  The statement is exactly the hypothesis form
`IntegralBound.hasLocalBound_convPow_of_integral_le` consumes; no Darboux grids, no `tsum`
over an `iUnion`, no integrability on an unbounded set.

* **head** `∫_0^π ≤ ∫_0^∞ e^{-38x²/π²} = √(π³/38)/2 ≤ 2/3`
  (`Cin_ge_sq` + `integral_mono_on` + `integral_gaussian_Ioi`; the numeric bound is
  `π³ ≤ 64`, `√38 ≥ 6`, so `π√π/(2√38) ≤ 8/12`).
* **mid** `∫_π^4 ≤ (4-π)e^{-38} ≤ 4/39`  (`Cin_ge_one`; `e^{-38} ≤ 1/39` from
  `Real.add_one_le_exp 38`).
* **tail** on `[4·2^k, 4·2^{k+1})`: `Cin x ≥ 1+k/4` (`Cin_dyadic` + `Cin_mono`), and
  `e^{-(38(1+k/4))} = e^{-38}·(e^{-19/2})^k ≤ e^{-38}·4^{-k}` (`e^{-19/2} ≤ 1/4` from
  `log 4 ≤ 3`), so the block integral is `≤ 4e^{-38}·2^{-k}`; the blocks up to `4·2^N`
  telescope (`sum_integral_adjacent_intervals`) into `≤ 8e^{-38} ≤ 8/39`, and any `R` is
  dominated by some `4·2^N` (`pow_unbounded_of_one_lt`).

Total `38/39 ≈ 0.9744 < 4/π ≈ 1.2732`.  Two structural lemmas had to come first: `Cin` is
continuous (it is the primitive of an interval-integrable integrand —
`intervalIntegral.continuous_primitive`), hence the profile is measurable/integrable.

Only non-elementary ingredient: `integral_gaussian_Ioi` (already in Mathlib).

## 2. (N1) — the ℂ/Bochner Poisson bridge: what is proved, what is named

`Pg182D2/CharFunBridge.lean` (d2 now `require`s `pg182-d1` for the law definitions).

**PROVED (all stdlib axioms):**

| theorem | content |
|---|---|
| `integral_finitePoissonLaw_normalized` | the **Bochner twin** of the real mixture lemma: `∫ c, F c ∂(finitePoissonLaw μ) = ∫ n, (∫ x : Fin n, F (weightedEmpirical n x) ∂π(μ.normalize)) ∂Po(μ.mass)` — `integral_map` + `integral_prod` + the `infinitePi → pi` marginal of `Fin n` |
| `poisson_integral_pow` | **the analytic core**: `‖q‖ ≤ 1 ⟹ ∫ n, q^n ∂Po(m) = exp (m (q-1))` |
| `ennreal_mass_weightedEmpirical`, `mass_weightedEmpirical_of_nonneg` | mass of an `n`-point empirical measure = `Σ_i x_i` |
| `exp_mass_weightedEmpirical` | `exp (I t mass) = ∏_i exp (I t x_i)` — collapses the `Fin n` product integral to `q^n` |
| `charFun_mass_map`, `charFun_mass_map_single` | the interface: charFun of the mass pushforward = `∫ c, exp (I (c.mass t))` |

**The residual is now a Lean `Prop`, not prose:** `N1Residual`, and its single-band half
`N1ResidualBand`, at the end of `CharFunBridge.lean`.

**The exact Mathlib gap** (stated in the file):

    There is no Bochner analogue of "the integral of a product family over
    `Measure.infinitePi` is the product of the integrals."

The finite-index case is `MeasureTheory.integral_fintype_prod_eq_prod`; the infinite-index
case exists only for `∫⁻` of nonnegative integrands, which is exactly how
`Pg182D1/Support.lean`'s `lintegral_fragment_sum` does the real (EReal) version.  A `ℂ`
version cannot use monotone convergence: it needs a `HasSum`/`HasProd` convergence argument.

**What remains, in three concrete steps** (each named, none requiring new mathematics):

1. **single band**, from the theorems above: extract `q = ∫ u, exp (I t u) ∂μ.normalize`
   (`‖q‖ ≤ 1` by `Complex.norm_exp`), apply `integral_finitePoissonLaw_normalized` +
   `exp_mass_weightedEmpirical` + `poisson_integral_pow` (needs a.e. nonnegativity of the
   samples under `Measure.pi (μ.normalize)`, which holds because each band is supported on
   `Ioc (2^k) (2^{k+1})`), then `∫ u, (e^{Itu} - 1) ∂μ = μ.mass • (q - 1)`
   (`FiniteMeasure.coe_eq_mass_smul_normalize` + `integral_smul_measure` + `integral_sub`).
2. **band product**: the per-band charFuns multiply — the missing Bochner `infinitePi`
   product-integral above, plus `HasSum.exp` (`exp` of a summable exponent family is the
   product of the exponentials, `HasProd`) for the `exp (Σ_k)` step.
3. **the join** `Σ_k ∫_{band k} = ∫_0^ζ` for the ℂ integrand `(1 - e^{Itu})/u`: this one IS
   available (`integral_iUnion_ae` + the already-proved `integrable_charExponent_integrand`
   in `CharFunMod`, and `sum_cappedDyadicIntensity`/`dyadic_bands_disjoint` from d1).

Estimated remaining work: 150–250 lines, mechanical, no new analysis.  Step 2 is the only
one with a Mathlib-level risk.

## 3. The FINAL 182 named-input list

Data side (this lane closes N2, reduces N1):

| # | input | status |
|---|---|---|
| 1 | **(N1)** the fragment-law charFun identity, `= exp (-charExponent t ζ)` | prefix proved; residual = the band assembly (§2), blocked on the Bochner `infinitePi` product-integral |
| 2 | ~~(N2) the certified integral~~ | **CLOSED** (this lane) |

Everything else on the data side is a theorem: the Fejér smoothing lemma (D3), the `d = 38`
product structure and `HasLocalBound ⇒ cell mass ≤ hq` (D3), the modulus identity, the
`Cin` structural bounds, the margin (D4), and now the integral bound (this lane).

Campaign-level deep inputs (unchanged by the data side, and not Lean-reachable today):

* **Katz** — `|Kl₃(c)| ≤ 3` and raw rank-four `≤ 4p√p` (Katz, *Gauss sums, Kloosterman
  sheaves and monodromy*, Thm 4.1.1; Deligne purity).
* **FKM** — two-Kloosterman correlation `≤ 8p√p` (Fouvry–Kowalski–Michel, Prop 2).
* **Type III** — `TypeIII.LocalFourierHypothesis` (no closed proof anywhere).
* **Deduction** — the tuple/admissibility bound-from-tuple step (already in `formal/`,
  credited romyar1); the arithmetic surface a reviewer checks.

So: **"182 certified given N1's band assembly + Katz + FKM + Type III"**, with the
*analytic-support* half now empty: no Darboux cells, no smoothing lemma, no integral
estimate left as an assumption.

## 4. Build / reproduction

`lakefile.toml` now requires `pg182-d1` (path dependency) for `fragmentLaw`,
`finitePoissonLaw`, `cappedDyadicIntensity` and `measurable_mass` — a `lake update pg182-d1`
was run; the path dependency resolves as `../d1` in this umbrella (see `lakefile.toml`).

    LAKE_JOBS=1 LEAN_NUM_THREADS=1 lake build Pg182D2                     # 8936 jobs
    LAKE_JOBS=1 LEAN_NUM_THREADS=1 lake env lean receipt/axcheck_headtail.lean
    LAKE_JOBS=1 LEAN_NUM_THREADS=1 lake env lean receipt/axcheck_charfunbridge.lean

## 5. Axcheck

`receipt/axcheck_headtail.txt` (15 theorems) and `receipt/axcheck_charfunbridge.txt`
(7 theorems): **`[propext, Classical.choice, Quot.sound]` only.**  No `sorryAx`, no
`native_decide`, no new axioms.  `N1Residual` / `N1ResidualBand` are *definitions of
propositions*, not assumptions — nothing depends on them.
