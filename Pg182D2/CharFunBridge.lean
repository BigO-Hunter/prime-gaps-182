import Mathlib
import Pg182D1.Support
import Pg182D2.CharFunMod

/-!
# CHARFUNBRIDGE.lean — item (N1): the ℂ (Bochner) Poisson bridge

`FINALSET_REPORT.md` §3 named (N1) as the last analytic input of the 182 data side:

    charFun ((fragmentLaw ζ).map (fun X => (X.mass : ℝ))) t = Complex.exp (-(charExponent t ζ))

the ℂ-valued twin of the vendored real (EReal) computation `lintegral_exp_neg_finitePoissonLaw`
(`Pg182D1/Support.lean`).  The real proof runs through `∫⁻`/`EReal` and its step `∏ i, g (x i)`
has no ℂ analogue there, so the ℂ version has to be redone with **Bochner** integrals.

## PROVED here

* `charFun_mass_map`, `charFun_mass_map_single` — the interface: the charFun of the mass
  pushforward is `∫ c, exp (I (c.mass t))` against the law.
* `ennreal_mass_weightedEmpirical`, `mass_weightedEmpirical_of_nonneg`,
  `exp_mass_weightedEmpirical` — the mass of an `n`-point empirical measure is `Σ_i x_i`, and
  `exp` of it splits into the product of the per-atom factors (the step that makes the
  `Fin n`-product integral collapse to `q^n`).
* `poisson_integral_pow` — **the analytic core**: for `‖q‖ ≤ 1`,
  `∫ n, q^n ∂Po(m) = exp (m (q - 1))`.
* `integral_finitePoissonLaw_normalized` — the **Bochner twin** of the real mixture lemma:
  the Poisson law on finite measures is a Poisson-weighted mixture of the *normalized*
  `n`-point empirical laws (`integral_map` + Fubini + the `infinitePi → pi` marginal on `Fin n`).

## NAMED: what is left of (N1), exactly

The single band is `map`ped through `exp` + `poisson_integral_pow` into
`exp (∫ u, (e^{I t u} - 1)/u du)` — that is `charExponent`.  What remains is the **band
assembly**: `fragmentLaw ζ` is a product over the dyadic bands `k : ℤ` of independent Poisson
laws, so its charFun is the *infinite product* of the per-band charFuns, and the sum
`Σ_k ∫_{band k}` has to be reassembled into `∫_0^ζ`.

    MISSING (Mathlib, v4.34.1): no Bochner analogue of "the integral of a product family over
    `Measure.infinitePi` is the product of the integrals".  The finite-index case is
    `MeasureTheory.integral_fintype_prod_eq_prod`; the `∫⁻` machinery
    (`lintegral_fragment_sum` in `Pg182D1/Support.lean`) does the infinite-index case for
    nonnegative integrands only, via `lintegral_tsum` — which has no ℂ counterpart because a
    `HasSum`/`HasProd` convergence argument is needed in place of monotone convergence.

`N1N2_REPORT.md` §2 gives the exact statement of the missing lemma and the 3-step plan.
-/

noncomputable section
namespace PrimeGap182D2
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

set_option maxHeartbeats 1000000

/-! ### 1. The interface: charFun of the mass pushforward -/

/-- `charFun` of the mass pushforward, unwound into the Bochner integral over the law of the
fragment measure — the shape every step of (N1) works in. -/
theorem charFun_mass_map (ζ : ℝ) (t : ℝ) :
    charFun ((PrimeGap182D1.fragmentLaw ζ).map
        (fun X : FiniteMeasure ℝ => (X.mass : ℝ))) t
      = ∫ X, Complex.exp (↑((X.mass : ℝ) * t) * Complex.I) ∂(PrimeGap182D1.fragmentLaw ζ) := by
  rw [charFun_apply, integral_map]
  · apply integral_congr_ae
    filter_upwards with X
    have h1 : inner ℝ ((X.mass : ℝ)) t = t * (X.mass : ℝ) := by simp
    rw [h1]
    norm_num
    ring_nf
  · exact PrimeGap182D1.measurable_mass.aemeasurable
  · exact (by fun_prop : Continuous fun x : ℝ =>
      Complex.exp (↑(inner ℝ x t) * Complex.I)).aestronglyMeasurable

/-- The same, for a single band's Poisson law. -/
theorem charFun_mass_map_single (μ : FiniteMeasure ℝ) (t : ℝ) :
    charFun ((PrimeGap182D1.finitePoissonLaw μ).map (fun X => (X.mass : ℝ))) t
      = ∫ X, Complex.exp (↑((X.mass : ℝ) * t) * Complex.I)
          ∂(PrimeGap182D1.finitePoissonLaw μ) := by
  rw [charFun_apply, integral_map]
  · apply integral_congr_ae
    filter_upwards with X
    have h1 : inner ℝ ((X.mass : ℝ)) t = t * (X.mass : ℝ) := by simp
    rw [h1]
    norm_num
    ring_nf
  · exact PrimeGap182D1.measurable_mass.aemeasurable
  · exact (by fun_prop : Continuous fun x : ℝ =>
      Complex.exp (↑(inner ℝ x t) * Complex.I)).aestronglyMeasurable

/-! ### 2. The mass of the `n`-point empirical measure -/

theorem ennreal_mass_weightedEmpirical (n : ℕ) (x : Fin n → ℝ) :
    ((PrimeGap182D1.weightedEmpirical n x).mass : ℝ≥0∞)
      = ∑ i, ENNReal.ofReal (x i) := by
  rw [FiniteMeasure.ennreal_mass, PrimeGap182D1.coe_weightedEmpirical, Measure.finsetSum_apply]
  simp [Measure.smul_apply, smul_eq_mul]

theorem mass_weightedEmpirical_of_nonneg (n : ℕ) (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) :
    ((PrimeGap182D1.weightedEmpirical n x).mass : ℝ) = ∑ i, x i := by
  have hcoe := ennreal_mass_weightedEmpirical n x
  have hfin : ∀ i ∈ (Finset.univ : Finset (Fin n)), ENNReal.ofReal (x i) ≠ ∞ :=
    fun i _ => ENNReal.ofReal_ne_top
  have h1 : (((PrimeGap182D1.weightedEmpirical n x).mass : ℝ≥0∞)).toReal
      = ((PrimeGap182D1.weightedEmpirical n x).mass : ℝ) := ENNReal.coe_toReal _
  have h2 : (∑ i, ENNReal.ofReal (x i)).toReal = ∑ i, x i := by
    rw [ENNReal.toReal_sum hfin]
    exact Finset.sum_congr rfl fun i _ => ENNReal.toReal_ofReal (hx i)
  rw [← h1, hcoe, h2]

/-- `exp` of the mass splits into the product of the per-atom factors. -/
theorem exp_mass_weightedEmpirical (n : ℕ) (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) (t : ℝ) :
    Complex.exp (↑(((PrimeGap182D1.weightedEmpirical n x).mass : ℝ) * t) * Complex.I)
      = ∏ i, Complex.exp (↑((x i) * t) * Complex.I) := by
  rw [mass_weightedEmpirical_of_nonneg n x hx]
  have hsplit : (↑((∑ i, x i) * t) : ℂ) * Complex.I
      = ∑ i, (↑((x i) * t) : ℂ) * Complex.I := by
    push_cast
    rw [Finset.sum_mul, Finset.sum_mul]
  rw [hsplit, Complex.exp_sum]

/-! ### 3. The analytic core: the Poisson mixture of `q^n` -/

/-- **The Poisson/geometric identity.**  For `‖q‖ ≤ 1`, `∫ n, q^n ∂Po(m) = exp (m (q - 1))`. -/
theorem poisson_integral_pow (m : ℝ≥0) (q : ℂ) (hq : ‖q‖ ≤ 1) :
    ∫ n : ℕ, q ^ n ∂(ProbabilityTheory.poissonMeasure m)
      = Complex.exp ((m : ℂ) * (q - 1)) := by
  have hb : ∀ n : ℕ, ‖q ^ n‖ ≤ 1 := by
    intro n
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg q) hq
  have hint : Integrable (fun n : ℕ => q ^ n) (ProbabilityTheory.poissonMeasure m) :=
    Integrable.of_bound (by fun_prop : Continuous fun n : ℕ => q ^ n).aestronglyMeasurable 1
      (Filter.Eventually.of_forall hb)
  have hreal : ∀ n : ℕ, (ProbabilityTheory.poissonMeasure m).real {n}
      = Real.exp (-(m : ℝ)) * (m : ℝ) ^ n / (n.factorial : ℝ) := by
    intro n
    rw [Measure.real, ProbabilityTheory.poissonMeasure_singleton,
      ENNReal.toReal_ofReal (by positivity)]
  have hterm : ∀ n : ℕ, (ProbabilityTheory.poissonMeasure m).real {n} • q ^ n
      = (Real.exp (-(m : ℝ)) : ℂ) * ((((m : ℂ) * q) ^ n) / (n.factorial : ℂ)) := by
    intro n
    rw [hreal, Complex.real_smul, div_eq_mul_inv, div_eq_mul_inv]
    push_cast
    rw [mul_pow]
    field_simp
  have hseries : HasSum (fun n : ℕ => (((m : ℂ) * q) ^ n) / (n.factorial : ℂ))
      (Complex.exp ((m : ℂ) * q)) := by
    have h := NormedSpace.expSeries_div_hasSum_exp ((m : ℂ) * q)
    rwa [← Complex.exp_eq_exp_ℂ] at h
  calc ∫ n : ℕ, q ^ n ∂(ProbabilityTheory.poissonMeasure m)
      = ∑' n : ℕ, (ProbabilityTheory.poissonMeasure m).real {n} • q ^ n :=
        integral_countable' hint
    _ = ∑' n : ℕ, (Real.exp (-(m : ℝ)) : ℂ) * ((((m : ℂ) * q) ^ n) / (n.factorial : ℂ)) :=
        tsum_congr hterm
    _ = (Real.exp (-(m : ℝ)) : ℂ) * Complex.exp ((m : ℂ) * q) := by
        rw [tsum_mul_left, hseries.tsum_eq]
    _ = Complex.exp ((m : ℂ) * (q - 1)) := by
        rw [Complex.ofReal_exp, ← Complex.exp_add]
        congr 1
        push_cast
        ring

/-! ### 4. The Bochner mixture: a Poisson law is a mixture of empirical laws -/

/-- **Bochner twin of `lintegral_finitePoissonLaw_normalized`**: the Poisson law on finite
measures is a Poisson-weighted mixture of the *normalized* `n`-point empirical laws. -/
theorem integral_finitePoissonLaw_normalized (μ : FiniteMeasure ℝ) (F : FiniteMeasure ℝ → ℂ)
    (hF : Measurable F) (hFb : ∀ c, ‖F c‖ ≤ 1) :
    ∫ c, F c ∂(PrimeGap182D1.finitePoissonLaw μ)
      = ∫ n, (∫ x : Fin n → ℝ, F (PrimeGap182D1.weightedEmpirical n x)
          ∂(Measure.pi (fun _ : Fin n => (μ.normalize : Measure ℝ))))
        ∂(ProbabilityTheory.poissonMeasure μ.mass) := by
  let P : ∀ _ : ℕ, Measure ℝ := fun _ => (μ.normalize : Measure ℝ)
  have hP : ∀ i : ℕ, IsProbabilityMeasure (P i) := fun _ => inferInstance
  have hφ : Measurable (fun p : ℕ × (ℕ → ℝ) =>
      PrimeGap182D1.weightedEmpirical p.1 (fun i : Fin p.1 => p.2 i.val)) :=
    PrimeGap182D1.measurable_weightedEmpirical_sample
  unfold PrimeGap182D1.finitePoissonLaw
  rw [integral_map]
  · rw [integral_prod]
    · apply integral_congr_ae
      filter_upwards with n
      have hmap : Measure.map (fun ω : ℕ → ℝ => fun i : Fin n => ω i.val)
          (Measure.infinitePi P) = Measure.pi (fun i : Fin n => P i.val) := by
        rw [Measure.map_infinitePi_infinitePi_of_inj (P := P) (f := fun i : Fin n => i.val)
          Fin.val_injective, Measure.infinitePi_eq_pi]
      rw [← hmap, integral_map]
      · exact (by fun_prop : Measurable fun ω : ℕ → ℝ => fun i : Fin n => ω i.val).aemeasurable
      · exact (hF.comp (PrimeGap182D1.measurable_weightedEmpirical n)).aestronglyMeasurable
    · haveI : IsProbabilityMeasure (ProbabilityTheory.poissonMeasure μ.mass) := inferInstance
      haveI : IsProbabilityMeasure (Measure.infinitePi P) := inferInstance
      refine Integrable.of_bound (hF.comp hφ).aestronglyMeasurable 1 ?_
      exact Filter.Eventually.of_forall fun p => hFb _
  · exact hφ.aemeasurable
  · exact hF.aestronglyMeasurable

end PrimeGap182D2
