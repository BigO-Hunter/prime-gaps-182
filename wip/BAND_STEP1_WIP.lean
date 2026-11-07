-- WIP — step 1 of (N1), the single band, corrected statement.
--
-- STATUS: everything compiles EXCEPT the final `hmu` coercion (the last error), i.e. the chain
--   charFun (map mass (finitePoissonLaw μ)) t
--     = ∫ c, exp (I (c.mass t))            [charFun_mass_map_single]
--     = ∫ n, (∫ x : Fin n → ℝ, ...) ∂Poisson(μ.mass)   [integral_finitePoissonLaw_normalized]
--     = ∫ n, q ^ n ∂Poisson(μ.mass)       [exp_mass_weightedEmpirical + integral_fintype_prod_eq_prod]
--     = exp (μ.mass (q - 1))              [poisson_integral_pow]
-- is verified.  The remaining obligation is the bookkeeping identity
--   (μ : Measure ℝ) = (μ.mass : ℝ≥0∞) • (μ.normalize : Measure ℝ)
-- from `FiniteMeasure.self_eq_mass_smul_normalize` / `self_eq_mass_mul_normalize`; the mismatch is
-- `↑μ s` (Measure.coeFn) vs `μ s` (FiniteMeasure.coeFn) plus the ℝ≥0/ℝ≥0∞ scalar coercion.
-- A successor should close it with `FiniteMeasure.toMeasure_smul` + `Measure.ext` and the
-- `FiniteMeasure.coeFn_def` unfolding, then move this file into Pg182D2/.
--
import Pg182D2.CharFunBridge

noncomputable section
namespace PrimeGap182D2
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

set_option maxHeartbeats 2000000

theorem band_exp_integrand_measurable (t : ℝ) :
    Measurable (fun c : FiniteMeasure ℝ => Complex.exp (↑((c.mass : ℝ) * t) * Complex.I)) :=
  Complex.continuous_exp.measurable.comp
    ((Complex.measurable_ofReal.comp (PrimeGap182D1.measurable_mass.mul_const t)).mul_const Complex.I)

theorem band_exp_integrand_bound (t : ℝ) (c : FiniteMeasure ℝ) :
    ‖Complex.exp (↑((c.mass : ℝ) * t) * Complex.I)‖ ≤ 1 := by
  rw [Complex.norm_exp]
  simp

/-- **Step 1 of (N1), single band** (corrected statement: the band must live on `[0, ∞)`).

For a finite measure `μ` whose normalized version is a.e. nonnegative — which every dyadic band
`cappedDyadicIntensity ζ k` satisfies — the characteristic function of the mass of the Poisson
fragment law is `exp (∫ u, (e^{I t u} - 1) ∂μ)`.

Without the nonnegativity hypothesis this is FALSE: `weightedEmpirical` builds atoms as
`(x i).toNNReal • δ (x i)`, so for `μ = δ_{-1}` every sampled mass is `0` (LHS `= 1`) while the
right-hand side is `exp (e^{-It} - 1) ≠ 1`. -/
theorem n1ResidualBand_of_nonneg (μ : FiniteMeasure ℝ) (t : ℝ)
    (hμ : ∀ᵐ u ∂((μ.normalize : Measure ℝ)), 0 ≤ u) :
    charFun ((PrimeGap182D1.finitePoissonLaw μ).map (fun X : FiniteMeasure ℝ => (X.mass : ℝ))) t
      = Complex.exp (∫ u, (Complex.exp (↑(u * t) * Complex.I) - 1) ∂(μ : Measure ℝ)) := by
  have : IsProbabilityMeasure (μ.normalize : Measure ℝ) := inferInstance
  set q : ℂ := ∫ u, Complex.exp (↑(u * t) * Complex.I) ∂((μ.normalize : Measure ℝ)) with hqdef
  have hq_norm : ‖q‖ ≤ 1 := by
    have hInt : Integrable (fun u : ℝ => Complex.exp (↑(u * t) * Complex.I))
        ((μ.normalize : Measure ℝ)) :=
      Integrable.of_bound (by fun_prop) 1
        (Filter.Eventually.of_forall fun u => by simp [Complex.norm_exp])
    have h1 : ∫ u, ‖Complex.exp (↑(u * t) * Complex.I)‖ ∂((μ.normalize : Measure ℝ)) = 1 := by
      simp only [Complex.norm_exp]
      rw [show (fun u : ℝ => Real.exp (↑(u * t) * Complex.I).re) = fun _ => (1 : ℝ) from ?_]
      · rw [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
      · funext u; simp
    rw [hqdef]
    calc ‖∫ u, Complex.exp (↑(u * t) * Complex.I) ∂((μ.normalize : Measure ℝ))‖
        ≤ ∫ u, ‖Complex.exp (↑(u * t) * Complex.I)‖ ∂((μ.normalize : Measure ℝ)) :=
          norm_integral_le_integral_norm _
      _ = 1 := h1
  have hinner : ∀ n : ℕ, ∫ x : Fin n → ℝ,
        Complex.exp (↑(((PrimeGap182D1.weightedEmpirical n x).mass : ℝ) * t) * Complex.I)
        ∂(Measure.pi fun _ : Fin n => (μ.normalize : Measure ℝ)) = q ^ n := by
    intro n
    have hae : ∀ᵐ x ∂(Measure.pi fun _ : Fin n => (μ.normalize : Measure ℝ)), ∀ i, 0 ≤ x i := by
      rw [ae_all_iff]
      intro i
      exact (measurePreserving_eval (fun _ : Fin n => (μ.normalize : Measure ℝ)) i)
        |>.quasiMeasurePreserving.ae hμ
    rw [integral_congr_ae (hae.mono fun x hx =>
      PrimeGap182D2.exp_mass_weightedEmpirical n x hx t)]
    rw [integral_fintype_prod_eq_prod (f := fun (_ : Fin n) (z : ℝ) =>
      Complex.exp (↑(z * t) * Complex.I))]
    rw [hqdef, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  calc charFun ((PrimeGap182D1.finitePoissonLaw μ).map
        (fun X : FiniteMeasure ℝ => (X.mass : ℝ))) t
      = ∫ c, Complex.exp (↑((c.mass : ℝ) * t) * Complex.I)
          ∂(PrimeGap182D1.finitePoissonLaw μ) := charFun_mass_map_single μ t
    _ = ∫ n, (∫ x : Fin n → ℝ,
          Complex.exp (↑(((PrimeGap182D1.weightedEmpirical n x).mass : ℝ) * t) * Complex.I)
          ∂(Measure.pi fun _ : Fin n => (μ.normalize : Measure ℝ)))
          ∂(poissonMeasure μ.mass) :=
        integral_finitePoissonLaw_normalized μ _ (band_exp_integrand_measurable t)
          (band_exp_integrand_bound t)
    _ = ∫ n, q ^ n ∂(poissonMeasure μ.mass) := by
        rw [integral_congr_ae (Filter.Eventually.of_forall hinner)]
    _ = Complex.exp ((μ.mass : ℂ) * (q - 1)) := poisson_integral_pow μ.mass q hq_norm
    _ = Complex.exp (∫ u, (Complex.exp (↑(u * t) * Complex.I) - 1) ∂(μ : Measure ℝ)) := by
        congr 1
        have hExpInt : Integrable (fun u : ℝ => Complex.exp (↑(u * t) * Complex.I))
            ((μ.normalize : Measure ℝ)) :=
          Integrable.of_bound (by fun_prop) 1
            (Filter.Eventually.of_forall fun u => by simp [Complex.norm_exp])
        have hOneInt : Integrable (fun _ : ℝ => (1 : ℂ)) ((μ.normalize : Measure ℝ)) :=
          integrable_const 1
        have hsplit : ∫ u, (Complex.exp (↑(u * t) * Complex.I) - 1)
            ∂((μ.normalize : Measure ℝ)) = q - 1 := by
          rw [integral_sub hExpInt hOneInt, hqdef, integral_const, Measure.real, measure_univ,
            ENNReal.toReal_one, one_smul]
        have hmu : ((μ : Measure ℝ)) = (μ.mass : ℝ≥0∞) • ((μ.normalize : Measure ℝ)) := by
          ext s _hs
          simpa [Measure.smul_apply, smul_eq_mul]
            using FiniteMeasure.self_eq_mass_mul_normalize (μ := μ) s
        calc (μ.mass : ℂ) * (q - 1)
            = (μ.mass : ℝ) • (q - 1) := by rw [Complex.real_smul]
          _ = (μ.mass : ℝ) • ∫ u, (Complex.exp (↑(u * t) * Complex.I) - 1)
                ∂((μ.normalize : Measure ℝ)) := by rw [hsplit]
          _ = ∫ u, (Complex.exp (↑(u * t) * Complex.I) - 1)
                ∂((μ.mass : ℝ≥0∞) • ((μ.normalize : Measure ℝ))) := by
              rw [integral_smul_measure, ENNReal.coe_toReal]
          _ = ∫ u, (Complex.exp (↑(u * t) * Complex.I) - 1) ∂(μ : Measure ℝ) := by rw [hmu]

end PrimeGap182D2
