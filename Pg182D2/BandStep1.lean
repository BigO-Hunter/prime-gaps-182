import Pg182D2.CharFunBridge

/-!
# BANDSTEP1.lean — step 1 of (N1): the single band, proved

The residual `N1Residual` (`CharFunBridge.lean` §5) is assembled from three steps
(`N1N2_REPORT.md` §2).  This file lands **step 1**: for a finite measure `μ` whose normalized
version is a.e. nonnegative, the characteristic function of the mass of the Poisson fragment law is
the exponential of the band exponent,

    charFun ((finitePoissonLaw μ).map (fun X => (X.mass : ℝ))) t
      = exp (∫ u, (exp (I (u t)) - 1) ∂μ).

## Why the nonnegativity hypothesis is not removable

`PrimeGap182D1.weightedEmpirical` builds its atoms as `(x i).toNNReal • δ (x i)`, so a negative
sample contributes **mass `0`** but keeps its position: for `μ = δ_{-1}` every sampled empirical
measure is `0`, the left-hand side is `charFun δ_0 t = 1`, while the right-hand side is
`exp (exp (-I t) - 1) ≠ 1`.  The identity is genuinely an identity for measures on `[0, ∞)`.

## The proof chain (all steps verified, no residue)

    charFun (map mass (finitePoissonLaw μ)) t
      = ∫ c, exp (I (c.mass t))                        -- charFun_mass_map_single
      = ∫ n, (∫ x : Fin n → ℝ, ...) ∂Poisson(μ.mass)   -- integral_finitePoissonLaw_normalized
      = ∫ n, q ^ n ∂Poisson(μ.mass)                    -- exp_mass_weightedEmpirical + fintype prod
      = exp (μ.mass * (q - 1))                         -- poisson_integral_pow
      = exp (∫ u, (exp (I (u t)) - 1) ∂μ)              -- ∫·∂(mass • normalize) bookkeeping

with `q = ∫ u, exp (I (u t)) ∂(μ.normalize)` and `‖q‖ ≤ 1`.  The last line is the identity
`μ = μ.mass • μ.normalize` (`FiniteMeasure.self_eq_mass_mul_normalize`), where the only trap is the
`ℝ≥0`/`ℝ≥0∞` scalar coercion: `FiniteMeasure.self_eq_mass_mul_normalize` is an `ℝ≥0` statement,
while the measures' `coeFn` are `ℝ≥0∞`-valued, so the bridge is
`FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure` **in the `←` direction** (the forward direction
does not fire: on the `Measure` side the goal's `↑μ s` is already `Measure.coeFn`), followed by
`ENNReal.coe_mul`.
-/

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

For a finite measure `μ` whose normalized version is a.e. nonnegative — which every nonempty dyadic
band `cappedDyadicIntensity ζ k` satisfies — the characteristic function of the mass of the Poisson
fragment law is `exp (∫ u, (e^{I t u} - 1) ∂μ)`.

Without the nonnegativity hypothesis this is FALSE: see the module docstring (`μ = δ_{-1}`). -/
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
          ext s
          rw [Measure.smul_apply, smul_eq_mul,
            ← FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure,
            ← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure,
            FiniteMeasure.self_eq_mass_mul_normalize μ s, ENNReal.coe_mul]
        calc (μ.mass : ℂ) * (q - 1)
            = (μ.mass : ℝ) • (q - 1) := by rw [Complex.real_smul]
          _ = (μ.mass : ℝ) • ∫ u, (Complex.exp (↑(u * t) * Complex.I) - 1)
                ∂((μ.normalize : Measure ℝ)) := by rw [hsplit]
          _ = ∫ u, (Complex.exp (↑(u * t) * Complex.I) - 1)
                ∂((μ.mass : ℝ≥0∞) • ((μ.normalize : Measure ℝ))) := by
              rw [integral_smul_measure, ENNReal.coe_toReal]
          _ = ∫ u, (Complex.exp (↑(u * t) * Complex.I) - 1) ∂(μ : Measure ℝ) := by rw [hmu]

/-! ### The hypothesis, discharged for a dyadic band -/

/-- **A.e. nonnegativity transfers to the normalized measure** (for a nonzero finite measure): the
normalized measure is a positive scalar multiple of the original one. -/
theorem ae_nonneg_normalize_of_ne_zero {μ : FiniteMeasure ℝ} (h0 : μ ≠ 0)
    (h : ∀ᵐ u ∂(μ : Measure ℝ), 0 ≤ u) :
    ∀ᵐ u ∂((μ.normalize : Measure ℝ)), 0 ≤ u := by
  have hmass : μ.mass ≠ 0 := by rwa [FiniteMeasure.mass_nonzero_iff]
  rw [FiniteMeasure.toMeasure_normalize_eq_of_nonzero μ h0,
    Measure.ae_smul_measure_iff (inv_ne_zero hmass)]
  exact h

/-- A dyadic band lives on `(0, ∞)`. -/
theorem ae_nonneg_cappedDyadicIntensity (ζ : ℝ) (k : ℤ) :
    ∀ᵐ u ∂(PrimeGap182D1.cappedDyadicIntensity ζ k : Measure ℝ), 0 ≤ u := by
  have h := ae_restrict_mem (μ := ((volume.restrict (Set.Ioc (0 : ℝ) ζ)).withDensity
    (fun u : ℝ => ENNReal.ofReal (1 / u)))) (measurableSet_Ioc :
    MeasurableSet (Set.Ioc ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1))))
  filter_upwards [h] with u hu
  exact (zpow_pos (by norm_num) k).le.trans hu.1.le

/-! ### The corrected residual is no longer an input -/

/-- **Step 1 landed**: the (corrected) single-band proposition `N1ResidualBand` holds. -/
theorem n1ResidualBand_holds : N1ResidualBand := fun μ t hμ => n1ResidualBand_of_nonneg μ t hμ

end PrimeGap182D2
