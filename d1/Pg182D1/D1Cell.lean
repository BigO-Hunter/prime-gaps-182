import Pg182D1.Support

/-!
# D1CELL.lean — the per-coordinate Markov cell envelope (D1 workhorse)

For a coordinate `X` drawn from the true fragment law, the probability of
landing in grid cell `n` (`trialCellIndex X = n`, i.e. mass in
`[n·mesh, (n+1)·mesh)`) is dominated, for EVERY `s ≥ 0`, by the exp-sandwich

    μ{cell = n}  ≤  exp(s·(n+1)·mesh) · E[exp(-s·mass)].

This is the per-cell majorant engine: any upper bound on the mass MGF of the
law yields an explicit computable envelope for every cell. The D1 chain
combines it with the MGF bound of `D1Mgf.lean`.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace PrimeGap182D1

/-- The ENNReal-valued mass exponential `e^{-s·mass}` (the Markov integrand). -/
def massExp (s : ℝ) (X : FiniteMeasure ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-s * (X.mass : ℝ)))

theorem measurable_massExp (s : ℝ) : Measurable (massExp s) := by
  unfold massExp
  exact Measurable.ennreal_ofReal ((measurable_const.mul measurable_mass).exp)

theorem massExp_le_one (s : ℝ) (hs : 0 ≤ s) (X : FiniteMeasure ℝ) :
    massExp s X ≤ 1 := by
  unfold massExp
  refine ENNReal.ofReal_le_one.mpr ?_
  rw [Real.exp_le_one_iff]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs) X.mass.coe_nonneg

/-- D1-CELL (Markov): the probability that a `fragmentLaw ζ` sample lands in
cell `n` is at most `exp(s·(n+1)·mesh)` times the mass MGF
`∫ exp(-s·mass) d(fragmentLaw ζ)`, for every `s ≥ 0` and every cell `n`. -/
theorem cell_probability_le (ζ : ℝ) (n : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    (fragmentLaw ζ).real {X : FiniteMeasure ℝ | trialCellIndex X = n}
      ≤ Real.exp (s * (((n : ℝ) + 1) * (trialMesh : ℝ))) *
        ∫ X : FiniteMeasure ℝ, Real.exp (-s * (X.mass : ℝ)) ∂(fragmentLaw ζ) := by
  have hprob : IsProbabilityMeasure (fragmentLaw ζ) := fragmentLaw_isProbabilityMeasure ζ
  set b : ℝ := ((n : ℝ) + 1) * (trialMesh : ℝ) with hb
  set A : Set (FiniteMeasure ℝ) := {X : FiniteMeasure ℝ | trialCellIndex X = n} with hA
  set c : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-s * b)) with hc
  set g : FiniteMeasure ℝ → ℝ≥0∞ := massExp s with hg
  have hb0 : (0 : ℝ) ≤ b :=
    mul_nonneg (by exact_mod_cast Nat.zero_le (n + 1))
      (by exact_mod_cast trialMesh_pos.le)  -- measurability of the set and of the real integrand
  have hAmeas : MeasurableSet A := measurable_cellIndex (measurableSet_singleton n)
  have hfre : Measurable fun X : FiniteMeasure ℝ => Real.exp (-s * (X.mass : ℝ)) :=
    (measurable_const.mul measurable_mass).exp
  have hfnn : 0 ≤ᵐ[fragmentLaw ζ] fun X : FiniteMeasure ℝ => Real.exp (-s * (X.mass : ℝ)) :=
    Filter.Eventually.of_forall (fun _ => Real.exp_nonneg _)
  -- pointwise domination on A
  have hge : ∀ X ∈ A, c ≤ g X := by
    intro X hX
    have hmass := cell_mass_lt hX
    have hneg : -s * b ≤ -s * (X.mass : ℝ) := by
      nlinarith [hs, hmass]
    rw [hc]
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hneg)
  have hAle : (fragmentLaw ζ) A ≤ 1 := by
    rw [← hprob.measure_univ]
    exact measure_mono (Set.subset_univ A)
  have hc1 : c ≤ 1 := by
    rw [hc]
    refine ENNReal.ofReal_le_one.mpr (Real.exp_le_one_iff.mpr ?_)
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) hb0
  -- c · μ A ≤ ∫⁻ g  via indicator monotonicity
  have hkey : c * (fragmentLaw ζ) A
      ≤ ∫⁻ X, g X ∂(fragmentLaw ζ) := by
    have hpt : (fun X => A.indicator (fun _ => c) X) ≤
        (fun X => A.indicator g X) := by
      intro X
      by_cases hX : X ∈ A
      · simp only [hX, Set.indicator_of_mem]
        exact hge X hX
      · simp only [Set.indicator_of_notMem hX]
        exact le_refl _
    have hint1 : ∫⁻ X, A.indicator (fun _ => c) X ∂(fragmentLaw ζ)
        = c * (fragmentLaw ζ) A := lintegral_indicator_const hAmeas c
    have hint2 : ∫⁻ X, A.indicator g X ∂(fragmentLaw ζ)
        = ∫⁻ X in A, g X ∂(fragmentLaw ζ) := lintegral_indicator hAmeas g
    calc c * (fragmentLaw ζ) A
        = ∫⁻ X, A.indicator (fun _ => c) X ∂(fragmentLaw ζ) := hint1.symm
      _ ≤ ∫⁻ X, A.indicator g X ∂(fragmentLaw ζ) := lintegral_mono hpt
      _ = ∫⁻ X in A, g X ∂(fragmentLaw ζ) := hint2
      _ ≤ ∫⁻ X, g X ∂(fragmentLaw ζ) := by
          simpa using lintegral_mono_set (Set.subset_univ A)
  -- toReal chain: exp(-s·b) · μ.real A ≤ ∫ real
  have hIfin : (∫⁻ X, g X ∂(fragmentLaw ζ)) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
    have h1 : (∫⁻ X, g X ∂(fragmentLaw ζ))
        ≤ (∫⁻ _ : FiniteMeasure ℝ, (1 : ℝ≥0∞) ∂(fragmentLaw ζ)) :=
      lintegral_mono (fun X => massExp_le_one s hs X)
    rw [lintegral_one, hprob.measure_univ] at h1
    exact h1
  have hcfin : c ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hc1
  -- divide through at the toReal level (all quantities finite)
  have hc0 : c ≠ 0 := by
    intro hz
    rw [hc, ENNReal.ofReal_eq_zero] at hz
    linarith [Real.exp_pos (-s * b), hz]
  have hmul : c * (fragmentLaw ζ) A ≠ ⊤ :=
    ENNReal.mul_ne_top hcfin (ne_top_of_le_ne_top ENNReal.one_ne_top hAle)
  have hstep0 := (ENNReal.toReal_le_toReal hmul hIfin).mpr hkey
  rw [ENNReal.toReal_mul, hc, ENNReal.toReal_ofReal (Real.exp_nonneg (-s * b))] at hstep0
  have hbpos : 0 < Real.exp (-s * b) := Real.exp_pos _
  have hfin2 : Real.exp (s * b) * (∫⁻ X, g X ∂(fragmentLaw ζ)).toReal
      = (∫⁻ X, g X ∂(fragmentLaw ζ)).toReal / Real.exp (-s * b) := by
    rw [neg_mul, Real.exp_neg, div_eq_inv_mul, inv_inv]
  -- the real integral = toReal of the lintegral
  have hint : ∫ X : FiniteMeasure ℝ, Real.exp (-s * (X.mass : ℝ)) ∂(fragmentLaw ζ)
      = (∫⁻ X, g X ∂(fragmentLaw ζ)).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae hfnn hfre.aestronglyMeasurable]
    congr 1
  -- probability mass real = toReal of ENNReal measure
  have hmassreal : (fragmentLaw ζ).real A
      = ((fragmentLaw ζ) A : ℝ≥0∞).toReal := rfl
  rw [hmassreal, hint, hfin2]
  exact (le_div_iff₀ hbpos).mpr (by
    have hcomm := mul_comm (Real.exp (-s * b)) (((fragmentLaw ζ) A : ℝ≥0∞).toReal)
    linarith [hstep0, hcomm])

end PrimeGap182D1
