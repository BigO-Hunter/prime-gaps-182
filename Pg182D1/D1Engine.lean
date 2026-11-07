import Pg182D1.D1Sum

/-!
# D1ENGINE.lean — the coarse-run partition engine (the C0 interface)

The bridge from the discrete law to the integral: if an integrand `f` on the
configuration space is (i) pointwise dominated by a per-coarse-run envelope
`σ r` depending only on the run index `r = Σ_j trialCellIndex (Y j)`, (ii)
supported on a finite set `K` of runs, and (iii) each run-class carries at
most the discrete-law mass `env r`, then

    ∫ f dμ^d  ≤  Σ_{r∈K} σ r · env r.

This is the algorithm-to-integral correspondence in exactly the shape the C0
certificate consumes: the frozen per-run constants play `σ`, the discrete-law
per-run masses play `env` (instantiated from `sum_cell_probability_le` or the
frozen payload), and the bound is the discrete sum.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace PrimeGap182D1

variable {d : ℕ}

/-- Measurability of a finite σ-weighted sum of class indicators. -/
theorem measurable_runEnvelope (σ : ℕ → ℝ) (K : Finset ℕ) :
    Measurable fun Y : Fin d → FiniteMeasure ℝ =>
      ∑ c ∈ K, {Y' : Fin d → FiniteMeasure ℝ | sumCell Y' = c}.indicator
        (fun _ => σ c) Y := by
  classical
  induction K using Finset.induction_on with
  | empty => simpa using measurable_const
  | @insert c K hc ih =>
      have h : (fun Y : Fin d → FiniteMeasure ℝ =>
          ∑ c' ∈ insert c K, {Y' : Fin d → FiniteMeasure ℝ | sumCell Y' = c'}.indicator
            (fun _ => σ c') Y)
        = fun Y => {Y' : Fin d → FiniteMeasure ℝ | sumCell Y' = c}.indicator
            (fun _ => σ c) Y + ∑ c' ∈ K, {Y' : Fin d → FiniteMeasure ℝ |
              sumCell Y' = c'}.indicator (fun _ => σ c') Y := by
        funext Y
        rw [Finset.sum_insert hc]
      rw [h]
      exact (measurable_const.indicator (measurableSet_sumCell c)).add ih

/-- D1-ENGINE: the coarse-run partition bound (see module docstring). -/
theorem integral_le_discrete {μ : Measure (FiniteMeasure ℝ)}
    [IsProbabilityMeasure μ] {f : (Fin d → FiniteMeasure ℝ) → ℝ}
    (σ : ℕ → ℝ) (env : ℕ → ℝ) (K : Finset ℕ)
    (hnn : ∀ Y, 0 ≤ f Y)
    (hσ : ∀ Y, f Y ≤ σ (sumCell Y))
    (hσ_nn : ∀ c ∈ K, 0 ≤ σ c)
    (hzero : ∀ Y, sumCell Y ∉ K → f Y = 0)
    (hcell : ∀ c ∈ K, (Measure.pi fun _ : Fin d => μ).real
      {Y : Fin d → FiniteMeasure ℝ | sumCell Y = c} ≤ env c)
    (henv_nn : ∀ c ∈ K, 0 ≤ env c) :
    (∫ Y, f Y ∂(Measure.pi fun _ : Fin d => μ)) ≤ ∑ c ∈ K, σ c * env c := by
  classical
  set S : (Fin d → FiniteMeasure ℝ) → ℝ := fun Y =>
    ∑ c ∈ K, {Y' : Fin d → FiniteMeasure ℝ | sumCell Y' = c}.indicator
      (fun _ => σ c) Y with hS
  -- termwise facts
  have hterm0 : ∀ (Y : Fin d → FiniteMeasure ℝ) (c : ℕ), c ∈ K →
      0 ≤ {Y' : Fin d → FiniteMeasure ℝ | sumCell Y' = c}.indicator (fun _ => σ c) Y := by
    intro Y c hc
    by_cases hYc : sumCell Y = c
    · have hmem : Y ∈ ({Y' : Fin d → FiniteMeasure ℝ | sumCell Y' = c} : Set _) := hYc
      rw [Set.indicator_of_mem hmem]
      exact hσ_nn c hc
    · have hmem : Y ∉ ({Y' : Fin d → FiniteMeasure ℝ | sumCell Y' = c} : Set _) :=
        fun h => hYc h
      rw [Set.indicator_of_notMem hmem]
  have htermle : ∀ (Y : Fin d → FiniteMeasure ℝ) (c : ℕ), c ∈ K →
      {Y' : Fin d → FiniteMeasure ℝ | sumCell Y' = c}.indicator (fun _ => σ c) Y ≤ σ c := by
    intro Y c hc
    by_cases hYc : sumCell Y = c
    · have hmem : Y ∈ ({Y' : Fin d → FiniteMeasure ℝ | sumCell Y' = c} : Set _) := hYc
      rw [Set.indicator_of_mem hmem]
    · have hmem : Y ∉ ({Y' : Fin d → FiniteMeasure ℝ | sumCell Y' = c} : Set _) :=
        fun h => hYc h
      rw [Set.indicator_of_notMem hmem]
      exact hσ_nn c hc
  -- S is measurable, integrable, and dominates f
  have hSmeas : Measurable S := measurable_runEnvelope σ K
  have hS0 : ∀ Y, 0 ≤ S Y := fun Y =>
    Finset.sum_nonneg (fun c hc => hterm0 Y c hc)
  have hSint : Integrable S (Measure.pi fun _ : Fin d => μ) := by
    refine (integrable_const (∑ c ∈ K, σ c)).mono' hSmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun Y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hS0 Y)]
        exact Finset.sum_le_sum (fun c hc => htermle Y c hc)))
  have hpt : ∀ Y, f Y ≤ S Y := by
    intro Y
    by_cases hY : sumCell Y ∈ K
    · have hmem : Y ∈ ({Y' : Fin d → FiniteMeasure ℝ | sumCell Y' = sumCell Y} :
        Set (Fin d → FiniteMeasure ℝ)) := rfl
      calc f Y ≤ σ (sumCell Y) := hσ Y
        _ = {Y' : Fin d → FiniteMeasure ℝ | sumCell Y' = sumCell Y}.indicator
              (fun _ => σ (sumCell Y)) Y :=
              (Set.indicator_of_mem (f := fun _ => σ (sumCell Y)) hmem).symm
        _ ≤ S Y := by
            refine Finset.single_le_sum (f := fun c : ℕ =>
              {Y' : Fin d → FiniteMeasure ℝ | sumCell Y' = c}.indicator
                (fun _ => σ c) Y) ?_ hY
            intro c hc
            exact hterm0 Y c hc
    · rw [hzero Y hY]
      exact hS0 Y
  have hstep : (∫ Y, f Y ∂(Measure.pi fun _ : Fin d => μ))
      ≤ (∫ Y, S Y ∂(Measure.pi fun _ : Fin d => μ)) :=
    integral_mono_of_nonneg (Filter.Eventually.of_forall hnn)
      hSint (Filter.Eventually.of_forall hpt)
  -- per-class integrals
  have hintc : ∀ c ∈ K,
      (∫ Y : Fin d → FiniteMeasure ℝ, {Y' : Fin d → FiniteMeasure ℝ |
          sumCell Y' = c}.indicator (fun _ => σ c) Y
        ∂(Measure.pi fun _ : Fin d => μ))
        = σ c * (Measure.pi fun _ : Fin d => μ).real
          {Y : Fin d → FiniteMeasure ℝ | sumCell Y = c} := by
    intro c hc
    have hmeasc : MeasurableSet ({Y' : Fin d → FiniteMeasure ℝ | sumCell Y' = c} :
      Set (Fin d → FiniteMeasure ℝ)) := measurableSet_sumCell c
    rw [integral_indicator_const (σ c) hmeasc]
    simp [mul_comm]
  -- the envelope integral splits over K
  have hSsplit : (∫ Y, S Y ∂(Measure.pi fun _ : Fin d => μ))
      = ∑ c ∈ K, (∫ Y : Fin d → FiniteMeasure ℝ, {Y' : Fin d → FiniteMeasure ℝ |
          sumCell Y' = c}.indicator (fun _ => σ c) Y
        ∂(Measure.pi fun _ : Fin d => μ)) := by
    simp only [hS]
    exact integral_finsetSum K (fun c _ =>
      ((integrable_const (σ c)).indicator (measurableSet_sumCell c)))
  refine le_trans hstep ?_
  rw [hSsplit]
  exact Finset.sum_le_sum (fun c hc => by
    rw [hintc c hc]
    exact mul_le_mul_of_nonneg_left (hcell c hc) (hσ_nn c hc))

end PrimeGap182D1
