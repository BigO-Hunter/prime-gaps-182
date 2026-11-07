import Pg182D1.D1Cell

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

/-- The sum of the coordinate cell indices (the coarse-run index). -/
def sumCell (Y : Fin d → FiniteMeasure ℝ) : ℕ := ∑ j, trialCellIndex (Y j)

theorem measurable_sumCell :
    Measurable (fun Y : Fin d → FiniteMeasure ℝ => sumCell Y) := by
  induction d with
  | zero => simpa [sumCell] using measurable_const
  | succ n ih =>
      have h : (fun Y : Fin (n + 1) → FiniteMeasure ℝ => sumCell Y)
          = fun Y => sumCell (fun i : Fin n => Y i.castSucc)
            + trialCellIndex (Y (Fin.last n)) := by
        funext Y
        show ∑ i : Fin (n + 1), trialCellIndex (Y i) = _
        unfold sumCell
        rw [Fin.sum_univ_castSucc]
      rw [h]
      have hres : Measurable
          (fun (Y : Fin (n + 1) → FiniteMeasure ℝ) (i : Fin n) => Y i.castSucc) :=
        measurable_pi_iff.mpr (fun i => measurable_pi_apply (i.castSucc))
      exact (ih.comp hres).add
        ((measurable_cellIndex).comp (measurable_pi_apply (Fin.last n)))

theorem measurableSet_sumCell (c : ℕ) :
    MeasurableSet {Y : Fin d → FiniteMeasure ℝ | sumCell Y = c} :=
  measurable_sumCell (measurableSet_singleton c)

/-- Measurability of a finite σ-weighted sum of class indicators. -/
theorem measurable_runEnvelope (σ : ℕ → ℝ) (K : Finset ℕ) :
    Measurable fun Y : Fin d → FiniteMeasure ℝ =>
      ∑ c ∈ K, σ c * Set.indicator
        {Y' : Fin d → FiniteMeasure ℝ | sumCell Y' = c} (fun _ => (1 : ℝ)) Y := by
  classical
  induction K using Finset.induction_on with
  | empty => simpa using measurable_const
  | @insert c K hc ih =>
      have h1 : Measurable (fun _ : Fin d → FiniteMeasure ℝ => (σ c : ℝ)) :=
        measurable_const
      have h2 : Measurable (fun Y : Fin d → FiniteMeasure ℝ =>
          {Y' : Fin d → FiniteMeasure ℝ | sumCell Y' = c}.indicator
            (fun _ => (1 : ℝ)) Y) :=
        (measurable_const).indicator (measurableSet_sumCell c)
      exact (h1.mul h2).add ih

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
    ∑ c ∈ K, σ c * Set.indicator
      {Y' : Fin d → FiniteMeasure ℝ | sumCell Y' = c} (fun _ => (1 : ℝ)) Y with hS
  -- S is measurable and integrable on the probability measure
  have hSmeas : Measurable S := measurable_runEnvelope σ K
  have hSint : Integrable S (Measure.pi fun _ : Fin d => μ) := by
    have hsumnn : (0 : ℝ) ≤ ∑ c ∈ K, σ c := Finset.sum_nonneg hσ_nn
    refine (integrable_const (∑ c ∈ K, σ c)).mono' hSmeas.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall (fun Y => ?_)
    have hS0 : (0 : ℝ) ≤ S Y := by
      rw [hS]
      refine Finset.sum_nonneg (fun c hc => ?_)
      by_cases hc' : c = sumCell Y
      · subst hc'
        simp [Set.indicator_of_mem]
        exact hσ_nn c hc
      · simp [Set.indicator_of_notMem hc']
    have hSle : S Y ≤ ∑ c ∈ K, σ c := by
      rw [hS]
      refine Finset.sum_le_sum (fun c hc => ?_)
      by_cases hc' : c = sumCell Y
      · subst hc'
        simp [Set.indicator_of_mem]
        exact hσ_nn c hc
      · simp [Set.indicator_of_notMem hc']
        linarith [hσ_nn c hc]
    exact abs_le.2 ⟨by linarith [hS0], by linarith [hSle]⟩
  -- pointwise domination f ≤ S
  have hpt : ∀ Y, f Y ≤ S Y := by
    intro Y
    by_cases hY : sumCell Y ∈ K
    · calc f Y ≤ σ (sumCell Y) := hσ Y
        _ ≤ S Y := by
            rw [hS]
            refine Finset.single_le_sum (f := fun c =>
              σ c * Set.indicator
                {Y' : Fin d → FiniteMeasure ℝ | sumCell Y' = c}
                (fun _ => (1 : ℝ)) Y) ?_ ?_
            · intro c hc
              by_cases hc' : c = sumCell Y
              · subst hc'
                simp [Set.indicator_of_mem]
              · simp [Set.indicator_of_notMem hc']
                exact hσ_nn c hc
            · exact Finset.mem_union_left _ (Finset.mem_univ _)
    · have hf0 : f Y = 0 := hzero Y hY
      rw [hf0]
      refine Finset.sum_nonneg (fun c hc => ?_)
      by_cases hc' : c = sumCell Y
      · exact absurd hY (hc' ▸ hc)
      · simp [Set.indicator_of_notMem hc']
  -- the monotone step
  have hstep : (∫ Y, f Y ∂(Measure.pi fun _ : Fin d => μ))
      ≤ (∫ Y, S Y ∂(Measure.pi fun _ : Fin d => μ)) :=
    integral_mono_of_nonneg (fun Y => hnn Y)
      (fun Y => hpt Y) hSint
  -- per-class integrals and the mass majorization
  have hclass : ∀ c ∈ K,
      (∫ Y : Fin d → FiniteMeasure ℝ, σ c * Set.indicator
          {Y' : Fin d → FiniteMeasure ℝ | sumCell Y' = c} (fun _ => (1 : ℝ)) Y
        ∂(Measure.pi fun _ : Fin d => μ))
        ≤ σ c * env c := by
    intro c hc
    have hmeasc : MeasurableSet {Y : Fin d → FiniteMeasure ℝ | sumCell Y = c} :=
      measurableSet_sumCell c
    have heq : (fun Y : Fin d → FiniteMeasure ℝ =>
        σ c * Set.indicator {Y' : Fin d → FiniteMeasure ℝ | sumCell Y' = c}
          (fun _ => (1 : ℝ)) Y)
      = fun Y => Set.indicator {Y' : Fin d → FiniteMeasure ℝ | sumCell Y' = c}
          (fun _ => (σ c : ℝ)) Y := by
      funext Y
      by_cases hY : sumCell Y = c
      · simp [hY, Set.indicator_of_mem]
      · simp [Set.indicator_of_notMem hY]
    have hintc : (∫ Y : Fin d → FiniteMeasure ℝ, σ c * Set.indicator
        {Y' : Fin d → FiniteMeasure ℝ | sumCell Y' = c} (fun _ => (1 : ℝ)) Y
      ∂(Measure.pi fun _ : Fin d => μ))
      = σ c * (Measure.pi fun _ : Fin d => μ).real
        {Y : Fin d → FiniteMeasure ℝ | sumCell Y = c} := by
      rw [heq, integral_indicator hmeasc, set_integral_const]
      simp [Measure.real, mul_comm]
    rw [hintc]
    exact mul_le_mul_of_nonneg_left (hcell c hc) (hσ_nn c hc)
  -- the envelope integral splits over K
  have hSsplit : (∫ Y, S Y ∂(Measure.pi fun _ : Fin d => μ))
      = ∑ c ∈ K, (∫ Y : Fin d → FiniteMeasure ℝ, σ c * Set.indicator
          {Y' : Fin d → FiniteMeasure ℝ | sumCell Y' = c} (fun _ => (1 : ℝ)) Y
        ∂(Measure.pi fun _ : Fin d => μ)) := by
    rw [hS]
    refine integral_finsetSum K (fun c hc => ?_)
    exact ((integrable_const (σ c)).indicator (measurableSet_sumCell c))
  refine le_trans hstep ?_
  rw [hSsplit]
  exact Finset.sum_le_sum (fun c hc => hclass c hc)

end PrimeGap182D1
