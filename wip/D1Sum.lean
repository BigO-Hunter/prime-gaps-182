import Pg182D1.D1Mgf

/-!
# D1SUM.lean — the coarse-run cell envelope for the 38-coordinate trial

The discrete law of the frozen programs is a law on the SUM of the 38
coordinate cell indices (the coarse-run index `r = Σ_j trialCellIndex (Y j)`,
0 ≤ r < 393216). This module lifts the per-coordinate D1-CELL envelope to the
sum level:

    μ^{d}{Σ_j cell(X_j) = c}  ≤  exp(s·(c+d)·mesh) · (E[e^{-s·mass}])^d,

with the per-coordinate MGF further bounded by `mgf_fragmentLaw_le_finset`.
Every quantity on the right is computable rational-exponential data: this is
the per-coarse-bin majorant of the discrete law.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal
open scoped NNReal

namespace PrimeGap182D1

variable {d : ℕ}

/-- The ℝ-coercion commutes with finite sums in ℝ≥0. -/
theorem nnreal_sum_coe {ι : Type*} [DecidableEq ι] (f : ι → ℝ≥0) (s : Finset ι) :
    ((∑ i ∈ s, f i : ℝ≥0) : ℝ) = ∑ i ∈ s, ((f i : ℝ≥0) : ℝ) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, NNReal.coe_add, ih]

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

/-- On the event `Σ cell = c` (with `d ≥ 1`), the total mass is `< (c+d)·mesh`. -/
theorem mass_lt_of_sumCell {Y : Fin d → FiniteMeasure ℝ} {c : ℕ} (hd : 0 < d)
    (h : sumCell Y = c) :
    (∑ j, (Y j).mass : ℝ) < (((c : ℝ) + d) * (trialMesh : ℝ)) := by
  have hperj : ∀ j : Fin d, ((Y j).mass : ℝ)
      < ((trialCellIndex (Y j) : ℝ) + 1) * (trialMesh : ℝ) :=
    fun j => cell_mass_lt rfl
  have hsum : (∑ j, (Y j).mass : ℝ)
      < (∑ j : Fin d, ((trialCellIndex (Y j) : ℝ) + 1) * (trialMesh : ℝ)) := by
    refine Finset.sum_lt_sum
      (f := fun j => ((Y j).mass : ℝ))
      (g := fun j => ((trialCellIndex (Y j) : ℝ) + 1) * (trialMesh : ℝ))
      (fun j _ => le_of_lt (hperj j))
      ⟨⟨0, by omega⟩, Finset.mem_univ _, hperj ⟨0, by omega⟩⟩
  have hrhs : (∑ j : Fin d, ((trialCellIndex (Y j) : ℝ) + 1) * (trialMesh : ℝ))
      = (((c : ℝ) + d) * (trialMesh : ℝ)) := by
    have hsc : (∑ j : Fin d, trialCellIndex (Y j)) = c := h
    rw [Finset.sum_mul]
    rw [show (∑ j : Fin d, ((trialCellIndex (Y j) : ℝ) + 1))
        = (((∑ j : Fin d, trialCellIndex (Y j) : ℕ) : ℝ) + (d : ℝ)) from by
      rw [Finset.sum_add_distrib, map_sum (Nat.cast : ℕ →+* ℝ) _ Finset.univ,
        Finset.card_univ, hsc]]
    ring
  rw [hrhs] at hsum
  exact hsum

theorem massExp_pi (s : ℝ) (Y : Fin d → FiniteMeasure ℝ) :
    ENNReal.ofReal (Real.exp (-s * ((∑ j, (Y j).mass : ℝ))))
      = ∏ j, massExp s (Y j) := by
  rw [show ((∑ j, (Y j).mass : ℝ≥0) : ℝ) = ∑ j, ((Y j).mass : ℝ) from
    nnreal_sum_coe (fun j => (Y j).mass) Finset.univ,
    ENNReal.ofReal_prod_of_nonneg (fun j _ => Real.exp_nonneg _), ← Real.exp_sum]
  congr 1
  rw [← Finset.sum_mul]
  simp [mul_comm]

theorem measurable_piMassExp (s : ℝ) :
    Measurable (fun Y : Fin d → FiniteMeasure ℝ =>
      ENNReal.ofReal (Real.exp (-s * ((∑ j, (Y j).mass : ℝ))))) := by
  have hEq : (fun Y : Fin d → FiniteMeasure ℝ =>
      ENNReal.ofReal (Real.exp (-s * ((∑ j, (Y j).mass : ℝ)))))
      = fun Y => ∏ j, massExp s (Y j) := funext (massExp_pi s)
  rw [hEq]
  clear hEq
  induction d with
  | zero => simpa using measurable_const
  | succ n ih =>
      have h : (fun Y : Fin (n + 1) → FiniteMeasure ℝ => ∏ j, massExp s (Y j))
          = fun Y => (∏ i : Fin n, massExp s (Y i.castSucc))
            * massExp s (Y (Fin.last n)) := by
        funext Y
        show ∏ j, _ = _
        rw [Fin.prod_univ_castSucc]
      rw [h]
      have hres : Measurable
          (fun (Y : Fin (n + 1) → FiniteMeasure ℝ) (i : Fin n) => Y i.castSucc) :=
        measurable_pi_iff.mpr (fun i => measurable_pi_apply (i.castSucc))
      exact ((ih.comp hres).mul
        ((measurable_massExp s).comp (measurable_pi_apply (Fin.last n))))

/-- The MGF of the total mass over the `d`-fold product is the `d`-th power
of the per-coordinate MGF. -/
theorem lintegral_massExp_pi (μ : Measure (FiniteMeasure ℝ))
    [IsProbabilityMeasure μ] (s : ℝ) :
    (∫⁻ Y : Fin d → FiniteMeasure ℝ,
        ENNReal.ofReal (Real.exp (-s * ((∑ j, (Y j).mass : ℝ)))))
        ∂(Measure.pi fun _ : Fin d => μ)
      = (∫⁻ X, massExp s X ∂μ) ^ d := by
  have hEq : (fun Y : Fin d → FiniteMeasure ℝ =>
      ENNReal.ofReal (Real.exp (-s * ((∑ j, (Y j).mass : ℝ)))))
      = fun Y => ∏ j, massExp s (Y j) := funext (massExp_pi s)
  rw [hEq]
  rw [ProbabilityTheory.lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ
    (fun i (x : Fin d → FiniteMeasure ℝ) => massExp s (x i))
    (ProbabilityTheory.iIndepFun_pi (fun _ => (measurable_massExp s).aemeasurable))
    (fun i => (measurable_massExp s).comp (measurable_pi_apply i))]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- D1-SUM: the probability that the `d`-tuple lands in coarse run `c` is at
most the exp-sandwich at the total level. -/
theorem sum_cell_probability_le (μ : Measure (FiniteMeasure ℝ))
    [IsProbabilityMeasure μ] (hd : 0 < d) (c : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    (Measure.pi fun _ : Fin d => μ).real {Y : Fin d → FiniteMeasure ℝ | sumCell Y = c}
      ≤ Real.exp (s * (((c : ℝ) + d) * (trialMesh : ℝ))) *
        (((∫⁻ X, massExp s X ∂μ) ^ d).toReal) := by
  have hprob : IsProbabilityMeasure (Measure.pi fun _ : Fin d => μ) := by
    infer_instance
  set ν : Measure (Fin d → FiniteMeasure ℝ) := Measure.pi fun _ : Fin d => μ with hν
  set A : Set (Fin d → FiniteMeasure ℝ) := {Y : Fin d → FiniteMeasure ℝ | sumCell Y = c} with hA
  set b : ℝ := ((c : ℝ) + d) * (trialMesh : ℝ) with hb
  have hb0 : (0 : ℝ) ≤ b := by
    have h1 : (0 : ℝ) ≤ ((c : ℝ) + d) := by positivity
    nlinarith [trialMesh_pos]
  set g : Fin d → FiniteMeasure ℝ → ℝ≥0∞ :=
    fun Y => ENNReal.ofReal (Real.exp (-s * ((∑ j, (Y j).mass : ℝ))))) with hg
  have hAmeas : MeasurableSet A := measurableSet_sumCell c
  have hge : ∀ Y ∈ A, ENNReal.ofReal (Real.exp (-s * b)) ≤ g Y := by
    intro Y hY
    have hmass := mass_lt_of_sumCell hd hY
    have hneg : -s * b ≤ -s * ((∑ j, (Y j).mass : ℝ)) := by
      nlinarith [hs, hmass]
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hneg)
  have hAle : ν A ≤ 1 := by
    rw [← hprob.measure_univ]
    exact measure_mono (Set.subset_univ A)
  have hc1 : ENNReal.ofReal (Real.exp (-s * b)) ≤ 1 := by
    refine ENNReal.ofReal_le_one.mpr (Real.exp_le_one_iff.mpr ?_)
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) hb0
  have hkey : ENNReal.ofReal (Real.exp (-s * b)) * ν A
      ≤ ∫⁻ Y, g Y ∂ν := by
    have hint1 : ∫⁻ Y, A.indicator (fun _ => ENNReal.ofReal (Real.exp (-s * b))) Y ∂ν
        = ENNReal.ofReal (Real.exp (-s * b)) * ν A :=
      lintegral_indicator_const hAmeas _
    have hint2 : ∫⁻ Y, A.indicator g Y ∂ν
        = ∫⁻ Y in A, g Y ∂ν := lintegral_indicator hAmeas g
    have hpt : (fun Y => A.indicator (fun _ => ENNReal.ofReal (Real.exp (-s * b))) Y) ≤
        (fun Y => A.indicator g Y) := by
      intro Y
      by_cases hY : Y ∈ A
      · simp only [hY, Set.indicator_of_mem]
        exact hge Y hY
      · simp only [Set.indicator_of_notMem hY]
        exact le_refl _
    calc ENNReal.ofReal (Real.exp (-s * b)) * ν A
        = ∫⁻ Y, A.indicator (fun _ => ENNReal.ofReal (Real.exp (-s * b))) Y ∂ν := hint1.symm
      _ ≤ ∫⁻ Y, A.indicator g Y ∂ν := lintegral_mono hpt
      _ = ∫⁻ Y in A, g Y ∂ν := hint2
      _ ≤ ∫⁻ Y, g Y ∂ν := by
          simpa using lintegral_mono_set (Set.subset_univ A)
  have hIfin : (∫⁻ Y, g Y ∂ν) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
    have h1 : (∫⁻ Y, g Y ∂ν)
        ≤ (∫⁻ _ : Fin d → FiniteMeasure ℝ, (1 : ℝ≥0∞) ∂ν) :=
      lintegral_mono (fun Y => by
        unfold g
        refine ENNReal.ofReal_le_one.mpr (Real.exp_le_one_iff.mpr ?_)
        have hpos : (0 : ℝ) ≤ (∑ j, (Y j).mass : ℝ) := by
          refine Finset.sum_nonneg (fun j _ => ?_)
          exact (Y j).mass.coe_nonneg
        exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs) hpos)
    rw [lintegral_one, hprob.measure_univ] at h1
    exact h1
  have hcfin : ENNReal.ofReal (Real.exp (-s * b)) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top hc1
  have hmul : ENNReal.ofReal (Real.exp (-s * b)) * ν A ≠ ⊤ :=
    ENNReal.mul_ne_top hcfin (ne_top_of_le_ne_top ENNReal.one_ne_top hAle)
  have hstep := (ENNReal.toReal_le_toReal hmul hIfin).mp hkey
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_nonneg (-s * b))] at hstep
  have hInt : (∫⁻ Y, g Y ∂ν) = (∫⁻ X, massExp s X ∂μ) ^ d := by
    have hEq : g = fun Y => ENNReal.ofReal (Real.exp (-s * ((∑ j, (Y j).mass : ℝ))))) := rfl
    rw [hEq, lintegral_massExp_pi]
  have hbpos : 0 < Real.exp (-s * b) := Real.exp_pos _
  have hstep' : ((∫⁻ X, massExp s X ∂μ) ^ d).toReal
      ≤ ((ν A : ℝ≥0∞).toReal) * Real.exp (-s * b) := by
    have hcomm := mul_comm (Real.exp (-s * b)) ((ν A : ℝ≥0∞).toReal)
    rw [hInt]
    linarith [hstep, hcomm]
  have hfin2 : Real.exp (s * b) * ((∫⁻ X, massExp s X ∂μ) ^ d).toReal
      = ((∫⁻ X, massExp s X ∂μ) ^ d).toReal / Real.exp (-s * b) := by
    rw [neg_mul, Real.exp_neg, div_eq_inv_mul, inv_inv]
    ring
  have hmassreal : ν.real A = ((ν A : ℝ≥0∞)).toReal := rfl
  rw [hmassreal, hfin2]
  exact (le_div_iff₀ hbpos).mpr hstep'

end PrimeGap182D1
