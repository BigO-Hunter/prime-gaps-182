/-
Copyright (c) 2026 ...
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.ProductMeasure

/-!
# Integration of product families over `Measure.infinitePi`

Mathlib has the finite-index identity `MeasureTheory.integral_fintype_prod_eq_prod`, and the
nonnegative infinite-index analogue follows from `lintegral_tsum`.  There is no analogue for
Bochner integrals: for a countable index type `ι`, a family of probability measures `μ i`, and
Bochner-integrable `f i : X i → ℂ`,

  `∫ x, ∏' i, f i (x i) ∂(Measure.infinitePi μ) = ∏' i, ∫ x, f i x ∂(μ i)`.

Monotone convergence cannot be used because the integrands are not nonnegative; instead the proof
takes the limit of the finite-subset products along `atTop` on `Finset ι`, dominated by `1` (the
hypothesis `‖f i x‖ ≤ 1`).  The pointwise convergence comes from
`multipliable_one_add_of_summable`, fed by a.e. summability of `∑ i, ‖f i (x i) - 1‖`, which is
Tonelli's theorem over the product measure.

## Main results

* `MeasureTheory.integral_finset_prod_infinitePi` — the finite-subset case (the marginal of
  `Measure.infinitePi` on a `Finset` is `Measure.pi`, then `integral_fintype_prod_eq_prod`).
* `MeasureTheory.ae_summable_norm_sub_one_infinitePi` — a.e. summability of `‖f i (x i) - 1‖`.
* `MeasureTheory.hasProd_integral_tprod_infinitePi` — the convergence form of the main theorem.
* `MeasureTheory.integral_tprod_infinitePi` — the equation form.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace MeasureTheory

variable {ι : Type*} [Countable ι]
variable {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
variable {μ : (i : ι) → Measure (X i)} [hμ : ∀ i, IsProbabilityMeasure (μ i)]

omit [Countable ι] in
/-- **The finite-subset product integral over `Measure.infinitePi`.**  For a `Finset` of
coordinates, the integral of the product family is the product of the integrals. -/
theorem integral_finset_prod_infinitePi {f : (i : ι) → X i → ℂ}
    (hf : ∀ i, AEStronglyMeasurable (f i) (μ i)) (s : Finset ι) :
    ∫ x, ∏ i ∈ s, f i (x i) ∂(Measure.infinitePi μ) = ∏ i ∈ s, ∫ x, f i x ∂(μ i) := by
  classical
  have hp : MeasurePreserving (Finset.restrict (π := X) s) (Measure.infinitePi μ)
      (Measure.pi fun i : s => μ i.1) :=
    ⟨Finset.measurable_restrict _, Measure.infinitePi_map_restrict μ⟩
  have hgmeas : AEStronglyMeasurable (fun y : (i : s) → X i.1 => ∏ i, f i.1 (y i))
      (Measure.pi fun i : s => μ i.1) := by
    have := Finset.aestronglyMeasurable_fun_prod (μ := Measure.pi fun j : s => μ j.1)
      (s := (Finset.univ : Finset s)) (f := fun (i : s) (y : (j : s) → X j.1) => f i.1 (y i))
      (fun i _ => (hf i.1).comp_quasiMeasurePreserving (Measure.quasiMeasurePreserving_eval _ i))
    simpa using this
  have key : ∫ y : (i : s) → X i.1, ∏ i, f i.1 (y i) ∂(Measure.pi fun i : s => μ i.1)
      = ∏ i : s, ∫ x, f i.1 x ∂(μ i.1) :=
    integral_fintype_prod_eq_prod (f := fun (i : s) (y : X i.1) => f i.1 y)
  have hcomp : ∫ x : (i : ι) → X i, ∏ i ∈ s, f i (x i) ∂(Measure.infinitePi μ)
      = ∫ y : (i : s) → X i.1, ∏ i, f i.1 (y i) ∂(Measure.pi fun i : s => μ i.1) := by
    rw [← hp.map_eq, integral_map hp.aemeasurable (by rw [hp.map_eq]; exact hgmeas)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [Finset.restrict]
    exact (Finset.prod_coe_sort s (fun i => f i (x i))).symm
  rw [hcomp, key, Finset.prod_coe_sort (s := s) (f := fun i => ∫ x, f i x ∂(μ i))]

/-- **A.e. summability of the deviations from `1`.**  Tonelli over the product measure turns the
hypothesis on the sum of the `∫⁻`-norms into a.e. summability of `∑ i, ‖f i (x i) - 1‖`. -/
theorem ae_summable_norm_sub_one_infinitePi {f : (i : ι) → X i → ℂ}
    (hf : ∀ i, AEStronglyMeasurable (f i) (μ i))
    (hsum : (∑' i, ∫⁻ x, (‖f i x - 1‖₊ : ℝ≥0∞) ∂(μ i)) ≠ ⊤) :
    ∀ᵐ x ∂(Measure.infinitePi μ), Summable fun i => ‖f i (x i) - 1‖ := by
  have hφ : ∀ i, AEMeasurable (fun y => (‖f i y - 1‖₊ : ℝ≥0∞)) (μ i) := fun i =>
    (((hf i).aemeasurable.sub aestronglyMeasurable_const.aemeasurable).nnnorm).coe_nnreal_ennreal
  have hmeas : ∀ i, AEMeasurable (fun x : (j : ι) → X j => (‖f i (x i) - 1‖₊ : ℝ≥0∞))
      (Measure.infinitePi μ) := by
    intro i
    exact ((((hf i).comp_quasiMeasurePreserving
      (measurePreserving_eval_infinitePi μ i).quasiMeasurePreserving).aemeasurable.sub
        aestronglyMeasurable_const.aemeasurable).nnnorm).coe_nnreal_ennreal
  have hcomp : ∀ i, ∫⁻ x : (j : ι) → X j, (‖f i (x i) - 1‖₊ : ℝ≥0∞) ∂(Measure.infinitePi μ)
      = ∫⁻ y, (‖f i y - 1‖₊ : ℝ≥0∞) ∂(μ i) := by
    intro i
    have hmap := Measure.infinitePi_map_eval (μ := μ) (i := i)
    rw [← hmap]
    have hf' : AEMeasurable (fun y => (‖f i y - 1‖₊ : ℝ≥0∞))
        (Measure.map (fun x : (j : ι) → X j => x i) (Measure.infinitePi μ)) := by
      rw [hmap]; exact hφ i
    exact (lintegral_map' hf' (measurable_pi_apply i).aemeasurable).symm
  have hfin : ∫⁻ x, ∑' i, (‖f i (x i) - 1‖₊ : ℝ≥0∞) ∂(Measure.infinitePi μ) ≠ ⊤ := by
    rw [lintegral_tsum hmeas]
    simpa only [hcomp] using hsum
  filter_upwards [ae_lt_top' (AEMeasurable.tsum hmeas) hfin] with x hx
  have hx' : Summable fun i => (‖f i (x i) - 1‖₊ : ℝ≥0) :=
    ENNReal.tsum_coe_ne_top_iff_summable.mp (ne_of_lt hx)
  simpa only [coe_nnnorm] using NNReal.summable_coe.mpr hx'

/-- **The Bochner product integral over `Measure.infinitePi`, convergence form.**

For a countable index type, probability measures `μ i`, and measurable `f i : X i → ℂ` bounded by
`1` in norm, with `∑ i, ∫⁻ x, ‖f i x - 1‖` finite, the family of integrals is multipliable and its
product is the integral of the pointwise infinite product. -/
theorem hasProd_integral_tprod_infinitePi {f : (i : ι) → X i → ℂ}
    (hf : ∀ i, AEStronglyMeasurable (f i) (μ i))
    (hb : ∀ i, ∀ᵐ x ∂(μ i), ‖f i x‖ ≤ 1)
    (hsum : (∑' i, ∫⁻ x, (‖f i x - 1‖₊ : ℝ≥0∞) ∂(μ i)) ≠ ⊤) :
    HasProd (fun i => ∫ x, f i x ∂(μ i))
      (∫ x, ∏' i, f i (x i) ∂(Measure.infinitePi μ)) := by
  classical
  -- the a.e. norm bound `∀ i, ‖f i (x i)‖ ≤ 1`
  have hbnd : ∀ᵐ x ∂(Measure.infinitePi μ), ∀ i, ‖f i (x i)‖ ≤ 1 := by
    rw [ae_all_iff]
    intro i
    exact (measurePreserving_eval_infinitePi μ i).quasiMeasurePreserving.ae (hb i)
  -- a.e. pointwise multipliability
  have hconv : ∀ᵐ x ∂(Measure.infinitePi μ),
      Tendsto (fun s : Finset ι => ∏ i ∈ s, f i (x i)) atTop (𝓝 (∏' i, f i (x i))) := by
    filter_upwards [ae_summable_norm_sub_one_infinitePi hf hsum] with x hx
    have hM : Multipliable fun i => f i (x i) := by
      have h := multipliable_one_add_of_summable (f := fun i => f i (x i) - 1) hx
      have hfun : (fun i => 1 + (f i (x i) - 1)) = fun i => f i (x i) := by
        funext i; ring
      rwa [hfun] at h
    exact hM.hasProd
  -- dominated convergence over the filter `atTop` on `Finset ι`
  have hDCT := tendsto_integral_filter_of_dominated_convergence
    (l := atTop) (F := fun (s : Finset ι) (x : (i : ι) → X i) => ∏ i ∈ s, f i (x i))
    (f := fun x => ∏' i, f i (x i)) (bound := fun _ => (1 : ℝ))
    (Filter.Eventually.of_forall fun s =>
      Finset.aestronglyMeasurable_fun_prod s fun i _ =>
        (hf i).comp_quasiMeasurePreserving
          (measurePreserving_eval_infinitePi μ i).quasiMeasurePreserving)
    (by
      filter_upwards with s
      filter_upwards [hbnd] with x hx
      have hle : ∏ i ∈ s, ‖f i (x i)‖₊ ≤ 1 := Finset.prod_le_one fun i _ => by exact_mod_cast hx i
      have hnorm : ‖∏ i ∈ s, f i (x i)‖₊ = ∏ i ∈ s, ‖f i (x i)‖₊ := by simp
      calc ‖∏ i ∈ s, f i (x i)‖ = (‖∏ i ∈ s, f i (x i)‖₊ : ℝ) := (coe_nnnorm _).symm
        _ = ((∏ i ∈ s, ‖f i (x i)‖₊ : ℝ≥0) : ℝ) := by rw [hnorm]
        _ ≤ 1 := by exact_mod_cast hle)
    (integrable_const 1) hconv
  rw [HasProd]
  refine hDCT.congr' (Filter.Eventually.of_forall fun s => ?_)
  exact integral_finset_prod_infinitePi hf s

/-- **The Bochner product integral over `Measure.infinitePi`, equation form.** -/
theorem integral_tprod_infinitePi {f : (i : ι) → X i → ℂ}
    (hf : ∀ i, AEStronglyMeasurable (f i) (μ i))
    (hb : ∀ i, ∀ᵐ x ∂(μ i), ‖f i x‖ ≤ 1)
    (hsum : (∑' i, ∫⁻ x, (‖f i x - 1‖₊ : ℝ≥0∞) ∂(μ i)) ≠ ⊤) :
    ∫ x, ∏' i, f i (x i) ∂(Measure.infinitePi μ) = ∏' i, ∫ x, f i x ∂(μ i) :=
  (hasProd_integral_tprod_infinitePi hf hb hsum).tprod_eq.symm

end MeasureTheory
