import Pg182D1.D1Cell

/-!
# D1MGF.lean — the mass MGF of the fragment law, bounded per finite band set

The D1 hard core. For every finite set `S` of dyadic bands, the MGF of the
total mass under the full `fragmentLaw ζ` is bounded by the product of the
per-band MGFs over `S`:

    E[e^{-s·mass}]  ≤  ∏_{k∈S} E_k[e^{-s·mass}],

because (i) different bands are independent under the infinite product, and
(ii) the total mass dominates any finite partial band sum, so `e^{-s·total}`
is (a.e.) at most the finite product `∏_S e^{-s·mass_k}`.

Taking `S` growing to the whole support turns this into the exact
exp-sandwich `E[e^{-s·mass}] ≤ exp(∫_{(0,ζ]}(e^{-su}-1)/u du)` (the closed
form per band is a refinement lemma; the structural bound is what the D1
chain consumes).
-/

noncomputable section
open MeasureTheory
open scoped ENNReal
open scoped NNReal

namespace PrimeGap182D1

/-- The total band mass of a band configuration (an ℝ≥0∞ tsum). -/
noncomputable def bandMass (ω : ℤ → FiniteMeasure ℝ) : ℝ≥0∞ :=
  ∑' k : ℤ, ((ω k).mass : ℝ≥0∞)

/-- The product-of-factors function: `ω ↦ ∏_{k∈S} e^{-s·mass(ω k)}`. -/
noncomputable def bandExpProd (s : ℝ) (S : Finset ℤ) (ω : ℤ → FiniteMeasure ℝ) : ℝ≥0∞ :=
  ∏ k ∈ S, massExp s (ω k)

theorem measurable_bandExpProd (s : ℝ) (S : Finset ℤ) :
    Measurable (bandExpProd s S) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      have h1 : bandExpProd s ∅ = fun _ => (1 : ℝ≥0∞) :=
        funext (fun _ => (Finset.prod_empty))
      rw [h1]
      exact measurable_const
  | @insert i S hi ih =>
      have h2 : bandExpProd s (insert i S)
          = fun ω => massExp s (ω i) * bandExpProd s S ω :=
        funext (fun ω => by unfold bandExpProd; rw [Finset.prod_insert hi])
      rw [h2]
      exact ((measurable_massExp s).comp (measurable_pi_apply i)).mul ih

/-- The truncated mass exponential of a band configuration (toNNReal of the
total tsum; exactly the mass of `finiteFragments ω`). -/
noncomputable def bandExpTrunc (s : ℝ) (ω : ℤ → FiniteMeasure ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-s * ((bandMass ω).toNNReal : ℝ)))

/-- The mass of `finiteFragments ω` is exactly the truncated total band mass
(convergent branch: the sum's mass is the tsum; fallback branch: both are 0). -/
theorem mass_finiteFragments (ω : ℤ → FiniteMeasure ℝ) :
    (finiteFragments ω).mass = (bandMass ω).toNNReal := by
  classical
  by_cases hω : IsFiniteMeasure (Measure.sum (fun k : ℤ => (ω k : Measure ℝ)))
  · have key : finiteFragments ω = ⟨Measure.sum (fun k : ℤ => (ω k : Measure ℝ)), hω⟩ := by
      simp [finiteFragments, hω]
      rfl
    rw [key]
    show ((Measure.sum (fun k : ℤ => (ω k : Measure ℝ))) Set.univ).toNNReal = _
    rw [Measure.sum_apply _ MeasurableSet.univ,
      tsum_congr (fun k => (FiniteMeasure.ennreal_mass (μ := ω k)).symm)]
    rfl
  · have key : finiteFragments ω = 0 := by
      simp [finiteFragments, hω]
    have hsumtop : ((Measure.sum (fun k : ℤ => (ω k : Measure ℝ))) Set.univ) = ⊤ := by
      by_contra hc
      exact hω ⟨lt_top_iff_ne_top.mpr hc⟩
    rw [key, bandMass, ← tsum_congr (fun k => (FiniteMeasure.ennreal_mass (μ := ω k)).symm),
      ← Measure.sum_apply _ MeasurableSet.univ, hsumtop]
    simp

/-- Pointwise identity: the mass exponential of `finiteFragments ω` is the
exponential of the truncated total band mass. -/
theorem massExp_finiteFragments (s : ℝ) (ω : ℤ → FiniteMeasure ℝ) :
    massExp s (finiteFragments ω)
      = ENNReal.ofReal (Real.exp (-s * ((bandMass ω).toNNReal : ℝ))) := by
  unfold massExp
  rw [mass_finiteFragments]

/-- A.e. domination: off the (null) divergence set, the truncated mass
exponential of the total is at most the band product over `S`. -/
theorem bandExpTrunc_le_prod_ae (ζ : ℝ) (s : ℝ) (hs : 0 ≤ s) (S : Finset ℤ) :
    ∀ᵐ ω ∂(Measure.infinitePi (fun k : ℤ =>
        finitePoissonLaw (cappedDyadicIntensity ζ k))),
      bandExpTrunc s ω ≤ bandExpProd s S ω := by
  filter_upwards [ae_isFiniteMeasure_fragment_sum ζ] with ω hω
  have huniv : ((Measure.sum (fun k : ℤ => (ω k : Measure ℝ))) Set.univ) = bandMass ω := by
    rw [Measure.sum_apply _ MeasurableSet.univ]
    exact tsum_congr (fun k => (FiniteMeasure.ennreal_mass (μ := ω k)).symm)
  haveI := hω
  have hb : bandMass ω ≠ ⊤ := by
    rw [← huniv]
    exact measure_ne_top _ _
  have hsumcoe : ((↑(∑ k ∈ S, (ω k).mass) : ℝ≥0∞))
      = (∑ k ∈ S, ((ω k).mass : ℝ≥0∞)) := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert i S hi ih =>
        simp only [Finset.sum_insert hi, ENNReal.coe_add]
        rw [ih]
  have hfin : ((∑ k ∈ S, ((ω k).mass : ℝ≥0∞)) : ℝ≥0∞) ≠ ⊤ :=
    ne_of_lt (ENNReal.sum_lt_top.mpr (fun k _ => ENNReal.coe_lt_top))
  have htoNNR : ((∑ k ∈ S, ((ω k).mass : ℝ≥0∞)).toNNReal) = (∑ k ∈ S, (ω k).mass : ℝ≥0) := by
    refine ENNReal.coe_injective ?_
    rw [ENNReal.coe_toNNReal hfin, hsumcoe]
  have hge : ((∑ k ∈ S, ((ω k).mass : ℝ≥0∞)).toNNReal) ≤ ((bandMass ω).toNNReal) := by
    refine ENNReal.coe_le_coe.mp ?_
    rw [ENNReal.coe_toNNReal hfin, ← hsumcoe, ENNReal.coe_toNNReal hb]
    exact le_trans (by rw [hsumcoe]) (ENNReal.sum_le_tsum S)
  have hgeR : ((↑(∑ k ∈ S, (ω k).mass) : ℝ)) ≤ ((bandMass ω).toNNReal : ℝ) := by
    exact_mod_cast hge
  have hexp : -s * ((bandMass ω).toNNReal : ℝ)
      ≤ -s * ((↑(∑ k ∈ S, (ω k).mass) : ℝ)) := by
    calc -s * ((bandMass ω).toNNReal : ℝ)
        = -(s * ((bandMass ω).toNNReal : ℝ)) := by ring
      _ ≤ -(s * ((↑(∑ k ∈ S, (ω k).mass) : ℝ))) := by
          refine neg_le_neg ?_
          rw [mul_comm s _, mul_comm s _]
          exact mul_le_mul_of_nonneg_right hgeR hs
      _ = -s * ((↑(∑ k ∈ S, (ω k).mass) : ℝ)) := by ring
  have hrfl : ((↑(∑ k ∈ S, (ω k).mass) : ℝ))
      = ((∑ k ∈ S, ((ω k).mass : ℝ≥0∞)).toReal) := by
    rw [← hsumcoe, ENNReal.coe_toReal]
  have hprod : ENNReal.ofReal
      (Real.exp (-s * ((↑(∑ k ∈ S, (ω k).mass) : ℝ))))
      = bandExpProd s S ω := by
    rw [bandExpProd, hrfl, ENNReal.toReal_sum (fun k _ => ENNReal.coe_ne_top),
      Finset.mul_sum, Real.exp_sum,
      ENNReal.ofReal_prod_of_nonneg (fun k _ => Real.exp_nonneg _)]
    rfl
  calc bandExpTrunc s ω
      ≤ ENNReal.ofReal (Real.exp (-s * ((∑ k ∈ S, (ω k).mass : ℝ≥0) : ℝ))) :=
        ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hexp)
    _ = bandExpProd s S ω := hprod

/-- D1-MGF (structural form): for every finite set `S` of dyadic bands, the
mass MGF of the full fragment law is bounded by the product of the per-band
MGFs over `S`. -/
theorem mgf_fragmentLaw_le_finset (ζ : ℝ) (s : ℝ) (hs : 0 ≤ s) (S : Finset ℤ) :
    (∫⁻ X, massExp s X ∂(fragmentLaw ζ))
      ≤ ∏ k ∈ S, (∫⁻ X, massExp s X ∂(finitePoissonLaw (cappedDyadicIntensity ζ k))) := by
  haveI hprobk : ∀ k : ℤ, IsProbabilityMeasure
      (finitePoissonLaw (cappedDyadicIntensity ζ k)) :=
    fun k => finitePoissonLaw_isProbabilityMeasure _
  have hG : Measurable (massExp s) := measurable_massExp s
  set π : Measure (ℤ → FiniteMeasure ℝ) :=
    Measure.infinitePi (fun k : ℤ => finitePoissonLaw (cappedDyadicIntensity ζ k)) with hπ
  -- pull back along finiteFragments; the integrand is the truncated band mass
  have hpull : (∫⁻ X, massExp s X ∂(fragmentLaw ζ))
      = ∫⁻ ω, bandExpTrunc s ω ∂π := by
    unfold fragmentLaw
    rw [lintegral_map (measurable_massExp s) measurable_finiteFragments]
    exact lintegral_congr (fun ω => massExp_finiteFragments s ω)
  -- a.e. domination and the independence product
  have hmono : (∫⁻ ω, bandExpTrunc s ω ∂π)
      ≤ ∫⁻ ω, bandExpProd s S ω ∂π :=
    lintegral_mono_ae (bandExpTrunc_le_prod_ae ζ s hs S)
  have hprod : (∫⁻ ω, bandExpProd s S ω ∂π)
      = ∏ k ∈ S, (∫⁻ X, massExp s X ∂(finitePoissonLaw (cappedDyadicIntensity ζ k))) := by
    unfold bandExpProd
    rw [ProbabilityTheory.lintegral_prod_eq_prod_lintegral_of_indepFun S _
      (ProbabilityTheory.iIndepFun_infinitePi
        (P := fun k : ℤ => finitePoissonLaw (cappedDyadicIntensity ζ k))
        (fun _ => hG))
      (fun k => hG.comp (measurable_pi_apply k))]
    refine Finset.prod_congr rfl (fun k _ => ?_)
    exact (measurePreserving_eval_infinitePi
      (fun j : ℤ => finitePoissonLaw (cappedDyadicIntensity ζ j)) k).lintegral_comp hG
  rw [hpull]
  exact hmono.trans hprod.le

end PrimeGap182D1
