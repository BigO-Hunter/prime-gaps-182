import Pg182D1.D1Cell
import Pg182D1.D1Mgf
import Pg182D1.BandForm

/-!
# PERCELL.lean — the per-cell envelope in closed form (the D1-data interface)

Composes the proved chain into the single inequality the frozen-data checks
consume. For every cell `n`, every `s ≥ 0`, every finite band set `S`:

    (fragmentLaw ζ).real {cell = n}
      ≤ exp( s·(n+1)·mesh − Σ_{k∈S} b_k ),      b_k := ∫_{band_k∩(0,ζ]} (1−e^{−s·u})/u,

with `b_k` the BandForm exponents. Every `b_k` admits exact ℚ interval bounds
(certified by `receipt/percell_gen.py`), so the per-cell check
`p^frozen_c ≥ env(c)` reduces to one ℚ comparison per cell against exp of a
certified rational interval — the C0 receipt pattern.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace PrimeGap182D1

/-- The real mass MGF of a probability law on `FiniteMeasure ℝ` is the toReal
of its ENNReal MGF. -/
theorem realMgf_eq_toReal {μ : Measure (FiniteMeasure ℝ)} [IsProbabilityMeasure μ] (s : ℝ) :
    (∫ X : FiniteMeasure ℝ, Real.exp (-s * (X.mass : ℝ)) ∂μ)
      = (∫⁻ X, massExp s X ∂μ).toReal := by
  have hfre : Measurable (fun X : FiniteMeasure ℝ => Real.exp (-s * (X.mass : ℝ))) :=
    (measurable_const.mul measurable_mass).exp
  have hfnn : 0 ≤ᵐ[μ] (fun X : FiniteMeasure ℝ => Real.exp (-s * (X.mass : ℝ))) :=
    Filter.Eventually.of_forall fun _ => Real.exp_nonneg _
  rw [integral_eq_lintegral_of_nonneg_ae hfnn hfre.aestronglyMeasurable]
  rfl

/-- **D1-PERCELL (closed form).** The per-cell majorant with the exact
per-band closed forms: for every cell `n`, `s ≥ 0`, finite band set `S`,

    μ{cell = n} ≤ exp(s·(n+1)·mesh) · exp(−Σ_{k∈S} b_k),

`b_k = ∫_{(2^k,2^{k+1}]∩(0,ζ]} (1−e^{−s·u})/u` — the frozen program's per-cell
probabilities must dominate this envelope (one ℚ inequality per cell once the
`b_k` are certified below by rational intervals). -/
theorem cell_probability_closed (ζ : ℝ) (n : ℕ) (s : ℝ) (hs : 0 ≤ s) (S : Finset ℤ) :
    (fragmentLaw ζ).real {X : FiniteMeasure ℝ | trialCellIndex X = n}
      ≤ Real.exp (s * (((n : ℝ) + 1) * (trialMesh : ℝ))) *
        Real.exp (- (∑ k ∈ S, ∫ u in bandWindow ζ k, (1 - Real.exp (-s * u)) / u)) := by
  haveI : IsProbabilityMeasure (fragmentLaw ζ) := fragmentLaw_isProbabilityMeasure ζ
  have h1 := cell_probability_le ζ n s hs
  refine le_trans h1 (mul_le_mul_of_nonneg_left ?_ (Real.exp_nonneg _))
  -- the closed-form MGF bound
  have hE1 : ∀ k : ℤ,
      (∫⁻ X, massExp s X ∂(finitePoissonLaw (cappedDyadicIntensity ζ k))) ≤ 1 := by
    intro k
    haveI : IsProbabilityMeasure
        (finitePoissonLaw (cappedDyadicIntensity ζ k)) :=
      finitePoissonLaw_isProbabilityMeasure _
    have hle := lintegral_mono
      (μ := finitePoissonLaw (cappedDyadicIntensity ζ k)) (f := massExp s)
      (g := fun _ => (1:ℝ≥0∞)) (fun X => massExp_le_one s hs X)
    rwa [lintegral_one, (finitePoissonLaw_isProbabilityMeasure _).measure_univ] at hle
  have hfin1 : (∫⁻ X, massExp s X ∂(fragmentLaw ζ)) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
    have hle := lintegral_mono (μ := fragmentLaw ζ) (f := massExp s)
      (g := fun _ => (1:ℝ≥0∞)) (fun X => massExp_le_one s hs X)
    rwa [lintegral_one, (fragmentLaw_isProbabilityMeasure ζ).measure_univ] at hle
  have hfin2 : (∏ k ∈ S,
      (∫⁻ X, massExp s X ∂(finitePoissonLaw (cappedDyadicIntensity ζ k)))) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
    refine Finset.prod_le_one (fun k _ => hE1 k)
  have hband : ∀ k ∈ S,
      (∫⁻ X, massExp s X ∂(finitePoissonLaw (cappedDyadicIntensity ζ k))).toReal
        = Real.exp (- ∫ u in bandWindow ζ k, (1 - Real.exp (-s * u)) / u) := by
    intro k _
    haveI : IsProbabilityMeasure
        (finitePoissonLaw (cappedDyadicIntensity ζ k)) :=
      finitePoissonLaw_isProbabilityMeasure _
    rw [← realMgf_eq_toReal s, bandMgf_eq ζ s k hs]
  calc (∫ X : FiniteMeasure ℝ, Real.exp (-s * (X.mass : ℝ)) ∂(fragmentLaw ζ))
      = (∫⁻ X, massExp s X ∂(fragmentLaw ζ)).toReal := realMgf_eq_toReal s
    _ ≤ (∏ k ∈ S,
          (∫⁻ X, massExp s X ∂(finitePoissonLaw (cappedDyadicIntensity ζ k)))).toReal :=
        (ENNReal.toReal_le_toReal hfin1 hfin2).mpr
          (mgf_fragmentLaw_le_finset ζ s hs S)
    _ = ∏ k ∈ S,
          (∫⁻ X, massExp s X ∂(finitePoissonLaw (cappedDyadicIntensity ζ k))).toReal := by
        rw [ENNReal.toReal_prod]
    _ = ∏ k ∈ S, Real.exp (- ∫ u in bandWindow ζ k, (1 - Real.exp (-s * u)) / u) :=
        Finset.prod_congr rfl (fun k hk => hband k hk)
    _ = Real.exp (- (∑ k ∈ S, ∫ u in bandWindow ζ k, (1 - Real.exp (-s * u)) / u)) := by
        rw [← Real.exp_sum, Finset.sum_neg_distrib]

end PrimeGap182D1
