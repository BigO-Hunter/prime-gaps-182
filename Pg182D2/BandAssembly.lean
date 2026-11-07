import Pg182D2.BandStep1
import Pg182D2.InfinitePiProduct

/-!
# BANDASSEMBLY.lean — the last three mechanical steps of (N1), and the join

`OBLIGATION_MAP.md` §7.3 lists the exact remainder of the 182 data side: the band assembly of
`N1Residual` — the product form over the dyadic bands, `HasSum.exp`, the bounded estimate — plus the
join `Σ'_k ∫_{band k} = ∫_0^ζ`.

## The chain

    charFun ((fragmentLaw ζ).map mass) t
      = ∫ X, exp (I (X.mass t)) ∂(fragmentLaw ζ)            -- charFun_mass_map
      = ∫ ω, ∏' k, exp (I ((ω k).mass t)) ∂(infinitePi ν)   -- finiteFragments is a.e. the mass sum
      = ∏' k, ∫ c, exp (I (c.mass t)) ∂(Poisson ν_k)        -- integral_tprod_infinitePi (C ≡ 1)
      = ∏' k, exp (∫ u, (e^{I t u} - 1) ∂ν_k)               -- n1ResidualBand_of_nonneg
      = exp (Σ' k, ∫ u, (e^{I t u} - 1) ∂ν_k)               -- HasSum.cexp
      = exp (-(charExponent t ζ))                           -- the join

## Pieces

* `norm_exp_imag_sub_one_le` — the chord bound `‖e^{ia} − 1‖ ≤ 2|a|`, from scratch (two cases on
  `|a| ≤ 1`: `Complex.norm_exp_sub_one_le`; `|a| ≥ 1`: triangle inequality + unit modulus).
* `band_inter_period`, `cappedDyadicIntensity_eq_restrict_withDensity`,
  `cappedDyadicIntensity_ne_zero_of_lt` — the nonzero-band bridge: a band meeting `(0, ζ)` carries
  positive mass, which is what `ae_nonneg_normalize_of_ne_zero` needs (an *empty* band is the zero
  measure, whose `normalize` is a point mass at an unspecified real).
* `lintegral_firstMoment_cappedDyadic` — `Σ' k, ∫⁻ u, u ∂ν_k = ζ`: the first moment of the
  intensity, i.e. `lintegral_weighted_finitePoissonLaw` with `h ≡ 1` summed over the bands.
* `tsum_band_charFun_lintegral_ne_top` — the bounded estimate the product lemma consumes, from the
  chord bound plus the first moment.
* `tsum_integral_band_exp` — **the join**: `Σ' k ∫ (e^{I t u} − 1) ∂ν_k = −charExponent t ζ`, via
  `integral_sum_measure` on `Measure.sum ν_k` and the density `1/u`.
* `charFun_mass_fragmentLaw` — the characterization, i.e. `N1Residual` itself.
-/

noncomputable section
namespace PrimeGap182D2

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

set_option maxHeartbeats 1000000

/-- Shorthand for the `1/u` density of the fragment intensity. -/
private def bandDensity (u : ℝ) : ℝ≥0∞ := ENNReal.ofReal (1 / u)

/-! ### 1. The chord bound `‖e^{ia} − 1‖ ≤ 2|a|` -/

/-- **The chord bound.** `‖e^{i a} − 1‖ ≤ 2 |a|` for every real `a`, uniformly.

For `|a| ≤ 1` this is `Complex.norm_exp_sub_one_le` at `x = I a` (which needs `‖I a‖ ≤ 1`); for
`|a| ≥ 1` the triangle inequality with `‖e^{I a}‖ = exp (Re (I a)) = 1` gives `≤ 2 ≤ 2|a|`.
The sharp bound is `|a|`, but `2|a|` is what the `hsum` discharge consumes, and it needs no
small-angle argument. -/
theorem norm_exp_imag_sub_one_le (a : ℝ) :
    ‖Complex.exp (Complex.I * (a : ℂ)) - 1‖ ≤ 2 * |a| := by
  rcases le_or_gt |a| 1 with hsmall | hbig
  · have hnorm : ‖Complex.I * (a : ℂ)‖ = |a| := by
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    have h := Complex.norm_exp_sub_one_le (x := Complex.I * (a : ℂ)) (by rw [hnorm]; exact hsmall)
    rwa [hnorm] at h
  · have h1 : ‖Complex.exp (Complex.I * (a : ℂ))‖ = 1 := by
      rw [Complex.norm_exp]
      simp
    calc ‖Complex.exp (Complex.I * (a : ℂ)) - 1‖
        ≤ ‖Complex.exp (Complex.I * (a : ℂ))‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [h1, norm_one]; norm_num
      _ ≤ 2 * |a| := by linarith [abs_nonneg a]

/-! ### 2. The nonzero-band bridge -/

/-- The band `Ioc (2^k) (2^{k+1})` intersected with the period `(0, ζ]` is the interval
`Ioc (2^k) (min (2^{k+1}) ζ)`. -/
theorem band_inter_period (ζ : ℝ) (k : ℤ) :
    Set.Ioc ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1)) ∩ Set.Ioc (0 : ℝ) ζ
      = Set.Ioc ((2 : ℝ) ^ k) (min ((2 : ℝ) ^ (k + 1)) ζ) := by
  ext u
  simp only [Set.mem_inter_iff, Set.mem_Ioc]
  constructor
  · rintro ⟨⟨h1, h2⟩, -, h4⟩
    exact ⟨h1, le_min h2 h4⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h1, h2.trans (min_le_left _ _)⟩, (zpow_pos (by norm_num) k).trans h1,
      h2.trans (min_le_right _ _)⟩

/-- **The band measure, unwound onto plain Lebesgue measure.**  The `withDensity (1/u)` of the
period restricted to the band is `(volume.withDensity (1/u))` restricted to the *intersection* of
the band with the period — which is what lets the whole band computation happen against `volume`,
with no nested restrictions in the integrals. -/
theorem cappedDyadicIntensity_eq_restrict_withDensity (ζ : ℝ) (k : ℤ) :
    (PrimeGap182D1.cappedDyadicIntensity ζ k : Measure ℝ)
      = (volume.withDensity (bandDensity)).restrict
          (Set.Ioc ((2 : ℝ) ^ k) (min ((2 : ℝ) ^ (k + 1)) ζ)) := by
  show ((volume.restrict (Set.Ioc (0 : ℝ) ζ)).withDensity (bandDensity)).restrict
      (Set.Ioc ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1))) = _
  rw [← restrict_withDensity (μ := volume) measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc, band_inter_period]

/-- **A band meeting the period is nonzero.**  If `2^k < ζ` the band `Ioc (2^k) (2^{k+1})` meets
`(0, ζ]` in an interval of positive length on which the `1/u` density is bounded below by
`1/min (2^{k+1}) ζ > 0`, so the band's mass is positive.

This is the bridge `ae_nonneg_normalize_of_ne_zero` was missing: only *empty* bands are the zero
measure, and an empty band needs no hypothesis (both sides of the band identity are `1` there,
since `finitePoissonLaw 0 = δ_0`). -/
theorem cappedDyadicIntensity_ne_zero_of_lt {ζ : ℝ} {k : ℤ} (_hζ : 0 < ζ)
    (h : (2 : ℝ) ^ k < ζ) :
    PrimeGap182D1.cappedDyadicIntensity ζ k ≠ 0 := by
  have ha : (0 : ℝ) < (2 : ℝ) ^ k := zpow_pos (by norm_num) k
  have hnext : (2 : ℝ) ^ k < (2 : ℝ) ^ (k + 1) := by
    have hz : (2 : ℝ) ^ (k + 1) = (2 : ℝ) ^ k * 2 := by
      rw [zpow_add_one₀ (by norm_num : (2 : ℝ) ≠ 0)]
    linarith
  set b : ℝ := min ((2 : ℝ) ^ (k + 1)) ζ with hbdef
  have hab : (2 : ℝ) ^ k < b := lt_min hnext h
  have hbpos : (0 : ℝ) < b := (zpow_pos (by norm_num) k).trans hab
  have hmeasab : MeasurableSet (Set.Ioc ((2 : ℝ) ^ k) b) := measurableSet_Ioc
  -- the mass, as a plain Lebesgue integral of the density over the intersected interval
  have hmassEq : ((PrimeGap182D1.cappedDyadicIntensity ζ k : Measure ℝ)) Set.univ
      = ∫⁻ u in Set.Ioc ((2 : ℝ) ^ k) b, bandDensity u := by
    rw [cappedDyadicIntensity_eq_restrict_withDensity, ← hbdef,
      Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, withDensity_apply _ hmeasab]
  -- the density is bounded below on the interval
  have hlow : ∫⁻ u in Set.Ioc ((2 : ℝ) ^ k) b, ENNReal.ofReal (1 / b)
      ≤ ∫⁻ u in Set.Ioc ((2 : ℝ) ^ k) b, bandDensity u := by
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem hmeasab] with u hu
    have hu0 : (0 : ℝ) < u := (zpow_pos (by norm_num) k).trans hu.1
    exact ENNReal.ofReal_le_ofReal (one_div_le_one_div_of_le hu0 hu.2)
  have hconst : ∫⁻ u in Set.Ioc ((2 : ℝ) ^ k) b, ENNReal.ofReal (1 / b)
      = ENNReal.ofReal ((1 / b) * (b - (2 : ℝ) ^ k)) := by
    rw [setLIntegral_const, Real.volume_Ioc, ← ENNReal.ofReal_mul (by positivity)]
  have hpos : (0 : ℝ≥0∞) < ((PrimeGap182D1.cappedDyadicIntensity ζ k : Measure ℝ)) Set.univ := by
    rw [hmassEq]
    refine lt_of_lt_of_le ?_ hlow
    rw [hconst, ENNReal.ofReal_pos]
    exact mul_pos (one_div_pos.mpr hbpos) (sub_pos.mpr hab)
  have hmass : (PrimeGap182D1.cappedDyadicIntensity ζ k).mass ≠ 0 := by
    intro hm
    have hz : ((PrimeGap182D1.cappedDyadicIntensity ζ k).mass : ℝ≥0∞) = 0 := by rw [hm]; rfl
    rw [FiniteMeasure.ennreal_mass] at hz
    rw [hz] at hpos
    exact absurd hpos (lt_irrefl _)
  exact (FiniteMeasure.mass_nonzero_iff _).mp hmass

/-- The `ℝ≥0∞`-norm of a complex number is the `ofReal` of its norm (the two coercion routes). -/
theorem coe_nnnorm_eq_ofReal_norm (z : ℂ) : (‖z‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖z‖ := by
  rw [← ENNReal.ofReal_coe_nnreal]
  norm_cast

/-! ### 3. The first moment of the intensity -/

/-- **The per-band first moment.**  `lintegral_weighted_finitePoissonLaw` with `h ≡ 1`: the
`∫⁻`-moment of the mass of a Poisson fragment law is the intensity's first moment.  Careful — this
is the *intensity's* first moment, not `μ.mass`; for a dyadic band the two coincide because the
density is `1/u` (so `∫⁻ u, u ∂ν_k = ν_k.mass`), which is `lintegral_firstMoment_cappedDyadic`. -/
theorem lintegral_mass_finitePoissonLaw (μ : FiniteMeasure ℝ) :
    ∫⁻ c, ENNReal.ofReal ((c.mass : ℝ)) ∂(PrimeGap182D1.finitePoissonLaw μ)
      = ∫⁻ u, ENNReal.ofReal u ∂(μ : Measure ℝ) := by
  have h := PrimeGap182D1.lintegral_weighted_finitePoissonLaw μ (fun _ => 1) measurable_const
  simp only [lintegral_one, mul_one] at h
  rw [← h]
  refine lintegral_congr fun c => ?_
  rw [ENNReal.ofReal_coe_nnreal, FiniteMeasure.ennreal_mass]

/-- **The band sum of the first moments is `ζ`.**  Both the `hsum` discharge and the join consume
this: the `1/u` density makes the first moment of each band its mass, and the masses sum to the
period length. -/
theorem lintegral_firstMoment_cappedDyadic {ζ : ℝ} (_hζ : 0 < ζ) :
    ∑' k : ℤ, ∫⁻ u, ENNReal.ofReal u
      ∂(PrimeGap182D1.cappedDyadicIntensity ζ k : Measure ℝ) = ENNReal.ofReal ζ := by
  rw [← lintegral_sum_measure (fun u : ℝ => ENNReal.ofReal u)
    (fun k : ℤ => (PrimeGap182D1.cappedDyadicIntensity ζ k : Measure ℝ))]
  rw [PrimeGap182D1.sum_cappedDyadicIntensity]
  rw [lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop)]
  simp only [Pi.mul_apply]
  have hpt : ∀ᵐ u ∂(volume.restrict (Set.Ioc (0 : ℝ) ζ)),
      ENNReal.ofReal (1 / u) * ENNReal.ofReal u = 1 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    rw [← ENNReal.ofReal_mul (le_of_lt (one_div_pos.mpr hu.1)),
      one_div_mul_cancel hu.1.ne', ENNReal.ofReal_one]
  rw [lintegral_congr_ae hpt, lintegral_one, Measure.restrict_apply_univ, Real.volume_Ioc,
    sub_zero]

/-! ### 4. The bounded estimate (the `hsum` hypothesis of the product lemma) -/

/-- The pointwise chord bound in the form the measures consume: for `u > 0`,
`‖e^{I u t} − 1‖ ≤ 2|t| u`. -/
theorem band_norm_le (t : ℝ) {u : ℝ} (hu : 0 ≤ u) :
    ‖Complex.exp (↑(u * t) * Complex.I) - 1‖ ≤ 2 * |t| * u := by
  have h := norm_exp_imag_sub_one_le (u * t)
  have harg : Complex.I * ((u * t : ℝ) : ℂ) = ↑(u * t) * Complex.I := by
    push_cast; ring
  rw [harg] at h
  calc ‖Complex.exp (↑(u * t) * Complex.I) - 1‖ ≤ 2 * |u * t| := h
    _ = 2 * |t| * u := by rw [abs_mul, abs_of_nonneg hu]; ring

/-- **The `hsum` discharge.**  The bound the product lemma needs,
`Σ'_k ∫⁻ X, ‖e^{I (X.mass t)} − 1‖ ∂Poisson(ν_k) ≠ ⊤`: each band is bounded by `2|t|` times the
band's first moment, and the band first moments sum to `ζ`. -/
theorem tsum_band_charFun_lintegral_ne_top {ζ : ℝ} (hζ : 0 < ζ) (t : ℝ) :
    (∑' k : ℤ, ∫⁻ X, (‖Complex.exp (↑((X.mass : ℝ) * t) * Complex.I) - 1‖₊ : ℝ≥0∞)
        ∂(PrimeGap182D1.finitePoissonLaw (PrimeGap182D1.cappedDyadicIntensity ζ k))) ≠ ⊤ := by
  have hstep : ∀ k : ℤ,
      (∫⁻ X, (‖Complex.exp (↑((X.mass : ℝ) * t) * Complex.I) - 1‖₊ : ℝ≥0∞)
          ∂(PrimeGap182D1.finitePoissonLaw (PrimeGap182D1.cappedDyadicIntensity ζ k)))
        ≤ ENNReal.ofReal (2 * |t|) * ∫⁻ u, ENNReal.ofReal u
            ∂(PrimeGap182D1.cappedDyadicIntensity ζ k : Measure ℝ) := by
    intro k
    set ν := PrimeGap182D1.cappedDyadicIntensity ζ k with hν
    calc ∫⁻ X, (‖Complex.exp (↑((X.mass : ℝ) * t) * Complex.I) - 1‖₊ : ℝ≥0∞)
          ∂(PrimeGap182D1.finitePoissonLaw ν)
        = ∫⁻ X, ENNReal.ofReal ‖Complex.exp (↑((X.mass : ℝ) * t) * Complex.I) - 1‖
            ∂(PrimeGap182D1.finitePoissonLaw ν) := by
          refine lintegral_congr fun X => ?_
          exact coe_nnnorm_eq_ofReal_norm _
      _ ≤ ∫⁻ X, ENNReal.ofReal (2 * |t| * (X.mass : ℝ))
            ∂(PrimeGap182D1.finitePoissonLaw ν) := by
          refine lintegral_mono fun X => ?_
          refine ENNReal.ofReal_le_ofReal ?_
          calc ‖Complex.exp (↑((X.mass : ℝ) * t) * Complex.I) - 1‖
              ≤ 2 * |t| * (X.mass : ℝ) := band_norm_le t X.mass.coe_nonneg
            _ = 2 * |t| * (X.mass : ℝ) := rfl
      _ = ENNReal.ofReal (2 * |t|) * ∫⁻ X, ENNReal.ofReal ((X.mass : ℝ))
            ∂(PrimeGap182D1.finitePoissonLaw ν) := by
          rw [← lintegral_const_mul' (ENNReal.ofReal (2 * |t|))
            (fun X : FiniteMeasure ℝ => ENNReal.ofReal ((X.mass : ℝ))) ENNReal.ofReal_ne_top]
          refine lintegral_congr fun X => ?_
          rw [← ENNReal.ofReal_mul (by positivity)]
      _ = ENNReal.ofReal (2 * |t|) * ∫⁻ u, ENNReal.ofReal u ∂((ν : FiniteMeasure ℝ) : Measure ℝ) := by
          rw [lintegral_mass_finitePoissonLaw]
  have hsum_le : (∑' k : ℤ, ∫⁻ X, (‖Complex.exp (↑((X.mass : ℝ) * t) * Complex.I) - 1‖₊ : ℝ≥0∞)
        ∂(PrimeGap182D1.finitePoissonLaw (PrimeGap182D1.cappedDyadicIntensity ζ k)))
      ≤ ENNReal.ofReal (2 * |t| * ζ) := by
    calc _ ≤ ∑' k : ℤ, ENNReal.ofReal (2 * |t|) * ∫⁻ u, ENNReal.ofReal u
          ∂(PrimeGap182D1.cappedDyadicIntensity ζ k : Measure ℝ) := ENNReal.tsum_le_tsum hstep
      _ = ENNReal.ofReal (2 * |t|) * ∑' k : ℤ, ∫⁻ u, ENNReal.ofReal u
            ∂(PrimeGap182D1.cappedDyadicIntensity ζ k : Measure ℝ) := ENNReal.tsum_mul_left
      _ = ENNReal.ofReal (2 * |t|) * ENNReal.ofReal ζ := by
          rw [lintegral_firstMoment_cappedDyadic hζ]
      _ = ENNReal.ofReal (2 * |t| * ζ) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hsum_le

end PrimeGap182D2
