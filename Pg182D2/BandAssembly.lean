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

/-! ### 5. The join `Σ'_k ∫_{band k} = ∫_0^ζ` -/

/-- **The band sum of the `∫⁻`-norms.**  At most `2|t| ζ`: on `(0, ζ)` the `1/u` density cancels
the `u` in the chord bound, so the integrand against the joined measure is the constant `2|t|`. -/
theorem lintegral_band_integrand_sum_le {ζ : ℝ} (_hζ : 0 < ζ) (t : ℝ) :
    ∫⁻ u, ‖Complex.exp (↑(u * t) * Complex.I) - 1‖ₑ
      ∂(Measure.sum fun k : ℤ => (PrimeGap182D1.cappedDyadicIntensity ζ k : Measure ℝ))
      ≤ ENNReal.ofReal (2 * |t| * ζ) := by
    rw [PrimeGap182D1.sum_cappedDyadicIntensity,
      lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop)]
    simp only [Pi.mul_apply]
    have hpt : ∀ᵐ u ∂(volume.restrict (Set.Ioc (0 : ℝ) ζ)),
        ENNReal.ofReal (1 / u) * ‖Complex.exp (↑(u * t) * Complex.I) - 1‖ₑ
          ≤ ENNReal.ofReal (2 * |t|) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      have hnorm : ‖Complex.exp (↑(u * t) * Complex.I) - 1‖ₑ
          = ENNReal.ofReal ‖Complex.exp (↑(u * t) * Complex.I) - 1‖ := by
        rw [show ‖Complex.exp (↑(u * t) * Complex.I) - 1‖ₑ
            = (‖Complex.exp (↑(u * t) * Complex.I) - 1‖₊ : ℝ≥0∞) from rfl,
          coe_nnnorm_eq_ofReal_norm]
      rw [hnorm, ← ENNReal.ofReal_mul (le_of_lt (one_div_pos.mpr hu.1))]
      refine ENNReal.ofReal_le_ofReal ?_
      have h2 := band_norm_le t hu.1.le
      have h3 : (1 / u) * ‖Complex.exp (↑(u * t) * Complex.I) - 1‖
          ≤ (1 / u) * (2 * |t| * u) :=
        mul_le_mul_of_nonneg_left h2 (le_of_lt (one_div_pos.mpr hu.1))
      have hu0 : u ≠ 0 := hu.1.ne'
      calc (1 / u) * ‖Complex.exp (↑(u * t) * Complex.I) - 1‖ ≤ (1 / u) * (2 * |t| * u) := h3
        _ = 2 * |t| := by field_simp
    calc ∫⁻ u, ENNReal.ofReal (1 / u) * ‖Complex.exp (↑(u * t) * Complex.I) - 1‖ₑ
          ∂(volume.restrict (Set.Ioc (0 : ℝ) ζ))
        ≤ ∫⁻ _u, ENNReal.ofReal (2 * |t|) ∂(volume.restrict (Set.Ioc (0 : ℝ) ζ)) :=
          lintegral_mono_ae hpt
      _ = ENNReal.ofReal (2 * |t|) * ENNReal.ofReal ζ := by
          rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero]
      _ = ENNReal.ofReal (2 * |t| * ζ) := by
          rw [← ENNReal.ofReal_mul (by positivity)]

/-- **Integrability of the band integrand against the band sum**, from the `∫⁻` bound. -/
theorem integrable_band_integrand_sum {ζ : ℝ} (hζ : 0 < ζ) (t : ℝ) :
    Integrable (fun u : ℝ => Complex.exp (↑(u * t) * Complex.I) - 1)
      (Measure.sum fun k : ℤ => (PrimeGap182D1.cappedDyadicIntensity ζ k : Measure ℝ)) := by
  refine ⟨?_, ?_⟩
  · exact (by fun_prop : Measurable
      (fun u : ℝ => Complex.exp (↑(u * t) * Complex.I) - 1)).aestronglyMeasurable
  · rw [hasFiniteIntegral_iff_enorm]
    exact lt_of_le_of_lt (lintegral_band_integrand_sum_le hζ t) ENNReal.ofReal_lt_top

/-- **THE JOIN.**  `Σ'_k ∫_{band k} (e^{I t u} − 1) = −charExponent t ζ`: the bands partition
`(0, ζ]`, `Measure.sum` is the joined measure (`integral_sum_measure`), and the `1/u` density turns
the sum into the interval integral. -/
theorem tsum_integral_band_exp {ζ : ℝ} (hζ : 0 < ζ) (t : ℝ) :
    (∑' k : ℤ, ∫ u, (Complex.exp (↑(u * t) * Complex.I) - 1)
      ∂(PrimeGap182D1.cappedDyadicIntensity ζ k : Measure ℝ)) = -charExponent t ζ := by
  have hInt := integrable_band_integrand_sum hζ t
  rw [← integral_sum_measure hInt]
  rw [PrimeGap182D1.sum_cappedDyadicIntensity,
    integral_withDensity_eq_integral_toReal_smul (by fun_prop)
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  rw [show charExponent t ζ = ∫ u in Set.Ioc (0 : ℝ) ζ,
      (1 - Complex.exp (Complex.I * (↑t * ↑u))) / ↑u from by
    rw [charExponent, intervalIntegral.integral_of_le hζ.le]]
  rw [← integral_neg]
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
  rw [ENNReal.toReal_ofReal (le_of_lt (one_div_pos.mpr hu.1)), Complex.real_smul]
  have harg : Complex.exp (↑(u * t) * Complex.I) = Complex.exp (Complex.I * (↑t * ↑u)) := by
    congr 1
    push_cast
    ring
  rw [harg]
  have huC : (↑u : ℂ) ≠ 0 := by
    simp [Complex.ofReal_eq_zero, hu.1.ne']
  rw [one_div, Complex.ofReal_inv, div_eq_mul_inv]
  ring

/-- **The band exponents are summable.**  `∑' k, ‖∫_band (e^{Iut} − 1)‖ ≤ ∑' k, ∫⁻ ‖…‖ = 2|t|ζ`. -/
theorem summable_band_exponent {ζ : ℝ} (hζ : 0 < ζ) (t : ℝ) :
    Summable fun k : ℤ => ∫ u, (Complex.exp (↑(u * t) * Complex.I) - 1)
      ∂(PrimeGap182D1.cappedDyadicIntensity ζ k : Measure ℝ) := by
  have hstep : ∀ k : ℤ,
      (‖∫ u, (Complex.exp (↑(u * t) * Complex.I) - 1)
          ∂(PrimeGap182D1.cappedDyadicIntensity ζ k : Measure ℝ)‖₊ : ℝ≥0∞)
        ≤ ∫⁻ u, (‖Complex.exp (↑(u * t) * Complex.I) - 1‖₊ : ℝ≥0∞)
            ∂(PrimeGap182D1.cappedDyadicIntensity ζ k : Measure ℝ) := by
    intro k
    set ν : FiniteMeasure ℝ := PrimeGap182D1.cappedDyadicIntensity ζ k with hν
    calc (‖∫ u, (Complex.exp (↑(u * t) * Complex.I) - 1) ∂(ν : Measure ℝ)‖₊ : ℝ≥0∞)
        = ENNReal.ofReal ‖∫ u, (Complex.exp (↑(u * t) * Complex.I) - 1) ∂(ν : Measure ℝ)‖ :=
          coe_nnnorm_eq_ofReal_norm _
      _ ≤ ENNReal.ofReal (∫ u, ‖Complex.exp (↑(u * t) * Complex.I) - 1‖ ∂(ν : Measure ℝ)) :=
          ENNReal.ofReal_le_ofReal (norm_integral_le_integral_norm _)
      _ = ENNReal.ofReal
            ((∫⁻ u, ‖Complex.exp (↑(u * t) * Complex.I) - 1‖ₑ ∂(ν : Measure ℝ)).toReal) := by
          rw [integral_norm_eq_lintegral_enorm (by fun_prop : AEStronglyMeasurable
            (fun u : ℝ => Complex.exp (↑(u * t) * Complex.I) - 1) (ν : Measure ℝ))]
      _ ≤ ∫⁻ u, ‖Complex.exp (↑(u * t) * Complex.I) - 1‖ₑ ∂(ν : Measure ℝ) :=
          ENNReal.ofReal_toReal_le
      _ = ∫⁻ u, (‖Complex.exp (↑(u * t) * Complex.I) - 1‖₊ : ℝ≥0∞) ∂(ν : Measure ℝ) := rfl
  have hbound : (∑' k : ℤ, (‖∫ u, (Complex.exp (↑(u * t) * Complex.I) - 1)
        ∂(PrimeGap182D1.cappedDyadicIntensity ζ k : Measure ℝ)‖₊ : ℝ≥0∞))
      ≤ ENNReal.ofReal (2 * |t| * ζ) := by
    calc ∑' k : ℤ, (‖∫ u, (Complex.exp (↑(u * t) * Complex.I) - 1)
          ∂(PrimeGap182D1.cappedDyadicIntensity ζ k : Measure ℝ)‖₊ : ℝ≥0∞)
        ≤ ∑' k : ℤ, ∫⁻ u, (‖Complex.exp (↑(u * t) * Complex.I) - 1‖₊ : ℝ≥0∞)
            ∂(PrimeGap182D1.cappedDyadicIntensity ζ k : Measure ℝ) := ENNReal.tsum_le_tsum hstep
      _ = ∫⁻ u, (‖Complex.exp (↑(u * t) * Complex.I) - 1‖₊ : ℝ≥0∞)
            ∂(Measure.sum fun k : ℤ => (PrimeGap182D1.cappedDyadicIntensity ζ k : Measure ℝ)) :=
          (lintegral_sum_measure _ _).symm
      _ ≤ ENNReal.ofReal (2 * |t| * ζ) := lintegral_band_integrand_sum_le hζ t
  have hnn : Summable fun k : ℤ => (‖∫ u, (Complex.exp (↑(u * t) * Complex.I) - 1)
      ∂(PrimeGap182D1.cappedDyadicIntensity ζ k : Measure ℝ)‖₊ : ℝ≥0) :=
    ENNReal.tsum_coe_ne_top_iff_summable.mp
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbound)
  have hreal : Summable fun k : ℤ => ‖∫ u, (Complex.exp (↑(u * t) * Complex.I) - 1)
      ∂(PrimeGap182D1.cappedDyadicIntensity ζ k : Measure ℝ)‖ :=
    NNReal.summable_coe.mpr hnn
  exact Summable.of_norm hreal

/-! ### 6. The empty bands, and the characterization -/

/-- **A band at or above the period is empty**, so its intensity is the zero measure. -/
theorem cappedDyadicIntensity_eq_zero_of_le {ζ : ℝ} {k : ℤ} (_hζ : 0 < ζ)
    (h : ζ ≤ (2 : ℝ) ^ k) : PrimeGap182D1.cappedDyadicIntensity ζ k = 0 := by
  have ha : (0 : ℝ) < (2 : ℝ) ^ k := zpow_pos (by norm_num) k
  have hmin : min ((2 : ℝ) ^ (k + 1)) ζ = ζ := by
    have hle : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ (k + 1) := by
      have hz : (2 : ℝ) ^ (k + 1) = (2 : ℝ) ^ k * 2 := by
        rw [zpow_add_one₀ (by norm_num : (2 : ℝ) ≠ 0)]
      linarith
    exact min_eq_right (h.trans hle)
  have hemp : Set.Ioc ((2 : ℝ) ^ k) (min ((2 : ℝ) ^ (k + 1)) ζ) = ∅ := by
    rw [hmin, Set.Ioc_eq_empty]
    exact not_lt.mpr h
  refine FiniteMeasure.toMeasure_injective ?_
  have hzero : ((PrimeGap182D1.cappedDyadicIntensity ζ k : Measure ℝ)) = 0 := by
    rw [cappedDyadicIntensity_eq_restrict_withDensity, hemp, Measure.restrict_empty]
  rw [hzero, FiniteMeasure.toMeasure_zero]

/-- **The per-band factor identity**, with the empty bands handled separately: a band meeting the
period is nonzero, so `n1ResidualBand_of_nonneg` applies; a band at or above the period is the zero
measure, whose law is `δ_0` and whose factor is `1` on both sides. -/
theorem band_factor_identity {ζ : ℝ} (hζ : 0 < ζ) (t : ℝ) (k : ℤ) :
    ∫ c, Complex.exp (↑((c.mass : ℝ) * t) * Complex.I)
        ∂(PrimeGap182D1.finitePoissonLaw (PrimeGap182D1.cappedDyadicIntensity ζ k))
      = Complex.exp (∫ u, (Complex.exp (↑(u * t) * Complex.I) - 1)
          ∂(PrimeGap182D1.cappedDyadicIntensity ζ k : Measure ℝ)) := by
  rcases lt_or_ge ((2 : ℝ) ^ k) ζ with hlt | hge
  · rw [← charFun_mass_map_single]
    exact n1ResidualBand_of_nonneg _ t (ae_nonneg_normalize_of_ne_zero
      (cappedDyadicIntensity_ne_zero_of_lt hζ hlt) (ae_nonneg_cappedDyadicIntensity ζ k))
  · have hzero : PrimeGap182D1.cappedDyadicIntensity ζ k = 0 :=
      cappedDyadicIntensity_eq_zero_of_le hζ hge
    have hL : ∫ c, Complex.exp (↑((c.mass : ℝ) * t) * Complex.I)
        ∂(PrimeGap182D1.finitePoissonLaw (0 : FiniteMeasure ℝ)) = 1 := by
      have hmass0 : ∀ᵐ c ∂(PrimeGap182D1.finitePoissonLaw (0 : FiniteMeasure ℝ)), c.mass = 0 := by
        have h := lintegral_mass_finitePoissonLaw (0 : FiniteMeasure ℝ)
        have h0 : ∫⁻ u, ENNReal.ofReal u ∂(((0 : FiniteMeasure ℝ) : Measure ℝ)) = 0 := by
          rw [FiniteMeasure.toMeasure_zero]
          simp
        rw [h0] at h
        have h1 : ∀ᵐ c ∂(PrimeGap182D1.finitePoissonLaw (0 : FiniteMeasure ℝ)),
            ENNReal.ofReal ((c.mass : ℝ)) = 0 :=
          (lintegral_eq_zero_iff
            (ENNReal.measurable_ofReal.comp PrimeGap182D1.measurable_mass)).mp h
        filter_upwards [h1] with c hc
        refine le_antisymm ?_ c.mass.coe_nonneg
        exact (ENNReal.ofReal_eq_zero).mp hc
      calc ∫ c, Complex.exp (↑((c.mass : ℝ) * t) * Complex.I)
            ∂(PrimeGap182D1.finitePoissonLaw (0 : FiniteMeasure ℝ))
          = ∫ _c, (1 : ℂ) ∂(PrimeGap182D1.finitePoissonLaw (0 : FiniteMeasure ℝ)) :=
            integral_congr_ae (hmass0.mono fun c hc => by simp [hc])
        _ = 1 := by
            rw [integral_const, Measure.real,
              @IsProbabilityMeasure.measure_univ _ _
                (PrimeGap182D1.finitePoissonLaw (0 : FiniteMeasure ℝ))
                (PrimeGap182D1.finitePoissonLaw_isProbabilityMeasure 0),
              ENNReal.toReal_one, one_smul]
    rw [hzero]
    simp only [FiniteMeasure.toMeasure_zero, integral_zero_measure, Complex.exp_zero]
    exact hL

set_option linter.style.haveILetI false in
/-- **THE CHARACTERIZATION.**  `N1Residual` is now a theorem: the characteristic function of the
mass of the fragment law is the exponential of the band exponent. -/
theorem charFun_mass_fragmentLaw {ζ : ℝ} (hζ : 0 < ζ) (t : ℝ) :
    charFun ((PrimeGap182D1.fragmentLaw ζ).map (fun X : FiniteMeasure ℝ => (X.mass : ℝ))) t
      = Complex.exp (-(charExponent t ζ)) := by
  letI : ∀ k : ℤ, IsProbabilityMeasure
      (PrimeGap182D1.finitePoissonLaw (PrimeGap182D1.cappedDyadicIntensity ζ k)) :=
    fun k => PrimeGap182D1.finitePoissonLaw_isProbabilityMeasure _
  rw [charFun_mass_map]
  have hstep1 : ∫ X, Complex.exp (↑((X.mass : ℝ) * t) * Complex.I)
        ∂(PrimeGap182D1.fragmentLaw ζ)
      = ∫ ω, Complex.exp (↑(((PrimeGap182D1.finiteFragments ω).mass : ℝ) * t) * Complex.I)
          ∂(Measure.infinitePi fun k : ℤ =>
            PrimeGap182D1.finitePoissonLaw (PrimeGap182D1.cappedDyadicIntensity ζ k)) := by
    unfold PrimeGap182D1.fragmentLaw
    exact integral_map PrimeGap182D1.measurable_finiteFragments.aemeasurable
      (band_exp_integrand_measurable t).aestronglyMeasurable
  rw [hstep1]
  -- the mass of the fragment measure is the sum of the band masses, a.e.
  have hae : ∀ᵐ ω ∂(Measure.infinitePi fun k : ℤ =>
        PrimeGap182D1.finitePoissonLaw (PrimeGap182D1.cappedDyadicIntensity ζ k)),
      Complex.exp (↑(((PrimeGap182D1.finiteFragments ω).mass : ℝ) * t) * Complex.I)
        = ∏' k : ℤ, Complex.exp (↑(((ω k).mass : ℝ) * t) * Complex.I) := by
    filter_upwards [PrimeGap182D1.ae_isFiniteMeasure_fragment_sum ζ] with ω hω
    have hcov : ((PrimeGap182D1.finiteFragments ω : Measure ℝ))
        = Measure.sum (fun k : ℤ => (ω k : Measure ℝ)) := by
      have h1 : PrimeGap182D1.finiteFragments ω
          = (⟨Measure.sum fun k : ℤ => (ω k : Measure ℝ), hω⟩ : FiniteMeasure ℝ) := by
        unfold PrimeGap182D1.finiteFragments
        exact dite_eq_left hω
      rw [h1]
      rfl
    have hsumE : ((PrimeGap182D1.finiteFragments ω).mass : ℝ≥0∞)
        = ∑' k : ℤ, ((ω k).mass : ℝ≥0∞) := by
      rw [FiniteMeasure.ennreal_mass, hcov, Measure.sum_apply _ MeasurableSet.univ]
      exact tsum_congr fun k => (FiniteMeasure.ennreal_mass).symm
    have hfin : (∑' k : ℤ, ((ω k).mass : ℝ≥0∞)) ≠ ⊤ := by
      rw [← hsumE]
      exact ENNReal.coe_ne_top
    have hsumm : Summable fun k : ℤ => ((ω k).mass : ℝ) :=
      NNReal.summable_coe.mpr (ENNReal.tsum_coe_ne_top_iff_summable.mp hfin)
    have hmassr : ((PrimeGap182D1.finiteFragments ω).mass : ℝ)
        = ∑' k : ℤ, ((ω k).mass : ℝ) := by
      rw [← ENNReal.coe_toReal (r := (PrimeGap182D1.finiteFragments ω).mass), hsumE,
        ENNReal.tsum_toReal_eq (fun k => ENNReal.coe_ne_top)]
      exact tsum_congr fun k => ENNReal.coe_toReal _
    have hSC : Summable fun k : ℤ => (↑(((ω k).mass : ℝ) * t) : ℂ) * Complex.I := by
      have h1 : Summable fun k : ℤ => ((ω k).mass : ℝ) * |t| := hsumm.mul_right |t|
      refine (Summable.of_norm_bounded h1 (fun k => ?_)).mul_right Complex.I
      rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (ω k).mass.coe_nonneg]
    have harg : (↑(((PrimeGap182D1.finiteFragments ω).mass : ℝ) * t) : ℂ) * Complex.I
        = ∑' k : ℤ, (↑(((ω k).mass : ℝ) * t) : ℂ) * Complex.I := by
      rw [hmassr, Complex.ofReal_mul, Complex.ofReal_tsum, ← tsum_mul_right,
        ← tsum_mul_right]
      refine tsum_congr fun k => ?_
      push_cast
      ring
    rw [harg]
    exact hSC.hasSum.cexp.tprod_eq.symm
  rw [integral_congr_ae hae]
  have hE := summable_band_exponent hζ t
  calc ∫ ω, ∏' k : ℤ, Complex.exp (↑(((ω k).mass : ℝ) * t) * Complex.I)
        ∂(Measure.infinitePi fun k : ℤ =>
          PrimeGap182D1.finitePoissonLaw (PrimeGap182D1.cappedDyadicIntensity ζ k))
      = ∏' k : ℤ, ∫ c, Complex.exp (↑((c.mass : ℝ) * t) * Complex.I)
          ∂(PrimeGap182D1.finitePoissonLaw (PrimeGap182D1.cappedDyadicIntensity ζ k)) :=
        MeasureTheory.integral_tprod_infinitePi
          (fun k => (band_exp_integrand_measurable t).aestronglyMeasurable)
          (fun k => Filter.Eventually.of_forall (band_exp_integrand_bound t))
          (tsum_band_charFun_lintegral_ne_top hζ t)
    _ = ∏' k : ℤ, Complex.exp (∫ u, (Complex.exp (↑(u * t) * Complex.I) - 1)
          ∂(PrimeGap182D1.cappedDyadicIntensity ζ k : Measure ℝ)) :=
        tprod_congr (band_factor_identity hζ t)
    _ = Complex.exp (∑' k : ℤ, ∫ u, (Complex.exp (↑(u * t) * Complex.I) - 1)
          ∂(PrimeGap182D1.cappedDyadicIntensity ζ k : Measure ℝ)) :=
        hE.hasSum.cexp.tprod_eq
    _ = Complex.exp (-(charExponent t ζ)) := by rw [tsum_integral_band_exp hζ t]

/-- **`N1Residual` is no longer a named input.** -/
theorem n1Residual_holds : N1Residual := fun _ζ t hζ => charFun_mass_fragmentLaw hζ t

end PrimeGap182D2
