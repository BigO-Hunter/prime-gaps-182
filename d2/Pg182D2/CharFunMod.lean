import Mathlib
import Pg182D2.HasLocalBound

/-!
# CHARFUNMOD.lean — item (i) of the D4 data closure: the modulus of the band charFun

The fragment-law band is a Poisson process of intensity `du/u` on `(0, ζ]`, so the
characteristic function of its total mass is the Poisson (Skorokhod) exponent

    φ_ζ(t) = exp (-Ein (-I t ζ)),     Ein (I t u) = ∫_0^ζ (1 - e^{I t u})/u du,

and **the modulus computation is the whole content of the identity**:

    ‖φ_ζ(t)‖ = exp (-Cin (t ζ)),      Cin x = ∫_0^x (1 - cos u)/u du,

because `‖exp z‖ = exp (Re z)` and `Re (1 - e^{I t u}) = 1 - cos (t u)`, so the real
part of the exponent is exactly the `Cin` integral (and `Re (Ein (-I x)) = Cin x`,
the series identity `Cin x = Σ_{m≥1} (-1)^{m+1} x^{2m}/((2m)(2m)!)`).

## What this file proves

* `re_charExponent` — `Re (∫_0^ζ (1 - e^{I t u})/u) = Cin (t ζ)` (all `t`; no sign case):
  `Re` of the ℂ interval integral, then the substitution `x = t u`.
* `norm_exp_neg_charExponent` — `‖exp (-Ein)‖ = exp (-Cin (t ζ))`.
* `norm_charFun_exp_exponent` — the same for `‖charFun μ t‖` **given** the ℂ charFun
  identity (the Poisson bridge, named input (N1); see FINALSET_REPORT.md).
* `integral_norm_charFun_pow` / `integral_norm_charFun_pow_le` — the `d`-th power and the
  substitution to `x = t ζ`, i.e. the smoothing lemma's hypothesis
  `∀ R, ∫_0^R ‖charFun μ t‖^d ≤ I/ζ` from the certified single-variable bound
  `∀ R, ∫_0^R e^{-d Cin} ≤ I` (named input (N2)).
* `hasLocalBound_convPow_of_certified` — the two named inputs together give
  `HasLocalBound (μ^{*38}) (1/ζ)`, i.e. the D2 ledger's layer M.

Everything is `[propext, Classical.choice, Quot.sound]` only.
-/

noncomputable section
namespace PrimeGap182D2
open MeasureTheory intervalIntegral

/-- The complementary exponential integral `Cin x = ∫_0^x (1 - cos u)/u du` (the receipt's
`Cin`; the integrand is bounded at `0`, so the interval integral is the honest one). -/
def Cin (x : ℝ) : ℝ := ∫ u in (0)..x, (1 - Real.cos u) / u

/-- The band exponent in integral form: `Ein (-I (t ζ)) = ∫_0^ζ (1 - e^{I t u})/u du`. -/
def charExponent (t ζ : ℝ) : ℂ :=
  ∫ u in (0)..ζ, (1 - Complex.exp (Complex.I * (t * u))) / u

/-! ### The real part of the integrand -/

theorem cinExponent_integrand_re (t u : ℝ) :
    ((1 - Complex.exp (Complex.I * (t * u))) / u).re = (1 - Real.cos (t * u)) / u := by
  have hre : (Complex.I * ((t : ℂ) * (u : ℂ))).re = 0 := by simp
  have him : (Complex.I * ((t : ℂ) * (u : ℂ))).im = t * u := by simp
  have hz : ((1 - Complex.exp (Complex.I * (t * u))) * ((u⁻¹ : ℝ) : ℂ)).re
      = (1 - Real.cos (t * u)) * u⁻¹ := by
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
      Complex.sub_re, Complex.one_re, Complex.exp_re, hre, him, Real.exp_zero, one_mul]
  rw [div_eq_mul_inv, ← Complex.ofReal_inv, hz, div_eq_mul_inv]

/-! ### Integrability of the ℂ integrand on the band

`‖1 - e^{I θ}‖ ≤ ‖θ‖ e^{‖θ‖}`, so on `(0, ζ]` the integrand is bounded by `|t| e^{|t| ζ}`. -/

theorem norm_integrand_le (t : ℝ) {ζ u : ℝ} (hu : u ∈ Set.Ioc (0 : ℝ) ζ) :
    ‖(1 - Complex.exp (Complex.I * (t * u))) / u‖ ≤ |t| * Real.exp (|t| * ζ) := by
  have hu0 : (0 : ℝ) < u := hu.1
  have hule : u ≤ ζ := hu.2
  have huabs : |u| = u := abs_of_pos hu0
  have hexp : ‖Complex.exp (Complex.I * ((t * u : ℝ) : ℂ)) - 1‖
      ≤ (|t| * |u|) * Real.exp (|t| * |u|) := by
    have h := Complex.norm_exp_sub_sum_le_norm_mul_exp (Complex.I * ((t * u : ℝ) : ℂ)) 1
    simpa [abs_mul] using h
  have hstep : ‖(1 - Complex.exp (Complex.I * (t * u))) / u‖
      = ‖Complex.exp (Complex.I * (t * u)) - 1‖ / u := by
    rw [Complex.norm_div, norm_sub_rev, Complex.norm_real, Real.norm_eq_abs, huabs]
  rw [hstep]
  have hexp' : ‖Complex.exp (Complex.I * (t * u)) - 1‖ ≤ (|t| * u) * Real.exp (|t| * u) := by
    simpa [huabs] using hexp
  have h1 : ‖Complex.exp (Complex.I * (t * u)) - 1‖ / u
      ≤ ((|t| * u) * Real.exp (|t| * u)) / u :=
    div_le_div_of_nonneg_right hexp' hu0.le
  have h2 : ((|t| * u) * Real.exp (|t| * u)) / u = |t| * Real.exp (|t| * u) := by
    field_simp
  have h3 : |t| * Real.exp (|t| * u) ≤ |t| * Real.exp (|t| * ζ) := by
    have hle : |t| * u ≤ |t| * ζ := by
      have h0 : (0 : ℝ) ≤ |t| := abs_nonneg t
      nlinarith
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hle) (abs_nonneg t)
  linarith

theorem integrable_charExponent_integrand (t : ℝ) {ζ : ℝ} (hζ : 0 ≤ ζ) :
    Integrable (fun u : ℝ => (1 - Complex.exp (Complex.I * (t * u))) / u)
      (volume.restrict (Set.Ioc (0 : ℝ) ζ)) := by
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) ζ)) :=
    isFiniteMeasure_restrict.mpr (by simp)
  refine Integrable.of_bound ?_ (|t| * Real.exp (|t| * ζ)) ?_
  · exact (by fun_prop : Measurable
      fun u : ℝ => (1 - Complex.exp (Complex.I * (t * u))) / u).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    exact norm_integrand_le t hu

/-! ### The modulus computation: `Re` of the exponent is `Cin` -/

theorem re_charExponent {t ζ : ℝ} (hζ : 0 ≤ ζ) : (charExponent t ζ).re = Cin (t * ζ) := by
  have hInt := integrable_charExponent_integrand t hζ
  have h1 : (charExponent t ζ).re = ∫ u in (0)..ζ, (1 - Real.cos (t * u)) / u := by
    unfold charExponent
    rw [intervalIntegral.integral_of_le hζ]
    have hclm : (∫ x in Set.Ioc (0 : ℝ) ζ,
          (1 - Complex.exp (Complex.I * (t * x))) / x).re
        = ∫ x in Set.Ioc (0 : ℝ) ζ,
          ((1 - Complex.exp (Complex.I * (t * x))) / x).re := by
      have h := ContinuousLinearMap.integral_comp_comm (𝕜 := ℝ) Complex.reCLM hInt
      simpa only [Complex.reCLM_apply] using h.symm
    rw [hclm]
    rw [intervalIntegral.integral_of_le hζ]
    exact integral_congr_ae (Filter.Eventually.of_forall fun u => cinExponent_integrand_re t u)
  rw [h1]
  rcases eq_or_ne t 0 with ht | ht
  · subst ht
    simp [Cin]
  · have hfun : (fun u : ℝ => (1 - Real.cos (t * u)) / u)
        = fun u : ℝ => t * ((1 - Real.cos (t * u)) / (t * u)) := by
      funext u
      by_cases hu : u = 0
      · subst hu; simp
      · field_simp
    rw [hfun, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_mul_left (fun x : ℝ => (1 - Real.cos x) / x) ht,
      smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ ht, one_mul, mul_zero]
    rfl

theorem norm_exp_neg_charExponent {t ζ : ℝ} (hζ : 0 ≤ ζ) :
    ‖Complex.exp (-(charExponent t ζ))‖ = Real.exp (-(Cin (t * ζ))) := by
  rw [Complex.norm_exp, Complex.neg_re, re_charExponent hζ]

/-- **The modulus identity**, for the characteristic function, given the ℂ charFun identity
(named input (N1): the Poisson bridge — `Pg182D1/Support.lean:220` in its real form). -/
theorem norm_charFun_exp_exponent {μ : Measure ℝ} {t ζ : ℝ} (hζ : 0 ≤ ζ)
    (hphi : charFun μ t = Complex.exp (-(charExponent t ζ))) :
    ‖charFun μ t‖ = Real.exp (-(Cin (t * ζ))) := by
  rw [hphi, norm_exp_neg_charExponent hζ]

/-! ### The `d`-th power and the substitution `x = t ζ` -/

theorem integral_norm_charFun_pow {μ : Measure ℝ} {ζ : ℝ} (hζ : 0 < ζ)
    (hphi : ∀ t : ℝ, charFun μ t = Complex.exp (-(charExponent t ζ))) (d : ℕ) (R : ℝ) :
    ∫ t in (0)..R, ‖charFun μ t‖ ^ d
      = ζ⁻¹ * ∫ x in (0)..(R * ζ), Real.exp (-(d * Cin x)) := by
  have hpt : ∀ t : ℝ, ‖charFun μ t‖ ^ d = Real.exp (-(d * Cin (t * ζ))) := by
    intro t
    rw [norm_charFun_exp_exponent hζ.le (hphi t), ← Real.exp_nat_mul]
    congr 1
    ring
  have hcomm : (fun t : ℝ => Real.exp (-(d * Cin (t * ζ))))
      = fun t : ℝ => Real.exp (-(d * Cin (ζ * t))) := by
    funext t; rw [mul_comm t ζ]
  calc ∫ t in (0)..R, ‖charFun μ t‖ ^ d
      = ∫ t in (0)..R, Real.exp (-(d * Cin (t * ζ))) :=
        intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun t _ => hpt t)
    _ = ζ⁻¹ * ∫ x in (0)..(R * ζ), Real.exp (-(d * Cin x)) := by
        rw [hcomm, intervalIntegral.integral_comp_mul_left
          (fun x : ℝ => Real.exp (-(d * Cin x))) hζ.ne', smul_eq_mul]
        simp [mul_comm]

/-- **The smoothing hypothesis from the certified single-variable bound**: if every truncation
of `∫_0^∞ e^{-d Cin}` is at most `I`, then every truncation of `∫_0^∞ ‖charFun μ‖^d` is at
most `I/ζ`.  (`R ≤ 0` is trivial because the integrand is nonnegative.) -/
theorem integral_norm_charFun_pow_le {μ : Measure ℝ} {ζ : ℝ} (hζ : 0 < ζ)
    (hphi : ∀ t : ℝ, charFun μ t = Complex.exp (-(charExponent t ζ))) (d : ℕ) {I : ℝ}
    (hI : ∀ R : ℝ, ∫ x in (0)..R, Real.exp (-(d * Cin x)) ≤ I) :
    ∀ R : ℝ, ∫ t in (0)..R, ‖charFun μ t‖ ^ d ≤ I / ζ := by
  have hI0 : (0 : ℝ) ≤ I := le_trans (by simp) (hI 0)
  intro R
  rcases le_or_gt R 0 with hR | hR
  · have hnn : (0 : ℝ) ≤ ∫ t in R..(0 : ℝ), ‖charFun μ t‖ ^ d :=
      intervalIntegral.integral_nonneg hR (fun u _ => by positivity)
    have hsymm : ∫ t in (0)..R, ‖charFun μ t‖ ^ d = -∫ t in R..(0 : ℝ), ‖charFun μ t‖ ^ d := by
      have h := intervalIntegral.integral_symm (μ := volume) (a := R) (b := (0 : ℝ))
        (f := fun t : ℝ => ‖charFun μ t‖ ^ d)
      linarith
    rw [hsymm]
    have hpos : (0 : ℝ) ≤ I / ζ := div_nonneg hI0 hζ.le
    linarith
  · rw [integral_norm_charFun_pow hζ hphi d R]
    have h2 : ∫ x in (0)..(R * ζ), Real.exp (-(d * Cin x)) ≤ I := hI (R * ζ)
    have hinv : (0 : ℝ) < ζ⁻¹ := inv_pos.mpr hζ
    calc ζ⁻¹ * ∫ x in (0)..(R * ζ), Real.exp (-(d * Cin x)) ≤ ζ⁻¹ * I :=
          mul_le_mul_of_nonneg_left h2 hinv.le
      _ = I / ζ := by rw [div_eq_mul_inv, mul_comm]

/-! ### The payload: `HasLocalBound` at `d = 38` from the two named inputs -/

theorem hasLocalBound_convPow_of_certified {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hphi : ∀ t : ℝ, charFun μ t = Complex.exp (-(charExponent t zeta))) {I : ℝ}
    (hI : ∀ R : ℝ, ∫ x in (0)..R, Real.exp (-(38 * Cin x)) ≤ I)
    (hIz : I / zeta ≤ 4 / (Real.pi * zeta)) :
    HasLocalBound (convPow μ 38) (1 / zeta) :=
  hasLocalBound_convPow_one_div_zeta μ 38
    (integral_norm_charFun_pow_le zeta_pos hphi 38 hI) hIz

end PrimeGap182D2
