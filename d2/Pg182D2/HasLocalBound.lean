/-
# HasLocalBound.lean — Lane D3: the Fejér smoothing lemma, and `HasLocalBound` at `d = 38`

`Pg182D2/EnvLemmas.lean` isolates the one object every D2 envelope route bottoms out in:

    structure HasLocalBound (mu : Measure ℝ) (D : ℝ) : Prop where
      nonneg : 0 ≤ D
      bound  : ∀ a h : ℝ, 0 < h → mu (Set.Ioc a (a + h)) ≤ ENNReal.ofReal (D * h)

and consumes it in `cell_measure_le_hq` / `cell_measure_lt_hq`.  D2 named the proof of that
structure as the lane's only remaining analytic debt: **Mathlib has no smoothing
(Fejér/Esseen) lemma**, so the step from the characteristic function to a *point* probability
had no formal proof.

This file proves that step.  The smoothing lemma proved below is

    mu.real (Ioc a (a+h))  ≤  (π/4) * B * h     whenever   B ≥ ∫_0^∞ ‖charFun mu t‖ dt,

the `θ = π` member of the family `θ h / (2(1 - cos θ)) · ∫_0^{2θ/h} (1 - t/(2θ/h)) ‖φ‖ dt`.
So the analytic debt is discharged **for every law whose characteristic function is integrable
to the first power** — exactly the `d = 38` situation (`‖φ_38‖ = ‖φ‖^38 = e^{-38 Cin}`), and
exactly NOT the `d = 1` situation, where `∫ ‖φ‖ = ∞` and the measured `5.724 hq` log divergence
of `ROUTE2.md` is the truth.  The lemma reproduces that boundary as a theorem.

The remaining inputs to the final `HasLocalBound` instance are then purely *computational*:
`‖charFun (38-fold law) t‖ = exp (-38 * Cin (t * zeta))`, and the certified rational bound
`∫_0^∞ e^{-38 Cin} ≤ 0.3945` of `receipt/receipt.py`.  Both are recorded, with their exact
shapes, in `LOCALBOUND_REPORT.md`.
-/
import Pg182D2.EnvLemmas

noncomputable section

open MeasureTheory intervalIntegral
open scoped ENNReal

namespace PrimeGap182D2

/-! ### 1. The Fejér kernel

`K_R(x) = R^2 (sinc (R x / 2))^2 = 2(1 - cos (R x))/x^2` (the second form for `x ≠ 0`) is the
inverse Fourier transform of the triangular weight `(1 - |t|/R)_+`.  Two properties are used:
`K_R ≥ 0`, `K_R ≤ R^2`, and `K_R(x) ≥ 4R^2/π^2` on `|Rx| ≤ π` (Jordan's inequality in cos form,
`Real.cos_le_one_sub_mul_cos_sq`).
-/

/-- The Fejér kernel, normalised so that `∫_0^R 2 r sinc (r x) dr = fejerKernel R x`. -/
def fejerKernel (R x : ℝ) : ℝ := R ^ 2 * (Real.sinc (R * x / 2)) ^ 2

theorem fejerKernel_nonneg (R : ℝ) (x : ℝ) : 0 ≤ fejerKernel R x := by
  unfold fejerKernel
  positivity

theorem fejerKernel_zero (R : ℝ) : fejerKernel R 0 = R ^ 2 := by
  unfold fejerKernel
  simp

theorem fejerKernel_of_ne {R x : ℝ} (hx : x ≠ 0) :
    fejerKernel R x = 2 * (1 - Real.cos (R * x)) / x ^ 2 := by
  unfold fejerKernel
  by_cases hR : R = 0
  · simp [hR]
  · have hy : R * x / 2 ≠ 0 := by
      intro h0
      have h1 : R * x = 0 := by linarith
      rcases mul_eq_zero.mp h1 with h | h
      · exact hR h
      · exact hx h
    rw [Real.sinc_of_ne_zero hy, div_pow, Real.sin_sq_eq_half_sub]
    field_simp

/-- The kernel is bounded by `R^2`. -/
theorem fejerKernel_le (R : ℝ) (x : ℝ) : fejerKernel R x ≤ R ^ 2 := by
  unfold fejerKernel
  have h1 : (Real.sinc (R * x / 2)) ^ 2 ≤ 1 := by
    have habs := Real.abs_sinc_le_one (R * x / 2)
    nlinarith [abs_nonneg (Real.sinc (R * x / 2)), sq_abs (Real.sinc (R * x / 2))]
  exact mul_le_of_le_one_right (sq_nonneg R) h1

theorem hasDerivAt_sinc_antideriv {x : ℝ} (hx : x ≠ 0) (r : ℝ) :
    HasDerivAt (fun r : ℝ => 2 * (1 - Real.cos (r * x)) / x ^ 2)
      (2 * Real.sin (r * x) / x) r := by
  have hd : HasDerivAt (fun y : ℝ => Real.cos (y * x)) (-(Real.sin (r * x)) * x) r := by
    simpa using ((hasDerivAt_id r).mul_const x).cos
  have h1 : HasDerivAt (fun y : ℝ => (1 : ℝ) - Real.cos (y * x))
      (0 - (-(Real.sin (r * x)) * x)) r :=
    (hasDerivAt_const (x := r) (c := (1 : ℝ))).sub hd
  have h2 : HasDerivAt (fun y : ℝ => 2 * (1 - Real.cos (y * x)))
      (2 * (0 - (-(Real.sin (r * x)) * x))) r := h1.const_mul 2
  have h3 : HasDerivAt (fun y : ℝ => 2 * (1 - Real.cos (y * x)) / x ^ 2)
      (2 * (0 - (-(Real.sin (r * x)) * x)) / x ^ 2) r := h2.div_const (x ^ 2)
  have hval : 2 * (0 - (-(Real.sin (r * x)) * x)) / x ^ 2 = 2 * Real.sin (r * x) / x := by
    field_simp
    ring
  rw [hval] at h3
  exact h3

/-- `2 r sinc (r x) = 2 sin (r x) / x` for `x ≠ 0`, including `r = 0` (both sides vanish). -/
theorem sinc_mul_eq {x : ℝ} (hx : x ≠ 0) (r : ℝ) :
    2 * r * Real.sinc (r * x) = 2 * Real.sin (r * x) / x := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  · rw [Real.sinc_of_ne_zero (mul_ne_zero hr hx)]
    field_simp

/-- **The kernel identity, pointwise.** `fejerKernel R` is exactly `∫_0^R 2 r sinc (r x) dr`. -/
theorem fejerKernel_eq_integral (R x : ℝ) :
    ∫ r in (0)..R, 2 * r * Real.sinc (r * x) = fejerKernel R x := by
  rcases eq_or_ne x 0 with rfl | hx
  · have hgoal : ∫ r in (0)..R, (2 * r * Real.sinc (r * 0)) = ∫ r in (0)..R, 2 * r := by
      apply intervalIntegral.integral_congr
      intro r _
      simp
    rw [hgoal, fejerKernel_zero]
    have hderiv : ∀ r ∈ Set.uIcc (0:ℝ) R, HasDerivAt (fun r : ℝ => r ^ 2) (2 * r) r :=
      fun r _ => by simpa using (hasDerivAt_pow 2 r)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      ((by fun_prop : Continuous fun r : ℝ => 2 * r).intervalIntegrable _ _)]
    simp
  · have hgoal : ∫ r in (0)..R, (2 * r * Real.sinc (r * x))
        = ∫ r in (0)..R, 2 * Real.sin (r * x) / x := by
      apply intervalIntegral.integral_congr
      intro r _
      exact sinc_mul_eq hx r
    rw [hgoal, fejerKernel_of_ne hx]
    have hderiv : ∀ r ∈ Set.uIcc (0:ℝ) R,
        HasDerivAt (fun r : ℝ => 2 * (1 - Real.cos (r * x)) / x ^ 2)
          (2 * Real.sin (r * x) / x) r :=
      fun r _ => hasDerivAt_sinc_antideriv hx r
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      ((by fun_prop : Continuous fun r : ℝ => 2 * Real.sin (r * x) / x).intervalIntegrable _ _)]
    simp

/-- **Kernel lower bound.** With `R h = 2π`, on `|z| ≤ h/2` the kernel is at least
`4 R^2 / π^2`. -/
theorem fejerKernel_ge (R h : ℝ) (hR : 0 < R) (hRh : R * h = 2 * Real.pi)
    {z : ℝ} (hz : |z| ≤ h / 2) : 4 * R ^ 2 / Real.pi ^ 2 ≤ fejerKernel R z := by
  rcases eq_or_ne z 0 with rfl | hz0
  · rw [fejerKernel_zero]
    have hle : (4 : ℝ) / Real.pi ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]
      nlinarith [Real.pi_gt_three]
    calc 4 * R ^ 2 / Real.pi ^ 2 = (4 / Real.pi ^ 2) * R ^ 2 := by ring
      _ ≤ 1 * R ^ 2 := by gcongr
      _ = R ^ 2 := by ring
  · rw [fejerKernel_of_ne hz0]
    have hRz : |R * z| ≤ Real.pi := by
      rw [abs_mul, abs_of_pos hR]
      calc R * |z| ≤ R * (h / 2) := mul_le_mul_of_nonneg_left hz hR.le
        _ = Real.pi := by
            have h2 : R * (h / 2) = R * h / 2 := by ring
            rw [h2, hRh]; ring
    have hcos := Real.cos_le_one_sub_mul_cos_sq hRz
    have hz2 : 0 < z ^ 2 := by positivity
    have h1 : 2 * (2 / Real.pi ^ 2 * (R * z) ^ 2) / z ^ 2 ≤
        2 * (1 - Real.cos (R * z)) / z ^ 2 := by
      apply div_le_div_of_nonneg_right _ hz2.le
      linarith
    have h2 : 2 * (2 / Real.pi ^ 2 * (R * z) ^ 2) / z ^ 2 = 4 * R ^ 2 / Real.pi ^ 2 := by
      field_simp
      ring
    rw [← h2]
    exact h1

/-! ### 2. The smoothing lemma

Mathlib's `integral_charFun_Icc` gives, for every `r > 0`,

    ∫ t in -r..r, charFun mu t = 2 r ∫ x, sinc (r x) dmu.

Averaging over `r ∈ (0, R]` (one rectangle Fubini) transcribes the Fejér kernel into the
characteristic function; the result is then bounded by `2 R B`.
-/

/-- Mathlib's sinc identity, real form. -/
theorem integral_charFun_re_Icc (ν : Measure ℝ) [IsFiniteMeasure ν] {r : ℝ} (hr : 0 < r) :
    ∫ t in (-r)..r, (charFun ν t).re = 2 * r * ∫ x, Real.sinc (r * x) ∂ν := by
  have h := MeasureTheory.integral_charFun_Icc (μ := ν) hr
  have h2 : (∫ t in (-r)..r, charFun ν t).re = 2 * r * ∫ x, Real.sinc (r * x) ∂ν := by
    simpa using congrArg Complex.re h
  rw [← h2, intervalIntegral.integral_of_le (by linarith : -r ≤ r),
    intervalIntegral.integral_of_le (by linarith : -r ≤ r)]
  exact integral_re (intervalIntegrable_charFun (μ := ν) (a := -r) (b := r)).1

/-- The characteristic function of a shifted measure has the same modulus. -/
theorem norm_charFun_shift (ν : Measure ℝ) (c t : ℝ) :
    ‖charFun (Measure.map (fun x : ℝ => x + (-c)) ν) t‖ = ‖charFun ν t‖ := by
  rw [charFun_map_add_const, norm_mul]
  have hone : ‖Complex.exp (((inner ℝ (-c) t : ℝ) : ℂ) * Complex.I)‖ = 1 := by
    rw [Complex.norm_exp]
    have hre : (((inner ℝ (-c) t : ℝ) : ℂ) * Complex.I).re = 0 := by simp
    rw [hre, Real.exp_zero]
  rw [hone, mul_one]

/-- The sinc integral with a shifted argument, as an integral against the shifted measure. -/
theorem integral_sinc_shift (ν : Measure ℝ) (r c : ℝ) :
    ∫ x, Real.sinc (r * (x - c)) ∂ν
      = ∫ y, Real.sinc (r * y) ∂(Measure.map (fun x : ℝ => x + (-c)) ν) := by
  rw [MeasureTheory.integral_map (by fun_prop) (by fun_prop)]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  simp only [sub_eq_add_neg]

/-- **The inner bound**: the sinc integral at scale `r` is controlled by the modulus of the
characteristic function on `(-r, r)`. -/
theorem abs_integral_sinc_le (ν : Measure ℝ) [IsFiniteMeasure ν] {r c : ℝ} (hr : 0 < r) :
    |∫ x, Real.sinc (r * (x - c)) ∂ν| ≤ (1 / (2 * r)) * ∫ t in (-r)..r, ‖charFun ν t‖ := by
  rw [integral_sinc_shift ν r c]
  have hcf := integral_charFun_re_Icc (Measure.map (fun x : ℝ => x + (-c)) ν) hr
  have hsinc : ∫ y, Real.sinc (r * y) ∂(Measure.map (fun x : ℝ => x + (-c)) ν)
      = (1 / (2 * r)) * ∫ t in (-r)..r,
          (charFun (Measure.map (fun x : ℝ => x + (-c)) ν) t).re := by
    rw [hcf]; field_simp
  rw [hsinc, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / (2 * r))]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  calc |∫ t in (-r)..r, (charFun (Measure.map (fun x : ℝ => x + (-c)) ν) t).re|
      ≤ ∫ t in (-r)..r, |(charFun (Measure.map (fun x : ℝ => x + (-c)) ν) t).re| :=
        intervalIntegral.norm_integral_le_integral_norm
          (f := fun t : ℝ => (charFun (Measure.map (fun x : ℝ => x + (-c)) ν) t).re) (by linarith)
    _ ≤ ∫ t in (-r)..r, ‖charFun (Measure.map (fun x : ℝ => x + (-c)) ν) t‖ := by
        refine intervalIntegral.integral_mono_on (by linarith) ?_ ?_ ?_
        · refine IntervalIntegrable.mono_fun'
            (g := fun t : ℝ => ‖charFun (Measure.map (fun x : ℝ => x + (-c)) ν) t‖)
            (intervalIntegrable_charFun (μ := Measure.map (fun x : ℝ => x + (-c)) ν)
              (a := -r) (b := r)).norm (by fun_prop) ?_
          filter_upwards with t
          simpa using Complex.abs_re_le_norm (charFun (Measure.map (fun x : ℝ => x + (-c)) ν) t)
        · exact (intervalIntegrable_charFun (μ := Measure.map (fun x : ℝ => x + (-c)) ν)
            (a := -r) (b := r)).norm
        · intro t _
          simpa using Complex.abs_re_le_norm (charFun (Measure.map (fun x : ℝ => x + (-c)) ν) t)
    _ = ∫ t in (-r)..r, ‖charFun ν t‖ := by
        apply intervalIntegral.integral_congr
        intro t _
        exact norm_charFun_shift ν c t

/-- **The rectangle Fubini.** The Fejér kernel against `ν` equals the averaged sinc integral. -/
theorem integral_fejerKernel_eq (ν : Measure ℝ) [IsFiniteMeasure ν] {R c : ℝ} (hR : 0 < R) :
    ∫ x, fejerKernel R (x - c) ∂ν
      = ∫ r in (0)..R, 2 * r * (∫ x, Real.sinc (r * (x - c)) ∂ν) := by
  have hpt : ∀ x : ℝ, fejerKernel R (x - c)
      = ∫ r in (0)..R, 2 * r * Real.sinc (r * (x - c)) :=
    fun x => (fejerKernel_eq_integral R (x - c)).symm
  simp_rw [hpt]
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioc (0:ℝ) R)) := by
    constructor
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top
  have hmeasure : ν.prod (volume.restrict (Set.Ioc (0:ℝ) R))
      = (ν.prod volume).restrict (Set.univ ×ˢ Set.Ioc (0:ℝ) R) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  have hbdd : ∀ᵐ p ∂(ν.prod (volume.restrict (Set.Ioc (0:ℝ) R))),
      ‖2 * p.2 * Real.sinc (p.2 * (p.1 - c))‖ ≤ 2 * R := by
    rw [hmeasure, ae_restrict_iff' (MeasurableSet.univ.prod measurableSet_Ioc)]
    filter_upwards with p hp
    obtain ⟨hr1, hr2⟩ := hp.2
    have h2p : |2 * p.2| ≤ 2 * R := by
      rw [abs_of_pos (by linarith : (0:ℝ) < 2 * p.2)]
      linarith
    rw [Real.norm_eq_abs, abs_mul]
    calc |2 * p.2| * |Real.sinc (p.2 * (p.1 - c))| ≤ (2 * R) * 1 :=
          mul_le_mul h2p (Real.abs_sinc_le_one _) (abs_nonneg _) (by linarith)
      _ = 2 * R := by ring
  have hInt' : Integrable (fun p : ℝ × ℝ => 2 * p.2 * Real.sinc (p.2 * (p.1 - c)))
      (ν.prod (volume.restrict (Set.Ioc (0:ℝ) R))) := by
    refine Integrable.of_bound (C := 2 * R) (by fun_prop) ?_
    exact hbdd
  calc ∫ x, (∫ r in (0)..R, 2 * r * Real.sinc (r * (x - c))) ∂ν
      = ∫ x, (∫ r, 2 * r * Real.sinc (r * (x - c))
            ∂(volume.restrict (Set.Ioc (0:ℝ) R))) ∂ν := by
        simp only [intervalIntegral.integral_of_le hR.le]
    _ = ∫ r, (∫ x, 2 * r * Real.sinc (r * (x - c)) ∂ν)
          ∂(volume.restrict (Set.Ioc (0:ℝ) R)) := MeasureTheory.integral_integral_swap hInt'
    _ = ∫ r in (0)..R, 2 * r * (∫ x, Real.sinc (r * (x - c)) ∂ν) := by
        rw [intervalIntegral.integral_of_le hR.le]
        apply MeasureTheory.integral_congr_ae
        filter_upwards with r
        rw [MeasureTheory.integral_const_mul]

/-- `∫_{-R}^{R} g = 2 ∫_0^R g` for an even integrand. -/
theorem integral_neg_eq_two (g : ℝ → ℝ) (hneg : ∀ t, g (-t) = g t) {R : ℝ} (hR : 0 ≤ R)
    (hint : ∀ a b : ℝ, IntervalIntegrable g volume a b) :
    ∫ t in (-R)..R, g t = 2 * ∫ t in (0)..R, g t := by
  have hadj : (∫ t in (-R)..0, g t) + (∫ t in (0)..R, g t) = ∫ t in (-R)..R, g t := by
    simpa using intervalIntegral.integral_add_adjacent_intervals (μ := volume) (hint (-R) 0) (hint 0 R)
  have hleft : ∫ t in (-R)..0, g t = ∫ t in (0)..R, g t := by
    have h1 : ∫ t in (-R)..0, g t = ∫ t in (-R)..0, g (-t) := by
      apply intervalIntegral.integral_congr
      intro t _
      exact (hneg t).symm
    rw [h1]
    have h2 : ∫ t in (-R)..0, g (-t) = ∫ t in (0)..R, g t := by
      have h3 := intervalIntegral.integral_comp_sub_left g (d := 0) (a := -R) (b := 0)
      simpa using h3
    rw [h2]
  have htwo : (∫ t in (-R)..R, g t) = (∫ t in (-R)..0, g t) + (∫ t in (0)..R, g t) := hadj.symm
  rw [htwo, hleft]
  ring

/-- **The smoothing bound.** `∫ K_R(· - c) dν ≤ 2 R B` when `B` bounds every truncation
`∫_0^R ‖charFun ν‖` of the characteristic function's modulus. -/
theorem integral_fejerKernel_le (ν : Measure ℝ) [IsFiniteMeasure ν] {B : ℝ}
    (hB : ∀ R : ℝ, ∫ t in (0)..R, ‖charFun ν t‖ ≤ B) {R c : ℝ} (hR : 0 < R) :
    ∫ x, fejerKernel R (x - c) ∂ν ≤ 2 * R * B := by
  rw [integral_fejerKernel_eq ν hR]
  have hsym : ∫ t in (-R)..R, ‖charFun ν t‖ = 2 * ∫ t in (0)..R, ‖charFun ν t‖ := by
    refine integral_neg_eq_two (fun t => ‖charFun ν t‖) (fun t => ?_) hR.le
      (fun a b => intervalIntegrable_charFun.norm)
    rw [MeasureTheory.charFun_neg, Complex.norm_conj]
  -- step 1: bound the integrand pointwise on [0, R]
  have hstep : ∀ r ∈ Set.Icc (0:ℝ) R,
      2 * r * (∫ x, Real.sinc (r * (x - c)) ∂ν) ≤ ∫ t in (-R)..R, ‖charFun ν t‖ := by
    intro r hr
    obtain ⟨hr0, hrR⟩ := hr
    rcases eq_or_ne r 0 with rfl | hrne
    · simp only [mul_zero, zero_mul]
      exact intervalIntegral.integral_nonneg (by linarith) (fun t _ => norm_nonneg _)
    · have hr0' : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hrne)
      have h1 : |∫ x, Real.sinc (r * (x - c)) ∂ν| ≤
          (1 / (2 * r)) * ∫ t in (-r)..r, ‖charFun ν t‖ := abs_integral_sinc_le ν hr0'
      have h2 : ∫ t in (-r)..r, ‖charFun ν t‖ ≤ ∫ t in (-R)..R, ‖charFun ν t‖ := by
        rw [intervalIntegral.integral_of_le (by linarith : -r ≤ r),
          intervalIntegral.integral_of_le (by linarith : -R ≤ R)]
        refine MeasureTheory.setIntegral_mono_set
          (intervalIntegrable_charFun (μ := ν) (a := -R) (b := R)).norm.1
          (MeasureTheory.ae_of_all _ fun t => norm_nonneg (charFun ν t)) ?_
        exact MeasureTheory.ae_of_all _ fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
      have h3 : 2 * r * (∫ x, Real.sinc (r * (x - c)) ∂ν)
          ≤ 2 * r * |∫ x, Real.sinc (r * (x - c)) ∂ν| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) (by linarith)
      have h4 : 2 * r * ((1 / (2 * r)) * ∫ t in (-r)..r, ‖charFun ν t‖)
          = ∫ t in (-r)..r, ‖charFun ν t‖ := by
        field_simp
      calc 2 * r * (∫ x, Real.sinc (r * (x - c)) ∂ν)
          ≤ 2 * r * |∫ x, Real.sinc (r * (x - c)) ∂ν| := h3
        _ ≤ 2 * r * ((1 / (2 * r)) * ∫ t in (-r)..r, ‖charFun ν t‖) := by
            apply mul_le_mul_of_nonneg_left h1 (by linarith)
        _ = ∫ t in (-r)..r, ‖charFun ν t‖ := h4
        _ ≤ ∫ t in (-R)..R, ‖charFun ν t‖ := h2
  -- step 2: the sinc side is interval integrable (bounded by `2 R * ν.real univ`)
  have hIg : IntervalIntegrable (fun r : ℝ => 2 * r * (∫ x, Real.sinc (r * (x - c)) ∂ν))
      volume 0 R := by
    have hm : StronglyMeasurable (fun r : ℝ => ∫ x, Real.sinc (r * (x - c)) ∂ν) :=
      MeasureTheory.StronglyMeasurable.integral_prod_right
        (f := fun r x => Real.sinc (r * (x - c))) (by fun_prop)
    have hsm : StronglyMeasurable (fun r : ℝ => 2 * r * (∫ x, Real.sinc (r * (x - c)) ∂ν)) := by
      have h1 : StronglyMeasurable
          (fun r : ℝ => (∫ x, Real.sinc (r * (x - c)) ∂ν) * (2 * r)) :=
        hm.mul (continuous_const.mul continuous_id).stronglyMeasurable
      simpa [mul_comm] using h1
    have hsin : ∀ r ∈ Set.Ioc (0:ℝ) R,
        |∫ x, Real.sinc (r * (x - c)) ∂ν| ≤ ν.real Set.univ := by
      intro r _
      have hcomp : Integrable (fun x : ℝ => Real.sinc (r * (x - c))) ν :=
        Integrable.of_bound (C := 1) (by fun_prop) (MeasureTheory.ae_of_all _ fun x => by
          rw [Real.norm_eq_abs]; exact Real.abs_sinc_le_one _)
      calc |∫ x, Real.sinc (r * (x - c)) ∂ν|
          ≤ ∫ x, ‖Real.sinc (r * (x - c))‖ ∂ν := by
            rw [← Real.norm_eq_abs]
            exact MeasureTheory.norm_integral_le_integral_norm _
        _ ≤ ∫ x, (1:ℝ) ∂ν := by
            refine MeasureTheory.integral_mono hcomp.norm
              (MeasureTheory.integrable_const (μ := ν) (c := (1:ℝ))) ?_
            intro x
            simpa using Real.abs_sinc_le_one (r * (x - c))
        _ = ν.real Set.univ := by
            rw [MeasureTheory.integral_const]
            simp
    refine IntervalIntegrable.mono_fun'
      (g := fun _ : ℝ => 2 * R * ν.real Set.univ) intervalIntegrable_const
      hsm.aestronglyMeasurable ?_
    rw [Set.uIoc_of_le hR.le]
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with r hr
    have hsinr := hsin r hr
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by linarith [hr.1] : (0:ℝ) < 2 * r)]
    calc (2 * r) * |∫ x, Real.sinc (r * (x - c)) ∂ν| ≤ (2 * R) * (ν.real Set.univ) :=
          mul_le_mul (by linarith [hr.2]) hsinr (abs_nonneg _) (by linarith)
      _ = 2 * R * ν.real Set.univ := by ring
  have hmono : ∫ r in (0)..R, 2 * r * (∫ x, Real.sinc (r * (x - c)) ∂ν)
      ≤ ∫ r in (0)..R, (∫ t in (-R)..R, ‖charFun ν t‖) := by
    refine intervalIntegral.integral_mono_on (by linarith) hIg intervalIntegrable_const ?_
    intro r hr
    exact hstep r ⟨hr.1, hr.2⟩
  have hconst : ∫ r in (0)..R, (∫ t in (-R)..R, ‖charFun ν t‖)
      = R * ∫ t in (-R)..R, ‖charFun ν t‖ := by
    rw [intervalIntegral.integral_const]
    ring
  have hbound2 : ∫ t in (-R)..R, ‖charFun ν t‖ ≤ 2 * B := by
    rw [hsym]
    have hle := hB R
    linarith
  calc ∫ r in (0)..R, 2 * r * (∫ x, Real.sinc (r * (x - c)) ∂ν)
      ≤ ∫ r in (0)..R, (∫ t in (-R)..R, ‖charFun ν t‖) := hmono
    _ = R * ∫ t in (-R)..R, ‖charFun ν t‖ := hconst
    _ ≤ R * (2 * B) := by
        apply mul_le_mul_of_nonneg_left hbound2 hR.le
    _ = 2 * R * B := by ring

/-! ### 3. `HasLocalBound` from a bounded truncated Fejér integral -/

/-- **The Fejér smoothing lemma, in `HasLocalBound` form.**  For a finite measure `ν` and a real
`B` that bounds every truncated integral `∫_0^R ‖charFun ν‖` (`R > 0`), the measure has local
density bound `π/4 · B`.  (The optimal constant is `min_θ θ/(2(1-cos θ)) = 0.6900`; `π/4` is the
`θ = π` member, chosen because it needs no trigonometric optimisation.) -/
theorem hasLocalBound_of_charFun_bound (ν : Measure ℝ) [IsFiniteMeasure ν] {B : ℝ}
    (hB : ∀ R : ℝ, ∫ t in (0)..R, ‖charFun ν t‖ ≤ B) :
    HasLocalBound ν (Real.pi / 4 * B) := by
  have hB0 : 0 ≤ B := le_trans (intervalIntegral.integral_nonneg (by norm_num)
    (fun t _ => norm_nonneg _)) (hB 1)
  refine ⟨by positivity, ?_⟩
  intro a h hh
  set R : ℝ := 2 * Real.pi / h with hRdef
  have hR : 0 < R := by rw [hRdef]; positivity
  have hRh : R * h = 2 * Real.pi := by rw [hRdef]; field_simp
  set c : ℝ := a + h / 2 with hcdef
  have hmem : ∀ x ∈ Set.Icc a (a + h), |x - c| ≤ h / 2 := by
    intro x hx
    obtain ⟨h1, h2⟩ := hx
    rw [abs_le]
    constructor <;> simp only [hcdef] <;> linarith
  have hpoint : ∀ x ∈ Set.Icc a (a + h), 4 * R ^ 2 / Real.pi ^ 2 ≤ fejerKernel R (x - c) :=
    fun x hx => fejerKernel_ge R h hR hRh (hmem x hx)
  have hIntK : Integrable (fun x : ℝ => fejerKernel R (x - c)) ν := by
    refine Integrable.of_bound (C := R ^ 2) ?_ ?_
    · have hfun : (fun x : ℝ => fejerKernel R (x - c))
          = fun x : ℝ => R ^ 2 * (Real.sinc (R * (x - c) / 2)) ^ 2 := by
        funext x; rfl
      rw [hfun]
      fun_prop
    · filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (fejerKernel_nonneg R (x - c))]
      exact fejerKernel_le R (x - c)
  have hreal : ν.real (Set.Icc a (a + h)) * (4 * R ^ 2 / Real.pi ^ 2)
      ≤ ∫ x, fejerKernel R (x - c) ∂ν := by
    haveI : IsFiniteMeasure (ν.restrict (Set.Icc a (a + h))) := by
      constructor
      rw [Measure.restrict_apply_univ]
      exact measure_lt_top _ _
    calc ν.real (Set.Icc a (a + h)) * (4 * R ^ 2 / Real.pi ^ 2)
        = ∫ x in Set.Icc a (a + h), (4 * R ^ 2 / Real.pi ^ 2) ∂ν := by
          rw [MeasureTheory.setIntegral_const, smul_eq_mul, mul_comm]
      _ ≤ ∫ x in Set.Icc a (a + h), fejerKernel R (x - c) ∂ν := by
          refine MeasureTheory.setIntegral_mono_on ?_ hIntK.integrableOn measurableSet_Icc hpoint
          exact MeasureTheory.integrable_const
            (μ := ν.restrict (Set.Icc a (a + h))) (c := 4 * R ^ 2 / Real.pi ^ 2)
      _ ≤ ∫ x, fejerKernel R (x - c) ∂ν :=
          MeasureTheory.setIntegral_le_integral hIntK
            (MeasureTheory.ae_of_all _ fun x => fejerKernel_nonneg R (x - c))
  have hupper : ∫ x, fejerKernel R (x - c) ∂ν ≤ 2 * R * B :=
    integral_fejerKernel_le (ν := ν) (B := B) (R := R) (c := c) hB hR
  have hmain : ν.real (Set.Icc a (a + h)) * (4 * R ^ 2 / Real.pi ^ 2) ≤ 2 * R * B :=
    le_trans hreal hupper
  have hpos : 0 < 4 * R ^ 2 / Real.pi ^ 2 := by positivity
  have hle : ν.real (Set.Icc a (a + h)) ≤ Real.pi / 4 * B * h := by
    have heq : Real.pi / 4 * B * h = (2 * R * B) / (4 * R ^ 2 / Real.pi ^ 2) := by
      rw [hRdef]; field_simp
    rw [heq]
    exact (le_div_iff₀ hpos).mpr hmain
  have hmono : ν.real (Set.Ioc a (a + h)) ≤ ν.real (Set.Icc a (a + h)) :=
    measureReal_mono (Set.Ioc_subset_Icc_self) (measure_ne_top _ _)
  have hfin : ν (Set.Ioc a (a + h)) ≠ ⊤ := measure_ne_top _ _
  calc ν (Set.Ioc a (a + h))
      = ENNReal.ofReal (ν.real (Set.Ioc a (a + h))) := by
        rw [measureReal_def, ENNReal.ofReal_toReal hfin]
    _ ≤ ENNReal.ofReal (Real.pi / 4 * B * h) := ENNReal.ofReal_le_ofReal (le_trans hmono hle)

/-- The same, from the full integral `∫_0^∞ ‖charFun ν‖ ≤ B` (the natural hypothesis for a law
with an integrable characteristic function, e.g. `|φ_38| = e^{-38 Cin}`). -/
theorem hasLocalBound_of_integrable_charFun (ν : Measure ℝ) [IsFiniteMeasure ν] {B : ℝ}
    (hint : IntegrableOn (fun t : ℝ => ‖charFun ν t‖) (Set.Ioi (0:ℝ)) volume)
    (hB : ∫ t in Set.Ioi (0:ℝ), ‖charFun ν t‖ ≤ B) :
    HasLocalBound ν (Real.pi / 4 * B) := by
  have hB0 : 0 ≤ B := le_trans (MeasureTheory.setIntegral_nonneg measurableSet_Ioi
    (fun t _ => norm_nonneg (charFun ν t))) hB
  refine hasLocalBound_of_charFun_bound ν (fun R => ?_)
  rcases le_or_gt 0 R with hR | hR
  · rw [intervalIntegral.integral_of_le hR]
    refine le_trans ?_ hB
    refine MeasureTheory.setIntegral_mono_set hint
      (MeasureTheory.ae_of_all _ fun t => norm_nonneg (charFun ν t)) ?_
    exact MeasureTheory.ae_of_all _ fun t ht => ht.1
  · rw [intervalIntegral.integral_of_ge hR.le]
    have hpos : 0 ≤ ∫ x in Set.Ioc R 0, ‖charFun ν x‖ ∂volume :=
      MeasureTheory.setIntegral_nonneg measurableSet_Ioc (fun t _ => norm_nonneg _)
    linarith

/-- **The `d = 38` shape.**  If `B` bounds every truncated Fejér integral and
`B ≤ 4/(π ζ)`, the measure satisfies the *same* local bound `1/ζ` that
`EnvLemmas.cell_measure_le_hq` consumes.  The certified `C38 = 0.29586259` (and a fortiori the
true value `0.1894`) is `4/(π ζ) = 1.2113` inside this. -/
theorem hasLocalBound_one_div_zeta (ν : Measure ℝ) [IsFiniteMeasure ν] {B : ℝ}
    (hB : ∀ R : ℝ, ∫ t in (0)..R, ‖charFun ν t‖ ≤ B) (hBz : B ≤ 4 / (Real.pi * zeta)) :
    HasLocalBound ν (1 / zeta) := by
  have hz : 0 < zeta := zeta_pos
  have hB0 : 0 ≤ B := le_trans (intervalIntegral.integral_nonneg (by norm_num)
    (fun t _ => norm_nonneg _)) (hB 1)
  have hle : Real.pi / 4 * B ≤ 1 / zeta := by
    have h4 : (0:ℝ) < 4 := by norm_num
    have hpz : (0:ℝ) < Real.pi * zeta := by positivity
    rw [show Real.pi / 4 * B = Real.pi * B / 4 by ring, div_le_iff₀ h4,
      show (1 / zeta) * 4 = 4 / zeta by ring, le_div_iff₀ hz]
    have h1 : B * (Real.pi * zeta) ≤ 4 := by
      rw [le_div_iff₀ hpz] at hBz
      exact hBz
    nlinarith [h1]
  exact ⟨by positivity, fun a h hh => le_trans
    ((hasLocalBound_of_charFun_bound ν hB).bound a h hh) (ENNReal.ofReal_le_ofReal (by
      have h2 := mul_le_mul_of_nonneg_right hle hh.le
      linarith))⟩

/-- **The payload.**  `HasLocalBound` at `D = 1/ζ` from a truncated-Fejér-integral bound,
consumed exactly as `EnvLemmas.cell_measure_le_hq` consumes it: every cell of the frozen grid
gets mass at most the frozen uniform mass `hq`.  This is the whole D2 lane in one statement —
smoothing lemma (this file) → local bound → per-cell contract — with only the arithmetic
hypothesis `B ≤ 4/(π ζ)` left, and the certified `C38` far inside it. -/
theorem cell_measure_le_hq_of_charFun (ν : Measure ℝ) [IsFiniteMeasure ν] {B : ℝ}
    (hB : ∀ R : ℝ, ∫ t in (0)..R, ‖charFun ν t‖ ≤ B) (hBz : B ≤ 4 / (Real.pi * zeta))
    (n : ℕ) :
    ν (Set.Ioc ((n : ℝ) * mesh) ((n : ℝ) * mesh + mesh)) ≤ ENNReal.ofReal hq :=
  cell_measure_le_hq ν (hasLocalBound_one_div_zeta ν hB hBz) n

/-! ### 4. The `d = 38` product structure, as a convolution power

The sum coordinate `r = Σ_i cellIndex (X i)` is the sum of `38` independent copies of the
fragment law, so its law is the `38`-fold convolution power.  Formally:

    ‖charFun (μ^{*d}) t‖ = ‖charFun μ t‖ ^ d,

which is exactly the `|φ|^38 = e^{-38 Cin}` product structure ROUTE2.md measured.  With this,
the remaining hypothesis of the smoothing lemma is a statement about the *single band* only —
the place where the `Cin` computation lives.
-/

/-- The `d`-fold convolution power of a measure (`δ_0` for `d = 0`). -/
def convPow (μ : Measure ℝ) : ℕ → Measure ℝ
  | 0 => Measure.dirac 0
  | n + 1 => convPow μ n ∗ μ

instance instIsFiniteMeasureConvPow (μ : Measure ℝ) [IsFiniteMeasure μ] (d : ℕ) :
    IsFiniteMeasure (convPow μ d) := by
  induction d with
  | zero => show IsFiniteMeasure (Measure.dirac (0 : ℝ)); infer_instance
  | succ n ih =>
      haveI := ih
      show IsFiniteMeasure (Measure.map (fun x : ℝ × ℝ => x.1 + x.2) ((convPow μ n).prod μ))
      constructor
      rw [Measure.map_apply (by fun_prop) MeasurableSet.univ, Set.preimage_univ,
        ← Set.univ_prod_univ, Measure.prod_prod]
      exact ENNReal.mul_lt_top (measure_lt_top _ _) (measure_lt_top _ _)

theorem charFun_convPow (μ : Measure ℝ) [IsFiniteMeasure μ] (d : ℕ) (t : ℝ) :
    charFun (convPow μ d) t = (charFun μ t) ^ d := by
  induction d with
  | zero => simp [convPow, charFun_dirac]
  | succ n ih =>
      rw [convPow, charFun_conv, ih, pow_succ]

/-- The sum-level `d`-fold law has the same smoothing instance as the single band, with the
characteristic function raised to the `d`-th power. -/
theorem hasLocalBound_convPow (μ : Measure ℝ) [IsProbabilityMeasure μ] (d : ℕ) {B : ℝ}
    (hB : ∀ R : ℝ, ∫ t in (0)..R, ‖charFun μ t‖ ^ d ≤ B) :
    HasLocalBound (convPow μ d) (Real.pi / 4 * B) := by
  refine hasLocalBound_of_charFun_bound (convPow μ d) (fun R => ?_)
  have hfun : (fun t : ℝ => ‖charFun (convPow μ d) t‖) = fun t : ℝ => ‖charFun μ t‖ ^ d := by
    funext t
    rw [charFun_convPow μ d t, norm_pow]
  rw [hfun]
  exact hB R

/-- **The `d = 38` instance**: one band's Fejér integral to the power `d`, and the arithmetic
margin `B ≤ 4/(π ζ)`, give `HasLocalBound` at `D = 1/ζ` for the `d`-fold sum law. -/
theorem hasLocalBound_convPow_one_div_zeta (μ : Measure ℝ) [IsProbabilityMeasure μ] (d : ℕ)
    {B : ℝ} (hB : ∀ R : ℝ, ∫ t in (0)..R, ‖charFun μ t‖ ^ d ≤ B)
    (hBz : B ≤ 4 / (Real.pi * zeta)) :
    HasLocalBound (convPow μ d) (1 / zeta) :=
  hasLocalBound_one_div_zeta (convPow μ d) (by
    intro R
    have hfun : (fun t : ℝ => ‖charFun (convPow μ d) t‖) = fun t : ℝ => ‖charFun μ t‖ ^ d := by
      funext t
      rw [charFun_convPow μ d t, norm_pow]
    rw [hfun]
    exact hB R) hBz

/-- The payload at the `d`-fold level: every frozen cell gets at most the uniform mass `hq`. -/
theorem cell_measure_le_hq_convPow (μ : Measure ℝ) [IsProbabilityMeasure μ] (d : ℕ) {B : ℝ}
    (hB : ∀ R : ℝ, ∫ t in (0)..R, ‖charFun μ t‖ ^ d ≤ B)
    (hBz : B ≤ 4 / (Real.pi * zeta)) (n : ℕ) :
    convPow μ d (Set.Ioc ((n : ℝ) * mesh) ((n : ℝ) * mesh + mesh)) ≤ ENNReal.ofReal hq :=
  cell_measure_le_hq (convPow μ d) (hasLocalBound_convPow_one_div_zeta μ d hB hBz) n

end PrimeGap182D2
