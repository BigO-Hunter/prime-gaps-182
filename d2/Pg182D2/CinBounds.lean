import Mathlib
import Pg182D2.CharFunMod

/-!
# CINBOUNDS.lean — the structural facts behind the elementary `∫ e^{-38 Cin}` bound

`FINALSET_REPORT.md` §5 replaces the receipt's 24 000-cell Darboux certificate with an
elementary chain, because the margin is `4/π = 1.27324` and the crude chain lands at `≈ 0.452`.
This file proves the structural half of that chain:

* `one_sub_cos_le_half_sq`, `cinIntegrand_le` — the integrand of `Cin` is bounded by `|u|/2`
  (so `Cin` is an honest interval integral even at `0`);
* `integrableOn_cinIntegrand`, `intervalIntegrable_cinIntegrand`, `Cin_mono` — `Cin` is
  monotone on `[0, ∞)`;
* `Cin_pi_ge_one`, `Cin_ge_one` — `Cin x ≥ 1` for `x ≥ π`;
* `Cin_ge_sq` — `Cin x ≥ x²/π²` on `[0, π]` (Jordan's inequality);
* `Cin_double`, `Cin_dyadic` — `Cin (2x) ≥ Cin x + 1/4` for `x ≥ 4`, hence
  `Cin (4·2^k) ≥ 1 + k/4`.

Still missing for the unconditional `∀ R, ∫_0^R e^{-38 Cin} ≤ 1`: the *packaging* of the
dyadic tail (a `tsum` over the `iUnion` of the blocks `[4·2^k, 4·2^{k+1})`, or the pointwise
majorant `e^{-38 Cin x} ≤ e^{-38}(x/8)^{-13}` plus `integral_Ioi_rpow_of_lt`).
-/

noncomputable section
namespace PrimeGap182D2
open MeasureTheory intervalIntegral

/-- The `Cin` integrand, with Lean's junk value at `0` (which is the correct limit). -/
def cinIntegrand (u : ℝ) : ℝ := (1 - Real.cos u) / u

theorem one_sub_cos_le_half_sq (u : ℝ) : 1 - Real.cos u ≤ u ^ 2 / 2 := by
  have h1 : Real.cos u = 1 - 2 * Real.sin (u / 2) ^ 2 := by
    have h2 : Real.cos (2 * (u / 2)) = Real.cos u := by rw [mul_div_cancel₀ u two_ne_zero]
    nlinarith [Real.sin_sq_add_cos_sq (u / 2), h2, Real.cos_two_mul' (u / 2)]
  have h3 : Real.sin (u / 2) ^ 2 ≤ (u / 2) ^ 2 := Real.sin_sq_le_sq
  nlinarith [h1, h3]

theorem cinIntegrand_le (u : ℝ) : ‖cinIntegrand u‖ ≤ |u| / 2 := by
  have hc : 0 ≤ 1 - Real.cos u := by linarith [Real.cos_le_one u]
  rw [cinIntegrand, norm_div, Real.norm_eq_abs, Real.norm_eq_abs]
  rcases eq_or_ne u 0 with h | h
  · subst h; simp
  · have hu : 0 < |u| := abs_pos.mpr h
    rw [div_le_iff₀ hu]
    have h2 : 1 - Real.cos u ≤ u ^ 2 / 2 := one_sub_cos_le_half_sq u
    have h3 : |u| / 2 * |u| = u ^ 2 / 2 := by
      rw [← sq_abs]; ring
    calc |1 - Real.cos u| = 1 - Real.cos u := abs_of_nonneg hc
      _ ≤ u ^ 2 / 2 := h2
      _ = |u| / 2 * |u| := h3.symm

theorem integrableOn_cinIntegrand {c d : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d) :
    IntegrableOn cinIntegrand (Set.Ioc c d) volume := by
  haveI : IsFiniteMeasure ((volume : Measure ℝ).restrict (Set.Ioc c d)) :=
    isFiniteMeasure_restrict.mpr (by simp)
  refine Integrable.of_bound ?_ (d / 2) ?_
  · exact (by unfold cinIntegrand; fun_prop : Measurable cinIntegrand).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    have hu_lb : 0 ≤ u := hc.trans hu.1.le
    have hu_ub : u ≤ d := hu.2
    have h2 : |u| / 2 ≤ d / 2 := by
      rw [abs_of_nonneg hu_lb]; linarith
    calc ‖cinIntegrand u‖ ≤ |u| / 2 := cinIntegrand_le u
      _ ≤ d / 2 := h2

theorem intervalIntegrable_cinIntegrand {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable cinIntegrand volume a b :=
  ⟨integrableOn_cinIntegrand ha (ha.trans hab),
    integrableOn_cinIntegrand (ha.trans hab) ha⟩

theorem Cin_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : Cin a ≤ Cin b := by
  have h1 : IntervalIntegrable cinIntegrand volume 0 a := intervalIntegrable_cinIntegrand le_rfl ha
  have h2 : IntervalIntegrable cinIntegrand volume a b := intervalIntegrable_cinIntegrand ha hab
  have hsplit := intervalIntegral.integral_add_adjacent_intervals h1 h2
  have hnn : 0 ≤ ∫ u in a..b, cinIntegrand u :=
    intervalIntegral.integral_nonneg hab (fun u hu => by
      have hu0 : 0 ≤ u := ha.trans hu.1
      exact div_nonneg (by linarith [Real.cos_le_one u]) hu0)
  have hA : Cin a = ∫ u in (0)..a, cinIntegrand u := rfl
  have hB : Cin b = ∫ u in (0)..b, cinIntegrand u := rfl
  rw [hA, hB]
  linarith [hsplit, hnn]

theorem Cin_zero : Cin 0 = 0 := by simp [Cin]

theorem Cin_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ Cin x := by
  have h := Cin_mono le_rfl hx
  rwa [Cin_zero] at h

theorem cinIntegrand_ge_div_pi {u : ℝ} (h0 : 0 < u) (hu : u ≤ Real.pi) :
    (1 - Real.cos u) / Real.pi ≤ cinIntegrand u := by
  have hc : 0 ≤ 1 - Real.cos u := by linarith [Real.cos_le_one u]
  have hle : Real.pi⁻¹ ≤ u⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le h0 hu
  have e1 : (1 - Real.cos u) / Real.pi = (1 - Real.cos u) * Real.pi⁻¹ := by
    rw [div_eq_mul_inv]
  have e2 : cinIntegrand u = (1 - Real.cos u) * u⁻¹ := by
    rw [cinIntegrand, div_eq_mul_inv]
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_left hle hc

/-- `Cin x ≥ 1` for `x ≥ π`: on `(0, π]` the weight `1/u` dominates `1/π`, and
`∫_0^π (1 - cos u) du = π`. -/
theorem Cin_pi_ge_one : 1 ≤ Cin Real.pi := by
  have hpi := Real.pi_pos
  have hf : IntervalIntegrable cinIntegrand volume 0 Real.pi :=
    intervalIntegrable_cinIntegrand le_rfl hpi.le
  have hg : IntervalIntegrable (fun u : ℝ => (1 - Real.cos u) / Real.pi) volume 0 Real.pi :=
    (by fun_prop : Continuous fun u : ℝ => (1 - Real.cos u) / Real.pi).intervalIntegrable _ _
  have hmono : ∫ u in (0)..Real.pi, (1 - Real.cos u) / Real.pi
      ≤ ∫ u in (0)..Real.pi, cinIntegrand u := by
    refine intervalIntegral.integral_mono_on hpi.le hg hf (fun u hu => ?_)
    rcases eq_or_lt_of_le hu.1 with h0 | h0
    · subst h0; simp [cinIntegrand]
    · exact cinIntegrand_ge_div_pi h0 hu.2
  have hval : ∫ u in (0)..Real.pi, (1 - Real.cos u) / Real.pi = 1 := by
    have hrw : ∀ u : ℝ, (1 - Real.cos u) / Real.pi = Real.pi⁻¹ * (1 - Real.cos u) := by
      intro u; rw [div_eq_inv_mul]
    simp only [hrw, intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_sub intervalIntegrable_const
      (Real.continuous_cos.intervalIntegrable 0 Real.pi), intervalIntegral.integral_const,
      integral_cos]
    simp only [smul_eq_mul, Real.sin_pi, Real.sin_zero, sub_zero]
    field_simp
  rw [hval] at hmono
  rw [show Cin Real.pi = ∫ u in (0)..Real.pi, cinIntegrand u from rfl]
  exact hmono

theorem Cin_ge_one {x : ℝ} (hx : Real.pi ≤ x) : 1 ≤ Cin x :=
  Cin_pi_ge_one.trans (Cin_mono Real.pi_pos.le hx)

/-- Jordan on `[0, π]`: `Cin x ≥ x²/π²`. -/
theorem Cin_ge_sq {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ Real.pi) : x ^ 2 / Real.pi ^ 2 ≤ Cin x := by
  have hf : IntervalIntegrable cinIntegrand volume 0 x :=
    intervalIntegrable_cinIntegrand le_rfl hx0
  have hg : IntervalIntegrable (fun u : ℝ => 2 * u / Real.pi ^ 2) volume 0 x :=
    (by fun_prop : Continuous fun u : ℝ => 2 * u / Real.pi ^ 2).intervalIntegrable _ _
  have hmono : ∫ u in (0)..x, 2 * u / Real.pi ^ 2 ≤ ∫ u in (0)..x, cinIntegrand u := by
    refine intervalIntegral.integral_mono_on hx0 hg hf (fun u hu => ?_)
    rcases eq_or_lt_of_le hu.1 with h0 | h0
    · subst h0; simp [cinIntegrand]
    · have huabs : |u| ≤ Real.pi := by
        rw [abs_of_pos h0]; exact hu.2.trans hx
      have hj := Real.cos_le_one_sub_mul_cos_sq huabs
      have hc : 2 / Real.pi ^ 2 * u ^ 2 ≤ 1 - Real.cos u := by linarith
      have e1 : 2 * u / Real.pi ^ 2 = (2 / Real.pi ^ 2 * u ^ 2) / u := by
        field_simp
      have e2 : cinIntegrand u = (1 - Real.cos u) / u := rfl
      rw [e1, e2]
      exact div_le_div_of_nonneg_right hc h0.le
  have hval : ∫ u in (0)..x, 2 * u / Real.pi ^ 2 = x ^ 2 / Real.pi ^ 2 := by
    rw [show (fun u : ℝ => 2 * u / Real.pi ^ 2) = (fun u : ℝ => (2 / Real.pi ^ 2) * u) from by
      funext u; ring]
    rw [intervalIntegral.integral_const_mul, integral_id]
    field_simp
    ring
  rw [hval] at hmono
  rw [show Cin x = ∫ u in (0)..x, cinIntegrand u from rfl]
  exact hmono

theorem cinIntegrand_ge_div_two {x u : ℝ} (hx : 0 < x) (hu0 : 0 < u) (hu : u ≤ 2 * x) :
    (1 - Real.cos u) / (2 * x) ≤ cinIntegrand u := by
  have hc : 0 ≤ 1 - Real.cos u := by linarith [Real.cos_le_one u]
  have hle : (2 * x)⁻¹ ≤ u⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hu0 hu
  have e1 : (1 - Real.cos u) / (2 * x) = (1 - Real.cos u) * (2 * x)⁻¹ := by
    rw [div_eq_mul_inv]
  have e2 : cinIntegrand u = (1 - Real.cos u) * u⁻¹ := by
    rw [cinIntegrand, div_eq_mul_inv]
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_left hle hc

/-- The doubling gain: `Cin (2x) ≥ Cin x + 1/4` for `x ≥ 4`. -/
theorem Cin_double {x : ℝ} (hx : 4 ≤ x) : Cin x + 1 / 4 ≤ Cin (2 * x) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have h2x : x ≤ 2 * x := by linarith
  have h1 : IntervalIntegrable cinIntegrand volume x (2 * x) :=
    intervalIntegrable_cinIntegrand hx0.le h2x
  have hg : IntervalIntegrable (fun u : ℝ => (1 - Real.cos u) / (2 * x)) volume x (2 * x) :=
    (by fun_prop : Continuous fun u : ℝ => (1 - Real.cos u) / (2 * x)).intervalIntegrable _ _
  have hmono : ∫ u in x..(2 * x), (1 - Real.cos u) / (2 * x)
      ≤ ∫ u in x..(2 * x), cinIntegrand u := by
    refine intervalIntegral.integral_mono_on h2x hg h1 (fun u hu => ?_)
    exact cinIntegrand_ge_div_two hx0 (lt_of_lt_of_le hx0 hu.1) hu.2
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_cinIntegrand le_rfl hx0.le) h1
  have hval : (1 : ℝ) / 4 ≤ ∫ u in x..(2 * x), (1 - Real.cos u) / (2 * x) := by
    have hrw : ∀ u : ℝ, (1 - Real.cos u) / (2 * x) = (1 / (2 * x)) * (1 - Real.cos u) := by
      intro u; ring
    simp only [hrw, intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_sub intervalIntegrable_const
      (Real.continuous_cos.intervalIntegrable x (2 * x)), intervalIntegral.integral_const,
      integral_cos]
    simp only [smul_eq_mul]
    have hsin : Real.sin (2 * x) - Real.sin x ≤ 2 := by
      linarith [Real.sin_le_one (2 * x), Real.neg_one_le_sin x]
    have hstep : (1 / (2 * x)) * (x - 2)
        ≤ (1 / (2 * x)) * (x - (Real.sin (2 * x) - Real.sin x)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith
    have hstep2 : (1 / (2 * x)) * (x - 2) ≥ 1 / 4 := by
      rw [ge_iff_le, ← sub_nonneg]
      have hxne : x ≠ 0 := ne_of_gt hx0
      field_simp
      nlinarith
    linarith
  have hA : Cin x = ∫ u in (0)..x, cinIntegrand u := rfl
  have hB : Cin (2 * x) = ∫ u in (0)..(2 * x), cinIntegrand u := rfl
  rw [hA, hB]
  linarith [hsplit, hmono, hval]

/-- `Cin (4·2^k) ≥ 1 + k/4`. -/
theorem Cin_dyadic (k : ℕ) : 1 + k / 4 ≤ Cin (4 * 2 ^ k) := by
  induction k with
  | zero =>
    have h4 : Real.pi ≤ (4 : ℝ) := le_of_lt Real.pi_lt_four
    simpa using Cin_ge_one h4
  | succ n ih =>
    have hx : (4 : ℝ) ≤ 4 * 2 ^ n := by
      have h1 : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
      nlinarith
    have hd := Cin_double hx
    have hgoal : (4 : ℝ) * 2 ^ (n + 1 : ℕ) = 2 * (4 * 2 ^ n) := by
      rw [pow_succ]; ring
    rw [hgoal]
    push_cast
    linarith

end PrimeGap182D2
