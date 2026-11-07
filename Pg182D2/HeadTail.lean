import Mathlib
import Pg182D2.CinBounds
import Pg182D2.IntegralBound

/-!
# HEADTAIL.lean — item (N2): `∀ R, ∫_0^R e^{-38 Cin} ≤ 4/π`

`FINALSET_REPORT.md` §5b named the one missing assembly: with the structural `Cin` bounds of
`CinBounds.lean` in hand, the certified integral `∫_0^∞ e^{-38 Cin} ≤ 0.39446770` follows
elementarily, well inside the `4/π` margin that the Fejér smoothing lemma needs.

The proof is a head/mid/tail split, with no Darboux grids and no countable-union packaging:

* **head** — on `[0, π]`, `Cin x ≥ x²/π²` (Jordan, `Cin_ge_sq`), so
  `∫_0^π e^{-38 Cin} ≤ ∫_0^∞ e^{-38 x²/π²} = √(π³/38)/2 ≤ 2/3` (`integral_gaussian_Ioi`);
* **mid** — on `[π, 4]`, `Cin x ≥ 1` (`Cin_ge_one`), so the integral is `≤ (4-π) e^{-38} ≤ 4/39`;
* **tail** — on the dyadic block `[4·2^k, 4·2^{k+1})`, `Cin x ≥ 1 + k/4` (`Cin_dyadic` +
  monotonicity), so `e^{-38 Cin x} ≤ e^{-38}·4^{-k}` and the block integral is
  `≤ 4·e^{-38}·2^{-k}`; the finite blocks up to `4·2^N` telescope
  (`sum_integral_adjacent_intervals`) into a geometric sum `≤ 8 e^{-38} ≤ 8/39`, and any `R`
  is dominated by a sufficiently large `4·2^N` (`pow_unbounded_of_one_lt`).  No `tsum` over an
  `iUnion`, no integrability on an unbounded set.

Total: `2/3 + 4/39 + 8/39 = 38/39 < 4/π`.  The certified `0.39446770` of the receipt is *not*
needed: the elementary bound is `38/39 ≈ 0.9744`, still well below `4/π ≈ 1.2732`.

Every theorem here is `[propext, Classical.choice, Quot.sound]` only.
-/

noncomputable section
namespace PrimeGap182D2
open MeasureTheory intervalIntegral

/-- The decaying profile of the `d = 38` smoothing integrand: `e^{-38 Cin x}`. -/
def cinDecay (x : ℝ) : ℝ := Real.exp (-(38 * Cin x))

theorem cinDecay_pos (x : ℝ) : 0 < cinDecay x := Real.exp_pos _

theorem cinDecay_nonneg (x : ℝ) : 0 ≤ cinDecay x := (cinDecay_pos x).le

/-! ### Continuity of `Cin` (the profile's measurability and integrability) -/

/-- The `Cin` integrand is integrable on any `Ioc a b` (bound `|u|/2`, `CinBounds`). -/
theorem integrableOn_cinIntegrand_Ioc {a b : ℝ} (hab : a ≤ b) :
    IntegrableOn cinIntegrand (Set.Ioc a b) volume := by
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioc a b)) := isFiniteMeasure_restrict.mpr (by simp)
  refine Integrable.of_bound ?_ (max |a| |b| / 2) ?_
  · exact (by unfold cinIntegrand; fun_prop : Measurable cinIntegrand).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    have hM : |u| ≤ max |a| |b| := by
      rw [abs_le]
      refine ⟨?_, ?_⟩
      · have h1 : -|a| ≤ a := neg_abs_le a
        have h2 : |a| ≤ max |a| |b| := le_max_left _ _
        linarith [hu.1.le]
      · have h1 : b ≤ |b| := le_abs_self b
        have h2 : |b| ≤ max |a| |b| := le_max_right _ _
        linarith [hu.2]
    calc ‖cinIntegrand u‖ ≤ |u| / 2 := cinIntegrand_le u
      _ ≤ max |a| |b| / 2 := by linarith

theorem intervalIntegrable_cinIntegrand_all (a b : ℝ) :
    IntervalIntegrable cinIntegrand volume a b := by
  rcases le_total a b with hab | hba
  · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
      (integrableOn_cinIntegrand_Ioc hab)
  · exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le hba).mpr
      (integrableOn_cinIntegrand_Ioc hba)).symm

/-- `Cin` is continuous: it is the primitive of an interval-integrable integrand. -/
theorem continuous_Cin : Continuous Cin := by
  have h : Continuous fun b : ℝ => ∫ x in (0)..b, cinIntegrand x :=
    intervalIntegral.continuous_primitive (μ := volume) (f := cinIntegrand)
      intervalIntegrable_cinIntegrand_all 0
  exact h

theorem measurable_Cin : Measurable Cin := continuous_Cin.measurable

theorem continuous_cinDecay : Continuous cinDecay := by
  have h : Continuous fun x : ℝ => -(38 * Cin x) := (continuous_Cin.const_mul 38).neg
  exact Real.continuous_exp.comp h

theorem intervalIntegrable_cinDecay (a b : ℝ) : IntervalIntegrable cinDecay volume a b :=
  continuous_cinDecay.intervalIntegrable a b

/-! ### Two elementary numeric inputs -/

theorem exp_neg_38_le : Real.exp (-38) ≤ 1 / 39 := by
  have h : (39 : ℝ) ≤ Real.exp 38 := by
    have := Real.add_one_le_exp (38 : ℝ)
    linarith
  have hpos : (0 : ℝ) < Real.exp 38 := Real.exp_pos 38
  rw [Real.exp_neg]
  simpa [one_div] using (inv_le_inv₀ hpos (by norm_num : (0:ℝ) < 39)).mpr h

/-- `e^{-19/2} ≤ 1/4`, since `log 4 ≤ 3 ≤ 19/2`. -/
theorem exp_neg_nineteen_half_le : Real.exp (-(19 / 2)) ≤ 1 / 4 := by
  have hlog : Real.log 4 ≤ 19 / 2 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    linarith
  have h4 : (4 : ℝ) ≤ Real.exp (19 / 2) := (Real.log_le_iff_le_exp (by norm_num)).mp hlog
  have hpos : (0 : ℝ) < Real.exp (19 / 2) := Real.exp_pos _
  rw [Real.exp_neg]
  simpa [one_div] using (inv_le_inv₀ hpos (by norm_num : (0:ℝ) < 4)).mpr h4

/-! ### The dyadic block: `e^{-38 Cin x} ≤ e^{-38}·4^{-k}` for `x ≥ 4·2^k` -/

theorem cinDecay_block_le {k : ℕ} {x : ℝ} (hx : 4 * 2 ^ k ≤ x) :
    cinDecay x ≤ Real.exp (-38) * (1 / 4) ^ k := by
  have h0 : (0 : ℝ) ≤ 4 * 2 ^ k := by positivity
  have hCin : 1 + (k : ℝ) / 4 ≤ Cin x := (Cin_dyadic k).trans (Cin_mono h0 hx)
  have hExp : cinDecay x ≤ Real.exp (-(38 * (1 + (k : ℝ) / 4))) := by
    unfold cinDecay
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hfac : Real.exp (-(38 * (1 + (k : ℝ) / 4)))
      = Real.exp (-38) * (Real.exp (-(19 / 2))) ^ k := by
    rw [show -(38 * (1 + (k : ℝ) / 4)) = -38 + (k : ℝ) * (-(19 / 2)) by ring, Real.exp_add,
      Real.exp_nat_mul]
  have hpow : (Real.exp (-(19 / 2))) ^ k ≤ (1 / 4) ^ k :=
    pow_le_pow_left₀ (Real.exp_pos _).le exp_neg_nineteen_half_le k
  calc cinDecay x ≤ Real.exp (-(38 * (1 + (k : ℝ) / 4))) := hExp
    _ = Real.exp (-38) * (Real.exp (-(19 / 2))) ^ k := hfac
    _ ≤ Real.exp (-38) * (1 / 4) ^ k :=
        mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le

/-- The block integral bound: `∫_{4·2^k}^{4·2^{k+1}} e^{-38 Cin} ≤ 4 e^{-38} 2^{-k}`. -/
theorem block_bound (k : ℕ) :
    ∫ x in (4 * 2 ^ k)..(4 * 2 ^ (k + 1)), cinDecay x
      ≤ 4 * Real.exp (-38) * (1 / 2) ^ k := by
  have hmono : (4 : ℝ) * 2 ^ k ≤ 4 * 2 ^ (k + 1) := by
    have hp : (0 : ℝ) < 2 ^ k := pow_pos (by norm_num) k
    rw [pow_succ]
    nlinarith
  have hpt : ∀ x ∈ Set.Icc (4 * 2 ^ k) (4 * 2 ^ (k + 1)),
      cinDecay x ≤ Real.exp (-38) * (1 / 4) ^ k :=
    fun x hx => cinDecay_block_le hx.1
  have h2 : ∫ x in (4 * 2 ^ k)..(4 * 2 ^ (k + 1)), cinDecay x
      ≤ ∫ x in (4 * 2 ^ k)..(4 * 2 ^ (k + 1)), (Real.exp (-38) * (1 / 4) ^ k) :=
    intervalIntegral.integral_mono_on hmono (intervalIntegrable_cinDecay _ _)
      intervalIntegrable_const hpt
  have h3 : ∫ x in (4 * 2 ^ k)..(4 * 2 ^ (k + 1)), (Real.exp (-38) * (1 / 4) ^ k)
      = Real.exp (-38) * (1 / 4) ^ k * ((4 * 2 ^ (k + 1)) - 4 * 2 ^ k) := by
    rw [intervalIntegral.integral_const]; ring
  have h4 : (4 : ℝ) * 2 ^ (k + 1) - 4 * 2 ^ k = 4 * 2 ^ k := by
    rw [pow_succ]; ring
  rw [h3, h4] at h2
  refine h2.trans (le_of_eq ?_)
  have hp : (1 / 4 : ℝ) ^ k * 2 ^ k = (1 / 2) ^ k := by
    rw [← mul_pow]; norm_num
  calc Real.exp (-38) * (1 / 4) ^ k * (4 * 2 ^ k)
      = Real.exp (-38) * 4 * ((1 / 4) ^ k * 2 ^ k) := by ring
    _ = Real.exp (-38) * 4 * (1 / 2) ^ k := by rw [hp]
    _ = 4 * Real.exp (-38) * (1 / 2) ^ k := by ring

/-! ### The finite dyadic tail -/

theorem tail_telescope (N : ℕ) :
    ∑ k ∈ Finset.range N, ∫ x in (4 * 2 ^ k)..(4 * 2 ^ (k + 1)), cinDecay x
      = ∫ x in (4 : ℝ)..(4 * 2 ^ N), cinDecay x := by
  have hint : ∀ k < N, IntervalIntegrable cinDecay volume (4 * 2 ^ k) (4 * 2 ^ (k + 1)) :=
    fun k _ => intervalIntegrable_cinDecay _ _
  have h := intervalIntegral.sum_integral_adjacent_intervals (f := cinDecay) (μ := volume)
    (a := fun k : ℕ => (4 : ℝ) * 2 ^ k) hint
  simpa using h

/-- **The tail, uniformly in `N`**: `∫_4^{4·2^N} e^{-38 Cin} ≤ 8 e^{-38} ≤ 8/39`. -/
theorem tail_finite (N : ℕ) :
    ∫ x in (4 : ℝ)..(4 * 2 ^ N), cinDecay x ≤ 8 / 39 := by
  rw [← tail_telescope N]
  have hstep : ∑ k ∈ Finset.range N, ∫ x in (4 * 2 ^ k)..(4 * 2 ^ (k + 1)), cinDecay x
      ≤ ∑ k ∈ Finset.range N, 4 * Real.exp (-38) * (1 / 2) ^ k :=
    Finset.sum_le_sum fun k _ => block_bound k
  have hgeo : ∑ k ∈ Finset.range N, (1 / 2 : ℝ) ^ k ≤ 2 := by
    rw [geom_sum_eq (by norm_num : (1 / 2 : ℝ) ≠ 1) N]
    have hp : (0 : ℝ) < (1 / 2) ^ N := by positivity
    have heq : ((1 / 2 : ℝ) ^ N - 1) / (1 / 2 - 1) = 2 - 2 * (1 / 2) ^ N := by
      field_simp
      ring
    rw [heq]
    linarith
  have hsum : ∑ k ∈ Finset.range N, 4 * Real.exp (-38) * (1 / 2) ^ k
      = 4 * Real.exp (-38) * ∑ k ∈ Finset.range N, (1 / 2 : ℝ) ^ k := by
    rw [Finset.mul_sum]
  have h8 : (4 : ℝ) * Real.exp (-38) * 2 = 8 * Real.exp (-38) := by ring
  calc ∑ k ∈ Finset.range N, ∫ x in (4 * 2 ^ k)..(4 * 2 ^ (k + 1)), cinDecay x
      ≤ ∑ k ∈ Finset.range N, 4 * Real.exp (-38) * (1 / 2) ^ k := hstep
    _ = 4 * Real.exp (-38) * ∑ k ∈ Finset.range N, (1 / 2 : ℝ) ^ k := hsum
    _ ≤ 4 * Real.exp (-38) * 2 := by
        have h4 : (0 : ℝ) ≤ 4 * Real.exp (-38) := by positivity
        nlinarith
    _ = 8 * Real.exp (-38) := h8
    _ ≤ 8 / 39 := by
        have h := exp_neg_38_le
        have h0 : (0 : ℝ) < Real.exp (-38) := Real.exp_pos _
        nlinarith

/-- The tail from `4` to an arbitrary `R ≥ 4`. -/
theorem tail_bound (R : ℝ) (hR : 4 ≤ R) :
    ∫ x in (4 : ℝ)..R, cinDecay x ≤ 8 / 39 := by
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (R / 4) (by norm_num : (1 : ℝ) < 2)
  have hRN : R ≤ 4 * 2 ^ N := by
    rw [div_lt_iff₀ (by norm_num : (0:ℝ) < 4)] at hN
    linarith
  have hmono : ∫ x in (4 : ℝ)..R, cinDecay x ≤ ∫ x in (4 : ℝ)..(4 * 2 ^ N), cinDecay x :=
    intervalIntegral.integral_mono_interval le_rfl hR hRN
      (Filter.Eventually.of_forall fun x => cinDecay_nonneg x) (intervalIntegrable_cinDecay _ _)
  exact hmono.trans (tail_finite N)

/-! ### The mid piece `[π, 4]` -/

theorem mid_bound : ∫ x in Real.pi..(4 : ℝ), cinDecay x ≤ 4 / 39 := by
  have hpi4 : Real.pi ≤ (4 : ℝ) := le_of_lt Real.pi_lt_four
  have hpt : ∀ x ∈ Set.Icc Real.pi 4, cinDecay x ≤ Real.exp (-38) := by
    intro x hx
    have h1 : 1 ≤ Cin x := Cin_ge_one hx.1
    unfold cinDecay
    exact Real.exp_le_exp.mpr (by nlinarith)
  have h2 : ∫ x in Real.pi..(4 : ℝ), cinDecay x ≤ ∫ x in Real.pi..(4 : ℝ), (Real.exp (-38) : ℝ) :=
    intervalIntegral.integral_mono_on hpi4 (intervalIntegrable_cinDecay _ _)
      intervalIntegrable_const hpt
  have h3 : ∫ x in Real.pi..(4 : ℝ), (Real.exp (-38) : ℝ) = Real.exp (-38) * (4 - Real.pi) := by
    rw [intervalIntegral.integral_const]; ring
  rw [h3] at h2
  refine h2.trans ?_
  have h1 : Real.exp (-38) ≤ 1 / 39 := exp_neg_38_le
  have h2 : (0 : ℝ) < Real.exp (-38) := Real.exp_pos _
  have h3 : 4 - Real.pi ≤ 4 := by linarith [Real.pi_pos]
  nlinarith

/-! ### The head piece `[0, π]`, via the Gaussian integral -/

theorem head_bound : ∫ x in (0 : ℝ)..Real.pi, cinDecay x ≤ 2 / 3 := by
  set b : ℝ := 38 / Real.pi ^ 2 with hb
  have hbpos : 0 < b := by rw [hb]; positivity
  have hcont : Continuous fun x : ℝ => Real.exp (-b * x ^ 2) := by fun_prop
  have hpt : ∀ x ∈ Set.Icc (0:ℝ) Real.pi, cinDecay x ≤ Real.exp (-b * x ^ 2) := by
    intro x hx
    have hsq : x ^ 2 / Real.pi ^ 2 ≤ Cin x := Cin_ge_sq hx.1 hx.2
    have heq : -b * x ^ 2 = -(38 * (x ^ 2 / Real.pi ^ 2)) := by
      rw [hb]; field_simp
    unfold cinDecay
    rw [heq]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have h1 : ∫ x in (0 : ℝ)..Real.pi, cinDecay x
      ≤ ∫ x in (0 : ℝ)..Real.pi, Real.exp (-b * x ^ 2) :=
    intervalIntegral.integral_mono_on Real.pi_pos.le (intervalIntegrable_cinDecay _ _)
      (hcont.intervalIntegrable _ _) hpt
  have h2 : ∫ x in (0 : ℝ)..Real.pi, Real.exp (-b * x ^ 2)
      ≤ ∫ x in Set.Ioi (0:ℝ), Real.exp (-b * x ^ 2) := by
    rw [intervalIntegral.integral_of_le Real.pi_pos.le]
    refine setIntegral_mono_set ?_ ?_ ?_
    · exact (integrable_exp_neg_mul_sq hbpos).integrableOn
    · exact Filter.Eventually.of_forall fun x => (Real.exp_pos _).le
    · exact Filter.Eventually.of_forall fun x hx => hx.1
  have h3 : ∫ x in Set.Ioi (0:ℝ), Real.exp (-b * x ^ 2) = Real.sqrt (Real.pi / b) / 2 :=
    integral_gaussian_Ioi b
  have hpb : Real.pi / b ≤ 16 / 9 := by
    rw [hb]
    have hp3 : Real.pi ^ 3 ≤ 64 := by nlinarith [Real.pi_lt_four, Real.pi_pos]
    field_simp
    nlinarith
  have hsqrt : Real.sqrt (Real.pi / b) ≤ 4 / 3 := by
    have hpb' : Real.pi / b ≤ (4 / 3) ^ 2 := by
      rw [show ((4:ℝ) / 3) ^ 2 = 16 / 9 by norm_num]; exact hpb
    have h : Real.sqrt (Real.pi / b) ≤ Real.sqrt ((4 / 3) ^ 2) := Real.sqrt_le_sqrt hpb'
    rwa [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 4 / 3)] at h
  rw [h3] at h2
  refine h1.trans (h2.trans ?_)
  linarith

/-! ### The assembly: `∀ R, ∫_0^R e^{-38 Cin} ≤ 4/π` -/

theorem integral_cinDecay_le_38_39 (R : ℝ) :
    ∫ x in (0)..R, cinDecay x ≤ 38 / 39 := by
  have h38 : (0 : ℝ) ≤ 38 / 39 := by norm_num
  rcases le_or_gt R 0 with hR | hR
  · -- `R ≤ 0`: the integral is `≤ 0`
    have hsymm : ∫ x in (0)..R, cinDecay x = -∫ x in R..(0:ℝ), cinDecay x := by
      have h := intervalIntegral.integral_symm (μ := volume) (f := cinDecay) (a := R) (b := (0:ℝ))
      linarith
    rw [hsymm]
    have hnn : (0 : ℝ) ≤ ∫ x in R..(0:ℝ), cinDecay x :=
      intervalIntegral.integral_nonneg hR (fun u _ => cinDecay_nonneg u)
    linarith
  rcases le_or_gt R Real.pi with hRpi | hRpi
  · -- `0 < R ≤ π`
    have hmono : ∫ x in (0)..R, cinDecay x ≤ ∫ x in (0:ℝ)..Real.pi, cinDecay x :=
      intervalIntegral.integral_mono_interval le_rfl hR.le hRpi
        (Filter.Eventually.of_forall fun x => cinDecay_nonneg x) (intervalIntegrable_cinDecay _ _)
    linarith [head_bound]
  rcases le_or_gt R 4 with hR4 | hR4
  · -- `π < R ≤ 4`
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_cinDecay (0:ℝ) Real.pi) (intervalIntegrable_cinDecay Real.pi R)
    rw [← hsplit]
    have hmidR : ∫ x in Real.pi..R, cinDecay x ≤ ∫ x in Real.pi..(4:ℝ), cinDecay x :=
      intervalIntegral.integral_mono_interval le_rfl hRpi.le hR4
        (Filter.Eventually.of_forall fun x => cinDecay_nonneg x) (intervalIntegrable_cinDecay _ _)
    linarith [head_bound, mid_bound]
  · -- `4 < R`
    have hsplit1 := intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_cinDecay (0:ℝ) Real.pi) (intervalIntegrable_cinDecay Real.pi (4:ℝ))
    have hsplit2 := intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_cinDecay (0:ℝ) (4:ℝ)) (intervalIntegrable_cinDecay (4:ℝ) R)
    rw [← hsplit2, ← hsplit1]
    linarith [head_bound, mid_bound, tail_bound R hR4.le]

theorem integral_cinDecay_le_four_div_pi (R : ℝ) :
    ∫ x in (0)..R, cinDecay x ≤ 4 / Real.pi := by
  refine (integral_cinDecay_le_38_39 R).trans ?_
  rw [le_div_iff₀ Real.pi_pos, div_mul_eq_mul_div, div_le_iff₀ (by norm_num : (0:ℝ) < 39)]
  nlinarith [Real.pi_lt_four, Real.pi_pos]

/-- **Item (N2), closed.**  The certified truncation bound in the exact form the layer-M chain
consumes (`IntegralBound.hasLocalBound_convPow_of_integral_le`). -/
theorem integral_exp_neg_Cin_le_four_div_pi (R : ℝ) :
    ∫ x in (0)..R, Real.exp (-(38 * Cin x)) ≤ 4 / Real.pi :=
  integral_cinDecay_le_four_div_pi R

/-- **Layer M at `d = 38`, with N2 discharged**: only the charFun identity (N1) remains. -/
theorem hasLocalBound_convPow_of_charFun {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hphi : ∀ t : ℝ, charFun μ t = Complex.exp (-(charExponent t zeta))) :
    HasLocalBound (convPow μ 38) (1 / zeta) :=
  hasLocalBound_convPow_of_integral_le hphi integral_exp_neg_Cin_le_four_div_pi le_rfl

/-- **The payload, with N2 discharged**: every cell of the `d = 38` sum law has mass `≤ hq`,
given only the charFun identity. -/
theorem cell_measure_le_hq_of_charFun' {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hphi : ∀ t : ℝ, charFun μ t = Complex.exp (-(charExponent t zeta))) (n : ℕ) :
    convPow μ 38 (Set.Ioc ((n : ℝ) * mesh) ((n : ℝ) * mesh + mesh)) ≤ ENNReal.ofReal hq :=
  cell_measure_le_hq _ (hasLocalBound_convPow_of_charFun hphi) n

end PrimeGap182D2
