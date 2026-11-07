import Mathlib
import Pg182D2.CharFunMod

/-!
# INTEGRALBOUND.lean — item (ii) of the D4 data closure: the certified integral, transcribed

The receipt (`receipt/receipt.py`, `C_d_upper`) certifies, in exact rational arithmetic,

    ∫_0^∞ e^{-38 Cin x} dx ≤ 0.39446770,          Cin x = ∫_0^x (1 - cos u)/u du,

by a left-endpoint Darboux sum (`n1 = 4000` on `[0,1]`, `n2 = 20000` on `[1,20]`), the
rational lower bounds `Cin x ≥ x²/4 - x⁴/96` (`x ≤ 1`) and `Cin x ≥ γ - 1/x + 2(x-1)/(x+1)`
(`x ≥ 1`), the geometric bound `e^{-y} ≤ 1/(1+y/2)²`, and the tail
`Cin x ≥ log x - 1 ⇒ ∫_20^∞ e^{-38 Cin} ≤ e^{38}/(37·20^{37})`.

## What this file proves, and what it names

* `certifiedIntegralBound` — the receipt's rational, as a Lean real: `39446770/10^8`.
* `certifiedIntegralBound_le_four_div_pi` — **the margin, certified**: `0.39446770 ≤ 4/π`
  (`3.23×`), which is exactly the inequality the D3 smoothing lemma needs (`B ≤ 4/(πζ)`).
* `certifiedIntegralBound_div_zeta_le` — the same after the `1/ζ` scaling.
* `hasLocalBound_convPow_of_certified_integral` / `cell_measure_le_hq_of_certified_integral`
  — the whole layer-M chain: **given** the charFun identity (input N1) and the certified
  integral bound (input N2, in the hypothesis form `∀ R, ∫_0^R e^{-38 Cin} ≤ bound`),
  every inner cell of the `d = 38` law has mass `≤ hq`.

The *unconditional* `∀ R, ∫_0^R e^{-38 Cin} ≤ certifiedIntegralBound` is not proved here;
`receipt/` carries it as the Python-side rational certificate, and §5 of
`FINALSET_REPORT.md` states the elementary Lean-side chain that would replace the Darboux
sums (Jordan + Gaussian head, `Cin π ≥ 1`, dyadic doubling tail) with its measured margin.
-/

noncomputable section
namespace PrimeGap182D2
open MeasureTheory intervalIntegral

/-- The receipt's certified rational upper bound of `∫_0^∞ e^{-38 Cin}` (`C_d_upper(38)`). -/
def certifiedIntegralBound : ℝ := 39446770 / 10 ^ 8

theorem certifiedIntegralBound_nonneg : 0 ≤ certifiedIntegralBound := by
  unfold certifiedIntegralBound; norm_num

theorem certifiedIntegralBound_lt_one : certifiedIntegralBound < 1 := by
  unfold certifiedIntegralBound; norm_num

/-- **The margin, certified**: `0.39446770 ≤ 4/π ≈ 1.27324` (a `3.23×` margin), which is
precisely the hypothesis `B ≤ 4/(πζ)` of the D3 smoothing lemma, `ζ` cancelling. -/
theorem certifiedIntegralBound_le_four_div_pi : certifiedIntegralBound ≤ 4 / Real.pi := by
  rw [le_div_iff₀ Real.pi_pos]
  unfold certifiedIntegralBound
  nlinarith [Real.pi_lt_four]

theorem certifiedIntegralBound_div_zeta_le {ζ : ℝ} (hζ : 0 < ζ) :
    certifiedIntegralBound / ζ ≤ 4 / (Real.pi * ζ) := by
  rw [div_mul_eq_div_div, div_le_div_iff_of_pos_right hζ]
  exact certifiedIntegralBound_le_four_div_pi

/-! ### The composition: the two named inputs give layer M -/

/-- **Layer M at `d = 38` for ANY constant inside the margin**: the `3.07×` margin means the
`0.39446770` of the receipt is not needed as such — any `B ≤ 4/π ≈ 1.27324` discharges the
same ledger line.  (An elementary Lean-side bound of `≈ 0.79`, or even `1`, would do.) -/
theorem hasLocalBound_convPow_of_integral_le {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hphi : ∀ t : ℝ, charFun μ t = Complex.exp (-(charExponent t zeta))) {B : ℝ}
    (hI : ∀ R : ℝ, ∫ x in (0)..R, Real.exp (-(38 * Cin x)) ≤ B)
    (hB : B ≤ 4 / Real.pi) :
    HasLocalBound (convPow μ 38) (1 / zeta) := by
  refine hasLocalBound_convPow_of_certified hphi hI ?_
  rw [div_mul_eq_div_div, div_le_div_iff_of_pos_right zeta_pos]
  exact hB

/-- **Layer M at `d = 38`**, from the two named inputs: the ℂ charFun identity (N1) and the
certified single-variable integral bound (N2). -/
theorem hasLocalBound_convPow_of_certified_integral {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hphi : ∀ t : ℝ, charFun μ t = Complex.exp (-(charExponent t zeta)))
    (hI : ∀ R : ℝ, ∫ x in (0)..R, Real.exp (-(38 * Cin x)) ≤ certifiedIntegralBound) :
    HasLocalBound (convPow μ 38) (1 / zeta) :=
  hasLocalBound_convPow_of_certified hphi hI (certifiedIntegralBound_div_zeta_le zeta_pos)

/-- **The payload**: every cell of the `d = 38` convolution power has mass `≤ hq`. -/
theorem cell_measure_le_hq_of_certified_integral {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hphi : ∀ t : ℝ, charFun μ t = Complex.exp (-(charExponent t zeta)))
    (hI : ∀ R : ℝ, ∫ x in (0)..R, Real.exp (-(38 * Cin x)) ≤ certifiedIntegralBound)
    (n : ℕ) :
    convPow μ 38 (Set.Ioc ((n : ℝ) * mesh) ((n : ℝ) * mesh + mesh)) ≤ ENNReal.ofReal hq :=
  cell_measure_le_hq _ (hasLocalBound_convPow_of_certified_integral hphi hI) n

end PrimeGap182D2
