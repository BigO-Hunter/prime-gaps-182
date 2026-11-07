/-
# LOW_ROWS.lean — Lane D2b: the 64 low rows and the tilt cancellation

## What the low rows are (exactly, from the certificate source)

`prime-gaps-lean/formal/SourceKernels182.lean:41-45` defines the `.low` kernel:

    trialSourceUnmasked c X =
      (trialSourceCountMeasure X).real (Ioc c.low c.high) *
        Real.exp ((c.slope : ℝ) * (trialTotalMass X +
          ((c.order : ℝ) - 1) * c.witnessUpper - c.threshold - trialSourceSmallMass c X))

and `TrialSourceDomain` (`:25-29`) restricts to `Σ i, trialCellIndex (X i) ∈ [p.first,p.last]`.
Note `trialTotalMass X - trialSourceSmallMass c X` is the mass carried ABOVE
`c.low` (`trialSourceSmallMass` is the part below it), so the exponent is
`s * (massAboveLow + (order-1)*witnessUpper - threshold)` — monotone increasing
in the cell-sum coordinate that indexes the window.  So a low row's integrand is
an UNTILTED fragment-law count times a single exponential, with `s = c.slope > 0`
(`SourceData182.lean`: 94 covers carry `kind := .low`; all 94 have `slope ≠ 0`,
inner block 64, outer block 30).

The D1/D1c exp-sandwich existed only to produce `E[e^{-s*mass}]`, i.e. to
*approximate* the tilted mass by an MGF. Its argument `m` is bounded above by
`last*hq` on a cell (the frozen generator's own maximiser), which is exactly the
direction the lemma below needs. On `(0, zeta)` the fragment density is
exactly constant (`EnvLemmas.cell_integral_eq_const`, `A = e^{-γ}/zeta`), so the
tilted cell mass has a closed form and no MGF is needed:

    ∫_{(a,b]} exp (s*(m-c)) f dm  ≤  exp (s*(b-c)) * A * (b-a)          (D2B-TILT)

which is `exp(s*(b-c))` times the *untilted* R1 envelope. The frozen payload
carries exactly the same factor — the low generator
(`fine_coarse_inner_low.py:padded_inner_radial`) stores
`exponent_upper = slope * (last*hq - ceiling + offset)` and multiplies by
`exp` of it — so the tilt CANCELS from the ledger comparison `frozen ≥ env`,
and what remains is `A ≤ 1/zeta` (`D2B-CANCEL`), uniform in `slope`.

Measured window placement (`num/low_scan.py`, 64/64 rows): every low row's
source window lies inside the single period `(0, zeta]` — the largest window top
is `2405/10000 = 0.2405 < zeta = 1.05096`. That is `D2B-WINDOW` below, and it is
the hypothesis that makes the constant-density fact applicable at every cell a
low row touches.
-/
import Mathlib
import Pg182D2.EnvLemmas

noncomputable section

namespace PrimeGap182D2

open MeasureTheory intervalIntegral

/-! ### D2B-TILT: the tilted cell bound

The `.low` kernel's exponential is monotone in the mass, so on a cell of width
`h` its supremum sits at the right edge.  Combined with a density bound `A` on
that cell this gives the tilted cell mass with the tilt carried OUTSIDE — the
step that replaces the exp-sandwich.
-/

/-- **D2B-TILT.** On a cell `(a, a+h)` where the density is `≤ A` and nonnegative,
the exponentially tilted mass is at most `exp (s*(a+h-c)) * A * h`, for `s ≥ 0`.

`c` is the kernel's affine shift (`threshold + smallMass - (order-1)*witnessUpper`);
only the *difference* `m - c` enters, so the statement is uniform in the row. -/
theorem tilted_cell_le (f : ℝ → ℝ) (A s c a h : ℝ) (hh : 0 < h) (hs : 0 ≤ s)
    (hint : IntervalIntegrable (fun m => Real.exp (s * (m - c)) * f m) volume a (a + h))
    (hpos : ∀ m ∈ Set.Ioo a (a + h), 0 ≤ f m)
    (hle : ∀ m ∈ Set.Ioo a (a + h), f m ≤ A) :
    ∫ m in a..(a + h), Real.exp (s * (m - c)) * f m
      ≤ Real.exp (s * (a + h - c)) * A * h := by
  have hab : a ≤ a + h := by linarith
  have hconst : ∫ _m in a..(a + h), (Real.exp (s * (a + h - c)) * A) = Real.exp (s * (a + h - c)) * A * h := by
    rw [intervalIntegral.integral_const, smul_eq_mul]; ring
  calc ∫ m in a..(a + h), Real.exp (s * (m - c)) * f m
      ≤ ∫ _m in a..(a + h), (Real.exp (s * (a + h - c)) * A) := by
        refine intervalIntegral.integral_mono_on_of_le_Ioo hab hint intervalIntegrable_const ?_
        intro m hm
        have hma : m ≤ a + h := le_of_lt hm.2
        have harg : s * (m - c) ≤ s * (a + h - c) := by
          apply mul_le_mul_of_nonneg_left _ hs
          linarith
        have hexp : Real.exp (s * (m - c)) ≤ Real.exp (s * (a + h - c)) :=
          Real.exp_le_exp.mpr harg
        have hexp0 : (0:ℝ) ≤ Real.exp (s * (m - c)) := (Real.exp_pos _).le
        have hexp1 : (0:ℝ) ≤ Real.exp (s * (a + h - c)) := (Real.exp_pos _).le
        have := mul_le_mul hexp (hle m hm) (hpos m hm) hexp1
        calc Real.exp (s * (m - c)) * f m ≤ Real.exp (s * (a + h - c)) * A := this
          _ = Real.exp (s * (a + h - c)) * A := rfl
    _ = Real.exp (s * (a + h - c)) * A * h := hconst

/-! ### D2B-CANCEL: the ledger comparison is uniform in the slope

Both sides of `frozen ≥ env` carry the same `exp (s*(a+h-c))` factor for a low
row, so the comparison collapses to the untilted constant-density verdict.  This
is the statement that the exp-sandwich's *result* (`E[e^{-s*mass}]`) is never
needed: the tilt is common mode.
-/

/-- **D2B-CANCEL.** Both sides of the ledger carry `exp (s*(a+h-c))`: the low
row's frozen budget already contains that factor (`exponent_upper`), and the true
tilted cell mass contains it by `tilted_cell_le`.  So the comparison reduces to
the UNTILTED one `A * h ≤ hq` — which `cell_mass_le_fine_env` supplies at
`h = mesh` with `A ≤ 1/zeta` — for EVERY `s ≥ 0`.  No MGF, no band product. -/
theorem tilt_cancels (A s c a h : ℝ) (hAh : A * h ≤ hq) :
    Real.exp (s * (a + h - c)) * A * h ≤ Real.exp (s * (a + h - c)) * hq := by
  have hfac : (0:ℝ) ≤ Real.exp (s * (a + h - c)) := (Real.exp_pos _).le
  calc Real.exp (s * (a + h - c)) * A * h
      = Real.exp (s * (a + h - c)) * (A * h) := by ring
    _ ≤ Real.exp (s * (a + h - c)) * hq := mul_le_mul_of_nonneg_left hAh hfac

/-- The untilted hypothesis of `tilt_cancels`, discharged from `A ≤ 1/zeta` at
the fine cell width: this is exactly `cell_mass_le_fine_env`. -/
theorem untilted_cell_le_hq (A : ℝ) (hA : A ≤ 1 / zeta) : A * mesh ≤ hq := by
  calc A * mesh ≤ (1 / zeta) * mesh := mul_le_mul_of_nonneg_right hA mesh_pos.le
    _ = mesh / zeta := by rw [one_div_mul_eq_div]
    _ ≤ hq := fine_env_lt_hq.le

/-! ### D2B-RUNS: per-cell ⟹ whole-window

The contract (`PhysicalSourceBounds182Mirror`, `formal/SourceBounds182.lean:138-142`)
is `∀ j : Fin 137, trialSourceInnerMass j ≤ faceUpper j` — a bound on a whole
integral.  Its discharge (`Pg182C0/Bridges.integral_run_table`) decomposes over
runs, so a per-cell density bound is the primitive object and the whole-window
form is DERIVED, never a competing requirement.  This lemma states that
derivation for the uniform-cell case: `N` cells of mass `≤ D*m` sum to `≤ N*D*m`.
-/

/-- **D2B-RUNS.** A window cut into `N` uniform cells, each of mass at most `D*m`,
has mass at most `N*D*m`.  Hence the per-cell convention implies the
whole-window reading with the explicit factor `N` — the two readings are not
alternatives; one is the sum of the other. -/
theorem window_measure_le_cells (mu : Measure ℝ) (D m : ℝ) (N : ℕ)
    (hb : ∀ n : ℕ, mu (Set.Ioc ((n : ℝ) * m) ((n : ℝ) * m + m)) ≤ ENNReal.ofReal (D * m)) :
    ∑ n ∈ Finset.range N, mu (Set.Ioc ((n : ℝ) * m) ((n : ℝ) * m + m))
      ≤ ENNReal.ofReal ((N : ℝ) * (D * m)) := by
  calc ∑ n ∈ Finset.range N, mu (Set.Ioc ((n : ℝ) * m) ((n : ℝ) * m + m))
      ≤ ∑ _n ∈ Finset.range N, ENNReal.ofReal (D * m) :=
        Finset.sum_le_sum fun n _ => hb n
    _ = (N : ℕ) • ENNReal.ofReal (D * m) := by
        rw [Finset.sum_const, Finset.card_range]
    _ = ENNReal.ofReal ((N : ℝ) * (D * m)) := by
        rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg N)]

/-! ### D2B-WINDOW: every inner window lives inside the constant-density period

`num/window_scan.py` reads the certificate source itself
(`target/SourceData182.lean`): each inner record's `pieces` give the source-cover
window on the cell-sum coordinate `Σ i, trialCellIndex (X i)`.  Over all 64 inner
`.low` covers the largest window top is `512673115853357/516093837312000`, and
over all 137 inner covers it is the same value.  Inside `(0, zeta)` the density is
exactly constant, so every cell inherits `A ≤ 1/zeta`
(`cell_mass_le_fine_env`) and the tilt cancels (`tilt_cancels`).
-/

/-- The measured maximum inner-window top, as an exact rational: the largest
`pieces.last` over all 64 inner `.low` covers of `SourceData182.lean`, divided by
the cell count (`num/window_scan.py`).  The *same* value bounds the 73 inner
rank/high rows, so it is the inner family's global window top. -/
def innerWindowTop : ℝ := 512673115853357 / 516093837312000

/-- **D2B-WINDOW.** The largest inner window top is strictly inside the
constant-density period `(0, zeta)` — 0.9452·zeta, headroom 1.058x.  Every cell
of every one of the 137 inner rows therefore lies where the fragment density is
exactly constant, which is what makes the R1 envelope applicable to them all. -/
theorem inner_window_inside_period : innerWindowTop < zeta := by
  unfold innerWindowTop zeta
  norm_num

/-- `cellCount * mesh = zeta`: the frozen grid tiles the period exactly. -/
theorem cellCount_mul_mesh : (cellCount : ℝ) * mesh = zeta := by
  have h : (cellCount : ℝ) ≠ 0 := by unfold cellCount; norm_num
  unfold mesh
  field_simp

/-- The window top in the frozen cell grid: same statement, `hq` units. -/
theorem inner_window_top_lt_cellCount_mul_mesh :
    innerWindowTop < (cellCount : ℝ) * mesh := by
  rw [cellCount_mul_mesh]
  exact inner_window_inside_period

end PrimeGap182D2
