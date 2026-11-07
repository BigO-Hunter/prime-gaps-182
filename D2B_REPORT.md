# D2B_REPORT.md — Lane D2b: the low rows + the window convention

Work dir `~/bigo-campaign/pg182-d2/` (continues D2 at `da1af69`); 8927 jobs green.

## 1. Radial windows: R1 SERVES THE LOW ROWS — no exp-sandwich

The `.low` kernel is an untilted fragment mass times
`exp(slope · (affine in the mass))` (SourceKernels182:41-45). Monotone, so its cell
supremum sits at the right edge — exactly the frozen `exponent_upper`. Both sides
of `frozen ≥ env` carry the same `exp(s(b−c))`; it cancels and the comparison
reduces to `A ≤ 1/zeta`, uniform in `slope`. Proved: `tilted_cell_le`,
`tilt_cancels`, `untilted_cell_le_hq`.

All 64 low windows lie inside `(0, zeta)` — max top `0.993372` = 0.9452·zeta
(`num/window_scan.py`, from SourceData182; pinned `inner_window_inside_period`).
The 73 rank/high rows hit the same maximum.

## 2. Convention: PER-CELL STANDS, no recomputation

The contract (SourceBounds182:142) is `∀ j : Fin 137, innerMass j ≤ faceUpper j` —
a whole-set integral with no window probability on either side. Its discharge is a
run-table sum, so per-run measure is the primitive and the whole-window reading is
its sum with an explicit factor (`window_measure_le_cells`).

`source_mass = log(q_high/q_low)` (`LargestFragmentBin.mass`), verified 68/68 to
1.0e-16 — a multiplicative factor, not a window probability. G3's 400× spread is
`log(hi/lo)` over 15 distinct count bins sharing one cover window. The 0.0449
figure is withdrawn: it measures a set no obligation uses.

## 3. Final map

262 = 5 cap + 60 outer (28 rankTwo + 30 low + 2 high) + 137 inner (68 rankTwo +
5 high + 64 low). 94 low = 64 inner + 30 outer; the 30 outer low are
D1-independent. See `OBLIGATION_MAP.md`.

## 4. Axcheck

All nine theorems on `[propext, Classical.choice, Quot.sound]`
(`receipt/axcheck_lowrows.txt`). Remaining named input: `HasLocalBound` d=38.

Files: `Pg182D2/LowRows.lean`, `CONVENTION.md`, `OBLIGATION_MAP.md`,
`num/{window_scan,low_scan,reconcile}.py`.
