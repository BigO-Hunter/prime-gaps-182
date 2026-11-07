# D2B_REPORT — the low rows + the window convention

**Radial windows: R1 SERVES the 64 low rows; the exp-sandwich is dead.**
The `.low` kernel is an untilted fragment count times
`exp(slope·(massAboveLow + (order−1)·witnessUpper − threshold))`
(SourceKernels182:41-45) — monotone in the cell-sum coordinate, so its cell sup
sits at the right edge: exactly what the frozen generator stores as
`exponent_upper`. Both sides of `frozen ≥ env` carry that same `exp(s(b−c))`, it
cancels, and the comparison reduces to the untilted `A ≤ 1/ζ`, uniform in slope.
Proved: `tilted_cell_le`, `tilt_cancels`, `untilted_cell_le_hq`. All 137 inner
windows, low included, lie in `(0,ζ)` — max top 0.993372 = 0.9452·ζ
(`num/window_scan.py` from SourceData182's `pieces`; pinned
`inner_window_inside_period`). Qualifier: the density actually consumed at the
window is the d=38 one (D2's 0.2959); R1 supplies the exactness and the
per-coordinate layer.

**Convention: PER-CELL STANDS, no recomputation.** The contract
(SourceBounds182:142) is `∀ j, innerMass j ≤ faceUpper j` — a whole-set integral,
no window probability on either side. Its discharge is a run-table sum, so
per-run measure is the primitive and the whole-window statement is its sum
(`window_measure_le_cells`). `source_mass = log(q_high/q_low)`
(`LargestFragmentBin.mass`), 68/68 at 1e-16 — a factor, not a probability; G3's
400× spread is `log(hi/lo)` over 15 count bins sharing one cover window. The
0.0449 figure is withdrawn: it measures a set no obligation uses.

**Map.** 262 = 5 cap + 120 outer + 137 inner; in covers, 60 outer (28 rankTwo +
30 low + 2 high) and 137 inner (68 rankTwo + 5 high + 64 low); 94 low = 64 inner
+ 30 outer, the 30 outer low being D1-independent. Matches D1's 5/56/4/60/73/64
obligation split exactly.

**Axcheck:** nine theorems, `[propext, Classical.choice, Quot.sound]` only. One
named input remains: `HasLocalBound` d=38.
