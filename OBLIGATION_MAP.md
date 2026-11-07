# OBLIGATION_MAP.md — the 262 obligations, definitive counts (Lane D2b)

Supersedes `pg182-d1/OBLIGATION_MAP.md` on the count table and on the low-row
class. Source of every count here: **the certificate source itself**,
`frozen/.../target/SourceData182.lean` (parsed by `num/window_scan.py`), not the
payload file tree.

## 1. The table

```lean
structure TrialCerts182 where          -- formal/SourceData182.lean
  rootUpper      : Fin 60  → ℝ         -- outerRoot certificates
  faceUpper      : Fin 60  → ℝ         -- outerFace certificates
  innerFaceUpper : Fin 137 → ℝ         -- innerMass certificates
```
plus the 5 cap inequalities of `CapBounds182`. Contract:
`pg182-frame/Pg182Frame/Obligations.lean`, `PhysicalSourceBounds182Mirror`.

| family | count | kind split (from SourceData182.lean) | D1-data status |
|---|---:|---|---|
| Cap (denominator l/u, J0, Jplus, tail) | 5 | — | **D1-independent** |
| Outer root + face | 60 | **28 rankTwo + 30 low + 2 high** | **D1-independent** |
| Inner mass | 137 | **68 rankTwo + 5 high + 64 low** | **D1-data consumers** |
| **total** | **262** | **96 rankTwo + 94 low + 7 high = 197 covers** | |

Reconciliation of the "94 `.low` rows": **94 = 64 inner low + 30 outer low.** The
30 outer low rows lie in the outer root/face family, which consumes no per-cell
law mass (B1/B3 + D3 chain only), so they are not an envelope-class problem at
all. The 197-cover split `96/94/7` reproduces `pg182-r2/ARCHITECTURE.md:22`
exactly; the 137-inner split `68/5/64` reproduces D1c's map (73 rank/high + 64
low).

## 2. Per-class verdicts after D2 and D2b

Two layers, and only two, are needed by all 137 inner rows:

* **Layer M (cell masses).** `HasLocalBound mu D` with `D ≤ 1/zeta` (fine,
  R1 exact-convolution: the density is `e^{-γ}/zeta` on the whole period) and
  `D = 0.29586259` (sum, R4 Fejér with the exact `|φ|^38`). Both inside `hq`.
* **Layer I (integrand suprema).** The frozen affine-prefix / retained-maximum
  data (audit item 3, D3). Unchanged by this lane.

| class | n | layer M | layer I | status |
|---|---:|---|---|---|
| inner rankTwo | 68 | **closed** (`cell_measure_le_hq`, `HasLocalBound` d=38) | D3 data | envelope layer closed |
| inner high | 5 | **closed** | D3 data | envelope layer closed |
| **inner low** | **64** | **closed — tilt cancels** (`tilted_cell_le`, `tilt_cancels`, `untilted_cell_le_hq`) | D3 data | **envelope layer closed; no exp-sandwich owed** |
| outer low | 30 | not consumed | not consumed | D1-independent |
| outer rankTwo / high | 28 / 2 | not consumed | not consumed | D1-independent |

The low-row closure in one line: the `.low` kernel is an untilted fragment mass
times `exp(slope · (affine in the mass))` (`SourceKernels182.lean:41-45`); the
exponential is monotone so its cell supremum sits at the right edge — exactly what
the frozen generator stores as `exponent_upper`. Both sides of `frozen ≥ env`
carry the same factor, it cancels, and what is left is `A ≤ 1/zeta`. Uniform in
`slope`, no MGF product.

## 3. Window placement (why R1 applies to all of them)

`num/window_scan.py`, from `SourceData182.lean`'s `pieces` (the source-cover
window on `r = Σ i, trialCellIndex (X i)`), in mass units `r·hq`:

| family | n | window tops | max | vs `zeta = 1.050956` |
|---|---:|---|---:|---|
| inner low | 64 | 0.89337 … | **0.993372** | 0.9452·zeta, headroom 1.058× |
| inner rankTwo + high | 73 | 0.89337 … | 0.993372 | same |
| outer (all kinds) | 60 | 0.0195 … | 1.0508 | ≤ zeta |

Every window of every one of the 137 inner rows lies strictly inside the single
period `(0, zeta)` where the density is exactly constant — so no inner row touches
the dyadic tail, and R1's per-cell statement applies to every cell of every row.
Pinned in Lean as `inner_window_inside_period`.

## 4. The one remaining named input

`HasLocalBound` for `d = 38` at `D = 0.29586259` (the Fejér computation of
`ROUTE2.md` §Route 4). It serves the per-cell layer at the cell-sum coordinate,
is uniform in `(a, h)`, and is the only analytic debt in the D2/D2b envelope
class. It is *not* a data question: `D` is proved arithmetic
(`receipt/receipt.py`, all-rational) and consumed by `cell_measure_lt_hq`.

## 5. Axcheck

`receipt/axcheck_lowrows.txt` — `tilted_cell_le`, `tilt_cancels`,
`untilted_cell_le_hq`, `window_measure_le_cells`, `inner_window_inside_period`,
`cellCount_mul_mesh`, `inner_window_top_lt_cellCount_mul_mesh`, plus D2's
`fine_env_lt_hq`, `cell_measure_le_hq`: all on
**[propext, Classical.choice, Quot.sound]** only. No `sorryAx`, no
`native_decide`, no new axioms.
