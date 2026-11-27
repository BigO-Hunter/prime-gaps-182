# D2_REPORT.md — Lane D2: the stronger envelope class

Repo dir `d2/` (toolchain v4.34.1 + Mathlib `d13f23b7` git-pinned; frame and
D1 dependencies resolve as `../` and `../d1`).
Builds `LAKE_JOBS=1`, `LEAN_NUM_THREADS=1`; HEAD `109b92e` + this commit, 8924
jobs green.

## 1. The diagnosis (corrected)

D1c concluded the contract `frozen >= env` is void because every window sits
*below* the mean. Measured: that is not the mechanism. At cell 334254 the Chernoff
envelope is `0.9772` — already below 1. What makes the contract void is **scale**:
a cell mass is `O(mesh) = 2.67e-6`, six orders below the O(1) tail bound. The
Chernoff/Markov step divides by `inf_{cell} e^{-s·mass} ≈ e^{-s·m}`, and on a cell
the integrand is constant, so the bound can never see the cell's *width*. No `s`,
no band set and no refinement of `B(s)` recovers the missing `mesh` factor.
Quantified in hq units: D1 = 365 227 hq (fine) / 194 820 hq (sum).

## 2. What closed

Two structural facts about the fragment law make the class exact-computable, and
both are elementary because the law is a Poisson process of intensity `du/u` on
`(0, zeta]`:

* `φ(t) = exp(-Cin(t zeta) - i Si(t zeta))`, `L(l) = exp(-Ein(l zeta))`
* **the density is exactly constant on `(0, zeta)`: `f ≡ e^{-γ}/zeta = 0.534237`**

The second follows from `l L'(l) = -(1-e^{-l zeta}) L(l)`, which in `m`-space is
the delay identity `m f'(m) = -f(m-zeta)·1{m>zeta}` — on `(0, zeta)` the shifted
term vanishes and `f' = 0`. Verified by exact inversion and by simulation.

**Route 1 wins the fine level:** constant density ⟹ cell mass `= A·mesh` with
`A·zeta ≤ 1` ⟹ every cell below `zeta` is `≤ mesh/zeta = 0.951515 hq < hq`.
Proved: `cell_integral_eq_const`, `cell_mass_le_fine_env`, `cell_mass_lt_hq`,
`fine_env_lt_hq`.

**Route 4 wins the sum level:** the Fejér/Esseen smoothing bound with the exact
`|φ|^38` gives `0.189413 hq` (certified rational `0.295863 hq`), i.e. inside `hq`
with 3.4× margin. `θ* = 2.331`, `∫_0^∞ e^{-38 Cin} = 0.2737` (certified 0.3945).

Both compose into one Lean object, `HasLocalBound mu D`
(`∀ a h, 0 < h → mu (Ioc a (a+h)) ≤ D·h`), consumed by `cell_measure_le_hq` /
`cell_measure_lt_hq`: `D ≤ 1/zeta` ⟹ the frozen uniform per-cell mass dominates
the envelope at **every** cell.

Routes 2 and 3 were ranked and run down: Bernstein/Bennett is closable (all
moments finite, `Var M = zeta²/2`) but is a deviation bound of the same O(1) scale
— a refinement of Chernoff, not a new class; Berry–Esseen is a CDF statement that
must pass through the same smoothing lemma, with a `1e-2`-scale constant against a
`1e-6` target. Full ranking: ROUTE2.md.

## 3. Tightness verdict at the windows

| class | `c` (env/hq) | vs truth | verdict |
|---|---|---|---|
| D1 Chernoff fine | 365 227 | 6.8e5 × | void |
| D1 Chernoff sum | 194 820 | 4.0e6 × | void |
| D2 Fejér `d=1` | 5.724 | 10.7 × | **fails** — `∫\|φ\| = ∞` |
| **D2-R1 fine** | **0.9515** | **1.781 ×** | **holds (4.85 % inside)** |
| **D2-R4 sum** | 0.1894 (cert. 0.2959) | 3.86 × (6.05 ×) | **holds (3.4× inside)** |

The fine-level margin is remarkable: the frozen mass is `e^γ = 1.7811×` the truth,
and the provable bound is `1/zeta` = 1.872× the truth — it clears by 4.85 %. The
whole fine-level arithmetic reduces to `1312494500 < 1379373467`.
The truth at the sum window is `f_38(34.8) = 0.0489` (density), i.e. `1.31e-7` per
cell — so the sum-level envelope is honest, not a vacuous win.

## 4. Re-run of the D1c counts (same ledger, one exact `decide` per row)

`receipt/lean/D2Emission.lean` — 73 decided comparisons + a batch seal, core
`decide` only, compiles in 1.9 s (`receipt/receipt.py` regenerates it).

| level | D1c | D2 |
|---|---|---|
| fine, row-77 cells | 0 / 8 948 | **8 948 / 8 948** |
| fine, rows | 0 / 137 | **137 / 137** |
| sum, rows | 5 / 73 | **73 / 73** |

Margins: fine `1.05096×` (uniform in `n`, so it is a statement about *all* cells,
not a per-cell scan); sum `35.7×` against the smallest frozen `p` (`2.8224e-05 =
10.56 hq`).

## 5. The remaining debt, named

1. **One analytic input.** Mathlib has `charFun` and Fourier inversion but no
   smoothing lemma, so `HasLocalBound` for `d = 38` is carried as a named input.
   Its proof is the Fejér-kernel computation derived in ROUTE2.md §Route 4 — kernel
   positivity, `Λ̂_T = (2π/T)(1-|t|/T)_+`, and the explicit `φ`. Self-contained
   Fourier analysis, no structural obstacle. This is the honest residual.
2. **A hard wall, not a gap.** The `d = 1` case of route 4 diverges
   logarithmically (`∫|φ| = ∞`), so no smoothing-type bound can close the fine
   level; route 1 is not an alternative there, it is the only route.
3. **A data-side caveat for D1/C0.** The frozen per-row `source_mass` cannot be a
   whole-window probability: G3's 15 components share one window yet claim masses
   spread 400×, while the true window probability is 0.0449. On the per-cell
   reading D1c's emission itself used, the count is 73/73; on a whole-window
   reading no density bound closes it *and* the frozen data would under-estimate.
   Flagged in TIGHTNESS.md §4 — a question for the data lane, not the envelope class.

## 6. Axcheck

`receipt/axcheck.txt` — `fine_env_lt_hq`, `mesh_div_zeta`,
`cell_integral_le_of_le`, `cell_integral_eq_const`, `cell_mass_le_fine_env`,
`cell_mass_lt_hq`, `cell_measure_le_hq`, `cell_measure_lt_hq`, `sum_env_lt_hq`:
all on **[propext, Classical.choice, Quot.sound]** only. No `sorryAx`, no
`native_decide`. The emitted receipt theorems are core `decide` only.

## 7. Files

| file | content |
|---|---|
| `Pg182D2/EnvLemmas.lean` (alias `ENV_LEMMAS.lean`) | the envelope class, proved |
| `ROUTE2.md` | the four routes ranked, the two winners, the walls |
| `TIGHTNESS.md` | the measured table, margins, the ledger caveat |
| `num/core.py` | exact `φ`/`Cin`/`Ein`, Fejér bound sweep, D1 cross-check |
| `num/verify.py` | delay identity + 38-fold inversion (the two claims) |
| `num/tightness.py` | regenerates the §3 table |
| `receipt/receipt.py` | all-rational certificate + `D2Emission.lean` emitter |
| `receipt/lean/D2Emission.lean` | 73 decided comparisons + seal |
| `receipt/axcheck.txt` | axiom footprints |

## 8. What is next

* Prove `HasLocalBound` for `d = 38` in Lean (the Fejér computation) — turns the
  one named input into a theorem and closes the sum level with no debt.
* Hand C0 the fine-level discharge: `cell_measure_lt_hq` needs only
  `D ≤ 1/zeta`, which route 1 supplies at *every* cell — no per-row scan, no data
  supply, for the D1-data step of the inner rows.
* D1/C0: settle the `source_mass` semantics (§5.3) so the per-run widths in the
  ledger are fixed; D2's envelope takes any width `h` (`fejer_bound(h, 38)`).
