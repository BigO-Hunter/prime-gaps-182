# TIGHTNESS.md — measured tightness of the D2 envelope class at the windows

Everything below is measured, not asserted; reproductions are
`num/tightness.py`, `num/core.py`, `num/verify.py`, `receipt/receipt.py`.

Units: the obligation compares against the frozen uniform per-cell mass
`hq = mesh = zeta/393216 = 2.6727183455e-06`, with
`zeta = 1379373467/1312494500 = 1.0509556170`.
Writing `env = c·hq` is the useful normalisation because the D1c ledger asks
`p_frozen >= env`, and (fine level) `p_frozen = hq` exactly, so **the contract is
`c <= 1`**. For scale: the D1 envelopes exceeded it by 3.7e5.

## §1 The truth at the windows

| quantity | value | how |
|---|---|---|
| `f` on `(0, zeta)` | **0.534237 = e^{-γ}/zeta**, constant | delay identity + exact inversion |
| `f_1(0.5) / f_1(0.9) / f_1(1.2)` | 0.533631 / 0.537038 / 0.465842 | `vi.f_d` (inversion) |
| `f_38(34.4) / f_38(34.8) / f_38(35.5)` | 0.044091 / 0.048925 / 0.057433 | `vi.f_d` (inversion) |
| row-77 fine window | mass ∈ [0.893369, 0.917282] ⊂ (0, zeta) | cells 334254…343201 |
| row-77 sum window | mass ∈ [33.95, 34.87], `P = 0.0449` | 38 × the fine window |
| `E[M] / Var M` | 1.050961 / 0.552201 | sim 2e6; exact 1.050956 / 0.552254 |
| `P(M<ζ) / P(M<1)` | 0.561446 / 0.534347 | sim; exact `e^{-γ}=0.561459` / `A=0.534237` |
| density in 6 equal slices of `(0,ζ)` | .5326 .5353 .5364 .5344 .5337 .5343 | sim; predicted 0.534237 in every slice |

The single most important measurement: **the density is flat over the entire
first period `(0, zeta)`**, which contains every window the 137 rows touch. That
is why the fine level is not a marginal-gain problem at all.

## §2 The envelope classes, in hq units

| class | envelope | `c` | vs truth | verdict |
|---|---|---|---|---|
| D1 Chernoff, fine (cell 334254, s\*=0.318) | 0.9772 | **365 227** | 6.8e5 × | void |
| D1 Chernoff, sum (c = 38·fine_last, s\*=0.20) | 0.52 | **194 820** | 4.0e6 × | void |
| D2-R4 Fejér, `d=1` (cell width) | 5.7240·hq | 5.724 | 10.7 × | **fails** (log divergence) |
| **D2-R1 fine (delay identity)** | **0.951515·hq** | **0.9515** | **1.781 ×** | **holds** |
| **D2-R4 sum, exact `\|φ\|^38`** | 0.189413·hq | 0.1894 | 3.86 × | **holds** |
| **D2-R4 sum, rational certificate** | 0.295863·hq | 0.2959 | 6.05 × | **holds** |

Notes.
* The `d=1` Fourier row is the honest wall: `|φ(t)| ~ e^{-γ}/(t zeta)` is not
  integrable, so every smoothing-type concentration bound is `O(h log 1/h)` here
  and lands at `5.72·hq` — above `hq`, unusable. Fine level needs route 1.
* The sum row improves *because* `d` is large: raising `|φ|` to the 38th power
  makes the integrand integrable and concentrated at `t ≲ 1`.
* `θ* = 2.331` is the analytic optimum of `θ sin θ = 1 - cos θ`; sweeping a 2000
  point grid recovers it (`num/core.py`), which is a check on the derivation.
* The certified row is the same bound with every transcendental replaced by a
  rational inequality (`Cin ≥ x²/4 - x⁴/96`; `Cin ≥ γ - 1/x - 1/x²` with
  `log x ≥ 2(x-1)/(x+1)`, clamped at `23/96`; `e^{-y} ≤ (1+y/2)^{-2}`;
  left-Darboux upper sums; `e^{38} ≤ 3.2e16` for the tail). It costs 1.56× and is
  still 3.4× inside `hq`.

## §3 Margins against the frozen data (the D1c ledger, re-run)

* **Fine level.** Need `env ≤ hq`; have `1/zeta = 0.951515`. Margin `1.05096×`.
  Uniform in the cell: the bound does not depend on `n` at all (the density is
  flat), so the row-77 window holds at **8948/8948 cells** and all 137 rows hold.
* **Sum level.** Need `env ≤ p_frozen`; smallest frozen `p` across the 73
  rank/high rows is `2.8224e-05 = 10.56 hq`; have `0.2959 hq`. Margin `35.7×`.

Re-run counts (impossible-to-fudge, one exact `decide` per row,
`receipt/lean/D2Emission.lean`, compiles in 1.9 s):

| level | D1c | D2 |
|---|---|---|
| fine, row-77 cells | 0 / 8 948 | **8 948 / 8 948** |
| fine, rows | 0 / 137 | **137 / 137** |
| sum, rows | 5 / 73 | **73 / 73** |

(The five D1 holds were the `high` components with frozen mass exactly 1; they
hold here too, trivially.)

## §4 Caveat on the ledger's reading — measured, and it matters

If a frozen `p` were read as the probability of the **whole** row window at the sum
level, then that window's true probability is `0.0449` while G3's components claim
`0.0308 … 7.9e-05` — a 400× spread *inside one group sharing one window*. Two
consequences:

1. The per-row `source_mass` cannot be a window probability; it is a
   per-run/per-cell-scale quantity, which is the reading D1c's own emission used
   (`env` at a single sum cell `c_max = 38·fine_last`). D2's counts above are on
   that same convention.
2. On a whole-window reading, no density bound closes the contract **and** the
   frozen data would be an *under*-estimate of the truth. That is a data-side
   question for D1/C0 — the envelope class is not the obstacle there.

## §5 What the numbers say about the D1c diagnosis

D1c concluded "the blocker is the envelope CLASS, not the data", and put the void
down to "`m` below the mean". The first half is right, the second half is not the
mechanism: at `m` just below the mean the Chernoff envelope is `0.977`, i.e.
*already below 1*. What kills it is that a cell probability is `O(mesh)`, six
orders below 1, so the bound is void at the mean, below the mean, and above it.
The cure is not a different tilt; it is a different *scale* — the density factor.
