# CONVENTION.md — which reading does the 262-obligation contract require?

Lane D2b. Question raised by D2's TIGHTNESS.md §4: the 73/73 sum-level count rides
D1c's *per-cell* convention (`c_max = 38·fine_last`), and D2 noted that on a
*whole-window* reading "no density bound closes it", with a 400× spread of the
frozen mass inside one group and a "true window probability" of 0.0449 against a
per-cell reading.

**Verdict: per-cell (per-run) is the correct and sufficient convention, and the
"whole-window" alternative is not a second requirement — it is the sum of the
per-cell one. No data-side recomputation is needed.** Two findings support this,
one from the contract's own quantifiers and one from the frozen data's own code.
A third finding withdraws the 0.0449 number.

## 1. What the contract literally says

`physicalSourceBounds182` (`prime-gaps-lean/formal/SourceBounds182.lean:138-142`,
mirrored in `pg182-frame/Pg182Frame/Obligations.lean` as
`PhysicalSourceBounds182Mirror`):

```lean
innerMass : ∀ j : Fin 137, trialSourceInnerMass j ≤ (trialInnerCertificates j).faceUpper
```

with (`SourceBounds182.lean:41-43`)

```lean
trialSourceInnerMass j =
  (∑ i : Fin 39, ∫ Y, trialSourceInnerWeight j Y * trialMarginal i Y ^ 2
     ∂(trialProductMeasure 38)) / trialPhysicalNormalizer
```

Three consequences, all mechanical:

* **The contract is a whole-set integral.** Neither side is a window probability.
  The right-hand side is one exact ℚ literal (`faceUpper`), which an integral of
  the profile-squared face weight must stay under. Nothing in the statement is
  "the probability of the window".
* **The only window in the integrand is a cell-sum window.** `TrialSourceDomain`
  (`SourceKernels182.lean:25-29`) restricts to
  `Σ i, trialCellIndex (X i) ∈ [p.first, p.last]` (`trialSourceCellSum`, `:23-24`).
  It is a *set of configurations* indexed by the cell-sum coordinate `r`, not a
  per-coordinate mass interval.
* **The discharge is a run-table sum.** C0's `integral_run_table`
  (`pg182-c0/Pg182C0/Bridges.lean`) rewrites the integral as
  `Σ_runs (integrand value)·μ(run)`. So the primitive object a bound is applied to
  is a **per-run measure** — per-cell is the contract's own decomposition, not a
  convention chosen on top of it.

Hence a density bound is compared per cell, and the whole-window statement is
*derived* from it. One precision about "which cell": the window lives in the
**cell-sum** coordinate `r` (dimension 38 for every inner cover), so the operative
density is the one for the 38-fold law — D2's `D = 0.29586259` — not the
single-coordinate `d = 1` law of D1c's "fine level". Both are per-cell readings;
only the density differs, and `HasLocalBound` is uniform in `(a, h)` for either.
That derivation is now proved, with the factor explicit:

```lean
window_measure_le_cells :   -- Pg182D2LowRows
  (∀ n, μ (Ioc (n*m) (n*m + m)) ≤ ofReal (D*m)) →
  Σ_{n<N} μ (Ioc (n*m) (n*m + m)) ≤ ofReal (N * D * m)
```

The two "readings" are one statement and its sum. `HasLocalBound`
(`Pg182D2/EnvLemmas.lean:160`) is uniform in `(a, h)`, so the same `D` serves every
window at once; the whole-window measure is bounded by `D × width`, i.e. by
`(width/mesh) ×` the per-cell bound. Comparing `D·h` (a measure) with a
window probability would be comparing a density to a set measure — the 0.0449
figure was that category error, not an alternative requirement.

## 2. What `source_mass` actually is (the 400× spread, explained exactly)

`source_mass` is **not** a window probability. In the frozen generator
(`experiments/fragment_ritz/fine_coarse_rank_two_face.py:83`,
`source = P.LargestFragmentBin(lo, hi, ceiling, order)`, `:133`
`source_mass = M.S.ball_record(source.mass)`) and

```python
# sources/PrimeGaps186/prime_gap_186_certificate.py:2147-2149
@property
def mass(self):
    return (rational(self.upper) / rational(self.lower)).log().upper()
```

i.e. **`source_mass = log(q_high / q_low)`** — the fragment law's mass of the
coordinate's source bin, since the law's intensity is `du/u`. It enters the frozen
bound as a multiplicative *factor*
(`normalization: "source.mass*k*h_fine/Z_fine"`, and
`face = total * source.mass * k * h_fine**2 / Z` at `:135`).

Measured, all 68 inner `rank_two` components of
`fine_coarse_inner_sources_n393216.json`:

| check | result |
|---|---|
| `source_mass == log(q_high/q_low)` | **68 / 68**, worst relative error **1.0e-16** (double-precision exact) |
| spread inside group G3 | `7.886e-05 … 1.000` — the 15 components have **15 distinct count bins** `[q_low,q_high]` |

And from the certificate source itself, the 15 **rank/high** components of group
G3 **share one source-cover window** — all 14 `rankTwo` entries and the `high`
entry carry `pieces := [⟨334254, 343163, …⟩, ⟨343164, 343201, …⟩]` — while their
count bins differ: **14 distinct `(low, high)` pairs** among the 14 `rankTwo`
components. The group's own `low` bins (8 of them) sit on that same window or a
narrower one (`[334254, 343201]` or `[338077, 343201]`). So the 400× spread is
precisely the spread of `log(high/low)` across distinct count bins over a common
window. It is expected, it is not an inconsistency, and the frozen data is not an
under-estimate of anything it claims to bound.

(Across the whole inner block the same structure repeats: the rank/high group of
each family has exactly 1 distinct window (68 `rankTwo` + 5 `high` → 5 windows),
while the low bins of G4 and G6 spread over 14 distinct windows each — a fact that
matters only for D3's per-run bookkeeping, not for the envelope class.)

## 3. The 0.0449 figure is withdrawn

D2's "true window probability = 0.0449" was computed as the probability that
**each** of the 38 retained coordinates lands in the fine window
`[0.893, 0.917]` (the "38 × the fine window" construction, ROUTE2.md / TIGHTNESS.md
§1). That set appears in no obligation: the kernel's window is the single
cell-sum condition `r ∈ [334254, 343201]`, i.e. total configuration mass
`∈ [0.8934, 0.9172]`. The measure of the *actual* obligation set is
`μ^{38}{r ∈ [first,last]}`, which a density bound covers by
`window_measure_le_cells`. So the whole-window worry is a misreading of the
window's coordinate, not a defect in the frozen data — nothing needs to be
recomputed.

## 4. What stands

| claim | status |
|---|---|
| fine-level envelope `1/zeta ≤ hq` (D2, R1) | stands, uniform in the cell |
| sum-level envelope `0.2959 hq` (D2, R4 + `HasLocalBound` d=38) | stands; it is a density, applied per cell and summed |
| low rows close with the tilt cancelled (D2b, `LOW_ROWS.lean`) | stands; no exp-sandwich needed |
| `137/137` fine and `73/73` sum counts (D2) | stand **as envelope-vs-frozen-budget checks at the row's maximal run cell**, in the frozen program's own normalization |
| "whole-window reading needs a recomputation" | **withdrawn** — the reading is the sum of the per-cell one; the 0.0449 set is not an obligation set |
| the 400× spread is a data defect | **withdrawn** — it is `log(hi/lo)` over distinct count bins |

One honest limit remains, and it is the same one D2 named: the run-table rewrite
per row (B1) needs the run set and the integrand suprema (D3 data), and the density
`D` for `d = 38` is the named analytic input `HasLocalBound`. Nothing in this
document adds a new input or removes that one.
