# ROW_REPORT.md — Lane C0: the first rankTwo inner row, end to end

## The row

**Lean index 77** of `trialInnerCertificates` (SourceData182.lean) = coverage.json
inner[77] = **G3, bin 13** — the smallest of the 68 rankTwo inner rows
(one coarse run: fine cells 334254–343201, 8948 cells; two domain pieces).

## Exact Lean-side statement

```
trialSourceInnerMass 77
  = (∑ i : Fin 39, ∫ Y, trialMask 1 Y · trialSourceKernel cover77 Y · trialMarginal i Y²
       ∂trialProductMeasure 38) / trialPhysicalNormalizer
  ≤ rowFaceUpper77 = 1284030298488125680476898861995442227415740588344467984437
                     / 5928554968950589205686834432444820882087423214880796878820228301
                       2051522375647232        ≈ 2.165840251482751e-23
```

- `trialSourceKernel cover77` = the rankTwo kernel:
  `∫ q in Ioc(low, high), 𝟙(N(Ioi q)=0 ∧ 2 ≤ N(Ioc((θ−q)/2, q))) dN`,
  `N` = the fragment counting measure (`withDensity t⁻¹` of the summed coordinate
  measures on `Ioi 0`), low = 10203225535399/21503909888000,
  high = 122448362039057/258046918656000.
- `trialMask 1` = base-shell indicator (role 1, since family 2 < 4; proved
  as `innerRole77`).
- `trialMarginal i Y = ∫ X, trialStepFunction (insertNth X Y) ∂trialPhysicalMeasure`
  (the squared-sieve profile), `trialProductMeasure 38` = the 38-fold product of the
  scaled Poisson fragment law.
- The claimed bound is **byte-equal** to the frozen external payload
  (`fine_coarse_inner_sources_n393216.json`, G3 component 13 upper) and to
  `research/numerical_182/evidence/coverage.json` inner[77].

## Proof verdict: KERNEL-PROVED modulo one named hypothesis

`Pg182C0/RowCert.lean` builds (v4.34.1 + Mathlib). Axiom check
(`#print axioms` on row_77, row_77_of_frozen, arith77, NLB_le_normalizer,
integral_run_table, countMeasure_le_mass_mul, countMeasure_real_le_mass_div,
rankTwo_kernel_le_count): **propext, Classical.choice, Quot.sound only** —
no native_decide, no sorry, no new axioms.

Kernel-proved chain:
1. `hnormpos`/`NLB_le_normalizer` — `trialPhysicalNormalizer ≥ NLB` where
   `NLB = (mesh · Σ_{j<2} profile j²)³⁹` (partial-sum positivity; any larger
   partial sum strengthens it).
2. `row_77`: Σᵢ∫ᵢ ≤ 39·E77 (sum of the envelope bounds), then
   `sum/normalizer ≤ 39E77/normalizer ≤ 39E77/NLB ≤ faceUpper` — the last
   step is pure ℚ (`hArith`, norm_num-checked).
3. `arith77` — the required envelope strength is exactly
   `E77 = rowFaceUpper77 · NLB / 39` (an exact ℚ; ≈ 5.6e-64 at the true
   normalizer).

**The named gap (hypothesis `hEnv77`)**: for every i,
`∫ Y, trialMask 1 Y · kernel Y · marginal i Y² ≤ (E77:ℝ)`.
This is precisely the repo's flagged algorithm-to-integral argument — the
frozen FLINT programs' envelope contraction of the continuous Poisson-law
integrals. Nobody has closed it in Lean; C0 isolates it as one explicit,
quantified hypothesis with a computable required strength. Everything around
it is kernel-checked.

## Bridge-lemma inventory (BRIDGES.lean — all proved, all reusable)

| Lemma | Status | Role |
|---|---|---|
| `integral_le_of_pointwise_le` | proved | B1 engine (envelope majorization) |
| `integral_run_table` | proved | B1 run-table form: ∫(Σ cells·vals) = Σ v·μ(cell) |
| `countMeasure_le_mass_mul` | proved | B3 count part, ENNReal form |
| `countMeasure_real_le_mass_div` | proved | B3 count part, real form |
| `rankTwo_kernel_le_count` | proved (measurability as hypothesis) | B3 kernel ≤ N(q-window) |
| `trialMask_le_one` / `_nonneg` | proved | mask bounds |
| exp-sandwich | **not needed** for this row (slope-0 rankTwo), still owed for the 94 `.low` rows (C1) |
| B2 Fubini/marginal symmetry (Σᵢ marginal² = 39·marginal₀²) | **not proved** — folded into hEnv77's ∀i shape; owed when the frozen hypothesis is attacked directly |

## Cross-check receipt (python-flint / Fraction)

```
Lean rowFaceUpper77   = 1284030298488125680476898861995442227415740588344467984437/5928554…
coverage.json inner77 = same string, byte-equal: True
receipt G3 comp13 upper = same fraction (Fraction-equal: True)
value ≈ 2.165840251482751e-23
```

## Build notes

Toolchain v4.34.1; Mathlib `d13f23b7` (git-pinned); LAKE_JOBS=1,
LEAN_NUM_THREADS=1.
Files: `Pg182C0/Bridges.lean`, `Pg182C0/RowCert.lean`, committed 0de7aad.
