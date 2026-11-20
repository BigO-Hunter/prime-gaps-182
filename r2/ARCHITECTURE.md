# PG182-R2 — The 262 Certification Machine

## What we are certifying

`romyar1/prime-gaps-lean` (cloned at `prime-gaps-lean/`, commit base per its `asset.json`)
proves `PrimeGap182.infinite_consecutive_prime_pairs182_of_local_inputs` **conditionally**
on 262 integral inequalities + 3 all-primes finite-field estimates + Type III
(`docs/assumptions.md`). Nobody has discharged any of these in Lean. R2 designs the
machine that does, kernel-side, with no `native_decide` and no new axioms.

## Key discovery: the leaf arithmetic is nearly exact

R1's premise extraction pending; we read the primary sources directly
(`formal/SourceBounds182.lean`, `SourceKernels182.lean`, `TrialData182.lean`,
`SourceData182.lean`). Findings that decide the architecture:

- **All certificate data is exact ℚ literals** (20–80 digit numerators). No π, no exp in
  the *data*. Square roots appear only as `sqrtUpper` rational bounds → comparisons
  `√r ≤ q` reduce to `r ≤ q²`, exact.
- Source covers (197 rows) split by `kind`: **96 `.rankTwo`** (piecewise-constant
  indicator integrals — exact), **7 `.high`** (Nat.choose of a decidable floor — exact),
  **94 `.low` with `slope ≠ 0`** (kernel contains `Real.exp (slope * (affine rational))`),
  **103 rows with `slope := 0`** (exp collapses to 1 — exact).
- Grids are run-length encoded (`counts : List (Nat × Nat × ℕ × ℚ)`), tens of runs per
  row — NOT 393,216 kernel terms. The fine grid (8192 bins, 48 blocks) exists only in
  the external numerics; Lean never needs it.

So the DZQ lesson lands again: **the arithmetic leaf decides certifiability, and here the
leaves are ℚ (103+96+7 rows) plus exp-of-ℚ (94 rows)**. No Arb/Taylor-model machinery is
needed inside Lean; intervals only enter as exp endpoint bounds.

## Per-class machines

### Class E — exact rational (5 cap + 96 rankTwo + 7 high + 103 slope-0 = 211 of 262)

Each receipt: `theorem hE_<id> : <integral-def> ≤ <rational literal>`.
Proof = generic bridge lemmas (below) + `decide`/`norm_num` over a run-table sum of
~30–300 ℚ terms with ~10^80 numerators — trivial kernel work (our 36-digit pattern at
~10^80 with 30–300 terms, batched per row, parallel at elaboration).

### Class X — exponential rows (94 `.low` rows, slope ≠ 0)

Per-cell `exp(a·t)` with a,t ∈ ℚ. Machine:
1. Formalized exp sandwich `expLB ≤ Real.exp r ≤ expUB` for rational r, proven **once**
   from Mathlib's `exp` series with rational partial-sum bounds (monotone `exp_le_exp`),
   instantiated by `decide` per argument.
2. Cell-integral `(exp(a·hi) − exp(a·lo))/a` bounded between rational endpoint values.
3. Sum of ~30 interval-bound terms per row; slack budget: the published `rootUpper`
   margins are ~10^-75 relative — exp bounds to 10^-80 relative are cheap (partial sums
   converge geometrically; ~30 series terms at these argument sizes).
Verdict: buildable; the exp-sandwich lemma is the one genuinely new Lean lemma.

### The bridge (the real work): integral = run-table sum

The repo defines the integrals as honest `∫` over product/count measures. Discharging a
premise needs `∫ (kernel) ∂measure = Σ_runs (...)` **proven in Lean** — this is exactly
the "algorithm-to-integral" gap the repo's own README flags. It factors into a finite
set of generic lemmas (written once, reused by all 262):
- B1: integral of a measurable function constant on a finite measurable partition =
  Σ value·μ(cell) (Mathlib: `Set.integral_congr_finite` family / simple-function lemmas).
- B2: product-measure Fubini for the marginal sums (39/38 coordinates).
- B3: count-measure pushforward for the `.low`/`.high` families (integral over the
  fragment-count statistic = sum over count bins).
- B4: exp-sandwich instantiation (Class X only).
Estimate: 3–8 lemmas, each days of Mathlib measure theory. This finite set is the only
surface a mathematical reviewer must check — everything else is kernel arithmetic.

### Class F — 3 finite-field estimates: NOT enumerable. Holes, stated exactly

The lane premise "finite-field estimates → exhaustive enumeration" is **false for these
three**: they are quantified over *all* primes:
1. `|Kl₃(c)| ≤ 3` (c ≠ 0) — Katz, *Gauss sums, Kloosterman sheaves and monodromy*,
   Thm 4.1.1 (Deligne purity specialized to rank 3).
2. two-Kloosterman correlation `≤ 8p√p` — Fouvry–Kowalski–Michel, Prop 2.
3. raw rank-four `≤ 4p√p` — Katz Thm 4.1.1, n = 4.
A table over residues cannot discharge a ∀p statement. Discharging them needs the
étale-cohomology Kloosterman-sheaf machinery (rank/trace/purity): **Mathlib has no étale
cohomology and no Deligne RH** → OPEN. The repo's 400+ `TypeIII*` files attack an
adjacent premise (`TypeIII.LocalFourierHypothesis`) from published interfaces and remain
open ("no closed proof"). These stay honest premises; nothing R2 can kernel-check here.

## Certificate skeleton (Stage D shape)

```lean
theorem PhysicalSourceBounds182_discharged :
    PhysicalSourceBounds182 :=  -- the premise record, 262 conjuncts
  ⟨hCap1, …, hCap5, fun j => hOuterRoot j, fun j => hOuterFace j, fun j => hInner j⟩
-- each hX is: generic bridge lemma ▹ run-table instantiation ▹ by decide (ℚ)
```

with the tuple/admissibility + bound-from-tuple deduction already in `formal/`
(reused, credited to romyar1). Trust: git-hashed `.lean` data literals, kernel `decide` /
`norm_num`, formalized exp sandwich. No JSON files trusted at proof time (the repo's own
`inputs/source_certificates/*.json` are evidence, not proofs — same as its README says).

Full rationale: TOOLING.md (tooling inventory), BUILD_PLAN.md (stages A–D),
TRUST_MODEL.md (what a reviewer must believe).
