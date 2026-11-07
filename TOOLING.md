# TOOLING.md — what exists, what's missing

## Verified present (this machine, 2026-11-06)

| Tool | Status | Role |
|---|---|---|
| elan/lake/lean | installed; repo pins `leanprover/lean4:v4.34.0-rc2` (not cached; elan auto-fetches; v4.34.1 also cached) | build |
| **python-flint 0.9.0** | installed (fmpz/fmpq/arb/acb) | cross-check of every ℚ receipt + exp endpoint computation, independent of Lean |
| pdftotext / pypdf | installed | paper extraction |
| Mathlib | via lake-manifest of the repo (pin in `lake-manifest.json`) | measure theory, `exp` series, `norm_num` |

## Lean-side inventory

- **Kernel arithmetic over ℚ/ℤ literals**: `decide`, `norm_num` — proven pattern in our
  campaign (#158; 36-digit literals via `by decide` at ~176 s). The pg182 receipts are
  SMALLER (tens of terms, ~10^80 numerators). `maxRecDepth` raised **after imports**
  (campaign pattern). No `native_decide` anywhere — verifier policy.
- **Measure theory**: Mathlib has everything B1–B3 need (`MeasureTheory`,
  simple-function integrals, Fubini, pushforwards). No new library required —
  only new *instances* of existing lemmas for this measure family.
- **exp bounds**: Mathlib `Real.exp_le_exp`, `Real.exp_lt_exp`, series lemmas
  (`Real.exp_series`), `Real.exp_one_lt` etc. give the sandwich; missing piece is one
  reusable `exp_le_of_rational_series` helper — small, we write it.
- **Interval arithmetic in Lean**: NOT needed. This is the headline tooling result: the
  leaf class collapses to exact ℚ + rational exp endpoint bounds, so Arb-style balls,
  Taylor models, and validated ODE machinery are unnecessary kernel-side. python-flint
  arb is used only as an *independent cross-checker* of the endpoint data before it is
  frozen into `.lean` literals.

## Generator tooling (to write, plain Python, ~300 lines)

- `gen_receipts.py`: reads `TrialData182.lean`/`SourceData182.lean` structures,
  recomputes each run-table sum + comparison in `fmpq`, emits one Lean theorem per
  inequality with the tactic `by decide` (or a batched balanced-tree sum if elaboration
  depth demands), and an independent `fmpq` witness log (hash-committed).
- `gen_exp_bounds.py`: for the 94 slope rows, computes rational exp endpoints at
  10^-80 relative via `arb`, emits the per-row `decide` instantiations.
- Failure mode handled by design: if any row's published margin is tighter than our
  exp endpoint slack, the row FAILS the cross-check before Lean sees it → report to
  R1/board, do not hand-tune.

## Missing / open

1. **Mathlib étale cohomology / Deligne purity / Kloosterman sheaves** — absent; kills
   any kernel path to the 3 finite-field estimates. Not buildable this campaign;
   upstream dependency (exact refs in ARCHITECTURE.md §Class F).
2. **Type III `LocalFourierHypothesis`** — repo itself says "no closed proof"; R1's
   `type_iii/contractions/` work is the live attack. Not R2 scope.
3. **Toolchain pin**: building the repo downloads `v4.34.0-rc2` on first `lake build`;
   disk + network fine. `formal/` is 600+ files — full-build time unmeasured
   (BUILD_PLAN Stage 0 measures it).
4. **R1's PREMISE_MAP.md** — not landed yet at time of writing; our statements come
   from primary sources (`docs/assumptions.md` + the four `*182.lean` files). Cross-check
   against R1's map when it lands; divergence = stop and reconcile.
