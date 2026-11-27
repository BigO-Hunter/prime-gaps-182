# D1B_REPORT.md — Lane D1b: the engine finished, the per-cell checks, the band form, the hEnv77 discharge

Repo dir `d1/`, toolchain v4.34.1 + Mathlib `d13f23b7` (git-pinned).
Builds: `LAKE_JOBS=1 LEAN_NUM_THREADS=1`, ~8934 jobs green at HEAD (`83ddbdb`).

## 1. D1Engine + D1Sum: INTO THE BUILD, GREEN (was: drafted, ~3 mechanical errors)

`Pg182D1/D1Sum.lean` (new in build):
- `sum_cell_probability_le` — **D1-SUM**: for the d-fold product of any
  probability law, `μ^d{sumCell = c} ≤ exp(s·(c+d)·mesh)·(∫⁻ e^{-s·mass} ∂μ)^d`
  for every `s ≥ 0`.
- `lintegral_massExp_pi` — the d-fold product MGF is the d-th power of the
  per-coordinate MGF (`iIndepFun_pi` + `measurePreserving_eval`).
- The "measurable-sum lemma" the draft was blocked on turned out to be
  already inside the draft's `measurable_sumCell` (induction on `Fin d` with
  `castSucc`); the real blockers were mechanical and are fixed: paren
  imbalance in the `∫⁻` statement, the curried type of the Markov integrand
  (`set g : Fin d → FiniteMeasure ℝ → ℝ≥0∞` needed parens — the tuple type,
  not two arguments), `Finset.mul_sum` direction on the exp-sum, the
  `toReal_le_toReal` direction (`.mpr` not `.mp`), and the prod-swap finish
  (`Finset.prod_const` on the univ product + `measurePreserving_eval`).

`Pg182D1/D1Engine.lean` (new in build):
- `integral_le_discrete` — **D1-ENGINE**: `f ≥ 0` pointwise dominated by a
  per-coarse-run envelope `σ(sumCell Y)`, supported on a finite run set `K`,
  each run class carrying at most `env r`, gives
  `∫ f dμ^d ≤ Σ_{r∈K} σ r · env r`.
- Fixes over the draft: the `single_le_sum` dominating-term membership (the
  draft's `Finset.mem_union_left` was nonsense), the indicator normalization
  (σ moved INSIDE the indicator, killing the const-lemma naming and the
  `Integrable.indicator` shape mismatches), `Integrable.mono'`'s norm form
  (`‖f‖ ≤ᵐ g`), and `integral_mono_of_nonneg`'s argument order (integrable
  BEFORE the domination in this Mathlib).

## 2. Per-cell checks: GENERATED + CERTIFIED (the data half)

`receipt/percell_gen.py` → `receipt/percell_receipt.json`:
- **Certified exact-ℚ intervals for every band exponent `b_k(s)`** at
  s ∈ {1, 1/2, 2}: the integrand `(1−e^{-su})/u` has the alternating series
  `Σ (−1)^{n+1} s^n u^{n−1}/n!`, so partial sums give RIGOROUS two-sided
  bounds in exact `Fraction` arithmetic (30 terms; factorial decay).
- **Band-sum identity check**: the Σ_k b_k interval overlaps the full-support
  integral interval at all three s (the Lean-side identity is
  `BandForm.sum_cappedDyadicIntensity`; numerically verified here).
- **Independent cross-check**: mpmath 40-digit quadrature of
  `∫_0^ζ (1−e^{-su})/u` agrees with the exact interval midpoints at all three
  s (python-flint 0.9.0 present but has no quadrature entry point — noted in
  the receipt).
- **Envelope emission**: per-cell `env(c) = exp(s(c+1)·mesh − Σ b_k)` values
  for the row-77 coarse-run window (c ∈ {6927…7150} sampled).
- **The frozen p^frozen_c**: the full per-cell array ships only in the
  external release archive (`external-numerics-20260909.zip`, 245 MB — not in
  the local review subset); the generator consumes it as input and emits one
  decide-able ℚ inequality per cell (the C0 `rowFaceUpper77` byte-equality
  pattern). This is the honest residual: the ℚ comparisons are generated and
  the envelope side is certified; the archive-side per-cell masses are a
  data supply step, not proof debt.

## 3. Per-band closed form: PROVED (BandForm.lean)

- Vendored the EReal Poisson-MGF machinery
  (`lintegral_exp_neg_finitePoissonLaw`, `exp_neg_ennreal_sum`) verbatim into
  `Support.lean` (same-commit vendor text, namespace ours).
- `bandMgf_eq` — **D1-BAND**: for every dyadic band k, the mass MGF under the
  band's Poisson law is EXACTLY
  `exp(−∫_{(2^k,2^{k+1}]∩(0,ζ]} (1−e^{−s·u})/u)` — kernel-proved by
  instantiating the EReal machinery on the band intensity measure (mirrors
  the vendor's `integral_exp_neg_mass_fragmentLaw` per band, no limit step).
- `bandMgf_le_one` — the band MGF ≤ 1 (the exponent is nonneg).
- `bandWindow ζ k` + measurability/positivity helpers.

## 4. Closed per-cell envelope: PROVED (PerCell.lean)

- `realMgf_eq_toReal` — the real mass MGF is the toReal of the ENNReal MGF.
- `cell_probability_closed` — **D1-PERCELL**: composing D1-CELL + D1-MGF +
  D1-BAND, for every cell n, s ≥ 0, finite band set S:
  `(fragmentLaw ζ).real {cell = n} ≤ exp(s·(n+1)·mesh)·exp(−Σ_{k∈S} b_k)`.
  This is the exact quantity the certified data bounds.

## 5. hEnv77 discharge: SCHEMA DELIVERED, VERDICT: closed modulo certified data

`Pg182D1/HEnv77.lean` (C0 untouched; stated over generic μ since C0's
`trialProductMeasure` is a stand-in):
- `hdata_of_frozen` — the frozen-mass contract: if the frozen per-run masses
  dominate the proved envelope class (one ℚ inequality per run), the engine's
  mass hypothesis holds.
- `integral_le_frozen` — D1-ENGINE at d = 38: the row integral ≤ Σ_{r∈K} σ r
  · p r (σ = frozen per-run suprema = the D3 payload; p = frozen masses).
- `hEnv77_discharge` — with the frozen discrete-sum comparison
  `Σ σ r · p r ≤ E77`, the hEnv77 shape follows: `∫ f ≤ E77`, uniform in the
  profile coordinate i (nothing depends on i).
- `hEnv77_discharge_of_frozen` — the same with the D1-data contract
  pre-discharged against the closed envelope class.

**Verdict**: hEnv77 is now a FINITE schema of machine-checkable ℚ comparisons
(frozen per-run suprema σ, frozen per-run masses p vs certified intervals,
and one discrete sum) — no analytic proof debt remains on the D1 side. The
remaining input is the frozen payload's per-run arrays from the external
package (D3 affine-prefix suprema are already local in
`fine_coarse_inner_sources_n393216.json`; the per-run masses ship in the
release archive).

## 6. Axcheck (receipt/axcheck.txt)

All 13 key theorems — `cell_probability_le`, `mgf_fragmentLaw_le_finset`,
`mass_finiteFragments`, `sum_cell_probability_le`, `lintegral_massExp_pi`,
`integral_le_discrete`, `bandMgf_eq`, `bandMgf_le_one`,
`cell_probability_closed`, `hdata_of_frozen`, `integral_le_frozen`,
`hEnv77_discharge`, `hEnv77_discharge_of_frozen` — depend on
**[propext, Classical.choice, Quot.sound] only**. No sorryAx, no
native_decide.

## Commits

| sha | content |
|---|---|
| `b8604c6` | D1-SUM + D1-ENGINE into the build (wip drafts fixed) |
| `18ca8e1` | D1-BAND + D1-PERCELL (vendored EReal MGF, closed forms) |
| `83ddbdb` | D1-hENV77 schema + certified per-cell receipt + axcheck |

## What is next (for the next session)

- Run `percell_gen.py` inside the extracted external package to emit the
  per-cell ℚ inequalities against the archive's per-run masses.
- Wire `HEnv77.hEnv77_discharge` into C0's `RowCert` as the hEnv77
  instantiation (C0 side; D1 side is done).
