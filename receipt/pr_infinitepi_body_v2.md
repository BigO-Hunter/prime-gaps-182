# PR — Bochner product integral over `Measure.infinitePi`

The proof is a single new file, `Mathlib/MeasureTheory/Integral/InfinitePiProduct.lean`, carrying
the Mathlib module header (`module` / `public import` / `public section`), the Apache 2.0 licence
line with `Copyright (c) 2026 darkhipo`, and `namespace MeasureTheory`.

---

## Proposed title

`feat(MeasureTheory): Bochner product integral over Measure.infinitePi`

## Proposed file placement

`Mathlib/MeasureTheory/Integral/InfinitePiProduct.lean`

Imports (verified sufficient — the module compiles with exactly these, under
`set_option autoImplicit false`, in the modern `module`/`public import` form):

```lean
public import Mathlib.Analysis.SpecialFunctions.Log.Summable
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Probability.ProductMeasure
```

Rationale for placement: it is the infinite-index companion of
`MeasureTheory.integral_fintype_prod_eq_prod` (`Mathlib/MeasureTheory/Integral/Pi.lean`), and it
integrates over `Measure.infinitePi` (`Mathlib/Probability/ProductMeasure.lean`).

## Main results

```lean
theorem MeasureTheory.integral_finset_prod_infinitePi
    (hf : ∀ i, AEStronglyMeasurable (f i) (μ i)) (s : Finset ι) :
    ∫ x, ∏ i ∈ s, f i (x i) ∂(Measure.infinitePi μ) = ∏ i ∈ s, ∫ x, f i x ∂(μ i)

theorem MeasureTheory.ae_summable_norm_sub_one_infinitePi
    (hf : ∀ i, AEStronglyMeasurable (f i) (μ i))
    (hsum : ∑' i, ∫⁻ x, (‖f i x - 1‖₊ : ℝ≥0∞) ∂(μ i) ≠ ∞) :
    ∀ᵐ x ∂(Measure.infinitePi μ), Summable fun i => ‖f i (x i) - 1‖

-- the general form: a norm bound family instead of a flat 1
theorem MeasureTheory.hasProd_integral_tprod_infinitePi_of_norm_le
    (hf : ∀ i, AEStronglyMeasurable (f i) (μ i))
    (hC0 : ∀ i, 0 ≤ C i)
    (hb : ∀ i, ∀ᵐ x ∂(μ i), ‖f i x‖ ≤ C i)
    (hC : Summable fun i => ‖C i - 1‖)
    (hsum : ∑' i, ∫⁻ x, (‖f i x - 1‖₊ : ℝ≥0∞) ∂(μ i) ≠ ∞) :
    HasProd (fun i => ∫ x, f i x ∂(μ i)) (∫ x, ∏' i, f i (x i) ∂(Measure.infinitePi μ))

-- the ≤ 1 case, kept as a corollary (this is the form the campaign consumes)
theorem MeasureTheory.hasProd_integral_tprod_infinitePi
    (hf) (hb : ∀ i, ∀ᵐ x ∂(μ i), ‖f i x‖ ≤ 1) (hsum) : HasProd …

theorem MeasureTheory.integral_tprod_infinitePi (hf) (hb) (hsum) :
    ∫ x, ∏' i, f i (x i) ∂(Measure.infinitePi μ) = ∏' i, ∫ x, f i x ∂(μ i)
```

(`ι` countable, `[∀ i, MeasurableSpace (X i)]`, `μ : (i : ι) → Measure (X i)` with
`[∀ i, IsProbabilityMeasure (μ i)]`, `f : (i : ι) → X i → ℂ`, `C : ι → ℝ`.)

## Why it is not already there

* finite index, product-measure form: `MeasureTheory.integral_fintype_prod_eq_prod`;
* finite index, independence form: `ProbabilityTheory.iIndepFun.integral_prod_eq_prod_integral`
  (and the more general `iIndepFun.integral_fun_prod_comp` for functions of independent random
  variables), in `Mathlib/Probability/Independence/Integration.lean` — this is the closest existing
  relative of the present file, and it already contains the reduction of independence to the pi
  product measure (`iIndepFun.map_fun_eq_pi_map`) that the infinite-index statement takes as its
  starting point;
* nonnegative integrands, infinite index: derivable from `lintegral_tsum` (monotone convergence);
* Bochner/`ℂ` integrands, infinite index: **absent** — and monotone convergence does not apply,
  because the products are not nonnegative. The proof needs an honest convergence argument.

## Relation to `iIndepFun.integral_prod_eq_prod_integral`

That theorem and its neighbors state the **finite-index** identity `μ[∏ i, X i] = ∏ i, μ[X i]` for
a family of **mutually independent random variables** `X : (i : ι) → Ω → 𝓧 i` on a common
probability space (`[Fintype ι]`, `iIndepFun X μ`, measurability only — at finite index no
convergence content is even statable). The present file is the **countable-index, infinite-product,
bare-product-measure** analogue, and the delta is exactly what finiteness hid:

* **index**: `[Fintype ι]` there vs `[Countable ι]` with genuinely infinite `∏'` here — the
  conclusion is a `HasProd` convergence statement, so a.e. summability of `∑ i, ‖f i (x i) - 1‖`
  (Tonelli) and `multipliable_one_add_of_summable` enter, neither of which has a finite-index
  counterpart;
* **framing**: there, hypotheses on a common probability space plus `iIndepFun`; here, no
  random-variable layer at all — the statement is directly about `Measure.infinitePi μ`, the
  product-measure form their `iIndepFun.map_fun_eq_pi_map` reduces independence to;
* **bounds**: there, none needed; here, the `‖f i x‖ ≤ C i` bound family with
  `∑ i, ‖C i - 1‖` summable is what makes dominated convergence along `Finset ι` work ("Why the
  bound family is `∑ ‖C i - 1‖`" below).

Conversely, neither statement subsumes the other: the independence file cannot state an infinite
product, and this file does not require (or produce) the `iIndepFun` common-space packaging.

## Proof sketch (for the review)

1. **Finite subsets.** `(Measure.infinitePi μ).map (Finset.restrict s) = Measure.pi (μ|_s)`
   (`Measure.infinitePi_map_restrict`), then `integral_fintype_prod_eq_prod` and
   `measurePreserving_eval_infinitePi` for the single coordinates.
2. **A.e. summability of the deviations.** Tonelli: `∫⁻ x, ∑' i, ‖f i (x i) - 1‖` equals
   `∑' i, ∫⁻ x, ‖f i x - 1‖` (`lintegral_tsum` + `lintegral_map'`), finite by hypothesis, hence
   `∑ i, ‖f i (x i) - 1‖` is summable for a.e. `x`.
3. **A.e. multipliability.** `multipliable_one_add_of_summable` applied to `f i (x i) - 1`.
4. **Domination.** `‖∏ i ∈ s, f i (x i)‖ = ∏ i ∈ s, ‖f i (x i)‖ ≤ ∏ i ∈ s, C i`, and
   `C i ≤ exp (C i - 1)` for `C i ≥ 0` gives
   `∏ i ∈ s, C i ≤ exp (∑ i ∈ s, (C i - 1)) ≤ exp (∑' i, ‖C i - 1‖)` — a constant independent of `s`.
5. **Limit.** `tendsto_integral_filter_of_dominated_convergence` along `atTop : Filter (Finset ι)`,
   dominated by that constant, pointwise convergence from step 3; the finite-subset integrals are
   rewritten by step 1. `HasProd.tprod_eq` turns the convergence form into the equation form.

## Why the bound family is `∑ ‖C i - 1‖` and not `∑ C i`

A product of bounds is not additive in them: a factor `C i < 1` scales the bound *down*, a factor
`> 1` scales it *up*, so summability of `C` alone does not bound `∏ i ∈ s, C i` uniformly. The
log-scale hypothesis `Summable fun i => ‖C i - 1‖` is exactly the statement that the family `C` is
multipliable, made explicit; `exp (∑' i, ‖C i - 1‖)` is then the dominator. The flat case is
`C ≡ 1` (where `∑ ‖C i - 1‖ = 0` and the dominator is `1`), which is the corollary above.

## Review-risk notes (honest)

* The `𝕜`-generalization (any `RCLike 𝕜` / `NormedField` instead of `ℂ`) is **open**; `ℂ` is what
  the use case needs. The proofs use only the normed-field structure plus completeness of `ℂ`, so
  the generalization is plausible but not attempted here.
* The summability hypothesis `∑' i, ∫⁻ x, ‖f i x - 1‖₊ ≠ ∞` is chosen because
  `multipliable_one_add_of_summable` consumes the real-valued `Summable fun i => ‖f i (x i) - 1‖`
  and `ENNReal.tsum_coe_ne_top_iff_summable` converts between them. A reviewer may prefer a
  hypothesis phrased through `Summable` on `ℝ≥0`-norms directly; the two are equivalent.
* The bound family is not required to be *sharp* or to converge to `1`; `C i` may be any
  nonnegative family with `∑ ‖C i - 1‖` summable, including `C i < 1` for every `i`.
* No `sorry`, no `native_decide`, no new axioms: every declaration reports
  `[propext, Classical.choice, Quot.sound]`, including the generalized theorem (receipt:
  `receipt/axcheck_infinitepiproduct.txt`, regenerated by `receipt/axcheck_infinitepiproduct.lean`).

## AI usage disclosure (Mathlib requires one)

This contribution was produced by an AI agent (a large language model driven by the `opencode`
harness) inside a human-directed formalization campaign; the human, darkhipo, reviewed and is
submitting it. Every statement was checked by the Lean kernel; the proofs are machine-generated
and human-readable but not human-written. The docstrings and this description were written by the
agent.

## Checklist (Mathlib's)

- [x] depends on no new axioms / `sorry`-free (kernel-verified, `#print axioms` receipt attached
      for all five declarations)
- [x] builds with the narrowest import set that works (five `public import`s, each exercised)
- [x] `set_option autoImplicit false` clean
- [x] no linter warnings in this file (rebuilt clean: `lake build Pg182D2` reports no warning or
      error for `Pg182D2/InfinitePiProduct.lean`)
- [x] docstrings on every declaration, module docstring present, `## Main results` section
- [x] naming matches Mathlib conventions (`integral_*_prod_*`, `ae_*`, `hasProd_*`, `_of_norm_le`)
- [x] Mathlib module form (`module`, `public import`, `public section`)
- [x] licence header complete: `Copyright (c) 2026 darkhipo. All rights reserved.`,
      Apache 2.0, `Authors: darkhipo`
- [ ] reviewed by a human Lean expert — **not done**. Nothing in this file has been read by a
      human with Lean expertise; the human submitting it has reviewed the *statement* and the
      campaign's use of it, not the proof scripts.
- [ ] argued as `Mathlib`-worthy by a maintainer — that is the reviewers' call, not ours.

## Verification against upstream `master` at PR time

Copied into `Mathlib/MeasureTheory/Integral/InfinitePiProduct.lean` on branch `infinite-pi-product`,
based on `master` @ `71441a1480` (`chore: update Mathlib dependencies 2026-11-07`),
toolchain `leanprover/lean4:v4.36.0-rc2`.

* `lake exe cache get` + `lake build Mathlib.MeasureTheory.Integral.InfinitePiProduct`
  → `Build completed successfully`, **no warnings** (the build runs Mathlib's standard linter set,
  including `linter.style.longLine`, the header linter and `unusedSectionVars`).
* `lake exe lint-style Mathlib.MeasureTheory.Integral.InfinitePiProduct` → exit code 0.
* `lake exe mk_all` → the generated `Mathlib.lean` import line is byte-identical to the committed one.
* `#print axioms` on the upstream copy: all five declarations depend only on
  `[propext, Classical.choice, Quot.sound]`, i.e. no `sorry` and no new axioms.

Adaptations required by upstream `master` (the proof itself is unchanged from the version that
compiled against the pin used during the campaign):

1. removed `set_option autoImplicit false` — `autoImplicit` is `false` globally in `lakefile.lean`;
2. `AEMeasurable.nnnorm` → `AEMeasurable.nnNorm` (two sites) and `coe_nnnorm` → `coe_nnNorm`,
   which are deprecated at `master`;
3. two lines reflowed to satisfy the 100-character `linter.style.longLine`;
4. added the import to `Mathlib.lean`.

