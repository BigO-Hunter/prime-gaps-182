# PR — Bochner product integral over `Measure.infinitePi`

**Deliverable status: READY TO OPEN (never opened by the campaign itself — the coordinator opens it).**
Prepared by lane N3, generalized and made PR-ready by lane N3b, in `~/bigo-campaign/pg182-d2/`. The
proof lives in `Pg182D2/InfinitePiProduct.lean`; the file already carries the Mathlib module header
(`module` / `public import` / `public section`), the Apache 2.0 licence line with
`Copyright (c) 2026 darkhipo`, and `namespace MeasureTheory`, so it lifts into Mathlib by copying it
to `Mathlib/MeasureTheory/Integral/InfinitePiProduct.lean` and changing nothing else.

Coordinator's rulings already applied: the PR opens **after** the `‖f i x‖ ≤ C i` generalization
(done, §"Main results"); author/licence `Copyright (c) 2026 darkhipo`, Apache 2.0 (done); the AI
disclosure below stays as written.

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

* finite index: `MeasureTheory.integral_fintype_prod_eq_prod`;
* nonnegative integrands, infinite index: derivable from `lintegral_tsum` (monotone convergence);
* Bochner/`ℂ` integrands, infinite index: **absent** — and monotone convergence does not apply,
  because the products are not nonnegative. The proof needs an honest convergence argument.

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

## Decisions already made (was: "what the coordinator must decide")

1. **It opens** — after the generalization, which is now landed (ruling 1).
2. **The generalization to `‖f i x‖ ≤ C i` is done**, as the head theorem, with the flat `≤ 1`
   version kept as a corollary so no consumer of the ≤ 1 form breaks (ruling 2).
3. **Author/licence**: `Copyright (c) 2026 darkhipo`, Apache 2.0, `Authors: darkhipo`; the file
   header placeholder is filled (ruling 3). The AI disclosure above stays as written.
