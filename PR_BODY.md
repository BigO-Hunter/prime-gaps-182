# PR draft — Bochner product integral over `Measure.infinitePi`

**Deliverable status: DRAFT (not opened). The coordinator decides whether it goes to Mathlib.**
Prepared by lane N3 in `~/bigo-campaign/pg182-d2/`; the proof lives in
`Pg182D2/InfinitePiProduct.lean` (contents are already in `namespace MeasureTheory`, so the file
lifts into Mathlib by copying it and changing the header).

---

## Proposed title

`feat(MeasureTheory): Bochner product integral over Measure.infinitePi`

## Proposed file placement

`Mathlib/MeasureTheory/Integral/InfinitePiProduct.lean`

Imports (verified sufficient — the module compiles with exactly these, under
`set_option autoImplicit false`):

```lean
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.ProductMeasure
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

theorem MeasureTheory.hasProd_integral_tprod_infinitePi
    (hf : ∀ i, AEStronglyMeasurable (f i) (μ i))
    (hb : ∀ i, ∀ᵐ x ∂(μ i), ‖f i x‖ ≤ 1)
    (hsum : ∑' i, ∫⁻ x, (‖f i x - 1‖₊ : ℝ≥0∞) ∂(μ i) ≠ ∞) :
    HasProd (fun i => ∫ x, f i x ∂(μ i)) (∫ x, ∏' i, f i (x i) ∂(Measure.infinitePi μ))

theorem MeasureTheory.integral_tprod_infinitePi
    (hf) (hb) (hsum) :
    ∫ x, ∏' i, f i (x i) ∂(Measure.infinitePi μ) = ∏' i, ∫ x, f i x ∂(μ i)
```

(`ι` countable, `[∀ i, MeasurableSpace (X i)]`, `μ : (i : ι) → Measure (X i)` with
`[∀ i, IsProbabilityMeasure (μ i)]`, `f : (i : ι) → X i → ℂ`.)

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
3. **A.e. multipliability.** `multipliable_one_add_of_summable` applied to
   `f i (x i) - 1`, using step 2.
4. **Limit.** `tendsto_integral_filter_of_dominated_convergence` along
   `atTop : Filter (Finset ι)`, dominated by the constant `1` (hypothesis `‖f i x‖ ≤ 1`), pointwise
   convergence from step 3; rewrite the finite-subset integrals with step 1. The conclusion is
   literally `HasProd (fun i => ∫ x, f i x ∂(μ i)) (∫ x, ∏' i, f i (x i) ∂(infinitePi μ))`;
   `HasProd.tprod_eq` turns it into the equation form.

## Review-risk notes

* The bound `‖f i x‖ ≤ 1` is what makes the dominator the constant `1`. A PR reviewer may ask for
  a version with `‖f i x‖ ≤ C i` and `∑ ∫⁻ ‖f i‖ < ∞`; that is a straightforward generalization
  (`Finset.norm_prod_le` against the nonnegative product, whose `∫⁻` is `∏' i, ∫⁻ ‖f i‖` by the
  nonnegative infinite-index case) but it is **not** done here — flagging it as the obvious
  follow-up rather than claiming it.
* The summability hypothesis `∑' i, ∫⁻ x, ‖f i x - 1‖₊ ≠ ∞` is chosen because
  `multipliable_one_add_of_summable` consumes the real-valued `Summable fun i => ‖f i (x i) - 1‖`
  and `ENNReal.tsum_coe_ne_top_iff_summable` converts between them. A reviewer may prefer a
  hypothesis phrased through `Summable` on `ℝ≥0`-norms directly; the two are equivalent.
* `𝕜`-generalization (any `RCLike 𝕜` / `NormedField`) is open; `ℂ` is what the use case needs.
* No `sorry`, no `native_decide`, no new axioms: all four theorems report
  `[propext, Classical.choice, Quot.sound]` (a receipt is checked into the campaign at
  `receipt/axcheck_infinitepiproduct.txt`).

## AI usage disclosure (Mathlib requires one)

This contribution was produced by an AI agent (a large language model driven by the `opencode`
harness) inside a human-directed formalization campaign; the human, darkhipo, reviewed and is
submitting it. Every statement was checked by the Lean kernel; the proofs are machine-generated
and human-readable but not human-written. The docstrings and this description were written by the
agent.

## Checklist (Mathlib's)

- [x] depends on no new axioms / `sorry`-free (kernel-verified, `#print axioms` receipt attached)
- [x] builds with the narrowest import set that works
- [x] `set_option autoImplicit false` clean
- [x] no linter warnings (`linter.unusedSectionVars` silenced with `omit`, not globally)
- [x] docstrings on every declaration, module docstring present
- [x] naming matches Mathlib conventions (`integral_*_prod_*`, `ae_*`, `hasProd_*`)
- [ ] reviewed by a human Lean expert — **not done**
- [ ] argued as `Mathlib`-worthy by a maintainer — that is your call

## What the coordinator must decide

1. Open it at all (the campaign already has PR #45650 open; a second, independent contribution is
   allowed but two open PRs from one author can invite "please focus" review comments).
2. Whether to first generalize to `‖f i x‖ ≤ C i` per the risk note above — that is the version a
   Mathlib reviewer is more likely to accept, and it is a bounded extra effort.
3. Author/licence wording: `Copyright (c) 2026 darkhipo`? The file header currently says
   `Copyright (c) 2026 ...` (placeholder) and Apache 2.0, matching Mathlib.
