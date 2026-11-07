# MATHLIBGAP_REPORT — the Bochner `infinitePi` product integral: CLOSED

Lane N3, work dir `~/bigo-campaign/pg182-d2/`, continuing N1N2.  Deliverables:
`Pg182D2/InfinitePiProduct.lean` (the lemma), `PR_BODY.md` (Mathlib PR draft),
`receipt/axcheck_infinitepiproduct.txt`.

## 0. Verdict

| item | verdict |
|---|---|
| **the lemma** (`N1N2_REPORT.md` §2 step 2, the named Mathlib gap) | **PROVED — unconditionally**, all four theorems on `[propext, Classical.choice, Quot.sound]` |
| Mathlib PR | **DRAFT only** (`PR_BODY.md`); nothing opened, nothing posted externally |
| (N1) residual as a whole | **still open**, but its only *Mathlib-level* blocker is gone: what remains is steps 1 and 3, both mechanical, plus a **correction to step 1's statement** (§3) |

## 1. What was proved

`Pg182D2/InfinitePiProduct.lean`, module docstring and four declarations, in `namespace
MeasureTheory` so the file lifts into Mathlib by copying it and fixing the header.  `ι` countable,
`X : ι → Type*` with measurable spaces, `μ : (i : ι) → Measure (X i)` **probability** measures
(`Measure.infinitePi` is junk `0` otherwise), `f : (i : ι) → X i → ℂ`.

```lean
integral_finset_prod_infinitePi :
    ∫ x, ∏ i ∈ s, f i (x i) ∂(Measure.infinitePi μ) = ∏ i ∈ s, ∫ x, f i x ∂(μ i)

ae_summable_norm_sub_one_infinitePi :
    (∑' i, ∫⁻ x, (‖f i x - 1‖₊ : ℝ≥0∞) ∂(μ i)) ≠ ∞ →
    ∀ᵐ x ∂(Measure.infinitePi μ), Summable fun i => ‖f i (x i) - 1‖

hasProd_integral_tprod_infinitePi :
    (∀ i, ∀ᵐ x ∂(μ i), ‖f i x‖ ≤ 1) → (∑' i, ∫⁻ x, (‖f i x - 1‖₊ : ℝ≥0∞) ∂(μ i)) ≠ ∞ →
    HasProd (fun i => ∫ x, f i x ∂(μ i)) (∫ x, ∏' i, f i (x i) ∂(Measure.infinitePi μ))

integral_tprod_infinitePi :   -- the equation form, from the HasProd form and `HasProd.tprod_eq`
    ∫ x, ∏' i, f i (x i) ∂(Measure.infinitePi μ) = ∏' i, ∫ x, f i x ∂(μ i)
```

`hb : ∀ i, ∀ᵐ x ∂(μ i), ‖f i x‖ ≤ 1` (plus `hf` measurability) is what makes the DCT dominator the
constant `1`; `hsum` is what makes the pointwise product converge (`multipliable_one_add_of_summable`
fed by Tonelli).  Both hypotheses hold for every band function the 182 assembly uses
(`f k c = exp (I * (c.mass * t))`, `‖·‖ ≡ 1` everywhere).

Build/receipt:

    LAKE_JOBS=1 LEAN_NUM_THREADS=1 lake build Pg182D2.InfinitePiProduct
    LAKE_JOBS=1 LEAN_NUM_THREADS=1 lake env lean receipt/axcheck_infinitepiproduct.lean

→ four lines, each `[propext, Classical.choice, Quot.sound]`.  No `sorryAx`, no `native_decide`,
no new axioms.  Imports narrowed to five Mathlib modules and the file is clean under
`set_option autoImplicit false`.

## 2. Why this was the gap (and why the finite case does not extend)

Mathlib v4.34.1 has the finite-index identity (`integral_fintype_prod_eq_prod`,
`iIndepFun.integral_fun_prod_comp` — both `[Fintype ι]`) and the infinite-index case for
nonnegative integrands through `lintegral_tsum` (this is how `Pg182D1/Support.lean`'s
`lintegral_fragment_sum` does the `EReal` version).  For `ℂ` neither route works: the products are
not nonnegative, so monotone convergence does not apply, and the honest proof needs a limit of
finite products with a dominator — which is what §1 supplies.

## 3. A correction to the campaign's step 1 (`N1ResidualBand`)

**`N1ResidualBand` as stated in `CharFunBridge.lean` is FALSE.**  It quantifies over *all*
`μ : FiniteMeasure ℝ`:

```lean
∀ (μ : FiniteMeasure ℝ) (t : ℝ),
    charFun ((finitePoissonLaw μ).map (fun X => (X.mass : ℝ))) t
      = Complex.exp (∫ u, (Complex.exp (↑(u * t) * Complex.I) - 1) ∂(μ : Measure ℝ))
```

Counterexample: `μ = δ_{-1}`.  `PrimeGap182D1.weightedEmpirical` builds atoms as
`(x i).toNNReal • δ (x i)`, and `(-1).toNNReal = 0`, so every sampled empirical measure is `0`: the
LHS is `charFun δ_0 t = 1` for all `t`, while the RHS is `exp (exp (-I t) - 1) ≠ 1`.  The identity
genuinely needs the band measures to live on `[0, ∞)`; the repair is one hypothesis,

```lean
(hμ : ∀ᵐ u ∂((μ : Measure ℝ)), 0 ≤ u)
```

which every `cappedDyadicIntensity ζ k` satisfies (it is supported on `Ioc (2^k) (2^{k+1}) ∩
(0, ζ)`).  **N3 did not land the corrected step 1**: it is a ~120-line computation
(`integral_finitePoissonLaw_normalized` + `exp_mass_weightedEmpirical` + `poisson_integral_pow`
+ `FiniteMeasure.coe_eq_mass_smul_normalize`), mechanical but not finished in this lane.

## 4. Where the map stands now

`(N1)` decomposes into three steps (`N1N2_REPORT.md` §2).  After this lane:

| step | content | status |
|---|---|---|
| **2** | **band product** — the Bochner `infinitePi` product integral + `HasSum.exp` | **UNBLOCKED: the Mathlib lemma is proved (this lane).** The `HasSum.exp` half (`HasProd (fun k => exp (E k)) (exp (∑' k, E k))`) is `Complex.hasProd_of_hasSum_log` / `Complex.cexp_tsum_eq_tprod`, one line each. The residual hypothesis `hsum` still has to be discharged for the band family (bound `‖exp (I·mass) - 1‖ ≤ min 2 (\|t\|·mass)` and `∫ mass ∂ν_k = 2^k`, summable over `k : ℤ`) — a bounded estimate, not a Mathlib gap. |
| **1** | single band | open, **and needs the nonnegativity hypothesis of §3** |
| **3** | the join `Σ_k ∫_{band k} = ∫_0^ζ` | open; `integral_iUnion_ae` + `dyadic_bands_disjoint` + `integrable_charExponent_integrand`, as N1N2 said |

So the campaign's final statement is now **"182 certified given N1's steps 1 and 3 + Katz + FKM +
Type III"**, with no Mathlib-level obstruction left anywhere on the data side.  The honest summary
of this lane is: *the gap that was named is closed; the assembly that consumes it is not.*

## 5. What is NOT claimed

* No PR was opened, no issue filed, nothing posted to any external service (coordinator's call; see
  `PR_BODY.md` §"What the coordinator must decide").
* The `‖f i x‖ ≤ C i` generalization flagged in `PR_BODY.md` is not done.
* `N1Residual` itself remains a named `Prop`; nothing in the library depends on it, and the count
  of named inputs of the 182 data side is unchanged (one: the band assembly).
