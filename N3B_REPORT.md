# N3B_REPORT — the three rulings executed: fix, generalize, PR-ready

Lane N3b, work dir `~/bigo-campaign/pg182-d2/`, continuing lane N3. Three commits on top of N3's
`685fca9`:

    Step 1 of (N1) LANDED: the single-band identity, with the nonnegativity hypothesis it needs
    Generalize the infinitePi product integral to a norm bound family ‖f i x‖ ≤ C i
    Mathlib-PR form: licence header, module form, generalized statement in the PR body

Nothing external was touched: no PR opened, no issue filed, nothing posted.

## 0. Verdicts

| deliverable | verdict |
|---|---|
| **(a) `N1ResidualBand` fixed** | **DONE — and it is now PROVED, not an input.** The def carries `∀ᵐ u ∂μ.normalize, 0 ≤ u`; `n1ResidualBand_holds` is a proof term. The only consumer of the name is the campaign prose, re-wired below. |
| **(b) step 1 landed** | **YES** — `Pg182D2/BandStep1.lean`, `n1ResidualBand_of_nonneg`, no `sorry`, `[propext, Classical.choice, Quot.sound]`. `wip/BAND_STEP1_WIP.lean` is deleted (superseded). |
| **(2) generalization `‖f i x‖ ≤ C i`** | **PROVED**, as the head theorem `hasProd_integral_tprod_infinitePi_of_norm_le`; the `≤ 1` version kept as the `C ≡ 1` corollary with its statement unchanged. |
| **(3) PR form** | **DONE** — licence header filled (`Copyright (c) 2026 darkhipo`, Apache 2.0, `Authors: darkhipo`), modern Mathlib module form, docstrings, `autoImplicit false`, `PR_BODY.md` regenerated. Checklist: every box checked **except** "reviewed by a human Lean expert" (honest — no human with Lean expertise has read the proofs). |
| **(4) axcheck** | **DONE** — 11 receipt files, 116 declarations, all on `[propext, Classical.choice, Quot.sound]`; zero `sorryAx`. |
| **(4) map update** | **DONE** — `OBLIGATION_MAP.md` §7 with the exact 4-step mechanical remainder; §4's (N1) row, §5's axcheck list and §6's stale claim corrected. |

## 1. The `N1ResidualBand` fix

`Pg182D2/CharFunBridge.lean` §5 now reads

```lean
def N1ResidualBand : Prop :=
  ∀ (μ : FiniteMeasure ℝ) (t : ℝ), (∀ᵐ u ∂((μ.normalize : Measure ℝ)), 0 ≤ u) →
    charFun ((PrimeGap182D1.finitePoissonLaw μ).map (fun X => (X.mass : ℝ))) t
      = Complex.exp (∫ u, (Complex.exp (↑(u * t) * Complex.I) - 1) ∂(μ : Measure ℝ))
```

and `Pg182D2/BandStep1.lean` proves it (`n1ResidualBand_holds`). Why the hypothesis is not
cosmetic: `weightedEmpirical` builds atoms as `(x i).toNNReal • δ (x i)`, so a negative sample
contributes **mass 0** while keeping its position — for `μ = δ_{-1}` every sampled mass is 0, the
LHS is `charFun δ_0 t = 1`, the RHS is `exp (exp (-I t) - 1) ≠ 1`.

**A further correction than the ruling asked for.** "Every `cappedDyadicIntensity ζ k` satisfies it"
is *not* quite true, and the honest statement is narrower:

* `ae_nonneg_cappedDyadicIntensity : ∀ᵐ u ∂(cappedDyadicIntensity ζ k : Measure ℝ), 0 ≤ u`
  (the band is a restriction to `Ioc (2^k) (2^{k+1})`, and `2^k > 0`);
* `ae_nonneg_normalize_of_ne_zero` transfers it to `μ.normalize` **only for `μ ≠ 0`**, because
  Mathlib defines `FiniteMeasure.normalize 0 = ⟨Measure.dirac ‹Nonempty Ω›.some, _⟩` — for `Ω = ℝ`
  that is a point mass at `Classical.choice ‹Nonempty ℝ›`, a real whose sign is not provable.

So: **nonzero** bands satisfy the hypothesis; an **empty** band is the zero measure, whose identity
is trivial on both sides (`finitePoissonLaw 0 = δ_0`, charFun `= 1 = exp 0`). The assembly therefore
quantifies over the nonzero bands only. The one bridge left unwritten is
`cappedDyadicIntensity ζ k ≠ 0` under `2^k < ζ` (a positive-measure-plus-positive-density argument);
it is named in the map, not claimed.

## 2. Step 1 landed — and the coercion that blocked N3

The whole chain in `wip/BAND_STEP1_WIP.lean` compiled to its last line; the last line was the
bookkeeping identity `μ = μ.mass • μ.normalize`. The resolution is three rewrites:

```lean
have hmu : ((μ : Measure ℝ)) = (μ.mass : ℝ≥0∞) • ((μ.normalize : Measure ℝ)) := by
  ext s
  rw [Measure.smul_apply, smul_eq_mul,
    ← FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure,
    ← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure,
    FiniteMeasure.self_eq_mass_mul_normalize μ s, ENNReal.coe_mul]
```

The trap, for the next mind: `FiniteMeasure.self_eq_mass_mul_normalize` is an **`ℝ≥0`** statement
(`μ s = μ.mass * μ.normalize s` in `ℝ≥0`), while the goal is an **`ℝ≥0∞`** one.
`FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure` is stated `↑(μ s) = ↑μ s`, i.e. *left to right it
rewrites the `ℝ≥0`-coerced form*, and that form does not occur in the goal: on the `Measure` side
`↑μ s` is **already** `Measure.coeFn`, so the lemma must be used in the `←` direction. After the two
`←` rewrites both sides are `ℝ≥0`-coercions, the NNReal lemma applies, and `ENNReal.coe_mul` is the
last step. (`ENNReal.toNNReal`/`NNReal.toENNReal` round-trips are not needed at all — the direction
of `ennreal_coeFn_eq_coeFn_toMeasure` is the whole problem.)

## 3. The generalization

```lean
theorem MeasureTheory.hasProd_integral_tprod_infinitePi_of_norm_le
    (hf : ∀ i, AEStronglyMeasurable (f i) (μ i)) (hC0 : ∀ i, 0 ≤ C i)
    (hb : ∀ i, ∀ᵐ x ∂(μ i), ‖f i x‖ ≤ C i)
    (hC : Summable fun i => ‖C i - 1‖)
    (hsum : (∑' i, ∫⁻ x, (‖f i x - 1‖₊ : ℝ≥0∞) ∂(μ i)) ≠ ⊤) :
    HasProd (fun i => ∫ x, f i x ∂(μ i)) (∫ x, ∏' i, f i (x i) ∂(Measure.infinitePi μ))
```

* Domination: `‖∏ i ∈ s, f i (x i)‖ = ∏ i ∈ s, ‖f i (x i)‖ ≤ ∏ i ∈ s, C i ≤ ∏ i ∈ s, exp (C i - 1)
  = exp (∑ i ∈ s, (C i - 1)) ≤ exp (∑' i, ‖C i - 1‖)` — independent of `s`, so the existing DCT along
  `atTop : Filter (Finset ι)` applies unchanged.
* **Why `∑ ‖C i - 1‖`, not `∑ C i`**: a product of bounds is not additive in them (a factor below 1
  scales the bound down, above 1 up), so summability of `C` alone bounds nothing. The log-scale
  hypothesis *is* `Multipliable C`, stated explicitly; the flat case is `C ≡ 1` (dominator `1`).
* Structure kept reviewable: the DCT core is `private` and takes the constant `K`; the general
  theorem instantiates `K = exp (∑' ‖C i - 1‖)`; `hasProd_integral_tprod_infinitePi` keeps its
  **old statement** as the `C ≡ 1` corollary, so nothing the map consumes changed; the equation form
  is untouched.
* Coercion note for the next reader: in this Mathlib `Finset.prod_le_prod` requires `MulLeftMono`,
  which `ℝ` has not; the `ℝ` version is `Finset.prod_le_prod₀` (with a nonnegativity hypothesis).

**What was NOT done:** the `𝕜`-generalization (`RCLike 𝕜` instead of `ℂ`) — stated as open in
`PR_BODY.md`, not attempted.

## 4. PR-ready state

`Pg182D2/InfinitePiProduct.lean` is the file to copy to
`Mathlib/MeasureTheory/Integral/InfinitePiProduct.lean`: it carries
`Copyright (c) 2026 darkhipo. All rights reserved.` / Apache 2.0 / `Authors: darkhipo`, the
`module` / `public import` ×5 / `public section` form this Mathlib tree expects, module docstring,
docstrings on every declaration, `set_option autoImplicit false`, and no linter warning (rebuild is
clean for that file).

Checklist as of this lane: axiom-free ✓, narrow imports ✓, `autoImplicit false` ✓, no linter
warnings in the file ✓, docstrings ✓, naming ✓, module form ✓, licence ✓,
**"reviewed by a human Lean expert" — UNCHECKED** (honest: the human has read the statement and the
campaign's use of it, not the proof scripts), "argued as Mathlib-worthy by a maintainer" — the
reviewers' call.

## 5. The exact remaining steps of the 182 data side

With step 1 landed, `(N1)` is one mechanical assembly: three obligations plus the join, **every
ingredient either in Mathlib or already in `Pg182D1/Support.lean` / `Pg182D2/CharFunBridge.lean`.**
The only lemma that has to be written from scratch is the two-case norm bound of item 3.

1. **Product form of the fragment charFun.** `fragmentLaw ζ = Measure.infinitePi (fun k : ℤ =>
   finitePoissonLaw (cappedDyadicIntensity ζ k))` (`Pg182D1/Law.lean:85`, definitional), then
   `hasProd_integral_tprod_infinitePi` with `f k := fun X => exp (I (X.mass * t))` and `C ≡ 1`
   (`‖f k X‖ = 1` exactly).
2. **`HasSum.exp`** on the band exponents `E k = ∫ u, (e^{I t u} - 1) ∂(band k)`:
   `HasSum E a ⟹ HasProd (fun k => exp (E k)) (exp a)`.
3. **The bounded estimate**: discharge
   `∑' k, ∫⁻ X, ‖exp (I (X.mass * t)) - 1‖ ∂(finitePoissonLaw ν_k) ≠ ⊤`. The one new lemma is a
   norm bound: Mathlib's `Complex.norm_exp_sub_one_le` needs `‖x‖ ≤ 1`, so the sharp
   `‖e^{i a} - 1‖ ≤ |a|` is replaced by the uniform `≤ 2|a|` (two cases), enough for summability.
   The rest exists: `PrimeGap182D1.lintegral_weighted_finitePoissonLaw` (`Support.lean:96`) with
   `h ≡ 1` gives the Poisson **first moment**
   `∫⁻ X, ofReal X.mass ∂(finitePoissonLaw μ) = ∫⁻ u, ofReal u ∂μ` — which is the *intensity's first
   moment*, **not** `μ.mass` (a trap worth naming: they coincide for the dyadic bands only because
   the density is `1/u`), and `PrimeGap182D1.lintegral_fragment_sum` (`Support.lean:159`) with
   `h ≡ 1` gives `∑' k, ofReal (ν_k.mass) = ofReal ζ < ∞`.
4. ~~The mass integral~~ — not a separate obligation: the first-moment computation above is the `∫⁻`
   form the discharge consumes (and the Bochner form follows from it with `h ≡ 1`).
Plus **step 3 of the assembly** (the join, previously named): `∑'_k ∫_{band k} = ∫_0^ζ` for
`(e^{I t u} - 1)`, via `integral_iUnion_ae` + `dyadic_bands_disjoint` +
`sum_cappedDyadicIntensity` + `integrable_charExponent_integrand`.

Then the `(N1)` row becomes a theorem and the data side's named-input count is **zero**. Katz, FKM
and Type III are campaign-level deep inputs, untouched and untouchable by this lane.

The one loose end not in that list: `cappedDyadicIntensity ζ k ≠ 0` under `2^k < ζ` (§1), which
turns "the nonzero bands satisfy the hypothesis" from a documented case split into a computed one.

## 6. Build / reproduction

    LAKE_JOBS=1 LEAN_NUM_THREADS=1 lake build Pg182D2                       # 8938 jobs, green
    lake env lean receipt/axcheck_bandstep1.lean                            # 4 decls, stdlib axioms
    lake env lean receipt/axcheck_infinitepiproduct.lean                    # 5 decls, stdlib axioms
    for f in receipt/axcheck*.lean; do lake env lean "$f"; done             # 116 decls, all stdlib

No `sorry`, no `native_decide`, no new axioms anywhere in the lane.
