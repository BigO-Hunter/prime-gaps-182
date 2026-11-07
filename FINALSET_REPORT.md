# FINALSET_REPORT — the data side closed: zero mechanical residue

Lane: THE 182 FINAL-3 + JOIN (re-fired on deepseek after a zai connectivity outage killed the first
attempt at startup; nothing was lost — the earlier attempt had only reached a `wip/JOIN_WIP.lean`
draft, superseded here). Work dir `~/bigo-campaign/pg182-d2/`. Nothing public: no PR, no issue, no
post. `HOME` durable, `scratch/` gitignored.

`FINALSET_REPORT.md` (D4) is kept as `FINALSET_REPORT_D4.md`; `OBLIGATION_MAP.md` is kept as the
working history, with §8 pointing here. **The final map is `FINAL_MAP.md`.**

## 0. Verdicts

| deliverable | verdict |
|---|---|
| **(1) the characterization** — the fragment charFun as an `infinitePi` product with `f k X = exp (I (X.mass t))`, `C ≡ 1` | **PROVED** — `charFun_mass_fragmentLaw`, and `n1Residual_holds : N1Residual`. `N1Residual` is no longer a named input. |
| **(1b) the `cappedDyadicIntensity ζ k ≠ 0` bridge under `2^k < ζ`** (the N3b loose end, same band structure) | **PROVED, both directions** — `cappedDyadicIntensity_ne_zero_of_lt` and `cappedDyadicIntensity_eq_zero_of_le`. The empty bands are handled, not assumed away. |
| **(2) `HasSum.exp` + the band product** | **PROVED** — one application of Mathlib's `HasSum.cexp` (`Complex.exp` is `NormedSpace.exp`, so `HasSum.exp` is its `𝔸`-general form); the product integral is N3's `MeasureTheory.integral_tprod_infinitePi`. |
| **(2b) the `hsum` discharge** | **PROVED** — `tsum_band_charFun_lintegral_ne_top`, from the from-scratch chord bound and the intensity's first moment. |
| **(3) THE JOIN** | **PROVED** — `tsum_integral_band_exp`. |
| **composition** | **PROVED + axchecked** — `COMPOSITION.lean`, `h1_182_of`, on `[propext, Classical.choice, Quot.sound]`. |
| **final map** | **WRITTEN** — `FINAL_MAP.md`, claim: `182 certified given Katz + FKM + Type III`. |

## 1. What was written

| file | content |
|---|---|
| `Pg182D2/BandAssembly.lean` (new, 17 declarations) | the chord bound, the nonzero/empty-band bridges, the band-as-density identity, the intensity first moment, the `hsum` discharge, the join, the per-band factor identity, the characterization |
| `COMPOSITION.lean` (new, root module, in the lake globs) | `fragmentMassLaw`, `cell_measure_le_hq_final`, `h1_182_of` |
| `Pg182D2.lean` | imports `Pg182D2.BandAssembly` |
| `lakefile.toml` + `lake-manifest.json` | `pg182-frame` path-require (same prebuilt Mathlib; the require cost **0** rebuild jobs) |
| `receipt/axcheck_bandassembly.{lean,txt}` | 17 declarations, all clean |
| `receipt/axcheck_composition.{lean,txt}` | 2 declarations, all clean |
| `FINAL_MAP.md`, `FINALSET_REPORT.md` | the final map and this report |
| `OBLIGATION_MAP.md` §8 | pointer to the final map |

Commits (4): the chord bound + nonzero bridge; the first moment + `hsum`; the join + the
characterization; the composition.

## 2. The three obligations, exactly

### (1) The characterization

```
charFun ((fragmentLaw ζ).map mass) t = exp (-(charExponent t ζ))
```

Six rewrites, no analysis:

1. `charFun_mass_map` — unwind to `∫ X, exp (I (X.mass t)) ∂(fragmentLaw ζ)`;
2. `integral_map` through `finiteFragments` (`measurable_finiteFragments`);
3. a.e. (on `ae_isFiniteMeasure_fragment_sum`): the fragment measure *is*
   `Measure.sum (fun k => ω k)`, so its mass is `∑' k, (ω k).mass` — `Measure.sum_apply` +
   `ENNReal.tsum_toReal_eq`, then `Complex.ofReal_tsum`/`tsum_mul_right` and `HasSum.cexp` turn
   `exp (I (mass t))` into `∏' k, exp (I ((ω k).mass t))`;
4. `MeasureTheory.integral_tprod_infinitePi` (`f k := fun c => exp (I (c.mass t))`, `C ≡ 1` since
   `‖exp‖ = 1` exactly) — the N3 lemma, with `hsum` from (2b);
5. `band_factor_identity` per band — `n1ResidualBand_of_nonneg` where `2^k < ζ`, and the empty-band
   branch where `ζ ≤ 2^k`;
6. `HasSum.cexp.tprod_eq` (`∏' k exp (E k) = exp (∑' k, E k)`, `E k` summable by
   `summable_band_exponent`), then the join (3).

### (2) `HasSum.exp`

Audited: `Mathlib/Analysis/SpecialFunctions/Exponential.lean:411` has `HasSum.exp` for
`[NormedCommRing 𝔸] [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸]`; for `ℂ` the same statement is
`HasSum.cexp` (`Mathlib/Analysis/SpecialFunctions/Exp.lean:529`), which is what is used. No new
lemma needed — the obligation collapsed to one application once (2b) was discharged.

### (2b) The `hsum` discharge

```
Σ' k, ∫⁻ X, ‖e^{I (X.mass t)} − 1‖ ∂Poisson(ν_k) ≤ 2|t| · Σ' k, ∫⁻ u, u ∂ν_k = 2|t| ζ ≠ ⊤
```

* `norm_exp_imag_sub_one_le : ‖e^{ia} − 1‖ ≤ 2|a|` — **the only from-scratch lemma**: `|a| ≤ 1` is
  `Complex.norm_exp_sub_one_le` at `I a`; `|a| ≥ 1` is `‖·‖ ≤ 2 ≤ 2|a|`.
* `lintegral_mass_finitePoissonLaw : ∫⁻ c, c.mass ∂Poisson(μ) = ∫⁻ u, u ∂μ` —
  `lintegral_weighted_finitePoissonLaw` with `h ≡ 1`. This is the **intensity's** first moment
  (genuinely not `μ.mass`: `∫⁻ u, u² ∂μ` would be the second); for a band the two coincide because
  the density is `1/u`, which is `lintegral_firstMoment_cappedDyadic : Σ' k, ∫⁻ u, u ∂ν_k = ζ`.

### (3) The join

```
Σ' k, ∫ u, (e^{I u t} − 1) ∂ν_k = −charExponent t ζ
```

`integral_sum_measure` (needs `Integrable` of the integrand against `Measure.sum ν_k`, which follows
from the `∫⁻` bound `lintegral_band_integrand_sum_le = 2|t|ζ`), then
`sum_cappedDyadicIntensity : Measure.sum ν_k = (volume.restrict (0,ζ]).withDensity (1/u)`, then
`integral_withDensity_eq_integral_toReal_smul` (unconditional), and on `(0, ζ)` the density cancels:
`(1/u) • (e^{Iut} − 1) = −(1 − e^{Itu})/u`. Then `intervalIntegral.integral_of_le` folds
`∫_0^ζ` back into `charExponent`.

**Note on the route.** `OBLIGATION_MAP.md` §7.3 item 5 suggested `integral_iUnion_ae` +
`dyadic_bands_disjoint` + `integrable_charExponent_integrand`. The landed proof uses
`integral_sum_measure` instead: `Measure.sum` *is* the joined measure (that is exactly
`sum_cappedDyadicIntensity`), so the disjointness/`iUnion` bookkeeping is replaced by one application
of the sum-measure integral lemma. The `∫⁻` twin of this argument (`lintegral_fragment_sum`) is the
same shape, which is a good sign for both.

## 3. The empty-band subtlety, resolved

`N1ResidualBand` needs `∀ᵐ u ∂μ.normalize, 0 ≤ u`, and `ae_nonneg_normalize_of_ne_zero` needs
`μ ≠ 0` — because Mathlib's `FiniteMeasure.normalize 0 = δ (Classical.choice ‹Nonempty ℝ›)`, an
unspecified real with no provable sign. N3b left `cappedDyadicIntensity ζ k ≠ 0` under `2^k < ζ`
unwritten; the map called it "the one bridge not yet written". It is now two theorems:

* `cappedDyadicIntensity_ne_zero_of_lt` — the band ∩ `(0, ζ]` is `Ioc 2^k (min 2^{k+1} ζ)`, which has
  positive length, and on it `1/u ≥ 1/min(2^{k+1}, ζ) > 0`; the `∫⁻` of the density is therefore
  positive, so the mass is positive, so the measure is nonzero
  (`FiniteMeasure.mass_nonzero_iff`).
* `cappedDyadicIntensity_eq_zero_of_le` — for `ζ ≤ 2^k` the intersected interval is empty, so
  `ν_k = 0`. Then `∫⁻ c, c.mass ∂Poisson(0) = ∫⁻ u, u ∂0 = 0`, so `c.mass = 0` a.e.
  (`lintegral_eq_zero_iff`), the factor is `1`, and the exponent is `0`: both sides of the band
  identity are `1`.

So `band_factor_identity` covers **every** `k : ℤ` with no hypothesis, which is what let the tprod
quantify over all `k`.

## 4. The composition and its axcheck

```lean
theorem h1_182_of (h1 : Kloosterman3Bound) (h2 : Kloosterman2CorrelationBound)
    (hK4 : IncidenceRankFourBounds182) (h3 : TypeIIILocalFourier) (hd : Deduction182)
    (S : TrialSource182) (C : TrialCerts182)
    (hcap : CapBounds182 S)
    (hroot : ∀ j : Fin 60, S.outerRoot j ≤ C.rootUpper j)
    (hface : ∀ j : Fin 60, S.outerFace j ≤ C.faceUpper j)
    (cellOf : Fin 137 → ℕ) (envSup : Fin 137 → ℝ) (henv : ∀ j, 0 ≤ envSup j)
    (hrow : ∀ j, S.innerMass j ≤ envSup j * (convPow fragmentMassLaw 38 (cell (cellOf j))).toReal)
    (hmargin : ∀ j, envSup j * hq ≤ C.innerFaceUpper j) :
    BigOSpeedrun.PrimeGaps.Bound 182
```

The 137 inner rows are `hrow` ∘ (the **proved** cell bound) ∘ `hmargin`. `Pg182Frame.h1_182_of`
(`Pg182Frame/Frame.lean:131`) supplies the endpoint. The frame's 262 `sorry` stubs are untouched and
— this is the point — **not in the proof term**: `hobs` is assembled from the five hypotheses.

```
$ lake env lean receipt/axcheck_composition.lean
'PrimeGap182D2.cell_measure_le_hq_final' depends on axioms: [propext, Classical.choice, Quot.sound]
'PrimeGap182D2.h1_182_of' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`receipt/axcheck_bandassembly.txt`: 17 declarations, all `[propext, Classical.choice, Quot.sound]`,
zero `sorryAx`, zero `native_decide`. Lane aggregate (measured by counting the receipt lines):
**12 files, 120 declarations, all clean** — bandassembly 17, haslocalbound 23, headtail 15,
cinbounds 14, charfunmod 9, lowrows 9, charfunbridge 7, integralbound 6, infinitepiproduct 5,
bandstep1 4, composition 2, D2 aggregate 9.

Build: `LAKE_JOBS=1 LEAN_NUM_THREADS=1 lake build Pg182D2` — green (8945 jobs); both new files are
warning-free.

## 5. The final named-input list

1. **Katz** (`Kloosterman3Bound`).
2. **FKM** (`Kloosterman2CorrelationBound`).
3. **rank-four companion** (`IncidenceRankFourBounds182`) — not derivable from 1–2.
4. **Type III** (`TypeIIILocalFourier`).
5. **the deduction** (`Deduction182`) — kernel-checked in romyar1, transported by the frame.
6. **the frozen numeric table** — 5 cap + 120 outer rows, the Layer I envelope `envSup`/`cellOf`, the
   certificate margins `hmargin`.

Data side: **zero named analytic inputs.** That is the lane's claim, and it is the claim `FINAL_MAP.md`
makes.

## 6. Honest limits

* The 137 inner rows are not each individually proved. The **analytic half** (the cell mass bound) is
  proved for every cell; the **Layer I half** (the affine-prefix supremum and the row-to-cell map) is
  frozen table data from the romyar1 kernel and is not Lean-reachable from this tree. This is the
  same split `OBLIGATION_MAP.md` §2 recorded as "envelope layer closed".
* `hmargin` (`envSup j * hq ≤ C.innerFaceUpper j`) is arithmetic over frozen rationals, checkable by
  `num/`, not transcribed here.
* The composition consumes the frame theorem; a reader who does not accept the frame's `Deduction182`
  transport is not helped by this lane. That transport is `Pg182Frame/Frame.lean:54-61`, cited to
  `formal/PrimeGaps182Analytic.lean:67-74`.
* `Pg182D2/InfinitePiProduct.lean` went upstream as **mathlib4 PR #45771** from this lane's
  *earlier* attempt (before the outage). It is verified green upstream (`receipt/pr_infinitepi_*`:
  build with the Mathlib linter set, `lint-style` rc=0, `#print axioms` clean, `mk_all` byte-exact).
  **This session published nothing new and did not modify the PR.** The "reviewed by a human Lean
  expert" box is still unchecked, and that review is the maintainers' call.
* `wip/JOIN_WIP.lean` (the killed attempt's draft) is left in place, untracked and superseded: it does
  not compile and its content is subsumed by `Pg182D2/BandAssembly.lean`.

## 7. Where the next mind starts

Nothing mechanical is left on the data side. The open work is, in order of cost:

1. Transcribe the frozen table (items 6) into Lean and discharge `hmargin` by `norm_num` — a
   mechanical transcription job over `formal/SourceData182.lean`, would make `h1_182_of`'s inner rows
   fully Lean.
2. Transcribe the Layer I envelope (`envSup`, `cellOf`) — same job, but it needs the romyar1 kernel's
   affine-prefix definitions, which are not vendored here.
3. Items 1–4 of §5 are out of scope by construction: they are the campaign's deep inputs.
