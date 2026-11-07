# FINAL_MAP.md — the 182 data side, closed

**The final map: `182 certified given Katz + FKM + Type III`.**

This supersedes `OBLIGATION_MAP.md` (which is kept as the working history: §1 the 262-obligation
count, §2 the per-class verdicts, §3 window placement, §4–§7 the D3/D4/N1N2/N3/N3b ledgers). Every
row of the 262-obligation table now has either a theorem or a named frozen-data handle, and the
**analytic-support half of the data side is empty**: no smoothing lemma, no integral estimate, no
modulus computation, no charFun identity is an assumption any more.

Lane: THE FINAL-3 + JOIN, work dir `~/bigo-campaign/pg182-d2/`, continuing D1 → D2 → D3 → D4 → N1N2
→ N3 → N3b. New in this lane: `Pg182D2/BandAssembly.lean` (17 declarations), `COMPOSITION.lean`
(the composition theorem), `receipt/axcheck_bandassembly.txt`,
`receipt/axcheck_composition.txt`.

## 0. The claim, in one line each

| statement | status |
|---|---|
| the data side (Layer M at `d = 38` + the envelope layer of the 137 inner rows) | **PROVED**, zero named inputs |
| `(N1)` the fragment-law charFun identity | **PROVED** — `charFun_mass_fragmentLaw`, i.e. `n1Residual_holds : N1Residual` |
| `(N2)` the certified truncation integral | **PROVED** (lane N1N2) — `∫_0^R e^{-38 Cin} ≤ 38/39 < 4/π` |
| the join `Σ'_k ∫_{band k} = ∫_0^ζ` | **PROVED** — `tsum_integral_band_exp` |
| `HasSum.exp` | **one application of Mathlib's `HasSum.cexp`** (`Complex.exp` is `NormedSpace.exp`) |
| the composition `h1_182_of` | **PROVED**, axiom-clean; `hobs` built from the data side |
| Katz, FKM, rank-four, Type III, the deduction, the frozen numeric table | **named inputs** (campaign-level / offline) |

## 1. The chain, end to end

```
charFun (fragment mass law) t = exp (-(charExponent t ζ))          charFun_mass_fragmentLaw
  ⇒ ‖charFun (fragment mass law) t‖ = exp (-(Cin (t ζ)))           norm_charFun_exp_exponent (D4)
  ⇒ ∀ R, ∫_0^R ‖charFun‖^38 ≤ 38/39 < 4/π     integral_norm_charFun_pow_le + integral_cinDecay_le_four_div_pi (N1N2)
  ⇒ HasLocalBound ((fragment mass law)^{*38}) (1/ζ)                hasLocalBound_of_charFun_bound (D3)
  ⇒ every cell of the 38-fold sum law has mass ≤ hq                cell_measure_le_hq (EnvLemmas)
  ⇒ the 137 inner rows' envelope layer                             cell_measure_le_hq_final (this lane)
  ⇒ hobs (with the frozen Layer I envelope and certificate margins) h1_182_of (this lane)
  ⇒ Bound 182                                                      Pg182Frame.h1_182_of
```

The only inequality with a numeric constant anywhere is `38/39 < 4/π`, proved by `nlinarith` from
`Real.pi_lt_four`.

## 2. Per-obligation verdicts of this lane

`OBLIGATION_MAP.md` §7.3 listed 3 obligations plus the join. All four are discharged.

| # | obligation | verdict | where |
|---|---|---|---|
| 1 | the characterization: the fragment charFun as an `infinitePi` product with `f k X = exp (I (X.mass t))`, `C ≡ 1` | **PROVED** | `charFun_mass_fragmentLaw`, `n1Residual_holds` |
| 1b | the `cappedDyadicIntensity ζ k ≠ 0` bridge under `2^k < ζ` (the N3b loose end; the a.e.-nonnegativity hypothesis needs nonzero bands) | **PROVED, both directions** | `cappedDyadicIntensity_ne_zero_of_lt` (positive), `cappedDyadicIntensity_eq_zero_of_le` (the empty band ⇒ `ν_k = 0`, handled separately in `band_factor_identity`) |
| 2 | `HasSum.exp` + the band product | **PROVED** | `band_factor_identity` (per band), `HasSum.cexp` (`hSC.hasSum.cexp.tprod_eq`), `MeasureTheory.integral_tprod_infinitePi` (the N3 lemma) |
| 2b | the `hsum` discharge: `Σ' k, ∫⁻ ‖e^{I(·)t} − 1‖ ≠ ⊤` | **PROVED** | `tsum_band_charFun_lintegral_ne_top`, from the from-scratch chord bound `norm_exp_imag_sub_one_le` + the first moment `lintegral_firstMoment_cappedDyadic` |
| 3 | **THE JOIN** `Σ'_k ∫_{band k} = ∫_0^ζ` | **PROVED** | `tsum_integral_band_exp` (via `integral_sum_measure`, not `integral_iUnion_ae`: `Measure.sum` *is* the joined measure, and `sum_cappedDyadicIntensity` identifies it) |

Two supporting lemmas were needed and are proved here: `cappedDyadicIntensity_eq_restrict_withDensity`
(the band's `1/u`-density measure *is* `volume.withDensity (1/u)` restricted to `Ioc 2^k (min 2^{k+1} ζ)`
— this is what keeps every band integral on plain `volume`, with no nested restrictions) and
`lintegral_mass_finitePoissonLaw` (`∫⁻ c, c.mass ∂Poisson(μ) = ∫⁻ u, u ∂μ`: the **intensity's**
first moment, which for a band equals the band mass because the density is `1/u`).

### The one from-scratch lemma

`norm_exp_imag_sub_one_le : ‖e^{i a} − 1‖ ≤ 2|a|`. Two cases: `|a| ≤ 1` is
`Complex.norm_exp_sub_one_le` at `x = I a`; `|a| ≥ 1` is `‖·‖ ≤ 2 ≤ 2|a|` from the triangle
inequality and `‖e^{I a}‖ = 1`. Nothing else in this lane is non-elementary.

### Why `2|a|` and not `|a|`

The sharp chord bound would need a small-angle argument. `2|a|` is what the `hsum` discharge
consumes: `∫⁻ ‖e^{I(·)t} − 1‖ ≤ 2|t| · (band first moment)`, and the first moments sum to `ζ`.

## 3. The empty-band subtlety (resolved, not assumed)

`ae_nonneg_normalize_of_ne_zero` needs `μ ≠ 0`, and Mathlib's `FiniteMeasure.normalize 0` is a
point mass at `Classical.choice ‹Nonempty ℝ›` — an unspecified real with no provable sign. So the
assembly **cannot** quantify over all `k : ℤ`. Both directions are now proved:

* `2^k < ζ` ⇒ the band meets `(0, ζ]` in positive length with density `≥ 1/min (2^{k+1}) ζ > 0` ⇒
  `ν_k ≠ 0` (`cappedDyadicIntensity_ne_zero_of_lt`), so the corrected `N1ResidualBand` applies;
* `ζ ≤ 2^k` ⇒ the band is empty ⇒ `ν_k = 0` (`cappedDyadicIntensity_eq_zero_of_le`), and then
  `∫⁻ c, c.mass ∂Poisson(0) = ∫⁻ u, u ∂0 = 0`, so every atom has mass `0` a.e., the factor is `1`,
  and the band exponent is `0` — both sides are `1` (`band_factor_identity`, second branch).

## 4. The 262 obligations, final status

| family | n | status |
|---|---:|---|
| Cap (denominator l/u, J0, Jplus, tail) | 5 | D1-independent frozen data; carried by `hcap` in `h1_182_of` |
| Outer root **and** face | 120 | D1-independent frozen data; carried by `hroot`/`hface` |
| Inner mass | 137 | **envelope layer PROVED** (`cell_measure_le_hq_final`); the row itself is `hrow` (frozen Layer I envelope × the proved cell bound) + `hmargin` (frozen certificate margin) |
| **total** | **262** | no analytic input anywhere |

Layers, as in `OBLIGATION_MAP.md` §2:

* **Layer M (cell masses).** `HasLocalBound μ D` with `D ≤ 1/ζ` — proved for the `d = 38` sum law
  of the fragment mass law, unconditionally (`cell_measure_le_hq_final`).
* **Layer I (integrand suprema).** The frozen affine-prefix / retained-maximum data (D3, audit item
  3). Unchanged by this lane; it is a *table*, and it enters `h1_182_of` as `envSup`/`cellOf` plus
  the two inequalities `hrow`, `hmargin`.

## 5. The composition theorem

`COMPOSITION.lean`:

```lean
abbrev fragmentMassLaw : Measure ℝ :=
  (PrimeGap182D1.fragmentLaw zeta).map (fun X : FiniteMeasure ℝ => (X.mass : ℝ))

theorem cell_measure_le_hq_final (n : ℕ) :
    convPow fragmentMassLaw 38 (Set.Ioc (n * mesh) (n * mesh + mesh)) ≤ ENNReal.ofReal hq

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

The 137 inner rows are the composition `hrow ∘ (proved cell bound) ∘ hmargin`; the proved bound is
*used*, not restated. `Pg182Frame.h1_182_of` (frame theorem, `Pg182Frame/Frame.lean:131`) does the
rest. `pg182-frame` is now a lake path-require of this project, on the same prebuilt Mathlib — the
require cost **zero** rebuild jobs.

**Axcheck** (`receipt/axcheck_composition.txt`):

```
'PrimeGap182D2.cell_measure_le_hq_final' depends on axioms: [propext, Classical.choice, Quot.sound]
'PrimeGap182D2.h1_182_of'                depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorryAx`: the frame's 262 `sorry` stubs are **not** in the proof term, because `hobs` is taken
directly as a hypothesis and assembled from `hcap`/`hroot`/`hface`/`hrow`/`hmargin`.

## 6. The final named-input list

| # | input | kind | why not Lean |
|---|---|---|---|
| 1 | **Katz** — `\|Kl₃(c)\| ≤ 3`, raw rank-four `≤ 4p√p` | deep analytic | Katz Thm 4.1.1, Deligne purity; out of scope of this lane |
| 2 | **FKM** — two-Kloosterman correlation `≤ 8p√p` | deep analytic | Fouvry–Kowalski–Michel Prop 2 |
| 3 | **Type III** — `TypeIII.LocalFourierHypothesis` | deep analytic | no closed proof exists anywhere |
| 4 | rank-four companion `IncidenceRankFourBounds182` | deep analytic | not derivable from 1–2 (`PREMISE_MAP.md` P2 item 3) |
| 5 | the deduction `Deduction182` | kernel-checked elsewhere | romyar1 `formal/PrimeGaps182Analytic.lean:67-74`, transported by the frame |
| 6 | the frozen numeric table: 5 cap + 120 outer rows, the Layer I envelope `envSup`/`cellOf`, the certificate margins `hmargin` | offline data | `formal/SourceData182.lean` + `num/window_scan.py`; arithmetic, not mathematics |

**Zero analytic inputs on the data side.** Items 1–4 are the campaign's deep inputs; 5 is a
transported kernel theorem; 6 is a table. Nothing else.

## 7. Receipts

| file | content |
|---|---|
| `receipt/axcheck_bandassembly.txt` | 17 declarations of `Pg182D2/BandAssembly.lean`, all `[propext, Classical.choice, Quot.sound]` |
| `receipt/axcheck_composition.txt` | `cell_measure_le_hq_final`, `h1_182_of` — same three axioms |
| `receipt/axcheck_headtail.txt`, `axcheck_charfunbridge.txt`, `axcheck_charfunmod.txt`, `axcheck_integralbound.txt`, `axcheck_haslocalbound.txt`, `axcheck_bandstep1.txt`, `axcheck_infinitepiproduct.txt`, `axcheck_lowrows.txt` | the earlier lanes |

Lane aggregate: **13 receipt files, 135 declarations, every one on
`[propext, Classical.choice, Quot.sound]`; zero `sorryAx`, zero `native_decide`.**

Build: `LAKE_JOBS=1 LEAN_NUM_THREADS=1 lake build Pg182D2` — green, and `Pg182D2/BandAssembly.lean`
and `COMPOSITION.lean` are warning-free.

## 8. Honest limits

* The 137 inner rows are *not* each individually proved: their Layer I half (`hrow`) is frozen table
  data whose content (the affine-prefix supremum and the row-to-cell identification) lives in the
  romyar1 kernel, not in this tree. What is proved is the analytic half — the cell bound — for every
  cell. This is exactly the split `OBLIGATION_MAP.md` §2 records as "envelope layer closed".
* `envSup j * hq ≤ C.innerFaceUpper j` (`hmargin`) is arithmetic over the frozen rationals; it is
  checkable by `num/` but not transcribed into Lean here.
* Nothing in this lane was made public: no PR, no issue, no post. `Pg182D2/InfinitePiProduct.lean`
  remains the Mathlib-PR candidate from N3/N3b (checklist in `PR_BODY.md`, "reviewed by a human Lean
  expert" still unchecked).
