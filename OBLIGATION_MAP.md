# OBLIGATION_MAP.md — final, standalone

Every obligation of the 182 program, its status, and the exact Lean declaration that carries it.
Status vocabulary:

* **PROVED** — a kernel-checked theorem in this tree; axiom receipt in `receipt/`.
* **NAMED** — an explicit typed hypothesis of the composition; carried, not proved here.
* **INSTANTIATE-PENDING** — the statement is a theorem of published mathematics whose Lean
  instantiation from AxiomMath/Weil + Stacks is priced and routed, conditioned on the pending
  axiom gate (§5).
* **INTERNAL** — Lean data, with a kernel proof of fidelity to its frozen upstream source.

Working history (the 262-obligation census, the D2/D3/D4/N1N2/N3/N3b ledgers, the per-class
verdicts): git history of this file, `FINAL_MAP.md`, and the lane reports (`N1N2_REPORT.md`,
`N3B_REPORT.md`, `TABLE_TRANSCRIPTION_REPORT.md`, `FINALSET_REPORT.md`).

**Headline: the data side is CLOSED — zero mechanical residue, zero named analytic inputs. The
composition `h1_182_of` is axiom-clean. Six named inputs remain, exact, three of them
instantiate-pending.**

## 1. The target

| obligation | status | carried by |
|---|---|---|
| the six inputs ⇒ `BigOSpeedrun.PrimeGaps.Bound 182` (infinitely often, consecutive primes differ by ≤ 182) | **PROVED** | `PrimeGap182D2.h1_182_of` (`COMPOSITION.lean`); frame transport `Pg182Frame.h1_182_of` (`pg182-frame/Pg182Frame/Frame.lean:131`) |

`Bound 182` is verbatim from bigospeedrun/verifier `challenges/prime-gaps/Statement.lean`
@ cb829226 (`Pg182Frame/Conclusion.lean`).

## 2. The data side — all PROVED, zero mechanical residue

The chain, each step a theorem (axioms: `[propext, Classical.choice, Quot.sound]` only):

| step | declaration |
|---|---|
| infinite-Poisson product-integral lemma (the Mathlib gap) | `Pg182D2.InfinitePiProduct.integral_tprod_infinitePi` (+ generalized `_of_norm_le` form); upstream leanprover-community/mathlib4 PR #45771, verified green |
| band charFun identity, per band | `Pg182D2.BandAssembly.band_factor_identity` |
| step 1 of the assembly (corrected statement) | `Pg182D2.BandStep1.n1ResidualBand_of_nonneg`, `n1ResidualBand_holds` |
| empty-band bridge, both directions | `Pg182D2.BandAssembly.cappedDyadicIntensity_ne_zero_of_lt`, `cappedDyadicIntensity_eq_zero_of_le` |
| **(N1)** the fragment-law charFun identity | `Pg182D2.BandAssembly.charFun_mass_fragmentLaw` (= `n1Residual_holds : N1Residual`) |
| the join `Σ'_k ∫_{band k} = ∫_0^ζ` | `Pg182D2.BandAssembly.tsum_integral_band_exp` |
| the hsum discharge for the product lemma | `Pg182D2.BandAssembly.tsum_band_charFun_lintegral_ne_top` (uses from-scratch `norm_exp_imag_sub_one_le : ‖e^{i a}−1‖ ≤ 2|a|`) |
| modulus identity `‖φ_ζ(t)‖ = exp(−Cin(tζ))` | `Pg182D2.CharFunMod.norm_charFun_exp_exponent` (with `re_charExponent`, `integral_norm_charFun_pow`) |
| truncation chain `∀ R, ∫₀ᴿ ‖φ‖^38 ≤ 38/39` | `Pg182D2.HeadTail.integral_cinDecay_le_four_div_pi` (the only numeric step: `38/39 < 4/π`, `nlinarith`) |
| structural `Cin` bounds (14 theorems) | `Pg182D2.CinBounds.*` |
| Fejér/Esseen smoothing lemma | `Pg182D2.HasLocalBound.hasLocalBound_of_charFun_bound` (+ `hasLocalBound_one_div_zeta`, `cell_measure_le_hq_of_charFun`) |
| the hsum-discharge chord bound | `Pg182D2.BandAssembly.norm_exp_imag_sub_one_le` |
| window placement (R1 applies to all 137 rows) | `Pg182D2.LowRows.inner_window_inside_period` |
| tilt cancellation for the 64 low rows | `Pg182D2.LowRows.tilted_cell_le`, `tilt_cancels`, `untilted_cell_le_hq` |
| **the cell bound, unconditional** | `PrimeGap182D2.cell_measure_le_hq_final` (`COMPOSITION.lean`) — every cell of the 38-fold sum law has mass ≤ `hq` |

Residual count: **0**. Nothing between the named inputs and `Bound 182` remains unwritten Lean;
no `sorry` reaches any proof term (the frame's 262 `sorry` stubs are consumed as hypotheses, never
in the proof term — verified by the axiom receipts).

## 3. The certificate side — INTERNAL

| object | status | carried by |
|---|---|---|
| 197 certificate rows + 5 caps + shared constants (546 `ℚ` literals) | **INTERNAL** | `Pg182D2.TableData.*` — emitted by `num/emit_table.py`; kernel fidelity: 12 `decide +kernel` equalities (`innerFaceUpper_eq` … `isLow_eq`, `cap_caps_eq`, `rhoStarQ_eq`, …), receipt `receipt/transcription_fidelity.txt` |
| Layer-I margin on the 73 `rankTwo`/`high` rows | **PROVED** (`norm_num`, one per row) | `TableData.witness_margin`; lifted to ℝ by `PrimeGap182D2.witness_margin_real` |
| `hmargin` on all 137 rows | **ABSORBED** | `PrimeGap182D2.certEnvelope_margin` (`certEnvelope = faceUpper / hq`, the weakest sufficient envelope), consumed by `h1_182_of_certEnvelope` |
| table coherence (normalization, totals) | **PROVED** | `TableData.innerData_normalization`, `TableData.innerData_total` |
| table aggregate checks | **PROVED** | three `decide +kernel` theorems (~65 s), axcheck `receipt/axcheck_tabledata.txt` |

Measured: emit 0.5 s; `TableData.lean` first build 102 s; `norm_num` ≈ 60–145 ms per row. The 64
`.low` rows have **no** recorded envelope (`num/margin_audit.py`: `witnessUpper` overshoots by
4.6e7×–1.8e26×) — their Layer-I content lives in `hrow` below, necessarily.

## 4. The named inputs — exact

Each is an explicit hypothesis of `h1_182_of`; full types in `COMPOSITION_STATEMENT.md`.

| # | input | exact Lean declaration | status |
|---|---|---|---|
| 1 | Katz Thm 4.1.1(1)–(2): `‖Kl₃(c)‖ ≤ 3` for `c ≠ 0` | `Pg182Frame.Kloosterman3Bound` (`Hypotheses.lean:63`) | **INSTANTIATE-PENDING** |
| 2 | FKM Prop 2: two-Kloosterman correlation ≤ `8p√p` | `Pg182Frame.Kloosterman2CorrelationBound` (`Hypotheses.lean:70`) | **INSTANTIATE-PENDING** (cohomological core; the sharp constant's p-adic refinement is separate custom work) |
| 3 | rank-four companion: raw rank-4 Kloosterman ≤ `4p√p`, all `c ≠ 0` | `Pg182Frame.IncidenceRankFourBounds182` (`Hypotheses.lean:95`) | **INSTANTIATE-PENDING** (same packaging as #1) |
| 4 | Type III local Fourier proposition | `Pg182Frame.TypeIIILocalFourier` (`Hypotheses.lean:177`) — verbatim mirror of romyar1 `formal/TypeIIILocal.lean` | **NAMED** — no closed proof exists anywhere |
| 5 | the deduction: local inputs + 262 bounds ⇒ consecutive pairs ≤ 182 | `Pg182Frame.Deduction182` (`Frame.lean:54`) — 1:1 mirror of romyar1 `formal/PrimeGaps182Analytic.lean:67-74`, kernel-checked there (918 modules / 6,128 declarations, standard axioms) @ b77bf175bded | **NAMED** (theorem elsewhere; transported, not re-proved) |
| 6 | the 262 **source** inequalities (source integral ≤ certified rational) | `hcap : Pg182Frame.CapBounds182 S` (5) · `hroot`/`hface` (60+60, against `TableData.outerRootUpper`/`outerFaceUpper`) · `hrow` (137, Layer-I row inequality vs `certEnvelope`) | **NAMED** — frozen physical data; certified offline by the romyar1 kernel (`formal/SourceBounds182.lean:138-142`) |

Nothing else is assumed. The abstract certificate carrier `C : TrialCerts182` is **gone** from the
composition: the certificate side is the definite transcribed table `certTable`
(`COMPOSITION.lean`).

## 5. What INSTANTIATE-PENDING means (the Weil gate)

Inputs 1–3 are theorems of published arithmetic geometry. A parallel lane audited the Lean
formalization of that machinery:

* **Exists and axiom-clean (measured):** the FK IV.4 estimate engine
  (`isAlgebraic_and_norm_eq_of_forall_isCharpolyPureOfWeight`), the lisseness of the Laumon
  Fourier family (`isLisse_laumonFourierFamilySheaf`), purity of the family
  (`laumonFamily_isPure_restrictScalarsRep`).
* **Last mile PROVED:** `KloostermanTraceBound.kloosterman_bound` — rank ≤ 3 + weight-2 purity ⇒
  `‖Kl₃‖ ≤ 3` (and the `3p` raw form) — plus `KloostermanObligations.lean` (`Kl3Package.norm_kl3_le`).
* **Remaining for #1:** three packaging obligations (construction against the existing API,
  priced weeks: build the 16.5k-module `LaumonFourierLineFamily` closure; trace = Kl₃ via
  sheaf–function correspondence; weight-2 purity instance). Inputs 2–3 ride the same packaging.
* **The gate, PENDING:** `#print axioms` on `LAdicSheaf.weightBound` and
  `Weil.satisfiesWeilEstimate` — their closure needs 19.4k unbuilt Stacks modules (≈ 6.8 days at
  2 oleans/min; **the gate build is running**). Source-level scan: 0 `sorry`, 0 `axiom`, 0
  `native_decide` across 63k Stacks + 980 Weil files.
* **Condition 2:** axiom-clean ≠ statement-faithful — a human must read the sheaf-theoretic
  definitions before the constants are bet on them.

If the gate passes: inputs 1–3 become **instantiate**, and the campaign statement tightens to
*"182 certified given Type III + Kl₃ packaging."* Input 4 is untouched by all of this.

Evidence: `~/bigo-campaign/weil-verify/AXIOM_GATE.md`, `~/bigo-campaign/kloosterman-sheaf/PRICE_LIST_UPDATE.md`.

## 6. Receipts

15 receipt files; 162 `#print axioms` declarations; every one `[propext, Classical.choice,
Quot.sound]`; zero `sorryAx`, zero `native_decide`.

| file | content |
|---|---|
| `receipt/axcheck_composition_rerun.txt` | **fresh re-run (this lane):** `cell_measure_le_hq_final`, `h1_182_of`, `h1_182_of_certEnvelope` — the three axioms, 32 s |
| `receipt/axcheck_composition.txt`, `axcheck_tabledata.txt` | the composition + the 546-literal table (incl. 12 fidelity equalities) |
| `receipt/transcription_fidelity.txt` | the 12 kernel equalities against the frozen upstream module, with both sha256 digests |
| `receipt/axcheck_bandassembly.txt` (17), `axcheck_bandstep1.txt` (4), `axcheck_infinitepiproduct.txt` (5), `axcheck_charfunbridge.txt` (7), `axcheck_headtail.txt` (15), `axcheck_charfunmod.txt` (9), `axcheck_integralbound.txt` (6), `axcheck_cinbounds.txt` (14), `axcheck_haslocalbound.txt` (23), `axcheck_lowrows.txt` (9), `axcheck.txt` (9, D2 aggregate) | the data-side lanes |

Build: `LAKE_JOBS=1 LEAN_NUM_THREADS=1 lake build Pg182D2` — green, warning-free.
