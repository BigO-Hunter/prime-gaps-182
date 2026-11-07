# TABLE_TRANSCRIPTION_REPORT.md — the frozen 182 certificate table, in Lean

Lane: THE 182 TABLE TRANSCRIPTION, work dir `~/bigo-campaign/pg182-d2/`, continuing the FINAL-3 +
JOIN lane (`FINAL_MAP.md`). The job was to turn the last non-analytic residue — the frozen
numeric/certificate table stated as hypotheses — into kernel-checked Lean.

**Outcome in one line: the certificate table is now Lean data with a kernel proof of fidelity to the
upstream module; the Layer-I margin is a proved `norm_num` fact on 73 of the 137 inner rows; and on
the other 64 the margin is *measurably not* a table fact — the envelope there is not recorded
anywhere in the frozen data, so `hrow` cannot be reduced to arithmetic in this tree. That limit is
now measured, proved where provable, and marked in Lean (`TableData.isLow`).**

## 1. What was transcribed

| object | n | source |
|---|---:|---|
| inner certificate rows — `faceUpper`, `coefficientUpper`, `normalizedB`, `witnessUpper`, `kind`, `family` | 137 | `formal/SourceData182.lean` (`trialInnerCertificates`) |
| outer certificate rows — `rootUpper`, `faceUpper` | 60 | same (`trialOuterCertificates`) |
| cap rationals — `denominatorUpper`, `j0Lower`, `jPlusLower`, `tailUpper` | 4 | `formal/TrialData182.lean` |
| shared constants — `rhoStar`, `denominatorLower`, `innerTotalUpper` | 3 | both files |
| **total rational literals in `Pg182D2/TableData.lean`** | **546** | |

Literal sizes: numerators mean 50 digits, **max 209**; denominators **max 224**. The emitted file is
87.6 KB / 1303 lines; its `.olean` is 13.4 MB (all data, no proofs of substance).

Provenance is byte-exact: `sha256(SourceData182.lean) = 17cfa9f2…4d055c`,
`sha256(TrialData182.lean) = 3407df88…b5482b`, from romyar1/prime-gaps-lean release
`external-numerics-20260909`.

Generator: **`num/emit_table.py`** (reads the frozen modules, refuses to emit unless the row counts
are 60/137/5 and the margin partition is exactly the `rankTwo`/`high` rows). Proof of fidelity:
**`receipt/transcription_fidelity.txt`** + `receipt/transcription_crosscheck.lean` — 12
`decide +kernel` theorems equating every transcribed column with the frozen module's projection
(`innerFaceUpper_eq`, `innerCoefficientUpper_eq`, `innerNormalizedB_eq`, `innerWitnessUpper_eq`,
`isLow_eq`, `innerFamily_eq`, `outerRootUpper_eq`, `outerFaceUpper_eq`, `rhoStarQ_eq`,
`denominatorLowerQ_eq`, `cap_caps_eq`, `innerTotalUpperQ_eq`), each on
`[propext, Classical.choice, Quot.sound]`. The transcription is not eyeballed — a mis-parsed
rational, a shifted row or a transposed column breaks these.

## 2. What is now *proved* (and was hypothesis before)

| theorem | statement | rows |
|---|---|---:|
| `TableData.innerFaceUpper_pos` | every inner certificate is positive | 137 |
| `TableData.outerRootUpper_pos`, `outerFaceUpper_pos` | every outer certificate is positive | 60 + 60 |
| `TableData.innerData_normalization` | `rhoStar * coefficientUpper j * faceUpper j = denominatorLower * normalizedB j` | 137 |
| `TableData.innerData_total` | `Σ_j normalizedB j = innerTotalUpper` | 137 |
| `TableData.witness_margin_<j>` | `witnessUpper j * hq ≤ faceUpper j` | **73** |
| `TableData.witness_margin` | the same, as one predicate over `isLow j = false` | 73 |
| `witness_margin_real` (COMPOSITION) | the ℚ margin lifted to the ℝ form the composition consumes | 73 |

The two aggregate identities are the table's own internal coherence — the same facts the upstream
kernel checks in `SourceDataChecks182.lean`, here re-derived from the transcription (so they double
as fidelity evidence).

## 3. Measured cost

| measurement | value |
|---|---|
| `num/emit_table.py` (parse 480 KB of frozen Lean, emit 87.6 KB) | 0.5 s |
| first build of `Pg182D2.TableData` | 102 s |
| one `norm_num` margin proof (73 of them, over the import baseline) | ≈ 60–145 ms/row |
| the three aggregate `decide +kernel` checks (197 positivity + 137 normalization + total) | ≈ 65 s (≈0.5 s/row) |
| `receipt/axcheck_tabledata.lean` (15 `#print axioms`) | 6 m 19 s — dominated by loading the 13.4 MB olean |
| `receipt/transcription_crosscheck.lean` (12 kernel equalities vs the frozen module) | 18 s |

**No row needed chunking.** The big-literal worry (the MomOracle pattern) did not materialise: 100-
to 224-digit rational comparisons are single-tactic for `norm_num`, and `decide +kernel` handles the
137-way aggregates with `maxRecDepth` at 4096/8192. Cost is per-row sub-second throughout; the only
expensive object in the lane is the olean.

## 4. The measured limit — why 64 rows do not close

`FINAL_MAP.md` §8 said the Layer-I envelope is "frozen table data whose content lives in the romyar1
kernel, not in this tree". This lane **measured** that instead of asserting it:

`num/margin_audit.py`, over all 137 rows, with `hq = ζ/393216` and `envSup := witnessUpper` (the
retained-maximum affine-prefix witness — the only envelope-shaped number the table records):

```
witnessUpper * hq <= faceUpper holds on 73/137 rows
  rankTwo/high rows: 73, of which hold: 73
  low rows:          64, of which hold: 0
  low-row shortfall (certificate/required):
      worst 10^-26.3 (row 46), best 10^-7.7 (row 63)
```

So the partition is *exact*: `witnessUpper` is the integrand envelope precisely on the
`rankTwo`/`high` rows, and on the 64 `.low` rows it overshoots the certificate by 4.6e7× to 1.8e26×.
That is not a rounding gap, a convention mismatch, or a chunking problem — no repackaging of the
stored numbers closes it. It is the tilt: the `.low` kernel is an untilted fragment mass times
`exp (slope · affine)`, the generator expends that factor on **both** sides of its comparison
(`OBLIGATION_MAP.md` §2: "both sides carry the same factor, it cancels"), and the envelope it
cancels against is the per-bin `relative_inner_upper` of
`inputs/source_certificates/experiments/variational_routes/fine_coarse_inner_low_v3_g3g5g6_n393216_b48.json`
— which is recorded per *(group, bin)* in a 36-result payload, not per certificate row, so the
row-to-bin map is the missing piece (and that file carries 36 bins against the 64 low certificates —
the map is not the identity).

`TableData.isLow : Fin 137 → Bool` marks those rows, kernel-proved to be the frozen `kind = .low`
(`isLow_eq`), so the boundary is a Lean object rather than a footnote.

## 5. Wiring — `COMPOSITION.lean`

* **`C : TrialCerts182` is gone from the statement.** `certTable : TrialCerts182` reads the
  certificate side off `TableData`, so the frame's 197 abstract reals are definite data
  (`certTable_rootUpper`, `certTable_faceUpper`, `certTable_innerFaceUpper` are `rfl`).
* **`h1_182_of`** now takes the outer/inner row inequalities against the transcribed rationals
  (`TableData.outerRootUpper`, `outerFaceUpper`, `innerFaceUpper`) instead of against an abstract
  certificate record. Everything else — the proved cell bound `cell_measure_le_hq_final`, the
  composition's `calc` chain — is unchanged and still *used*, not restated.
* **`hrow` keeps its Layer-I form** (`S.innerMass j ≤ envSup j * cell mass`) and `hmargin` stays a
  hypothesis **over concrete rationals** — i.e. it is now a refutable numeric assertion, not an
  opaque one.
* **`h1_182_of_certEnvelope`** discharges `hmargin` outright by choosing the certificate-implied
  envelope `certEnvelope j = innerFaceUpper j / hq` — the *weakest sufficient* envelope, with
  `certEnvelope_nonneg` and `certEnvelope_margin` proved (`div_mul_cancel₀` + `hq > 0`). What is
  left is the row inequality alone, in its weakest form. This is an absorption, and it is labelled
  as one: the arithmetic content of `hmargin` was never independent of the table, it was the
  table's own arithmetic (`FINAL_MAP.md` §8 bullet 2, `FINALSET_REPORT.md` §6).
* **`witness_margin_real`** exposes the 73 proved margins for a reader who wants the sharp form.

Axcheck (`receipt/axcheck_tabledata.txt`): 15 declarations, **all on
`[propext, Classical.choice, Quot.sound]`; no `sorryAx`, no `native_decide`** — including
`h1_182_of` and `h1_182_of_certEnvelope`.

## 6. The final named-input list

| # | input | kind | status after this lane |
|---|---|---|---|
| 1 | **Katz** — `\|Kl₃(c)\| ≤ 3` | deep analytic | campaign input (peer lane: collapses to instantiation, see `OBLIGATION_MAP.md` §8) |
| 2 | **FKM** — two-Kloosterman correlation | deep analytic | campaign input (same) |
| 3 | **Type III** — `TypeIIILocalFourier` | deep analytic | campaign input |
| 4 | rank-four companion `IncidenceRankFourBounds182` | deep analytic | campaign input |
| 5 | the deduction `Deduction182` | kernel-checked elsewhere | transported |
| 6 | the 5 cap rows + 120 outer rows | frozen source inequalities | **certificate side internal** (`certTable`); the inequality `source ≤ certificate` remains |
| 7 | the 137 inner rows | frozen source inequalities | **certificate side internal**; `hmargin` absorbed (`h1_182_of_certEnvelope`); **the Layer-I row inequality remains** |
| — | the numeric table itself | offline data | **GONE as a hypothesis** — it is `Pg182D2/TableData.lean`, kernel-proved faithful |

So the honest final statement is now:

> **182 certified given Katz + FKM + rank-four + Type III + the kernel-checked deduction, plus the
> 262 rows of *source* inequalities (each: a source integral ≤ a kernel-checked certificate
> rational) — of which the 73 `rankTwo`/`high` inner rows' envelope step is itself a proved
> `norm_num` fact.**

The certificate table is no longer an assumption anywhere; the residual is the *physical* direction
(source integral below its certified bound), which is what the romyar1 kernel certifies and what no
amount of table transcription can produce.

## 7. Where the next mind starts

1. **The 64 `.low` rows' envelope row-to-bin map.** `fine_coarse_inner_low_v3_g3g5g6_n393216_b48.json`
   holds `relative_inner_upper` per (group, bin) with `inner_face_upper = physical_prefactor *
   relative_inner_upper`; the 64 low certificates are indexed by (family, binIndex) while that file
   lists 36 bins. Establish the map, then the low envelope is `physical_prefactor * relative_inner
   * (per-cell-mass factor)` and its margin becomes 64 more `norm_num` rows.
2. **The tilt cancellation in Lean.** `Pg182D2/LowRows.lean` already has `tilted_cell_le`,
   `tilt_cancels`, `untilted_cell_le_hq`; what is missing is the bridge from the certificate's
   normalised `relative_inner_upper` to those lemmas.
3. Nothing else on the table: 197 rows transcribed, fidelity proved, arithmetic proved.

## 8. Files

| file | content |
|---|---|
| `num/emit_table.py` | the transcription generator (frozen Lean → `TableData.lean`) |
| `num/margin_audit.py` | the 73/64 partition measurement (§4) |
| `Pg182D2/TableData.lean` | 546 rational literals + sign data + the two coherence identities + 73 margin theorems |
| `COMPOSITION.lean` | `certTable`, `witness_margin_real`, `certEnvelope*`, `h1_182_of`, `h1_182_of_certEnvelope` |
| `receipt/axcheck_tabledata.{lean,txt}` | 15 declarations, axiom-clean |
| `receipt/transcription_crosscheck.lean`, `receipt/transcription_fidelity.txt` | the 12 kernel equalities against the frozen module + digests + reproduction recipe |
