# D1C_REPORT.md — Lane D1c: the frozen masses + the per-cell emission

Repo dir `d1/` (continues D1b at `68dcca6`).

## 1. Archive fetched, sha-pinned, extracted (binary-safe)

Asset identified: romyar1/prime-gaps-lean release `external-numerics-20260909`
→ `prime-gaps-external-182-verified-20260909.zip`, **244 843 318 bytes**,
sha256 `2960729efa8996538731820ce6cadc202831c8e98b2c0bdb14cfd19f33726f3b`
— matches the upstream `.sha256` pin byte-for-byte; the release-page asset
size matches too. Fetched via the pinned asset id 554239243 (gh api,
octet-stream); never read as text; extraction by `unzip -q`; per-file
manifest generated (`frozen/EXTRACTED_MANIFEST.sha256`, 914 files).
Internal integrity: the package's own `package-manifest.json` verifies
**913/913** files (status `PASS_COMPLETE_EXTERNAL_NUMERICAL_RECOMPUTATION`).
The blob is NOT committed (frozen/ gitignored); `fetch_frozen.sh` +
`frozen/HASHES.md` are.

## 2. The frozen payload located in full

- **Per-cell mass**: `fine_h` = ζ/393216 = 1379373467/516093837312000 — the
  frozen program's per-fine-cell mass is UNIFORM (certify_incidence_cap:
  `hq = S/intervals`); verified equal to the vendored ζ.
- **All 137 inner rows located**: 73 rank/high components in
  `evidence/rebuilt/.../fine_coarse_inner_sources_n393216.json` (G3 15, G4 13,
  G5 15, G6 14, C1 16 — each with `padded_source_window` + exact-ℚ
  `source_mass`) + 64 low rows (G3/G5/G6 36, G4 21, C 7, each with
  per-run `radial_windows`).
- **Row 77 byte-consistency**: G3 rank_two component 13 of the ARCHIVE
  (rebuilt tree, hash-pinned) = fine cells 334254..343201 (8948), coarse run
  6927..7150, `source_mass` = 2534388…4569/3213876…2752 (point interval) —
  identical in the snapshot tree and to C0's `row77_receipt_component.json`.

## 3. Per-cell emission: certified machinery + verdicts

`receipt/percell_emit.py` (exact `Fraction` arithmetic end-to-end):
- Certified b_k(s): alternating series per subinterval (bands split so
  s·u ≤ 24), **dynamic term count** N = max(64, 4·s·u + 40) with the
  truncation error asserted ≤ 1e-24 (the fixed N=30/64 brackets are
  worthless for s ≥ 32 — measured, then fixed);
- Certified exp lower bounds (scale-and-square squaring bracket);
- Outward rounding only (exponent down to 30 decimals; envelope lower
  bounds down/up per verdict direction);
- Emits per-cell/per-run verdicts + Lean batches
  (`receipt/lean/Percell77Fine.lean`, `Percell77RunLevel.lean`): stdlib-only
  Int-pair `decide` theorems, one per emitted comparison, plus a
  batch-count seal theorem per file. Both build in ~2 s.

**Verdicts** (also in `OBLIGATION_MAP.md`):
- fine level: **0/8948** row-77 window cells, **0/137** rows;
- sum level: **5/73** inner rank/high rows hold (the five `high`
  components, mass exactly 1, envelope ≤ 0.89 — decided holds);
  68 rank_two rows fail by factors 0.085–0.5; row 77 fails (7.9e-5 vs
  ≥ 5.2e-1).
- **Root cause, established numerically then named**: every inner window
  lies in the mass band [0.893, 0.993] — below the law's mean mass ζ ≈
  1.0510. For m < mean the Chernoff envelope min_s e^{s·m − B(s)} is bounded
  below by ≈ e^{−0.66} (sum) / ≈ 0.84 (per-coordinate) — the D1-data
  contract `frozen ≥ envelope` is void for ALL windows at ALL s. The
  blocker is the envelope CLASS, not the data.

## 4. hEnv77 row-77 instantiation (the C0 lemma)

`Pg182D1/HEnv77Row77.lean` — NEW, in the build (8935 jobs green):
- `sigma77`, `p77`, `c77max` — the frozen payload's exact numbers;
- `sigma77_mul_p77_eq` — the exact-ℚ product, kernel-checked (norm_num);
- `row77_data_gap_is_false` — the decided refutation of the row-77 D1-data
  comparison against the certified envelope bound `env38lo77`;
- `row77_integral_le` — the discharge: the `hEnv77_discharge` schema
  instantiated at the frozen numbers (constant envelope on the window run
  set, hdata as the per-class sum bound, hsum the frozen comparison) —
  uniform in the profile coordinate i. C0 supplies E77/NLB and the
  kernel-side hsup/hzero; D1's side is wired end-to-end.

**Axcheck** (`receipt/axcheck.txt`, `receipt/lean/axcheck_percell.txt`):
`row77_integral_le`, `row77_data_gap_is_false`, `sigma77_mul_p77_eq`,
`hEnv77_discharge`, `hEnv77_discharge_of_frozen` — all on
[propext, Classical.choice, Quot.sound] only. The emitted receipt theorems
(fine/run batches): **zero axioms** (core `decide` only).

## 5. The 262-obligation map

`OBLIGATION_MAP.md`: 5 cap + 120 outer are **D1-independent**; of the 137
D1-data consumers, **5 hold** (sum level), **132 blocked** by the
envelope-class weakness (verdicts certified per row); the archive-side data
supply is complete and the generator generalizes (all 137 rows emitted).

## Commits

| sha | content |
|---|---|
| `c49027c` | D1C-stage2: per-cell emission machinery + hEnv77 row-77 instantiation |
| `c49027c` (same, stage 1 landed together) | fetch script + HASHES.md + .gitignore |

## What is next (for the next session)

- The 132 blocked inner rows need a stronger envelope class in Lean
  (sub-exponential tails or exact convolution certificates) — the data side
  is done and emitted; the receipt batches are ready to extend the moment a
  class is proved.
- C0 side: wire `row77_integral_le` into `RowCert` (E77/NLB from the C0
  lane; do not edit pg182-c0 from D1).
