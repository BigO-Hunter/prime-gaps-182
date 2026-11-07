# OBLIGATION_MAP.md — the 262-obligation status table after D1C

Source of the 262: the archive's own README (`external-numerics-20260909`,
romyar1/prime-gaps-lean) and `evidence/verification.json`
(`target_inequalities: 262`, `all_262_recomputed: true`,
`lean_numerical_premises_discharged: 0`). The archive is sha-pinned in
`frozen/HASHES.md` (zip sha256 `2960729e…726f3b3b`).

## The table

| family | count | stage outputs | D1-data status (this lane) |
|---|---:|---|---|
| Denominator lower/upper, J0 lower, Jplus lower, tail upper (cap) | 5 | `multicap_a6_full_cap_n393216.json` | **D1-independent** (cap/outer chain: B1/B3 + D3; no per-cell law mass consumed) |
| Outer rank-two roots and faces | 56 | `outer-rank-roots`, `outer-rank-faces` | **D1-independent** (same chain) |
| Outer high roots and faces | 4 | `outer-high` | **D1-independent** |
| Outer low roots and faces | 60 | five G1/G2 low stages | **D1-independent** |
| **Inner rank-two and high masses** | **73** | `fine_coarse_inner_sources_n393216.json` (5 groups: G3 15, G4 13, G5 15, G6 14, C1 16) | **D1-data consumers** — see verdicts below |
| **Inner low masses** | **64** | `fine_coarse_inner_low_v3_g3g5g6…b48` (36), `fine393216_G4_low_v3` (21), `fine_C_low_v3_n393216` (7) | **D1-data consumers** — see verdicts below |
| **Total** | **262** | 13 integration stages + affine prep | |

## D1-data verdicts (certified exact-ℚ, receipt/percell_emission.json)

All 137 inner rows located and scanned. The emission machinery
(`receipt/percell_emit.py`) generalizes over rows unchanged.

**Fine level (per fine cell, d = 1): p = `fine_h` = ζ/393216 (the frozen
uniform per-cell mass, exact) vs env(n) = exp(s(n+1)·mesh − B(s)).**

| check | cells | HOLD | FAIL |
|---|---:|---:|---:|
| row 77 full window (334254..343201) | 8 948 | 0 | 8 948 |
| all 137 rows (window-min cell, monotone-sealed) | 137 rows | 0 | 137 |

**Sum level (per row, d = 38): p = `source_mass.upper` (exact ℚ) vs
env38(38·fine_last) = exp(s(c+38)·mesh − 38·B(s)), sound window-wide
(envelope increasing in c).**

| rows | HOLD | FAIL |
|---|---:|---:|
| 73 inner rank/high | **5** | 68 |
| 64 inner low | (fine level fails; run-level pending — the low payloads carry per-run radial bounds, not a per-row mass interval) | — |

The 5 holds are exactly the `high` components of all five groups (G3 comp 14,
G4 comp 12, G5 comp 14, G6 comp 13, C1 comp 15): their frozen source mass is
exactly 1 and the certified envelope lower bound at the run's maximal sum
cell is 0.52–0.89 — decided with 12–92% margin
(`receipt/lean/Percell77RunLevel.lean`, 73 decided lines + batch-count seal).
The 68 failing rank_two rows fail by factors 0.085–0.5 (worst:
G3/G5 comp 9–11 at ~0.09).

## The structural blocker (documented, not hand-waved)

Every inner window sits in the mass band **[0.893, 0.993]** — BELOW the
fragment law's mean mass ζ ≈ 1.0510. The Chernoff/Markov envelope
min_s exp(s·m − b(s)) for m < mean is bounded below by exp(−(small)) — it
never dips under ≈ e^(−0.66) ≈ 0.52 at the sum level and ≈ 0.84 per
coordinate — while the true per-cell / per-run masses are 1e-2 … 1e-5. The
D1-data contract `frozen ≥ envelope` is therefore **numerically void for
every window**, at every level, at every s (the certified B(s) grows only
logarithmically in s; the linear s·m term wins). This is a property of the
exp-sandwich envelope CLASS, not of the data supply: the frozen masses are
tight approximations of the true law, and the Lean-proved chain gives only
true ≤ env ≪ frozen. Discharging the remaining 132+ inner obligations needs
a stronger envelope class (e.g. sub-exponential / CLT-type tail bounds, or
exact discrete-convolution certificates), not more data.

## Scoreboard

- 262 obligations: **0** have their D1-data discharged via the per-cell
  Chernoff route; **5** inner high rows hold at the sum level via the
  emitted run-level comparisons; **132** inner rows are blocked by the
  envelope-class weakness; **125** outer/cap rows are D1-independent.
- The archive-side data supply is COMPLETE: the release asset is fetched,
  sha-verified, extracted (package-manifest: 913/913 internal hashes ok),
  and all 137 inner payloads parse and generalize in the generator.
