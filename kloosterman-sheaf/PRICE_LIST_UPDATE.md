# PRICE_LIST_UPDATE — the 182 price list after the Weil/Stacks content audit

2026-11-07. Supersedes the Katz/FKM line items of the earlier scope program
(Stages 1–3) and rewrites the frame statement at the end of
`../d2/OBLIGATION_MAP.md` §4. Evidence: `$WEIL_VERIFY/AXIOM_GATE.md`
(what is measured), `$WEIL_VERIFY/{CONTENT_AUDIT,REPO_MAP,INSTANTIATION}.md`, and
this directory (the packaging, with its own compiling receipts).

## The one-line change

| before | after |
|---|---|
| **182 certified given N1's band assembly + Katz + FKM + Type III** | **182 certified given N1's band assembly + Type III + Kl_3 packaging** |

with two conditions stated in §3: the packaging is *construction* (weeks), and the heavyweight
axiom gate (`weightBound`, `satisfiesWeilEstimate`) is still **PENDING** a build that needs
19.4k more Stacks modules.

## 1. What moved, and why

| line item | old price | new price | why |
|---|---|---|---|
| **Katz 1988 Thm 4.1.1(1)–(2)** (`kloosterman3_bound`) | Stage 3, "1–3 person-years on top of Stage 2"; Stage 2 "3–6 person-years" | **weeks** — instantiate from AxiomMath/Weil + Stacks | the Fourier–Deligne / AS-sheaf machinery and the purity engine exist: `laumonFourierFamilySheaf`, `isLisse_laumonFourierFamilySheaf`, `laumonFamily_isPure_restrictScalarsRep`, `LAdicSheaf.weightBound` (Tag 03VH), and the FK IV.4 lemma whose axiom set is **measured** `[propext, Classical.choice, Quot.sound]` |
| **FKM 2013 Prop 2** (`kloosterman2_correlation_bound`, ≤ 8p√p) | Stage 3, same | **weeks (cohomological core) + unchanged custom work (p-adic refinement)** | the rank-4 analogue rides the same packaging; the sharp constant's p-adic route is not in the repo (INSTANTIATION.md) |
| **Weil I / Hasse–Weil for curves** | Stage 1, "1–2 person-years" | **instantiate** (`ZetaRationality`, `DeligneFunctionalEquation`, `WeilRiemannHypothesisForm`, `Weil.satisfiesWeilEstimate`) | all four Weil conjectures are formalized; gate pending on the same build |
| **Deligne RH for lisse sheaves** | Stage 2, "3–6 person-years — the deep core" | **instantiate** | `LAdicSheaf.weightBound` + the ~12-module `WeilII*` induction + the ~10-module `LaumonFourier*` line family |
| **Stage 0** (finite-field character-sum toolkit: `Kl` as a `ZMod p` object, Gauss orthogonality, FKM Prop 6 identity, finite-range checks) | 1–3 person-months | **1–3 person-months — unchanged** | not supplied by Weil/Stacks; it is the arithmetic half, and it is also the acceptance test bed |
| **Type III** (`TypeIII.LocalFourierHypothesis`) | no closed proof anywhere | **unchanged** | untouched by the Weil/Stacks audit |

Net: the two line items whose price was set by *inventing* 20th-century arithmetic geometry
(Stages 1–2, 4–8 person-years; PROGRAM.md's total "~5–10+ person-years") become **instantiation**.
The programme's remaining long pole is no longer formalization — it is Type III and the
statement-fidelity read.

## 2. The Kloosterman packaging, priced

The gap in `INSTANTIATION.md` was four items. Their status after this lane:

| # | item | status |
|---|---|---|
| (a) | `Kl_3` as the (dual of the) Fourier family away from 0 — construction + lisseness + rank bound | **lisseness already proved in the repo** (`isLisse_laumonFourierFamilySheaf`); the rank bound is obligation 1 below |
| (b) | stalk trace = `Kl_3(a; q)` via sheaf–function correspondence | **obligation 3**, assembly of existing AS-character + trace-formula pieces |
| (c) | purity at every `a ≠ 0` | `laumonFamily_isPure_restrictScalarsRep` (weight `β+1`); weight-2 instance is **obligation 2** |
| (d) | rank ≤ 3 + weight ⇒ `‖Kl_3‖ ≤ 3 q^{1/2}` | **PROVED AND AXIOM-CLEAN** — `KloostermanTraceBound.lean` (`kloosterman_bound`, `kloosterman_bound_unnormalized` = Katz's `3p` form) and `KloostermanObligations.lean` (`Kl3Package.norm_kl3_le`) |

So three obligations remain, all *construction against an API that exists*, and the last mile is
already a theorem. Pricing: **weeks of API work + days of machine time**, not years. The two
concrete near-term steps are (i) build the 16.5k-module `LaumonFourierLineFamily` closure so
`KLOOSTERMAN_SHEAF.lean` elaborates, and (ii) discharge obligations 1–3 to produce a `Kl3Package`.

## 3. The two conditions, stated plainly

1. **The heavyweight axiom gate is PENDING, not passed.** Measured: the FK IV.4 lemma is clean; the
   Stacks theorems that already have oleans are clean; `weightBound` and `satisfiesWeilEstimate`
   have **no oleans**, and building them costs 19,363 / 19,424 unbuilt Stacks modules
   (≈ 6.8 days at the measured 2 oleans/min). Source-level: **0** code-level `sorry`, **0** `axiom`
   declarations, **0** `native_decide` across all 63k Stacks files and the 980 Weil files.
2. **Axiom-clean ≠ statement-faithful.** A human must read `IsCharpolyPureOfWeight`,
   `HasDeligneConclusions`, `rationalGeometricCompactlySupportedCohomology` and
   `isLisse_laumonFourierFamilySheaf` before the programme bets its constants on them.

If the pending gate comes back dirty, the price list reverts to naming the leaking `sorry` sites —
and the packaging work in `kloosterman-sheaf/` is unaffected, because it consumes only the
statements, not their proofs.

## 4. Files written by this lane

* `$WEIL_VERIFY/AXIOM_GATE.md` — the `#print axioms` output verbatim + the wall.
* `{KloostermanTraceBound,KloostermanObligations}.lean` (this directory) —
  compiling, axiom-clean receipts.
* `KLOOSTERMAN_SHEAF.lean` (this directory) — the packaging (status: pending build).
* `../d2/OBLIGATION_MAP.md` §4 — frame statement updated in place.
