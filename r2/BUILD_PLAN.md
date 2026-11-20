# BUILD_PLAN.md — staged, each stage a checkable artifact

## Stage 0 — reproduce the base (0.5 day)
`lake build` the cloned repo (toolchain `v4.34.0-rc2` auto-fetch). Artifact: green
build log of `formal/`, elapsed time, olean footprint. Gate: the conditional endpoint
theorem elaborates with its premises as hypotheses (no axioms beyond Mathlib's —
`#print axioms PrimeGap182.infinite_consecutive_prime_pairs182_of_local_inputs`).

## Stage A — admissibility + deduction reuse (2–3 days)
Artifact: the `Tuple182` admissibility path shown kernel-checked (finite sieving
decisions over the 39 integers — small-prime residue tables; if the repo already proves
it, this stage is verification + `#print axioms`, else emit the residue-table receipts).
Credit: romyar1. Gate: `#print axioms` clean on the tuple theorem.

## Stage C0 — ONE inner row end-to-end (1–2 weeks) ← FIRST STAGE TO ATTACK
Pick the smallest rankTwo row (j=0). Deliver:
1. Bridge lemmas B1 (partition integral) instantiated for that cover;
2. `gen_receipts.py` computing the row's run-table sum in `fmpq`, cross-checked in arb;
3. `theorem hInner_0 : trialSourceInnerMass 0 ≤ (trialInnerCertificates 0).faceUpper`
   with kernel-only proof.
This stage exercises every machine part on the smallest surface and de-risks the
measure-theory bridge, which is the only genuinely uncertain component.

## Stage C1 — exp sandwich + one `.low` row (1–1.5 weeks, overlaps C0)
Formalize `exp_le_of_rational_series` (rational endpoint bounds for `Real.exp` with
provable relative error ~10^-80). Instantiate for one slope≠0 row. Gate: the row's
margin survives our endpoint slack — else STOP and report (no hand-tuning).

## Stage C2 — batch all 197 source rows + 5 cap rows (2–4 weeks, mostly compute)
Generator emits all receipts; `lake build` batched per row (parallel elaboration across
~40 rows/batch). Expected wall time: hours-to-a-day of compute per batch given the
per-row kernel work is small; the risk is elaboration-time pathologies → batch sizing
tuned in C0. Artifact: `PhysicalSourceBounds182` fully discharged; `#print axioms` clean.

## Stage D — assembly (2–3 days)
Splice discharged premises into `PrimeGaps182Analytic.lean` (upstream, credited),
rebuild, artifact: **the first verified row in the #158 playbook sense** —
sorry-free modulo the two honest holes:
- 3 finite-field estimates (Katz/FKM — ∀p, needs Deligne machinery; NOT kernel-checkable
  today; stays an explicit premise),
- `TypeIII.LocalFourierHypothesis` (R1's lane; no closed proof anywhere).
Result: **"182 certified given Katz + FKM + Type III"** — every numerical premise gone.

## Honest total
~6–10 focused weeks to a fully-numerics-clean certificate; the two analytic holes
(finite-field, Type III) are outside any quadrature machine's reach and are documented
exactly in ARCHITECTURE.md §Class F / assumptions.md.
