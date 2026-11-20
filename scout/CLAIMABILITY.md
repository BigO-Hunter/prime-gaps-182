# CLAIMABILITY.md — can WE produce the first Lean-verified row on prime-gaps?

## VERDICT: **claimable-with-route-open** — and the work is already done

The first LV row on this board will be **`H_1 ≤ 246` (the classic Polymath baseline), not 182** — and our own darkhipo account already built and routed the proof:

1. **#148** (darkhipo, 2026-11-05T00:14): ASK-FIRST route request for `H_1 ≤ 246`, repo `darkhipo/prime-gaps-246-lean` @ `ac0eb01`. Composition: AxiomMath/PrimeGapsLib @ 1faa7b1 (implication + 50-tuple Lean-checked certificate) + kimihiro64/bombieri-vinogradov @ 7a17483 (full BV theorem from only propext/Classical.choice/Quot.sound). `lake build Submission`: 5437 jobs, exit 0; axiom audit clean, no sorryAx.
2. **Maintainer verdict on #148** (nmamano, closed 2026-11-06T00:39): route will open in Snaky steps — statement, closed profile, smoke run, open route. Statement form confirmed (Mathlib-only, `∃ᶠ m in atTop, Nat.nth Nat.Prime (m+1) − Nat.nth Nat.Prime m ≤ B`). **Credit fixed: Axiom Math first, Jonas Whidden second.** Explicit gate: no submission issue until they post the route is open on #148.
3. **#166–172 (2026-11-06)**: the smoke run — with OUR composition as the passing control (#166) and six must-refuse mutations (wrong bound 245, strictness, eventually, two-steps, prime-def). Closed ~9 min apart, same day. Site trust commits 21:14/22:36 ("prime gaps closed profile"). The pipeline is one step from open.

So "produce the first Lean-verified row" reduces to: **watch #148 for the open-route post, then file the real LV submission immediately** (the #158 playbook, with the fixture showing the exact passing layout). The row, if landed, names Axiom Math + Jonas Whidden first per #142 credit rule — darkhipo gets the composition credit. That is still the first LV row on the board and ours to file.

## Per-row claimability

| Row | Verdict | Why |
|-----|---------|-----|
| **246 (classic baseline → new row)** | **claimable-with-route-open** | Proof composed, maintainer-validated as smoke control; only the open-route post (#148) is missing. |
| 182 | not-ours (not anyone's, today) | Missing Lean content = the 262 integral inequalities + finite-field estimates = the paper's research core. Not an arithmetic certificate. Formalizing = research-level project. |
| 186 | not-ours | Same: Deligne-type exp sums + 152 numerical bounds; #152 precedent: packaging others' proofs is reserved to maintainers. |
| 212 | not-ours | 5 equidistribution estimates + Harman decomposition as hypotheses; same class. |
| 240 | not-ours | No Lean at all; same analytic core. |

## Why no arithmetic-certificate shortcut exists for 182–240

Every row B < 246 = admissible-tuple construction (finite, checkable — e.g. 39-tuple width 182) **plus** Maynard-sieve distribution estimates (infinite/asymptotic analysis). The tuple is trivially checkable; the distribution estimates are the proof. Lean-verified requires both, unconditionally. Our OMR/certificate tooling checks the first part only. (Contrast #158 directed-sssp: the whole claim WAS computational.)

## Secondary openings (if the coordinator wants more than the row)

- The 186 row's 152 numerical bounds are "Python-checked only" — a Lean interval-arithmetic certification of even a subset is a real, kernel-checkable community contribution toward an eventual 186 LV row. Bounded, but low-visibility (no row for us).
- romyar1/prime-gaps-lean has "No independent check" — an independent rebuild report of its deduction (sorry-free given stated premises) is cheap goodwill. Optional; #152 warns against unasked packaging.

**Recommendation: single-lane focus — camp #148, fire the submission on the open-route post.**
