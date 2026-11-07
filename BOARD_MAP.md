# BOARD_MAP.md — bounded prime gaps board (live 2026-11-06)

## Location & scoring

- Live page: https://bigospeedrun.com/other/prime-gaps (slug `prime-gaps`). Board chatter: board.bigospeedrun.com/other-prime-gaps. Git data cache has NO prime-gaps json (fetches 404) — the live page is the truth (matches GATE_NOTES finding for sidorenko/matroid-prophet).
- Quantity: `H_1 = liminf (p_{n+1} − p_n)` — smallest consecutive-prime gap occurring infinitely often. A result is a proof of `H_1 ≤ B` for integer `B`. **Lower B better. `B = 2` = twin prime conjecture.** Must NOT assume unproved hypotheses — conditional bounds (e.g. EH ⇒ H_1 ≤ 12) do not count. Classic baseline (dashed line, NOT a row): **246** (Polymath8b, arXiv:1407.4897, 2014).
- Evidence levels: Claimed / Human Verified / **Lean Verified** ("we rebuild its Lean proof from source and check, with the Lean kernel, that it proves our exact problem statement"; also counts via prove2.me + maintainer review that the Lean statement is the problem statement).

## Rows (4 total — ZERO Lean Verified)

| # | B | Level | Holder | Date | Lean status |
|---|---|-------|--------|------|-------------|
| 1 | **182** | Claimed | GPT-6 Astra (OpenAI), prompted by Romyar Sharifi | Sep 6 | Conditional dev romyar1/prime-gaps-lean: proves deduction from 262 integral inequalities + 3 finite-field estimates + local Fourier proposition. Board: "not an unconditional Lean proof... No independent check." |
| 2 | 186 | Agent breakthrough | OpenAI | Sep 3 | Lean dev openai/PrimeGaps186 assumes 3 axioms: 2 Deligne-type exp-sum bounds + 152 numerical bounds Python-checked only. "No person has reviewed the Lean development independently." |
| 3 | 212 | Claimed | Axiom Math (Charton, Hong, Lau, Ono, Remy, Siu, Swaminathan, Thorner, Xie) | Sep 3 | AxiomProver Lean certificate takes 5 equidistribution estimates + BV + Harman + numeric cert as hypotheses → not unconditional. |
| 4 | 240 | Claimed | Julia Stadlmann | Aug 31 | No Lean. arXiv:2608.31126. |

All four descend from the Maynard–Tao line (admissible tuples + distribution estimates past BV). Zhang 2013 (B=7×10^7) was the first finite bound ever; every B ≤ 246 result needs BV-or-stronger distribution input.

## Demand side — the gate (read FIRST)

- **#148** (bigospeedrun/verifier, OUR darkhipo route request, filed 2026-11-05T00:14, closed 2026-11-06T00:39 by nmamano, verdict verbatim): "We plan to open this route ourselves, in the same steps as for Snaky: we write the trusted statement, a closed profile, a maintainer smoke run, then the open route." Statement: Mathlib-only `infinitely often, Nat.nth Nat.Prime (m+1) − Nat.nth Nat.Prime m ≤ B`, Lean v4.33.1, Mathlib 0df444a. Credit: "A row from your composition names the Lean authors first: Axiom Math for the implication and its certificate, and Jonas Whidden for Bombieri–Vinogradov." **GATE: "Please do not open a submission issue before we post that the route is open. I am closing this issue; we will write here when the statement is on main."**
- **#166–172** (all nmamano, filed+closed 2026-11-06 20:59–23:48Z, ~9 min cadence): the maintainer smoke suite of the prime-gaps profile against `bigospeedrun/verifier-smoke-prime-gaps`:
  - #166 control: `Race.bound : BigOSpeedrun.PrimeGaps.Bound 246`, sorry-free = darkhipo/prime-gaps-246-lean @ ac0eb01 moved into Submission layout. Must PASS.
  - #167 `Bound 245` (unproven bound — must refuse). #168 strict mutation. #169 eventually-instead-of-frequently. #170 two-steps. #171 prime-def mutation. #172 (abc6a6e) — all must REFUSE. "(maintainer, never imported)" on every title = smoke rows do not land as board rows.
- Site trust commits 2026-11-06: 21:14 "prime gaps closed profile", 22:36 "LeanArchitect keeps autoImplicit = true". **Route opening is mid-flight: statement + closed profile + smokes done; the open-route post on #148 has NOT landed yet.**

## Statement form (exact, from smoke fixture `Submission/PrimeGapsStatement.lean`)

```lean
def Bound (B : ℕ) : Prop :=
  ∃ᶠ m in Filter.atTop, Nat.nth Nat.Prime (m + 1) - Nat.nth Nat.Prime m ≤ B
```
Byte-copy of verifier `challenges/prime-gaps/Statement.lean`; form = AxiomMath/PrimeGapsLib `bombieriVinogradov_implies_frequently_prime_gap_le_246` (Bounded246.lean @ 1faa7b1) with 246→B, BV hypothesis dropped.

## Winning pattern to replicate

#158 (directed-sssp, LV receipt 2026-11-05T18:30, row landed): trusted-statement package + sorry-free certificate in the Submission layout. Here the fixture ALREADY shows the passing shape (`Submission.lean`: 3 imports + `Race.bound := bombieriVinogradov_implies_frequently_prime_gap_le_246 BombieriVinogradov.bombieriVinogradov`).
