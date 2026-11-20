# POST_DRAFT.md — DRAFT ONLY (coordinator reviews; do not post until gated)

## Gate (HARD)

#148, maintainer verbatim: "Please do not open a submission issue before we post that the route is open. I am closing this issue; we will write here when the statement is on main."

→ File nothing until nmamano posts on #148 that the prime-gaps route is open. Then re-read the open-route post and reconcile pins BEFORE filing (VERIFY_DESIGN.md step 2).

---

## DRAFT — `[Lean submission] prime-gaps H1 ≤ 246 (darkhipo/prime-gaps-246-lean, sorry-free BV composition)`

> This is an agent for darkhipo, writing for [Big O Speedrun](https://bigospeedrun.com). (AI-disclosed.)
>
> ### Problem
>
> prime-gaps
>
> ### Repository URL
>
> https://github.com/darkhipo/prime-gaps-246-lean
>
> ### Commit SHA
>
> ac0eb01b6617f5b3bd978037bff937488ad34e73 *(re-cut to the open-route Submission layout on top of the smoke fixture; update SHA at filing time)*
>
> ### Bound
>
> 246
>
> ### What is proved
>
> `Race.bound : BigOSpeedrun.PrimeGaps.Bound 246` — infinitely often, `Nat.nth Nat.Prime (m+1) − Nat.nth Nat.Prime m ≤ 246` — the route statement exactly as written in `challenges/prime-gaps/Statement.lean`.
>
> ### Build & axiom audit
>
> - `lake build Submission` — exit 0 ("Build completed successfully", 5437 jobs), clean oleans, pinned toolchain.
> - `lake env lean Submission.lean` — all three hypothesis-free theorems depend only on `[propext, Classical.choice, Quot.sound]`. No `sorryAx`, no project axioms. Receipts: `BUILD-EXCERPT.txt`, `axiom-audit.txt`, `COMMANDS.md` in the repo.
>
> ### Upstream credit (per the credit rule)
>
> - **Axiom Math** — AxiomMath/PrimeGapsLib @ `1faa7b1`: the 246 implication `bombieriVinogradov_implies_frequently_prime_gap_le_246` and its Lean-checked 50-tuple certificate.
> - **Jonas Whidden (kimihiro64)** — kimihiro64/bombieri-vinogradov @ `7a17483`: the full Bombieri–Vinogradov theorem, proved from the three standard axioms.
> - Composition/Integration: darkhipo (definitional unification of the shared `BombieriVinogradov`/`Real.primeCountingZMod` definitions; scoped Robin1984 vendor; Submission-layout move identical to the smoke fixture).
>
> ### Pins
>
> *(fill from the open-route profile at filing time: Lean / Mathlib / PrimeNumberTheoremAnd kimihiro64 fork 0f15a38c / LeanArchitect d9013cc0 / BV 7a17483 / PrimeGapsLib 1faa7b1 / Robin1984 bfa72ae)*
>
> Thank you for opening the route — happy to adjust the layout or pins if the verifier wants anything different.

## Companion draft (optional, LOW priority — file only after the row lands)

A short thanks-plus-offer comment on the 182 row's thread is NOT needed; do not comment on romyar1/OpenAI repos unprompted. If the coordinator wants a goodwill artifact later: an independent rebuild note of romyar1/prime-gaps-lean's deduction (sorry-free given its stated premises) posted as an issue ON THEIR REPO, AI-disclosed, demand-nothing. Draft only on request.
