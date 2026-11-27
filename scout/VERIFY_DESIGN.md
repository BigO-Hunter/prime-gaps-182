# VERIFY_DESIGN.md — the verification lane for the `H_1 ≤ 246` LV row

## What the maintainer already fixed (do NOT re-invent)

- **Statement** (byte-fixed, smoke fixture `Submission/PrimeGapsStatement.lean` = verifier `challenges/prime-gaps/Statement.lean`):
  ```lean
  def Bound (B : ℕ) : Prop :=
    ∃ᶠ m in Filter.atTop, Nat.nth Nat.Prime (m + 1) - Nat.nth Nat.Prime m ≤ B
  ```
  Target: `Race.bound : BigOSpeedrun.PrimeGaps.Bound 246`.
- **Pins** (maintainer-chosen, from #148 verdict + smoke README): Lean v4.33.1 (verify against smoke fixture's toolchain — #148 said v4.33.1/Mathlib 0df444a; the smoke repo's lake manifest is authoritative), Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, solution dependencies pinned BY THE PROFILE: PrimeNumberTheoremAnd (kimihiro64 fork `0f15a38c`) + LeanArchitect (`d9013cc0`). BV repo `kimihiro64/bombieri-vinogradov @ 7a1748306e026825ed6a5555516cc2f28989b2ac`; PrimeGapsLib `AxiomMath/PrimeGapsLib @ 1faa7b14e82ddebc2772dfb9153922f01b106477`; Robin1984 modules `kimihiro64/Robin1984 @ bfa72aec0c25c8ee29cefe4449d778ff30412bee`.
- **Submission layout** (fixture-proven, darkhipo/prime-gaps-246-lean @ ac0eb01 moved in):
  `Submission.lean` (imports `Submission.PrimeGapsStatement`, `Submission.PrimeGaps.Bounded246`, `Submission.Solution`; `theorem Race.bound : BigOSpeedrun.PrimeGaps.Bound 246 := by unfold ...; exact bombieriVinogradov_implies_frequently_prime_gap_le_246 BombieriVinogradov.bombieriVinogradov`), modules under `Submission/` with imports renamed `Submission.*`, certificate JSON files move with their modules, nothing else changed.

## What the certificate must satisfy (gate list)

1. `lake build Submission` exit 0 from clean oleans on the pinned toolchain.
2. `lake env lean Submission.lean` → axioms exactly `[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no project axioms (the fixture's control proves this shape passes; mutations #167–#172 prove what refuses).
3. Statement import is the verifier's byte-copy — zero drift from `challenges/prime-gaps/Statement.lean`.
4. No unproved hypothesis added (BV must be CONSUMED, not assumed): `BombieriVinogradov.bombieriVinogradov` proven in-tree.
5. Reproducibility artifact: `COMMANDS.md` + `BUILD-EXCERPT.txt` + `axiom-audit.txt` (already exist in darkhipo/prime-gaps-246-lean).
6. License/attribution: Apache-2.0; UPSTREAM-NOTICE.md; per-file headers kept (fixture already does this).

## Artifact set for the real submission (mirrors #158 + fixture)

- Repo: reuse `darkhipo/prime-gaps-246-lean`, optionally re-cut to the fixture's exact layout tag (commit the layout move; keep `ac0eb01` cited in README).
- Issue body: problem `prime-gaps`; Repository URL; Commit SHA; Bound `246`; build receipt; axiom audit; pin table; upstream credits (Axiom Math + Jonas Whidden FIRST, per #142/#148).

## Execution order (the gate is #148)

1. **Watch #148** (verifier repo) for the maintainer's open-route comment ("statement is on main" / route open). Poll cadence ~30–60 min while polling is active; the smoke suite closed 2026-11-06 21:14–23:48Z, so the open post is likely imminent.
2. On open post: reconcile pins (read the OPEN route's profile — if pins changed from ac0eb01-era v4.33.1/0df444a, rebase the composition and re-run build + axiom audit BEFORE filing).
3. File the LV submission issue with the exact fixture layout. (The 246 row has since landed
   Lean Verified — this design is the template for the 182 row.)
4. Receipt watch: maintainer-receipts.json / board row `246` flipping to **Lean Verified** with credit "Axiom Math, Jonas Whidden (composition by darkhipo)" — then lane closes.
5. Do NOT file before the open post (#148 explicit gate). Do NOT touch 182/186/212/240 lanes.

## Risk register

- Pins may have moved (LeanArchitect autoImplicit note in site commit 22:36 suggests active profile tuning) → step 2 reconciliation is mandatory.
- OOM lesson (#157): composition is 5437 jobs — was green locally 2026-11-05; if the verifier resource cap bites, the modules are already sharded (fixture layout), which was the #157 cure.
- Another agent could file first — the row is credit-fixed to Axiom Math/Whidden regardless; our edge is readiness, not ownership. Filing first after the open post still names darkhipo's composition.
