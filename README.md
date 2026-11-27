# prime-gaps-182

A Lean 4 conditional frame toward **H₁ ≤ 182** (bounded prime gaps): the DZQ pattern applied to prime-gaps — frame structure, parity analysis, and the proof lanes that discharge its numeric obligations.

**Race status** ([Big O Speedrun](https://bigospeedrun.com) board, Nov 26 2026): **OPEN**. Leader: GPT-6 Astra (OpenAI), H₁ ≤ 182, Sep 6 2026 — *Claimed*, not Lean Verified. The unconditional **H₁ ≤ 246** (BigO-Hunter) is Lean Verified: [prime-gaps-246-lean](https://github.com/BigO-Hunter/prime-gaps-246-lean). This repo is the 182 lane: it does not yet verify 182 — it reduces `Bound 182` to explicit, cited hypotheses plus 262 named numeric obligations, and discharges them lane by lane.

## What is proved here

The frame theorem (`Pg182Frame/Frame.lean`):

```lean
theorem h1_182_of (h1 : Kloosterman3Bound) (h2 : Kloosterman2CorrelationBound)
    (hK4 : IncidenceRankFourBounds182) (h3 : TypeIIILocalFourier)
    (hd : Deduction182) (S : TrialSource182) (C : TrialCerts182)
    (hobs : PhysicalSourceBounds182Mirror S C) :
    BigOSpeedrun.PrimeGaps.Bound 182
```

Sorry-free: its axiom footprint is `[propext, Classical.choice, Quot.sound]` (`receipt/axcheck.txt`). The 262 numeric stubs are quarantined in `Pg182Frame/Obligations.lean` and reach the theorem only through explicit hypothesis arguments. `FRAME_REPORT.md` gives the exact shape and credits; `PARITY.md` compares the frame against OpenAI's PrimeGaps186.

Status: 3332 jobs green (`LAKE_JOBS=1`), toolchain `leanprover/lean4:v4.34.1`, Mathlib `d13f23b7`.

## Contents

- Repository root: the conditional frame (`Pg182Frame/`), `FRAME_REPORT.md`, `PARITY.md`, `receipt/axcheck.txt`.
- `c0/`: lane C0, first rankTwo inner row end-to-end — the discharge template for the remaining 67 inner rows (`c0/inner_rows.json`, `c0/ROW_REPORT.md`).
- `d1/`: lane D1, the discrete-law majorant — the algorithm-to-integral correspondence (`d1/ROUTE.md`: what closed, what remains).
- `d2/`: lane D2, the stronger envelope class — composition and statement work, plus the Bochner `infinitePi` product integral contributed upstream as [mathlib4#45771](https://github.com/leanprover-community/mathlib4/pull/45771) (receipts in `d2/receipt/`).
- `kloosterman-sheaf/`: the Kloosterman/Weil packaging lane — discharging the Kloosterman hypotheses from formalized arithmetic geometry.
- `r1/`: the 182 premise map and first-cut feasibility notes — design evidence, not a proof submission.
- `r2/`: the 262-certification architecture and trust model; its nested Lean project is fully inlined at `r2/prime-gaps-lean/` (upstream `b77bf175`), no submodule dependency.
- `scout/`: board map, claimability analysis and verification design — the verifier's ask-first gate and submission layout, as used for the landed 246 row.

Every Lake package uses the git-pinned Mathlib revision `d13f23b723b8a846827a245b89c10fc7d3f11612`. D2 resolves its frame and D1 dependencies as `../` and `../d1`, so the umbrella has no absolute-home or sibling-checkout dependency.

### Optional regeneration inputs

Committed artifacts need no external checkout. Optional regeneration/audit scripts accept `PG182_R2_SOURCE` (C0 source Lean file), `PG182_D1_DATA` (D1 frozen extraction), and `WEIL_VERIFY` (Kloosterman/Weil checkout). Those datasets are intentionally not duplicated in this umbrella.

## Reproduce / verify

- **CI**: `.github/workflows/ci.yml` builds the D2 envelope (frame + D1 + D2) and the C0 inner row on every push, via `leanprover/lean-action` with cached Mathlib.
- **Local**: build each Lake package from its own directory (`lake update && lake build`); D2's build covers the frame and D1. Use `LAKE_JOBS=1 LEAN_NUM_THREADS=1` on low-memory hosts.
- **Axiom audits**: `receipt/axcheck.txt` (frame) and `d2/receipt/axcheck*.txt` (lane theorems); re-run with `lake env lean <axcheck-file>`.

## Next steps for a continuer

1. Discharge the 262 obligations (`Pg182Frame/Obligations.lean`): the C0 row machine (`c0/ROW_REPORT.md`) is the template; 67 inner rows remain.
2. Discharge the frame hypotheses `h1`/`h2`/`hK4`/`h3` via the Kloosterman/Weil route (`kloosterman-sheaf/`, gate conditions in `d2/OBLIGATION_MAP.md` §5).
3. Close the D1 route remainder (`d1/ROUTE.md`) and the `PARITY.md` items.
4. For a verifier submission: `scout/BOARD_MAP.md` and `scout/VERIFY_DESIGN.md` record the ask-first gate, credit rule and fixture-proven Submission layout.

## License

Licensed under the Copy-Free/Stays-Free (CFSF) License — see [LICENSE](LICENSE). CFSF: copy-free (use for any purpose) and stays-free (nobody may fence this work). Third-party portions keep their upstream licenses (`kloosterman-sheaf/NOTICE.md`).

AI-assisted; disclosed. Author of record: darkhipo.

---

[BigO-Hunter](https://github.com/BigO-Hunter) — the tracking & packaging org for [Big O Speedrun](https://bigospeedrun.com) contributions. [Org profile](https://github.com/BigO-Hunter/.github) · [bigo-hunter.github.io](https://bigo-hunter.github.io).
