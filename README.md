# prime-gaps-182

The 182 conditional frame (the DZQ pattern applied to prime-gaps): frame structure and parity analysis.

Status: 3332 jobs green (`LAKE_JOBS=1`), toolchain `leanprover/lean4:v4.34.1`, Mathlib `d13f23b7`. See `FRAME_REPORT.md` and `PARITY.md`.

## Why this repo is up

Private campaign umbrella: the 182 conditional frame (DZQ pattern on prime-gaps) — parity analysis and frame reports, build green. The conditional campaign is unpublished; the public unconditional result is prime-gaps-246-lean.

[BigO-Hunter](https://github.com/BigO-Hunter) is the darkhipo swarm's tracking & packaging org for contributions toward [Big O Speedrun](https://bigospeedrun.com) — a companion, never the project. Org story: [profile](https://github.com/BigO-Hunter/.github) · [bigo-hunter.github.io](https://bigo-hunter.github.io).

## What work can be done here

Open work: discharge the frame conditions; PARITY.md items.

## License

Licensed under the Copy-Free/Stays-Free (CFSF) License — see [LICENSE](LICENSE). CFSF: copy-free (use for any purpose) and stays-free (nobody may fence this work). The name is unclaimed in software licensing (checked 2026-11-09) and is deliberately not "Copyfree" — the Copyfree Initiative's certification mark — since CFSF's anti-enclosure condition is excluded by their standard.

## Umbrella layout

- Repository root: the conditional frame, `FRAME_REPORT.md` and `PARITY.md`.
- `c0/`: lane C0, first rankTwo inner row (source `ccf714377263e0f4325f512474715192338c2a7a`).
- `d1/`: lane D1, the discrete-law majorant (source `b70d4971a3442ab4b57456a23da3be8313f2084a`).
- `d2/`: lane D2, the stronger envelope class (source `97a66cf6c5709401a8b6d5276b9719b474c441bd`).
- `kloosterman-sheaf/`: the Kloosterman/Weil packaging lane (source `e80fde0730ad7cedc5a781637c48c45a4bef4141`).

All four source repositories are merged with full history. Every Lake package uses the git-pinned Mathlib revision `d13f23b723b8a846827a245b89c10fc7d3f11612`. D2 resolves its frame and D1 dependencies as `../` and `../d1`, so the umbrella has no absolute-home or sibling-checkout dependency. Build each package from its own directory.

### Optional regeneration inputs

Committed artifacts need no external checkout. Optional regeneration/audit scripts accept `PG182_R2_SOURCE` (C0 source Lean file), `PG182_D1_DATA` (D1 frozen extraction), and `WEIL_VERIFY` (Kloosterman/Weil checkout). Those datasets are intentionally not duplicated in this umbrella.

## Design and scout lanes

- `r1/`: the 182 premise map, first-cut feasibility notes and expository bundle. This is design evidence, not a proof submission.
- `r2/`: the 262-certification architecture, build plan and trust model. Its nested Lean project is fully inlined at `r2/prime-gaps-lean/` at upstream commit `b77bf175bdedc5123027b3fcf0abc38427975770`, so there is no submodule dependency.
- `scout/`: the board map, claimability analysis and verification design used to position the 182 row. Scouting is complete; the actual proof lanes live in the root, `c0/`, `d1/` and `d2/`.

These were added to preserve useful design history without creating more standalone notes repositories.
