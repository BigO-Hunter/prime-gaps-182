# kloosterman-sheaf — packaging `|Kl_3(a; q)| ≤ 3 q^{1/2}` from AxiomMath/Weil + Stacks

Lane of the 182 campaign. Target: discharge `PrimeGap186.kloosterman3_bound`
(`‖normalizedKloosterman3 p c‖ ≤ 3`, Katz 1988 Thm 4.1.1 at `n = 3`, trivial characters,
`bᵢ = 1`) by **instantiating** the formalized arithmetic geometry in
`~/bigo-campaign/weil-verify/Weil` (AxiomMath/Weil + AxiomMath/Stacks), instead of formalizing
Weil II from scratch.

## What is verified here (compiles, axiom-clean)

| file | content | axiom set |
|---|---|---|
| `KloostermanTraceBound.lean` | `norm_multiset_sum_le_card_mul`, `norm_trace_le_of_monic_charpoly_pure`, `kloosterman_bound` (`≤ 3√q`), `kloosterman_bound_unnormalized` (`≤ 3p`, Katz's form) | `[propext, Classical.choice, Quot.sound]` |
| `KloostermanObligations.lean` | `Kl3Package` (rank ≤ 3, monic split charpoly, trace = `Kl_3`, weight-purity) and `Kl3Package.norm_kl3_le` — the packaging obligations are *sufficient* | `[propext, Classical.choice, Quot.sound]` |

Receipt: `gate_trace.lean`, output in `AXIOM_GATE` of `../weil-verify/AXIOM_GATE.md`.

## What is not yet verified

`KLOOSTERMAN_SHEAF.lean` — the Kl_3 definition against the `StacksFrontier` API
(`laumonFourierFamilySheaf`, `isLisse_laumonFourierFamilySheaf`, the three obligations as Props).
Its imports' oleans do not exist: the closure of `LaumonFourierLineFamily` is 17,567 Stacks
modules of which **16,525 are unbuilt**. Resume with:

```bash
cd ~/bigo-campaign/weil-verify/Weil
nohup env LAKE_JOBS=1 LEAN_NUM_THREADS=1 \
  lake build StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFourierLineFamily \
  > /tmp/build_laumon.log 2>&1 &
```

then `./build.sh KLOOSTERMAN_SHEAF.lean` (expect implicit-argument reconciliation; the binder
order follows the source files verbatim).

For the deeper gate (`weightBound`, `satisfiesWeilEstimate`), same command with
`Weil.AlgebraicGeometry.EtaleCohomology.Trace.DeligneWeilConjecture` — 19,424 unbuilt modules,
≈ 6.8 days at the measured 2 oleans/min.

## Building

`./build.sh <File.lean>` compiles against the Weil tree's existing oleans (no new lake package, no
Mathlib rebuild): it borrows `LEAN_PATH` from `lake env` inside `~/bigo-campaign/weil-verify/Weil`
and uses the pinned toolchain `leanprover/lean4:v4.34.0-rc2`.

## Instruments

* `closure_size.py <Module>` — import closure size + per-package unbuilt olean counts.
* `closure_sorry_scan.py <Module>` — code-level `sorry`/`admit` in the closure (regex
  sanity-checked against a known-`sorry` file before use).

---

## Why this repo is up

Public design input: the instantiation plan (and verified fragments) for discharging the Kloosterman bound from formalized arithmetic geometry instead of formalizing Weil II from scratch.

[BigO-Hunter](https://github.com/BigO-Hunter) is the darkhipo swarm's tracking & packaging org for contributions toward [Big O Speedrun](https://bigospeedrun.com) — a companion, never the project. Org story: [profile](https://github.com/BigO-Hunter/.github) · [bigo-hunter.github.io](https://bigo-hunter.github.io).

## What work can be done here

Open work: instantiate the AxiomMath/Weil + Stacks geometry to discharge `PrimeGap186.kloosterman3_bound`; complete the |Kl_3| ≤ 3q^{1/2} bridge (verified fragments listed in the README table).

## License

Licensed under the Copy-Free/Stays-Free (CFSF) License — see [LICENSE](LICENSE). CFSF: copy-free (use for any purpose) and stays-free (nobody may fence this work). The name is unclaimed in software licensing (checked 2026-11-09) and is deliberately not "Copyfree" — the Copyfree Initiative's certification mark — since CFSF's anti-enclosure condition is excluded by their standard.  Vendored third-party material keeps its upstream license — see [NOTICE](NOTICE.md).
