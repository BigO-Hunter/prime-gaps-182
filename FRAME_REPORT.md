# FRAME_REPORT — pg182-frame

Lane: THE 182 CONDITIONAL FRAME (DZQ pattern on prime-gaps). Built
2026-11-06/07. Toolchain: `leanprover/lean4:v4.34.1`, Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612` (git-pinned; see
`lake-manifest.json`).
Build: `LAKE_JOBS=1 LEAN_NUM_THREADS=1 lake build` — **3332 jobs, green**.

## Frame theorem (exact shape)

```lean
theorem h1_182_of (h1 : Kloosterman3Bound) (h2 : Kloosterman2CorrelationBound)
    (hK4 : IncidenceRankFourBounds182) (h3 : TypeIIILocalFourier)
    (hd : Deduction182) (S : TrialSource182) (C : TrialCerts182)
    (hobs : PhysicalSourceBounds182Mirror S C) :
    BigOSpeedrun.PrimeGaps.Bound 182
```

`Pg182Frame/Frame.lean`. Target `Bound B` is the def-equal restatement of
github.com/bigospeedrun/verifier `challenges/prime-gaps/Statement.lean` @
cb829226510350dc04c7b0c221943ed65daedfed (`Pg182Frame/Conclusion.lean`).

**Documented deviation from the 3-arg sketch**: the romyar1 endpoint takes the
rank-4 estimate as a premise SEPARATE from the Kl₃/Kl₂ pair
(`PREMISE_MAP.md` P2 item 3: "not derived from items 1-2 in the code"), so the
frame carries it as an explicit fourth input `hK4`. Also, per the
premise-parameterized pattern, the kernel-checked deduction and the 262
discharged obligations enter as explicit hypotheses (`hd`, `hobs`) — the frame
adds zero mathematical assumptions of its own. Every hypothesis's exact form
is cited to its source line (see HYPOTHESES docstrings).

## Kernel-checked delta

`frequently_gap182_of_infinite_consecutive_pairs`:
romyar1's endpoint conclusion (`Set.Infinite` of consecutive prime pairs with
gap ≤ 182, def-equal to `PrimeGap182.infinite_consecutive_prime_pairs182_of_local_inputs`'s
conclusion, formal/PrimeGaps182Analytic.lean:71-72) ⟹ `Bound 182`. Proof:
`p ↦ Nat.count Nat.Prime p` injects the pair set into the frequently-set via
`Nat.nth_count` / `Nat.nth_monotone` / `Nat.frequently_atTop_iff_infinite`.
Sorry-free.

## Stub inventory

**262 stubs** (`Pg182Frame/Obligations.lean`, `sorry` = honest inventory;
C0 lane discharges against the romyar1 kernel instantiation):

- 5 cap: `integral_le_cap_denominator_lower/_upper`, `..._base_lower`,
  `..._enlargement_lower`, `..._tail_upper`
- 60: `integral_le_outer_root_000..059`
- 60: `integral_le_outer_face_000..059`
- 137: `integral_le_inner_mass_000..136`

Each is a parameterized statement over the abstract mirrors `TrialSource182` /
`TrialCerts182` whose fields are documented 1:1 with the frozen quantities
(`trialSourceOuterRoot` etc., SourceBounds182.lean:138-142; exact rationals in
SourceData182.lean / TrialData182.lean). Landing: `hobs` is assembled from the
262 discharged theorems; each name is a stable handle.

## 186-parity headline

Same skeleton — two verbatim Kloosterman hypotheses (Katz 4.1.1, FKM Prop 2,
credited to openai/PrimeGaps186 axioms :147/:159) + a numeric block. 182 adds
`TypeIIILocalFourier` + the rank-4 companion and carries 262 vs 186's 152
numerics; 186's numerics are a bundled axiom where 182 uses named obligations.
Full table: `PARITY.md`.

## AXCHECK footprint (receipt/axcheck.txt)

```
'Pg182Frame.h1_182_of' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'Pg182Frame.frequently_gap182_of_infinite_consecutive_pairs' depends on axioms:
  [propext, Classical.choice, Quot.sound]
```

No `sorryAx` in the frame theorem: the 262 stubs are quarantined in
Obligations.lean and reach `h1_182_of` only through explicit hypothesis
arguments, so the frame theorem's Lean-level footprint is the standard three
axioms. `Deduction182` is a HYPOTHESIS mirroring the kernel-checked endpoint
at romyar1/prime-gaps-lean @ b77bf175bded (formal/PrimeGaps182Analytic.lean:67-74;
their own receipt: 918 modules / 6,128 declarations, standard axioms only,
verified 3 Oct 2026) — not an `axiom` here. Mathematical content therefore
rides entirely on: h1, h2, hK4, h3, hd, hobs — every one explicit in the
signature.

## Files

`Pg182Frame/Hypotheses.lean` (inputs a, b, hK4, c — verbatim + cited),
`Pg182Frame/Obligations.lean` (262 stubs + mirrors),
`Pg182Frame/Frame.lean` (bridge + conversion + frame theorem),
`Pg182Frame/Conclusion.lean` (Bound restatement), `PARITY.md`,
`receipt/axcheck.txt`.
