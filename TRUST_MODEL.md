# TRUST_MODEL.md

## What a user of the final certificate must believe

1. **The Lean kernel + Mathlib's axioms** (standard: propext/Classical.choice/Quot.sound
   only — asserted via `#print axioms` on every artifact).
2. **The formalized bridge lemmas** (B1–B3 + exp sandwich): ~3–8 theorems of ordinary
   Mathlib-style measure theory. This is the ONLY mathematical surface — finite, named,
   reviewable, reusable. It is precisely the gap the upstream repo flags as
   "algorithm-to-integral ... ordinary mathematics, not newly kernel-checked"; we close
   exactly that gap and nothing wider.
3. **Nothing else.** Not python-flint (cross-checker only — its agreement with Lean's
   `decide` is redundancy, not trust), not the upstream JSON evidence, not the external
   244 MB verification package (we keep it as provenance), not the run tables' provenance
   beyond the literals hashed in git.

## Policy compliance (board)

- Kernel-only evaluation: `decide` / `norm_num`; **no `native_decide`**, no `axiom`,
  no `sorry` in the certified lane; `maxRecDepth` raised after imports only.
- Unconditional intent honored honestly: all *numerical* premises become theorems.
  The 3 finite-field estimates and Type III remain premises because they require
  mathematics that does not exist in any proof assistant today (étale cohomology /
  Deligne purity / the FKM correlation bound; the Type III derivation). Any claim
  beyond "conditional on Katz Thm 4.1.1 + FKM Prop 2 + Type III" would be false and
  is not made.
- Data immutability: certificates freeze the upstream literals; the cross-checker
  recomputes them independently and disagreement halts the pipeline (no hand-tuning).

## Threat notes

- The upstream numerics were validated externally (14 audits, 4 negative controls) but
  their *conclusions* are re-derived here from the frozen literals — upstream process
  quality is nice-to-have, not load-bearing.
- Exp endpoint slack vs row margins: margins are ~10^-75 relative; our bounds target
  ~10^-80. If any row fails, that is a finding, not an obstacle — it goes to R1/the board.
