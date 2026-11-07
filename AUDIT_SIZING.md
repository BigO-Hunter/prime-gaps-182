# AUDIT_SIZING.md — the code↔integral correspondence audit (what remains)

The 262 premises say "the Lean-defined integral is ≤ the frozen ℚ literal".
The frozen programs compute rigorous enclosures of *something*. The remaining
ordinary-math trust is exactly: **the something equals (majorizes) the
Lean-defined integral.** Sizing that audit:

## What a reviewer must check today (per METHOD.md + the receipts)

1. **Law discretization.** Each coordinate's continuous Poisson fragment law
   (`PrimeGap186.fragmentLaw`, ℤ-indexed dyadic bands, intensity 1/u on
   (2^k,2^{k+1}]∩(0,ζ]) is replaced in the programs by a 393,216-cell
   discretization (`prepare_fine_source_affines.py`, blocks of 48, "signed
   marginal prefixes"). The reviewer must see: per-cell mass, profile² law,
   and the retained-index accounting reproduce the Lean law's pushforward
   through `trialCellIndex` — including the no-erased-coordinate and
   "exactly k−1 retained profile² laws" claims in each receipt's
   `normalization` field.
2. **Kernel correspondence.** The rankTwo kernel (count conditions on
   `N_X`), the exp tilt (low rows), and the C(n,3) (high rows) must match the
   Lean `trialSourceUnmasked` branch-for-branch, with the cap/mask/shell
   geometry (`TrialShellAllowed`, `TrialCapAllowed`, domain pieces) matching
   `TrialSourceDomain` + `trialMask`. The receipts' 328,936 geometry checks
   support this; they are self-audits, not Lean proofs.
3. **Envelope contraction validity.** Every bound inside the payloads
   (retained-maximum ranges, affine-prefix compositions, directed bounds)
   must dominate the true quantity — signed-arithmetic direction discipline.
4. **Normalization identity.** `source.mass·k·h_fine/Z_fine`, the rho/coefficient
   scalings, and the D_lower normalizations match
   `trialSourceInnerMass`/`trialSourceOuterRoot`/`trialSourceOuterFace`
   definitional forms (item 5 of METHOD.md).
5. **Count-measure semantics.** `physicalSourceCountMeasure` = the atom
   counting measure; the q-window integrals contract to finite sums over
   fragment configurations consistently with the Poisson structure.

## What closing it in Lean would take (the actual machine, next lanes)

- B1/B3 as in BRIDGES.lean (done here) + **B2** Fubini/marginal symmetry.
- **D1: per-coordinate law identity.** A Lean proof that the 393,216-cell
  discrete law used by the programs is a majorant of the true pushforward of
  `trialPhysicalMeasure` through the cell map — the hard core. Requires
  unfolding `fragmentLaw` (Poisson per dyadic band) and bounding per-cell
  Poisson probabilities by rational envelope data (exp-sandwich class).
- **D2: kernel-to-sum.** Conditional on D1, the rankTwo kernel integral
  becomes a finite count-sum (B3 already gives its domination).
- **D3: prefix-sum identities.** The 20 affine arrays' exact agreement with
  per-cell envelope constants — mechanical once D1 holds.

Estimate: D1 is the multi-week item; D2/D3 are days each once D1 stands.
Until then the frozen payloads remain computational evidence (as the repo's
README itself says), and the C0 certificate isolates the gap as the single
hypothesis `hEnv77` with exact required strength `faceUpper·NLB/39`.
