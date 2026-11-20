# FEASIBILITY FIRST CUT — what verifying each class actually requires

## Class (a): the 262 integral inequalities — COMPUTATIONAL (buildable now)

**What verification requires:** rigorous enclosures of explicitly-defined piecewise-smooth
integrands (exp-of-affine, indicators on cell sums, C(n,3) counts, 3-branch step face weights,
squared profile marginals) over fixed discretized domains (393,216 grid intervals; 726 spline
coefficients; finite radial bin ranges), compared against exact rational bounds.

**Status:** already done EXTERNALLY — frozen Python/NumPy/python-flint (FLINT 3.6.0, interval
arithmetic) programs; 2026-09-09 full re-run: 262/262 rational target comparisons PASS, 14
implementation audits, 4 deliberate-rejection controls, 1h44m wall on 3 workers, receipt
`PASS_COMPLETE_EXTERNAL_NUMERICAL_RECOMPUTATION`. Smoothness/domain/error-budget questions are
therefore answered in practice; quadrature error is inside the interval enclosures.

**What remains to make it a certificate:**
1. **Math review of the algorithm-to-integral correspondence** (the package itself flags this:
   "ordinary mathematics, not newly kernel-checked Lean endpoint proofs") — confirm the frozen
   programs enclose exactly the Lean-defined integrals, with sound discretization + tail
   envelopes (the face-weight epsilon branch). Human-scale: bounded, reviewable.
2. **Bridge to the Lean kernel** so `PhysicalSourceBounds182` has a proof term instead of being
   a hypothesis. Options: (i) verified certificate checker in Lean over the JSON records
   (`inputs/source_certificates/` are NOT kernel-read today); (ii) interval arithmetic in Lean
   re-deriving the 262 enclosures; (iii) proof-carrying numerics (FLINT-computed rational
   enclosures with justification terms). Feasible engineering, medium lift; 0/262 discharged today.

## Class (b): the 3 finite-field estimates — COMPUTABLE PER PRIME, ESTABLISHED FOR ∀p

Per prime p these are finite sums over F_p: brute-force verification for p ≤ P₀ is trivial
(microseconds-to-seconds each). BUT the premises quantify over EVERY prime (the incidence sums
run over all p), so pure computation cannot discharge them. They are, however, **established
published theorems**, not open analysis:
- Items 1, 3: Katz GKM Thm 4.1.1 (Kloosterman sheaf rank + trace formula + Deligne purity).
- Item 2: FKM Prop 2 (continuation/monodromy-theoretic correlation bound).
**Certificate routes:** (i) accept as cited unconditional literature (same epistemic tier as
Bombieri–Vinogradov inside the 246/186 records — the papers already cite them exactly);
(ii) computational for p ≤ P₀ + cited theorems for p > P₀; (iii) full formalization — blocked
today by the absence of Deligne-purity-scale étale machinery in mathlib (huge, not required if
(i) is acceptable to the board).

## Class (c): Type III local Fourier proposition — ANALYTIC, but PROVEN in the bundle

Genuinely-theoretic: Katz GKM + Laumon Fourier transform + BBD perverse sheaves + Deligne
purity/Weil II + quantitative sheaf theory (Sawin–Forey–Fresán–Kowalski). NOT computable by
finite means (uniformity in ALL primes is the content). Status: proven in the Type III
companion paper [11, Prop 3.1]; AND derived in Lean (Sept 18, `computedTypeIIIInput`) from
explicitly stated general-theorem interfaces — the residual external input is the existence
and joint ℓ-adic interpretation of that ONE common theory (standard mathematics, unformalized).
So: not open analysis (no new math appears missing), but formalizing is Deligne-scheme-scale.
**Certificate route:** human expert audit of the companion paper's §4–6 sheaf argument, or
formalize the interface instantiation. The proposition's constants (C, D, p₀) are existentially
quantified — no explicit witness is required by the endpoint, which matches the "established
estimate" tier of the 246/186 records.

## Verdict

- 262/265 explicit premises: **computational-checkable — in fact already externally checked**;
  the missing piece is only the Lean-side bridge + code-integral review.
- 3: **established-theory** (literature-cited, per-prime computable spot-checks trivial).
- 1 (Type III): **proven-in-manuscript analytic residue**, derivation already reduced in Lean to
  one interface-existence input.
- **No premise is open analysis.** A full certificate for 182 is a BUILD, contingent on (a) the
  Lean↔numerics bridge, (b) the board's tier policy for published-theorem inputs, (c) an expert
  read of the Type III companion's sheaf argument.
