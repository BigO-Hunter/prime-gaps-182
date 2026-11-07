# PARITY — the 186 frame vs the 182 frame

Both projects axiomatize the same two finite-field estimates and carry their
numerics as an explicit block; 182 adds the Type III local Fourier proposition
and the rank-4 companion estimate in exchange for the tighter bound.

## OpenAI PrimeGaps186 — 3 axioms (Apache-2.0)

Source: `vendor/primegaps186/PrimeGaps186.lean` (unchanged vendored copy in
romyar1/prime-gaps-lean @ b77bf175bded):

| # | Axiom | File:line | Content |
|---|-------|-----------|---------|
| 1 | `PrimeGap186.kloosterman3_bound` | :147-151 | normalized rank-3 hyper-Kloosterman ≤ 3 (Katz GKM Thm 4.1.1(1)-(2), p. 49) |
| 2 | `PrimeGap186.kloosterman2_correlation_bound` | :159-168 | Kl₂ correlation ≤ 8p√p over t ≠ 0, −1 (FKM, Friedlander-Iwaniec sum, Prop 2) |
| 3 | `PrimeGap186.physical_integral_bounds` | :1055+ | **152 numerics**: 104 outer + 45 inner physical integral bounds + 3 cap bounds (Tables 2.1-2.6, Eq. 2.33) |

Target: `PrimeGap186.h_1_le_186`-style endpoints, DHL[40,2], 40-tuple of
diameter 186.

## This frame (pg182-frame) — 3 named inputs + 1 companion + 262 obligations

| # | Input | Source (exact form) | Role vs 186 |
|---|-------|--------------------|-------------|
| a | `Kloosterman3Bound` | 186 axiom #1, **verbatim** (Hypotheses.lean, credited) | same |
| b | `Kloosterman2CorrelationBound` | 186 axiom #2, **verbatim** (Hypotheses.lean, credited) | same |
| hK4 | `IncidenceRankFourBounds182` | romyar1 `IncidenceRankFourBound` (IncidenceRankFour.lean:29) quantified as `AllIncidenceRankFourBounds` (IncidenceSquarefree.lean:19-20) | **182-only**: rank-4 weight-3 specialization of the same Katz theorem; a separate premise in romyar1's code, not derivable from (a)+(b) there |
| c | `TypeIIILocalFourier` | romyar1 `HasFiniteExceptionalTypeIIIInput` (TypeIIILocal.lean:158-159), full body unfolded | **182-only**: the "common adic theory" input; replaces nothing in 186 |
| — | 262 obligations (`integral_le_*`, stubs) | romyar1 `PhysicalSourceBounds182` (SourceBounds182.lean:138-142): 5 cap + 60 outerRoot + 60 outerFace + 137 innerMass | split of 186's axiom #3 role into named, C0-dischargeable theorems; **262 vs 152** numerics |

Target: `BigOSpeedrun.PrimeGaps.Bound 182` (verifier Statement.lean @ cb829226),
DHL[39,2], 39-tuple of diameter 182 (MIT prime-gaps tables; admissibility fixed
downstream, not a premise here).

## The rhyme and the deltas

- **Same skeleton**: two verbatim Kloosterman hypotheses (Katz + FKM) + one
  numeric block. The DZQ conditional-frame shape
  (`theorem ... (hA : ...) (hB : ...) : conclusion`) is identical.
- **Where 182 needs more**: (i) `TypeIIILocalFourier` — the genuine analytic
  input 186 does not carry; (ii) `IncidenceRankFourBounds182` — present in
  186 only implicitly inside its proved development (186 has no separate
  rank-4 premise; romyar1's incidence route does); (iii) 262 numerics vs 152.
- **Where 186 needs more**: nothing structural — its third axiom bundles its
  152 numerics; the 182 frame prefers named obligations over a bundled axiom
  so the C0 row machine can discharge them one at a time.
- **Net**: the 182 frame is strictly heavier as an assumption set (that is the
  price of 182 < 186 with a 39-tuple), but every added piece is explicit and
  cited.
