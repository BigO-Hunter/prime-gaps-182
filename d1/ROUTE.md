# ROUTE.md — Lane D1: the discrete-law majorant (what closed, what remains)

Lane: the 182 gate's one multi-week item — the algorithm-to-integral
correspondence: the 393,216-cell discrete law as a provable majorant of the
fragment-law pushforward. Repo dir `d1/`, toolchain v4.34.1 + Mathlib
`d13f23b7` (git-pinned).

## What is PROVED in Lean (all green, axcheck = {propext, Classical.choice, Quot.sound})

| File | Theorem | Content |
|---|---|---|
| `Pg182D1/Law.lean` | — | Verbatim vendored law (weightedEmpirical, finitePoissonLaw, cappedDyadicIntensity, finiteFragments, fragmentLaw) + C0 trial constants + the floor laws for `trialCellIndex` |
| `Pg182D1/Support.lean` | — | Verbatim vendor helper slice: normalized finitePoissonLaw integral, poisson identity, dyadic band sums, a.e. finiteness, probability instances |
| `Pg182D1/D1Cell.lean` | `cell_probability_le` | **D1-CELL**: μ{cell = n} ≤ exp(s·(n+1)·mesh) · E[e^{-s·mass}] for every cell n and every s ≥ 0 (Markov on e^{-s·mass} over the floor-law cell event) |
| `Pg182D1/D1Mgf.lean` | `mass_finiteFragments` | mass of finiteFragments = truncated total band mass, pointwise in BOTH convergence branches (no a.e. needed) |
| `Pg182D1/D1Mgf.lean` | `mgf_fragmentLaw_le_finset` | **D1-MGF**: for every finite set S of dyadic bands, E_full[e^{-s·mass}] ≤ ∏_{k∈S} E_k[e^{-s·mass}] — the full fragment law's MGF is bounded by ANY finite-band product |

## The route that closed

**Exp-sandwich (Chernoff) + independence + floor law.** The proof of the
per-cell majorant composes:

1. *Floor law* (elementary): `{trialCellIndex X = n} ⊆ {mass < (n+1)·mesh}`.
2. *Markov* (D1Cell): on that event e^{-s·mass} ≥ e^{-s·(n+1)·mesh}, so
   μ{cell = n} ≤ e^{s(n+1)mesh} · E[e^{-s·mass}].
3. *MGF bound* (D1Mgf): different bands are independent under the infinite
   product (iIndepFun_infinitePi), the total band mass dominates every
   finite partial band sum, so E[e^{-s·total}] ≤ ∏_{k∈S} E_k[e^{-s·mass}]
   pointwise-a.e. — exactly the shape the frozen program computes (per-band).

Every S gives a valid, computable, decreasing envelope; S → full support
reproduces the exact exp-sandwich E[e^{-s·mass}] ≤ exp(∫_{(0,ζ]}(e^{-su}-1)/u
du) — the vendor's `integral_exp_neg_mass_fragmentLaw` (proved there as an
equality via EReal machinery; the ≤ direction here is elementary and is all
D1 needs).

## Why this is the D1 shape

The audit named D1 as "the 393,216-cell discrete law as a provable majorant
of the fragment-law pushforward". The proved chain IS that majorization with
an explicitly computable per-cell envelope. What it reduces the remaining
trust to is now EXPLICIT and machine-checkable:

- **D1-data (the named remaining gap)**: per-cell, the frozen program's
  per-run masses `p^frozen_c` dominate the proved envelope class — i.e.
  `p^frozen_c ≥ exp(s(c+1)mesh) · ∏_{k∈S} E_k[e^{-s·mass}]` for the frozen
  S and optimal s (each a single ℚ inequality per cell once the rational
  bound on the per-band MGFs is fixed; the per-band closed form
  E_k = exp(-b_k), b_k = ∫_{band_k∩(0,ζ]}(1-e^{-su})/u, plus the band-sum
  identity Σ_k b_k = ∫_{(0,ζ]} — the vendor's `sum_cappedDyadicIntensity`
  + `lintegral_fragment_sum` templates, mirrored but not yet needed in Lean).
- **D3 (as in the audit)**: per-run suprema of the integrand (the frozen
  affine-prefix data) dominate the integrand per coarse run.

## Explicitly NOT closed this session (honest inventory)

1. The per-band closed-form MGF in Lean (Poisson-series computation; the
   structural bound above is what the chain consumes — the closed form is a
   numeric refinement, vendor templates at PrimeGaps186.lean:3436-3520).
2. The 38-dim sum-level lift (D1Sum) — file drafted at `wip/D1Sum.lean`,
   blocked on a measurable-sum lemma (Measurable.sum for ℕ/ℝ-valued finset
   sums) and paren-disciplined restatement; the plan is in the file.
3. The coarse-run partition engine (D1Engine) — file drafted at
   `wip/D1Engine.lean`; the remaining errors are mechanical (indicator
   const-lemma naming, one linarith side-condition). Both WIP files are
   excluded from the build and are the next session's starting point.
4. hEnv77 discharge — gated on 2+3 (the interface is documented in
   THE_LEMMAS_FOR_C0.md).

## Class coverage

The proved chain covers the **slope-0 rankTwo class** structure (row 77's
class, the 211 exact-Q leaves' shape) at the per-coordinate + MGF level.
The exp-tilt rows (94 .low) additionally need the exp-sandwich on the
witness factor — same Markov skeleton, different integrand.
