# PREMISE MAP — the 182 row (DHL[39,2], H₁ ≤ 182)

Source: romyar1/prime-gaps-lean @ b77bf175bded (docs/assumptions.md, formal/SourceBounds182.lean,
formal/TrialData182.lean, formal/SourceData182.lean) + the UCLA 3-paper bundle.
Endpoint theorem: `PrimeGap182.infinite_consecutive_prime_pairs182_of_local_inputs`
(formal/PrimeGaps182Analytic.lean) takes exactly FOUR explicit premises; there are zero `axiom`
declarations and zero `sorry`s in `formal/` — every deduction is kernel-checked, premises are
hypotheses.

## P1. `PhysicalSourceBounds182` — the 262 integral inequalities (class a)

| Field | Inequality (rational constants cast to ℝ) | Count |
|---|---|---:|
| cap.denominator_lower | `trialDenominatorLower ≤ trialSquareIntegral` | 1 |
| cap.denominator_upper | `trialSquareIntegral ≤ trialDenominatorUpper` | 1 |
| cap.base_lower | `trialJ0Lower ≤ trialBaseIntegral` | 1 |
| cap.enlargement_lower | `trialJPlusLower ≤ trialEnlargementIntegral` | 1 |
| cap.tail_upper | `trialTailIntegral ≤ trialTailUpper` | 1 |
| outerRoot | `trialSourceOuterRoot j ≤ (trialOuterCertificates j).rootUpper`, ∀ j : Fin 60 | 60 |
| outerFace | `trialSourceOuterFace j ≤ (trialOuterCertificates j).faceUpper`, ∀ j : Fin 60 | 60 |
| innerMass | `trialSourceInnerMass j ≤ (trialInnerCertificates j).faceUpper`, ∀ j : Fin 137 | 137 |
| **Total** | 5 cap + 120 outer + 137 inner | **262** |

Exact rational targets confirmed in TrialData182.lean (e.g.
`trialDenominatorLower = 9900316613656518642800593/664613997892457936451903530140172288`)
and SourceData182.lean (197 records with rootUpper/faceUpper rationals).

**Integrand shape (all 262):** integrals of explicit, bounded, piecewise-defined real functions
over products of "fragment-law" configuration spaces — X : Fin 39 (or 38) → FiniteMeasure ℝ
against a fixed product measure. Integrands are compositions of:
- `trialSourceKernel cover X`: piecewise (3 kinds: `.low` = exp of an affine form in total/small
  mass; `.rankTwo` = indicator of a rank condition integrated over one real variable;
  `.high` = C(n,3) of a cell count), masked to a domain `TrialSourceDomain` (cell-sum window +
  cap condition), i.e. indicators + exp-affine + polynomial pieces;
- `trialSourceCountMultiplier`, 3-branch step function `trialSourceFaceWeight` (1 /
  enlargement / εUpper by cell sum ≤ 355047 / ≤ 359896 / else);
- `trialStepFunction X²` or `trialMarginal i Y²` (the squared sieve profile).
Fixed discretization: 393,216 grid intervals, 393,177 retained radial indices, 726 independent
spline coefficients; bins spanned by explicit integer ranges (e.g. 7310..7843).
**All targets and all constants are exact rationals. Smoothness:** piecewise smooth, finitely
many breakpoint hypersurfaces (cell boundaries). Verified integrable in Lean
(`integrable_trialSourceOuterRoot/Face/InnerMass`, boundedness theorems in SourceBounds182.lean).

## P2. `PublicPrimeLocalBounds182` + `AllIncidenceRankFourBounds` — the 3 finite-field estimates (class b)

Write eₚ for the nontrivial additive character; required for EVERY prime p (incl. 2), all
nonzero parameters:
1. `|Kl₃(c)| = |p⁻¹ Σ_{u,v≠0} eₚ(u+v+c/(uv))| ≤ 3` for c ≠ 0.
   → Katz, GKM Thm 4.1.1(1)–(2): raw rank-3 bound 3p, divided by p. (Kloosterman sheaf rank,
   trace formula, Deligne purity.)
2. `|Σ_{t≠0,−1} Kl₂,raw(A/t)·Kl₂,raw(B/(t+1))| ≤ 8p√p` for A,B ≠ 0 (no A≠B assumption).
   → Fouvry–Kowalski–Michel, "The Friedlander–Iwaniec character sum", Prop 2 (×√p per
   normalized factor); cf. 186-baseline Lemma A.4.
3. `|Σ_{u,v,w≠0} eₚ(u+v+w+c/(uvw))| ≤ 4p√p` for c ≠ 0.
   → rank-4, weight-3 specialization of the same Katz theorem; a SEPARATE premise in Lean
   (`IncidenceRankFour.lean` quantified by `AllIncidenceRankFourBounds` in
   IncidenceSquarefree.lean), not derived from items 1–2 in the code.

Exact Lean statements: `PublicPrimeLocalBounds182` (PrimeSourcePublic182.lean) and
`AllIncidenceRankFourBounds` (IncidenceSquarefree.lean) — confirmed in the explicit-premises log.

## P3. Type III `LocalFourierHypothesis C D p₀` — the local Fourier proposition (class c)

Constants C ≥ 0, D, p₀ uniform over ALL primes p > p₀ and all nonzero α,m,m′,n,n′; for the
four-cycle W's unnormalized 2-variable Fourier transform Ŵ:
- distinct row/col indices: ∃ Z ⊆ F_p², #Z ≤ D, with |Ŵ(h,k)| ≤ C·p³(1 + √p·1_Z(h,k));
- repeated index: ∃ nonzero P ∈ F_p[x], deg ≤ D, with |Ŵ| ≤ C·p³(1 + √p·1_{P=0} + 1_{(0,0)}).

Proven as [11, Prop 3.1] of the Type III companion paper ("Kloosterman correlations with
finitely many exceptional Fourier frequencies") via Katz GKM sheaves, Laumon Fourier transform,
BBD perverse theory, Deligne purity (Weil II), and Sawin–Forey–Fresán–Kowalski quantitative
sheaf theory. In Lean: the Sept 18 derivation
(`TypeIIICoherentUniformApplicationsFromGeneralStandardTheory03.lean`, `computedTypeIIIInput`)
constructs the exact statement from explicitly stated "common general-theorem interfaces"
(étale/derived/perverse categories, Kloosterman objects) — the existence and joint continuous-ℓ-adic
interpretation of that one common theory is the remaining external input. `type_iii_proved: false`
in the numerical receipt; STATUS.md: `PASS_CONDITIONAL_DEVELOPMENT_AND_TYPE_III_SUPPORT` (918
modules, 6,128 declarations, 3 Oct 2026).

## Counts by class

| Class | Count | Items |
|---|---:|---|
| (a) explicit integral + rational bound | **262** | P1 (5+60+60+137) |
| (b) finite-field sum over stated finite set | **3** | P2 items 1–3 (∀p quantifier) |
| (c) analytic, needs genuine sheaf theory | **1** | P3 (Type III proposition) |
| (d) other | 0 | — |

Grand total of explicit endpoint premises: **262 + 3 + 1**. Note P3 is outside the "262+3" of
the lane description but IS a hypothesis of the posted endpoint theorem.

Downstream (not premises): the admissible 39-tuple of diameter 182 is from the MIT prime-gaps
tables [16], admissibility+diameter checked by finite computation; the final DHL[39,2] surplus
is fixed and explicit (> 0.000065213759) — the margins are frozen, no re-optimization needed.
