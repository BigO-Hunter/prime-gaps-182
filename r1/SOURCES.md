# SOURCES — exact citations for the 182 row

## The 3-paper bundle (fetched 2026-11-06)

`https://www.math.ucla.edu/~sharifi/AI/prime_gaps_182_expository_bundle.pdf`
(132 pp., PDF 2.0, 17,271,479 bytes; SHA256 of our copy: see git log). All three papers:
"GPT-6 Astra (OpenAI), prompted by Romyar Sharifi", dated 18 September 2026 (papers 2–3 note:
original version 4 September 2026; 11 September version expanded citations; this edition
"incorporates corrections to the Type III result and adds its formal verification as a
derivation from explicitly stated general published-theorem hypotheses"; repo references
updated 3 October 2026).

1. **"A fixed-profile proof for prime gaps of at most 182"** — bundle pp. 1–~52.
   Main paper. Theorem 1.2: DHL[39,2], hence H₁ ≤ 182. §13 "Formal verification" (pp. ~43–44)
   enumerates the explicit inputs: 262 physical integral inequalities (5 cap + 60 outer-root +
   60 outer-face + 137 inner-face, normalizations of its (8.8)); the established finite-field
   estimates; the local Fourier proposition. Margin: remaining surplus > 0.000065213759.
   Text extracted to `text/bundle.txt` (paper 1 starts line 1).
2. **"Incidence operators and intervals containing many primes"** — Type II companion
   (bundle from line ~2712). Incidence operator → circulant with rank-4 hyper-Kloosterman
   eigenvalues; Type II condition γ > 3/10 + ω/2 + δ; with Type III + Harman minorant gives
   H_m ≪ exp(3.7877m). NOT an input of the single-gap 182 endpoint.
3. **"Kloosterman correlations with finitely many exceptional Fourier frequencies"** —
   Type III companion (bundle from line ~4720). Proves the local Fourier proposition
   [11, Prop 3.1]: four-cycle of rank-3 Kloosterman correlations; exceptional Fourier set of
   bounded cardinality (distinct indices) / bounded-degree polynomial zero set (repeated);
   sheaf facts: Katz GKM, Laumon (IHÉS 65 (1987) 131–210), BBD Faisceaux pervers
   (Astérisque 100 (1982)), Sawin–Forey–Fresán–Kowalski, Quantitative sheaf theory,
   JAMS 36 (2023) 653–726.

## Lean development

`https://github.com/romyar1/prime-gaps-lean` — cloned 2026-11-06 into `lean/prime-gaps-lean`.
Paper 1 pins commit **b77bf175bded**. Key modules:
- `formal/PrimeGaps182Analytic.lean` — endpoint: `infinite_consecutive_prime_pairs182_of_local_inputs`
  (hypotheses: `PhysicalSourceBounds182`, `PublicPrimeLocalBounds182`,
  `AllIncidenceRankFourBounds`, `0 ≤ C`, `LocalFourierHypothesis C D p₀`).
- `formal/SourceBounds182.lean` — the 262 stated over actual fragment-law integrals.
- `formal/TrialData182.lean`, `formal/SourceData182.lean` — exact rational constants/targets.
- `formal/SourceKernels182.lean` — integrand definitions (3 kernel kinds, face weights).
- `formal/TypeIIILocal.lean` — Type III finite sums + `HasFiniteExceptionalTypeIIIInput`.
- `docs/assumptions.md`, `STATUS.md` — premise ledger; 3 Oct 2026 build receipt
  (`PASS_CONDITIONAL_DEVELOPMENT_AND_TYPE_III_SUPPORT`, 918 modules, 6,128 declarations).
- `research/numerical_182/` — external verification package; release
  `external-numerics-20260909` (ZIP 244,843,318 B, SHA256 2960729e…f3b);
  `evidence/verification.json`: `PASS_COMPLETE_EXTERNAL_NUMERICAL_RECOMPUTATION`,
  262/262 targets, 14 stages, 14 audits, 4 negative controls, 2026-09-09T07:57Z,
  `lean_numerical_premises_discharged: 0`, `type_iii_proved: false`.

## Cited inputs for the 3 finite-field estimates

- [Katz] N. M. Katz, *Gauss Sums, Kloosterman Sums, and Monodromy Groups*, Annals of Math.
  Studies 116, Princeton UP 1988 — Theorem 4.1.1(1)–(2) (raw n-rank bound n·p^((n−1)/2);
  items 1 and 3 of the premise set). Full text: web.math.princeton.edu/~nmk/Katz-GKM.pdf.
- [FKM] É. Fouvry, E. Kowalski, P. Michel, "The Friedlander–Iwaniec character sum"
  (14 June 2013 version) — Proposition 2 (item 2, the two-Kloosterman correlation).
- 186 baseline cross-ref: OpenAI, "Improved short gaps between primes", 30 Aug 2026
  (+ its Lemma A.4), github.com/openai/PrimeGaps186; Stadlmann 240: arXiv:2608.31126.
- Tuple: MIT prime gaps project, admissible 39-tuple of diameter 182 (online table [16]).

## Extraction method

Bundle PDF SHA256 (our copy):
`5362e977880af92a73a79b411a9c66daf0b93af4ec0ed6bec320090386f4b881`
(17,271,479 bytes; hashed, never read as text). PDF → text via `pdftotext -layout`
(poppler) to `text/bundle.txt` (6,902 lines). Lean sources read as text (plain text).
`lean/prime-gaps-lean` = full git clone, kept out of this repo's index; re-clone with
`git clone https://github.com/romyar1/prime-gaps-lean` (paper pins commit b77bf175bded).
pdfs/prime_gaps_182_expository_bundle.pdf 17,271,479 bytes — hashed above, never read as text.
lean/ = git clone of romyar1/prime-gaps-lean (2026-11-06, pinned in paper as b77bf175bded).
text/bundle.txt = pdftotext -layout extraction of the 3-paper bundle.
