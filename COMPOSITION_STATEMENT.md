# COMPOSITION_STATEMENT.md — the top-level theorem, hypothesis by hypothesis

This is the artifact to read first. It states, in order, exactly what
`PrimeGap182D2.h1_182_of` (`COMPOSITION.lean`) assumes and what it delivers. The Lean text below
is verbatim from `COMPOSITION.lean`; every hypothesis is then documented in the table.

## 1. The conclusion

```lean
def BigOSpeedrun.PrimeGaps.Bound (B : ℕ) : Prop :=            -- Pg182Frame/Conclusion.lean, verbatim
  ∃ᶠ m in Filter.atTop, Nat.nth Nat.Prime (m + 1) - Nat.nth Nat.Prime m ≤ B
```

Infinitely often (along the sequence of primes), consecutive primes differ by at most `B`. The
package delivers `Bound 182`.

## 2. The theorem

```lean
theorem h1_182_of (h1 : Pg182Frame.Kloosterman3Bound)
    (h2 : Pg182Frame.Kloosterman2CorrelationBound)
    (hK4 : Pg182Frame.IncidenceRankFourBounds182)
    (h3 : Pg182Frame.TypeIIILocalFourier)
    (hd : Pg182Frame.Deduction182)
    (S : Pg182Frame.TrialSource182)
    -- the 5 cap rows and the 120 outer rows: frozen source data against the transcribed table
    (hcap : Pg182Frame.CapBounds182 S)
    (hroot : ∀ j : Fin 60, S.outerRoot j ≤ (TableData.outerRootUpper j : ℝ))
    (hface : ∀ j : Fin 60, S.outerFace j ≤ (TableData.outerFaceUpper j : ℝ))
    -- the 137 inner rows: Layer I (envelope) against the proved cell bound
    (cellOf : Fin 137 → ℕ) (envSup : Fin 137 → ℝ)
    (henv : ∀ j : Fin 137, 0 ≤ envSup j)
    (hrow : ∀ j : Fin 137, S.innerMass j ≤ envSup j * (convPow fragmentMassLaw 38
      (Set.Ioc ((cellOf j : ℝ) * mesh) ((cellOf j : ℝ) * mesh + mesh))).toReal)
    (hmargin : ∀ j : Fin 137, envSup j * hq ≤ (TableData.innerFaceUpper j : ℝ)) :
    BigOSpeedrun.PrimeGaps.Bound 182
```

Read as a sentence: *given* the three deep Kloosterman estimates (h1, h2, hK4), the Type III
Fourier proposition (h3), the endpoint deduction (hd), a source record `S` satisfying the five cap
inequalities (hcap), the 120 outer inequalities against the transcribed certificate table
(hroot, hface), and, for each of the 137 inner rows, a cell index, a nonnegative integrand
envelope, and the two inequalities hrow + hmargin — *then* infinitely many consecutive prime
pairs have gap ≤ 182.

### The margin-free form

```lean
theorem h1_182_of_certEnvelope (h1 h2 hK4 h3 hd S hcap hroot hface as above)
    (cellOf : Fin 137 → ℕ)
    (hrow : ∀ j : Fin 137, S.innerMass j ≤ certEnvelope j * (convPow fragmentMassLaw 38
      (Set.Ioc ((cellOf j : ℝ) * mesh) ((cellOf j : ℝ) * mesh + mesh))).toReal) :
    BigOSpeedrun.PrimeGaps.Bound 182
```

Same theorem with `hmargin` discharged: taking the certificate-implied envelope
`certEnvelope j = TableData.innerFaceUpper j / hq` makes the margin an identity
(`certEnvelope_margin`), so the row inequality `hrow` is the single Layer-I input.

## 3. The hypotheses, typed and documented

### The deep analytic inputs (each `Prop`, defined in `pg182-frame/Pg182Frame/Hypotheses.lean`)

| name | statement | provenance | status |
|---|---|---|---|
| `h1 : Kloosterman3Bound` | `∀ p prime, ∀ c : ZMod p, c ≠ 0 → ‖normalizedKloosterman3 p c‖ ≤ 3` — the normalized rank-3 Kloosterman sum is bounded by 3 | Katz, *Gauss Sums, Kloosterman Sums, and Monodromy Groups*, Thm 4.1.1(1)–(2), p. 49 (Deligne purity); verbatim transcription of `axiom PrimeGap186.kloosterman3_bound` | **INSTANTIATE-PENDING** — the Lean/Stacks Weil machinery gives the engine, the last mile (`‖Kl₃‖ ≤ 3` from rank + weight-2 purity) is a proved axiom-clean theorem (`KloostermanTraceBound.kloosterman_bound`); three packaging obligations remain; axiom gate pending |
| `h2 : Kloosterman2CorrelationBound` | `∀ p prime, A B ≠ 0 → ‖Σ_t Kl₂(A/t)·Kl₂(B/(t+1))‖ ≤ 8·p·√p` — the two-Kloosterman correlation bound | Fouvry–Kowalski–Michel, "The Friedlander–Iwaniec character sum", Prop 2; verbatim transcription of `axiom PrimeGap186.kloosterman2_correlation_bound` | **INSTANTIATE-PENDING** — cohomological core rides the same packaging; the sharp constant's p-adic refinement is separate custom work |
| `hK4 : IncidenceRankFourBounds182` | `∀ p prime, ∀ c ≠ 0, ‖rawKloosterman4 p c‖ ≤ 4·p·√p` — the rank-four (weight-3) companion, a premise *separate* from h1 in the endpoint development | mirror of `IncidenceRankFourBound` (romyar1 `formal/IncidenceRankFour.lean:29-31`), quantified as `AllIncidenceRankFourBounds` (`formal/IncidenceSquarefree.lean:19-20`) | **INSTANTIATE-PENDING** — same machinery as h1 |
| `h3 : TypeIIILocalFourier` | `∃ C > 0, ∃ D p₀, LocalFourierHypothesis C D p₀`, with the two Fourier-inequality bodies and kernel objects fully unfolded | verbatim mirror of romyar1 `formal/TypeIIILocal.lean:144-159` (`HasFiniteExceptionalTypeIIIInput`) | **NAMED** — no closed proof exists anywhere, in or out of Lean |
| `hd : Deduction182` | `∀ S C, PhysicalSourceBounds182Mirror S C → h1 → h2 → hK4 → h3 → (ConsecutivePairs182).Infinite` — i.e. "the local inputs plus the 262 integral bounds ⇒ infinitely many consecutive prime pairs ≤ 182" | exact 1:1 mirror of the endpoint `PrimeGap182.infinite_consecutive_prime_pairs182_of_local_inputs` (romyar1/prime-gaps-lean @ b77bf175bded, `formal/PrimeGaps182Analytic.lean:67-74`; kernel-verified there 3 Oct 2026: 918 modules, 6,128 declarations, standard axioms only) | **NAMED** — a theorem of another repository, transported as a hypothesis; this package adds no axiom for it |

Frame note: the romyar1 endpoint takes the rank-4 estimate as a premise separate from the
Kl₃/Kl₂ pair — that is why there are four analytic hypotheses, not three.

### The source data (`S : TrialSource182`, defined in `pg182-frame/Pg182Frame/Obligations.lean`)

A record of 20 reals: the five trial cap integrals and their five rational enclosure targets
(`squareIntegral`, `baseIntegral`, `enlargementIntegral`, `tailIntegral`, `denominatorLower/Upper`,
`j0Lower`, `jPlusLower`, `tailUpper`), the 60 outer-root and 60 outer-face source integrals
(`outerRoot`, `outerFace : Fin 60 → ℝ`), and the 137 inner source masses
(`innerMass : Fin 137 → ℝ`). It is the *physical* half of the trial — the quantities the
source integrals actually take — abstracted from `formal/PhysicalTrial182.lean` and
`formal/SourceBounds182.lean`.

| name | statement | content | status |
|---|---|---|---|
| `hcap : CapBounds182 S` | `denominatorLower ≤ squareIntegral ≤ denominatorUpper`, `j0Lower ≤ baseIntegral`, `jPlusLower ≤ enlargementIntegral`, `tailIntegral ≤ tailUpper` | the 5 cap inequalities — the trial integrals sit in their rational enclosures | **NAMED** — frozen physical data (romyar1 `formal/PhysicalTrial182.lean:165-170`, kernel-certified) |
| `hroot : ∀ j, S.outerRoot j ≤ (TableData.outerRootUpper j : ℝ)` | 60 inequalities, source root integrals ≤ transcribed certificate rationals | the outer-root half of the certificate comparison | **NAMED** (source direction); the certificate side itself is **INTERNAL** (`TableData`, kernel-proved equal to the frozen module) |
| `hface : ∀ j, S.outerFace j ≤ (TableData.outerFaceUpper j : ℝ)` | 60 inequalities, source face integrals ≤ transcribed certificate rationals | the outer-face half | **NAMED** (source direction) |

### The 137 inner rows (Layer I)

| name | type | statement | content | status |
|---|---|---|---|---|
| `cellOf` | `Fin 137 → ℕ` | row `j` lives in the mesh cell `Ioc (cellOf j · mesh) (cellOf j · mesh + mesh)` | the row-to-cell identification | **NAMED** (Layer-I content) |
| `envSup` | `Fin 137 → ℝ` | with `henv : ∀ j, 0 ≤ envSup j` | the integrand envelope (affine-prefix supremum) | **NAMED** (Layer-I content) |
| `hrow` | `∀ j, S.innerMass j ≤ envSup j * (convPow fragmentMassLaw 38 (cell (cellOf j))).toReal` | the row inequality: source mass ≤ envelope × cell mass | the single irreducible Layer-I input. Its **cell-mass factor is proved** (`cell_measure_le_hq_final`, unconditional); what remains named is the envelope and the identification | **NAMED** in its weakest sufficient form; the analytic half is **PROVED** |
| `hmargin` | `∀ j, envSup j * hq ≤ (TableData.innerFaceUpper j : ℝ)` | envelope × cell bound ≤ certificate | **PROVED** on the 73 `rankTwo`/`high` rows (`TableData.witness_margin`, `norm_num`) and **ABSORBED** for all 137 by `h1_182_of_certEnvelope` | see left |

## 4. What the theorem uses but does not assume

The data side — everything below is a proved theorem of this package, feeding the theorem through
`cell_measure_le_hq_final`:

```lean
theorem cell_measure_le_hq_final (n : ℕ) :
    convPow fragmentMassLaw 38 (Set.Ioc ((n : ℝ) * mesh) ((n : ℝ) * mesh + mesh))
      ≤ ENNReal.ofReal hq
```

proof chain: `charFun_mass_fragmentLaw` (the fragment-law characteristic function is
`exp(−charExponent t ζ)`, `BandAssembly`) → `norm_charFun_exp_exponent` (`CharFunMod`) →
`integral_cinDecay_le_four_div_pi` (`∫₀ᴿ e^{−38 Cin} ≤ 38/39 < 4/π`, `HeadTail` + `CinBounds`) →
`hasLocalBound_of_charFun_bound` (Fejér smoothing, `HasLocalBound`) → per-cell bound
(`EnvLemmas`, `LowRows`). The certificate carrier `certTable : Pg182Frame.TrialCerts182` is the
transcribed table, not a hypothesis.

## 5. Axiom receipt (fresh re-run, verbatim)

`lake env lean receipt/axcheck_composition_rerun.lean` (2026-11-07, cached oleans, 32 s):

```
'PrimeGap182D2.cell_measure_le_hq_final' depends on axioms: [propext, Classical.choice, Quot.sound]
'PrimeGap182D2.h1_182_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'PrimeGap182D2.h1_182_of_certEnvelope' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorryAx` — the frame's 262 `sorry` stubs are not in any proof term, because `hobs` is
assembled from the hypotheses (`hcap`, `hroot`, `hface`, `hrow`, `hmargin`) inside the theorem.
Aggregate over the whole lane: 15 receipt files, 162 declarations, all on the same three axioms
(`OBLIGATION_MAP.md` §6).
