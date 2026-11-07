import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Data.Fin.VecNotation
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# The named inputs of the 182 conditional frame

Three hypotheses (plus one companion finite-field estimate) that the 182 lane
treats as *inputs*, stated exactly in their published/axiomatized forms. Every
declaration cites its source line. Nothing in this file is proved; these are
Props to be assumed, discharged elsewhere, or instantiated by the C0 lane.

* (a) `Kloosterman3Bound` — Katz, GKM Thm 4.1.1(1)-(2), transcribed verbatim
  from `axiom PrimeGap186.kloosterman3_bound`
  (openai/PrimeGaps186, vendored unchanged in
  romyar1/prime-gaps-lean @ b77bf175bded, vendor/primegaps186/PrimeGaps186.lean:147-151,
  Apache-2.0). The defs `normalizedKloosterman3` / `unnormalizedKloosterman2`
  below are verbatim copies of the 186 definitions (same file, :121 and :131).
* (b) `Kloosterman2CorrelationBound` — Fouvry-Kowalski-Michel, "The
  Friedlander-Iwaniec character sum", Prop 2; verbatim from
  `axiom PrimeGap186.kloosterman2_correlation_bound` (same file, :159-168).
* (hK4) `IncidenceRankFourBounds182` — the rank-4 weight-3 specialization of the
  same Katz theorem, a *separate* premise in the 182 development: verbatim
  mirror of `IncidenceRankFourBound` (romyar1/prime-gaps-lean @ b77bf175bded,
  formal/IncidenceRankFour.lean:29-31), quantified as in
  `AllIncidenceRankFourBounds` (formal/IncidenceSquarefree.lean:19-20).
* (c) `TypeIIILocalFourier` — the Type III local Fourier proposition in exactly
  the form romyar1's repo states it: verbatim mirror of
  `HasFiniteExceptionalTypeIIIInput` = `∃ C, 0 < C ∧ ∃ D p₀, LocalFourierHypothesis C D p₀`
  (formal/TypeIIILocal.lean:144-159), including the full unfolding of the two
  Fourier inequality bodies (:70-77, :108-119) and the kernel objects they
  quantify over (:34-56, :107-110).

Frame note (deviation from the 3-input sketch, documented in PARITY.md):
the romyar1 endpoint takes the rank-4 estimate as a premise *separate* from
the Kl₃/Kl₂ pair, so the frame carries it as an explicit fourth input.
-/

noncomputable section

namespace Pg182Frame

/-! ## (a)+(b): the two public finite-field estimates, verbatim from the 186 baseline -/

/-- Verbatim copy of `PrimeGap186.unnormalizedKloosterman2`
(vendor/primegaps186/PrimeGaps186.lean:131-135). -/
def unnormalizedKloosterman2 (p : ℕ) [Fact p.Prime] (c : ZMod p) : ℂ :=
  ∑ u : (ZMod p)ˣ,
    ZMod.stdAddChar ((u : ZMod p) + c / (u : ZMod p))

/-- Verbatim copy of `PrimeGap186.normalizedKloosterman3`
(vendor/primegaps186/PrimeGaps186.lean:121-125). -/
def normalizedKloosterman3 (p : ℕ) [Fact p.Prime] (c : ZMod p) : ℂ :=
  (p : ℂ)⁻¹ *
    ∑ u : ZMod p, ∑ v : ZMod p, ∑ w : ZMod p,
      if u * v * w = c then ZMod.stdAddChar (u + v + w) else 0

/-- Input (a). Exact transcription of `axiom PrimeGap186.kloosterman3_bound`
(vendor/primegaps186/PrimeGaps186.lean:147-151), itself the normalized form of
Katz, *Gauss Sums, Kloosterman Sums, and Monodromy Groups*, Thm 4.1.1(1)-(2),
p. 49 (rank 3, weight 2, trivial characters, b_i = 1: raw bound 3p, divided by p). -/
def Kloosterman3Bound : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (c : ZMod p),
    c ≠ 0 → ‖normalizedKloosterman3 p c‖ ≤ (3 : ℝ)

/-- Input (b). Exact transcription of `axiom PrimeGap186.kloosterman2_correlation_bound`
(vendor/primegaps186/PrimeGaps186.lean:159-168): FKM, Prop 2, with their
`Kl_2(c) = unnormalizedKloosterman2 p c / sqrt p` normalization giving `8 * p * sqrt p`. -/
def Kloosterman2CorrelationBound : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (A B : ZMod p),
    A ≠ 0 → B ≠ 0 →
      ‖∑ t : ZMod p, if t ≠ 0 ∧ t ≠ -1 then
        unnormalizedKloosterman2 p (A / t) *
          unnormalizedKloosterman2 p (B / (t + 1)) else 0‖ ≤
        8 * (p : ℝ) * Real.sqrt (p : ℝ)

/-! ## (hK4): the rank-4 companion estimate (romyar1-only premise) -/

/-- Mirror of `incidenceKloosterman4Raw` in its proved-equal hypersurface form
(`incidenceKloosterman4Raw_eq_hypersurface`, formal/IncidenceRankFour.lean): the
rank-4 weight-3 Kloosterman sum over nonzero u,v,w with constraint uvw = c. -/
def rawKloosterman4 (p : ℕ) [Fact p.Prime] (c : ZMod p) : ℂ :=
  ∑ u : ZMod p, ∑ v : ZMod p, ∑ w : ZMod p,
    if u ≠ 0 ∧ v ≠ 0 ∧ w ≠ 0 then ZMod.stdAddChar (u + v + w + c / (u * v * w)) else 0

/-- Verbatim mirror of `IncidenceRankFourBound`
(romyar1/prime-gaps-lean @ b77bf175bded, formal/IncidenceRankFour.lean:29-31). -/
def IncidenceRankFourBound182 (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ c : ZMod p, c ≠ 0 →
    ‖rawKloosterman4 p c‖ ≤ 4 * (p : ℝ) * Real.sqrt (p : ℝ)

/-- Verbatim mirror of `AllIncidenceRankFourBounds`
(romyar1/prime-gaps-lean @ b77bf175bded, formal/IncidenceSquarefree.lean:19-20). -/
def IncidenceRankFourBounds182 : Prop :=
  ∀ (p : ℕ), ∀ [Fact p.Prime], IncidenceRankFourBound182 p

/-! ## (c): the Type III local Fourier proposition, verbatim from romyar1 -/

/-- Mirror of `kl3` (formal/TypeIIILocal.lean:47-49). -/
def kl3 (p : ℕ) [Fact p.Prime] (t : ZMod p) : ℂ :=
  (p : ℂ)⁻¹ * ∑ u : (ZMod p)ˣ, ∑ v : (ZMod p)ˣ,
    ZMod.stdAddChar ((u : ZMod p) + (v : ZMod p) + t / ((u : ZMod p) * (v : ZMod p)))

/-- Mirror of `correlation` (formal/TypeIIILocal.lean:52-56). -/
def correlation (p : ℕ) [Fact p.Prime] (A B c : ZMod p) : ℂ :=
  ∑ h : (ZMod p)ˣ,
    kl3 p (A * (h : ZMod p)) * star (kl3 p (B * (h : ZMod p))) *
      ZMod.stdAddChar (c * (h : ZMod p))

/-- Mirror of `kernel` (formal/TypeIIILocal.lean:41-44, "the matrix kernel,
extended by zero away from the two-dimensional torus"). -/
def kernel (p : ℕ) [Fact p.Prime] (α m n r₁ r₂ : ZMod p) : ℂ :=
  if r₁ = 0 ∨ r₂ = 0 then 0 else
    correlation p (α * r₂ / (m * r₁ ^ 2)) (α * r₁ / (n * r₂ ^ 2)) 1

/-- Mirror of `fourCycle` (formal/TypeIIILocal.lean:46-49, "the four-cycle
occurring in `tr ((K K*)²)`"), partially applied as in romyar1's usage. -/
def fourCycle (p : ℕ) [Fact p.Prime] (α m m' n n' : ZMod p) : ZMod p → ZMod p → ℂ :=
  fun r₁ r₂ =>
    kernel p α m n r₁ r₂ * star (kernel p α m' n r₁ r₂) *
      kernel p α m' n' r₁ r₂ * star (kernel p α m n' r₁ r₂)

/-- Mirror of `fourier₂` (formal/TypeIIILocal.lean:51-54, unnormalized
two-dimensional additive Fourier transform on the residue space). -/
def fourier₂ (p : ℕ) [NeZero p] (f : ZMod p → ZMod p → ℂ) (h k : ZMod p) : ℂ :=
  ∑ r₁ : ZMod p, ∑ r₂ : ZMod p,
    f r₁ r₂ * ZMod.stdAddChar (h * r₁ + k * r₂)

/-- Mirror of `planeEval` (formal/TypeIIILocal.lean:107-110). -/
def planeEval (p : ℕ) [Fact p.Prime]
    (P : MvPolynomial (Fin 2) (AlgebraicClosure (ZMod p))) (h k : ZMod p) :
    AlgebraicClosure (ZMod p) :=
  MvPolynomial.eval ![algebraMap (ZMod p) (AlgebraicClosure (ZMod p)) h,
    algebraMap (ZMod p) (AlgebraicClosure (ZMod p)) k] P

/-- Mirror of `FiniteExceptionalFourierBound`
(formal/TypeIIILocal.lean:114-119, the distinct-index finite-exceptional
Fourier inequality). -/
def FiniteExceptionalFourierBound (p : ℕ) [Fact p.Prime] (C : ℝ) (D : ℕ)
    (α m m' n n' : ZMod p) : Prop :=
  ∃ Z : Finset (ZMod p × ZMod p), Z.card ≤ D ∧
    ∀ h k : ZMod p,
      ‖fourier₂ p (fourCycle p α m m' n n') h k‖ ≤
        C * (p : ℝ) ^ 3 *
          (1 + Real.sqrt (p : ℝ) * if (h, k) ∈ Z then 1 else 0)

/-- Mirror of `CurveExceptionalFourierBound`
(formal/TypeIIILocal.lean:122-129, the repeated-index inequality with an
algebraic exceptional curve; origin contribution `C*p^4`). -/
def CurveExceptionalFourierBound (p : ℕ) [Fact p.Prime] (C : ℝ) (D : ℕ)
    (α m m' n n' : ZMod p) : Prop :=
  ∃ P : MvPolynomial (Fin 2) (AlgebraicClosure (ZMod p)),
    P ≠ 0 ∧ P.totalDegree ≤ D ∧
    ∀ h k : ZMod p,
      ‖fourier₂ p (fourCycle p α m m' n n') h k‖ ≤
        C * (p : ℝ) ^ 3 *
          (1 + Real.sqrt (p : ℝ) * (if planeEval p P h k = 0 then 1 else 0) +
            (p : ℝ) * if h = 0 ∧ k = 0 then 1 else 0)

/-- Verbatim mirror of `LocalFourierHypothesis`
(romyar1/prime-gaps-lean @ b77bf175bded, formal/TypeIIILocal.lean:144-149):
fixed constants C, D, p₀, uniform over all primes p > p₀ and all nonzero
α, m, m', n, n'. -/
def LocalFourierHypothesis (C : ℝ) (D p₀ : ℕ) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p₀ < p →
    ∀ α m m' n n' : ZMod p,
      α ≠ 0 → m ≠ 0 → m' ≠ 0 → n ≠ 0 → n' ≠ 0 →
      ((m ≠ m' ∧ n ≠ n') → FiniteExceptionalFourierBound p C D α m m' n n') ∧
      ((m = m' ∨ n = n') → CurveExceptionalFourierBound p C D α m m' n n')

/-- Input (c). Verbatim mirror of `HasFiniteExceptionalTypeIIIInput`
(formal/TypeIIILocal.lean:158-159) under the mission's name. This is the
proposition the September 18 Type III derivation constructs from the
"common adic theory" interfaces; its existence remains an explicit input. -/
def TypeIIILocalFourier : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ D p₀ : ℕ, LocalFourierHypothesis C D p₀

end Pg182Frame
