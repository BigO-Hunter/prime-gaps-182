import Pg182Frame.Hypotheses
import Pg182Frame.Conclusion
import Pg182Frame.Obligations
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Order.Filter.Cofinite

/-!
# The 182 conditional frame

`h1_182_of` states: given the three named inputs — (a) `Kloosterman3Bound`
(Katz GKM Thm 4.1.1), (b) `Kloosterman2CorrelationBound` (FKM Prop 2),
(c) `TypeIIILocalFourier` (the Type III local Fourier proposition) — plus the
rank-4 companion estimate the romyar1 endpoint carries separately, the
kernel-checked deduction `Deduction182` (a 1:1 mirror of the endpoint
`PrimeGap182.infinite_consecutive_prime_pairs182_of_local_inputs`,
romyar1/prime-gaps-lean @ b77bf175bded, formal/PrimeGaps182Analytic.lean:67-74,
verified there 3 Oct 2026: 918 modules / 6,128 declarations, standard axioms
only), and the 262 integral obligations bundled by
`PhysicalSourceBounds182Mirror`, the race target `BigOSpeedrun.PrimeGaps.Bound 182`
holds.

The deduction is carried as an explicit HYPOTHESIS (`hd : Deduction182`), not
an axiom: this project adds no mathematical assumptions of its own. The
kernel-checked delta contributed here is
`frequently_gap182_of_infinite_consecutive_pairs`: romyar1's conclusion
(infinitely many consecutive prime pairs of gap <= 182) implies the race
statement `Bound 182`. The 262 obligations (Obligations.lean) plug into
`hobs` at C0 landing.
-/

noncomputable section

namespace Pg182Frame

open Filter

/-- The endpoint conclusion: infinitely many consecutive prime pairs of gap
at most 182. Def-equal to the conclusion of
`PrimeGap182.infinite_consecutive_prime_pairs182_of_local_inputs`
(formal/PrimeGaps182Analytic.lean:71-72). -/
def ConsecutivePairs182 : Set ℕ :=
  {p : ℕ | p.Prime ∧ ∃ q : ℕ, p < q ∧ q.Prime ∧ q - p ≤ 182 ∧
    ∀ r : ℕ, p < r → r < q → ¬r.Prime}

/-- Bridge (hypothesis, not axiom): exact 1:1 mirror of the premise-parameterized
endpoint `PrimeGap182.infinite_consecutive_prime_pairs182_of_local_inputs`
(romyar1/prime-gaps-lean @ b77bf175bded, formal/PrimeGaps182Analytic.lean:67-74).
There the premise groups are `(hn : PhysicalSourceBounds182)`,
`(hpublic : PublicPrimeLocalBounds182)` (the Kl3 ∧ Kl2 conjunction),
`(hK4 : AllIncidenceRankFourBounds)`, `{C : ℝ} (hC : 0 ≤ C) {D p₀ : ℕ}
(hlocal : LocalFourierHypothesis C D p₀)`; here they appear in the same order
as the parameters of this Prop. That theorem is kernel-checked at the pinned
commit; this frame transports it. -/
def Deduction182 : Prop :=
  ∀ (S : TrialSource182) (C : TrialCerts182),
    PhysicalSourceBounds182Mirror S C →
    Kloosterman3Bound → Kloosterman2CorrelationBound →
    IncidenceRankFourBounds182 → TypeIIILocalFourier →
    ConsecutivePairs182.Infinite

/-- The kernel-checked delta of this frame: romyar1's endpoint conclusion
implies the race target `Bound 182`. -/
theorem frequently_gap182_of_infinite_consecutive_pairs
    (h : ConsecutivePairs182.Infinite) :
    ∃ᶠ m in atTop, Nat.nth Nat.Prime (m + 1) - Nat.nth Nat.Prime m ≤ 182 := by
  rw [Nat.frequently_atTop_iff_infinite]
  have hpinf : {p : ℕ | Nat.Prime p}.Infinite := fun hf =>
    Nat.not_bddAbove_setOfPred_prime hf.bddAbove
  have hmono : Monotone (Nat.nth Nat.Prime) := Nat.nth_monotone (p := Nat.Prime) hpinf
  have hnthinj : Function.Injective (Nat.nth Nat.Prime) := fun a b hab => by
    have h1 : Nat.nth Nat.Prime a ≤ Nat.nth Nat.Prime b := hab ▸ le_rfl
    have h2 : Nat.nth Nat.Prime b ≤ Nat.nth Nat.Prime a := hab ▸ le_rfl
    have e1 : a ≤ b := (Nat.nth_le_nth (p := Nat.Prime) hpinf).mp h1
    have e2 : b ≤ a := (Nat.nth_le_nth (p := Nat.Prime) hpinf).mp h2
    omega
  have hcount : ∀ p : ℕ, p.Prime → Nat.nth Nat.Prime (Nat.count Nat.Prime p) = p :=
    fun p hp => Nat.nth_count (p := Nat.Prime) hp
  have hstrict : ∀ p q : ℕ, p.Prime → q.Prime → p < q →
      Nat.count Nat.Prime p < Nat.count Nat.Prime q := by
    intro p q hp hq hlt
    by_contra hge
    have hle : Nat.count Nat.Prime q ≤ Nat.count Nat.Prime p := by omega
    have hstep : Nat.nth Nat.Prime (Nat.count Nat.Prime q) ≤
        Nat.nth Nat.Prime (Nat.count Nat.Prime p) := hmono hle
    rw [hcount q hq, hcount p hp] at hstep
    omega
  have hinj : Set.InjOn (fun p => Nat.count Nat.Prime p) ConsecutivePairs182 := by
    intro p hp q hq hfe
    rcases lt_trichotomy p q with hlt | heq | hlt
    · exact absurd hfe (hstrict p q hp.1 hq.1 hlt).ne
    · exact heq
    · exact absurd hfe.symm (hstrict q p hq.1 hp.1 hlt).ne
  have himg : (fun p => Nat.count Nat.Prime p) '' ConsecutivePairs182 ⊆
      {m | Nat.nth Nat.Prime (m + 1) - Nat.nth Nat.Prime m ≤ 182} := by
    rintro m ⟨p, hp, rfl⟩
    obtain ⟨hqprime, hlt, hgap, hconsec⟩ := hp.2
    have hpq : Nat.nth Nat.Prime (Nat.count Nat.Prime p) = p := hcount p hp.1
    have hup : Nat.count Nat.Prime p + 1 ≤ Nat.count Nat.Prime q :=
      hstrict p q hp.1 hqprime hlt
    have hdown : Nat.count Nat.Prime q ≤ Nat.count Nat.Prime p + 1 := by
      by_contra hc
      have hlt2 : Nat.count Nat.Prime p + 1 < Nat.count Nat.Prime q := by omega
      have hle : Nat.nth Nat.Prime (Nat.count Nat.Prime p + 1) ≤
          Nat.nth Nat.Prime (Nat.count Nat.Prime q) := hmono hlt2.le
      rw [hcount q hqprime] at hle
      have hne : Nat.nth Nat.Prime (Nat.count Nat.Prime p + 1) ≠ q :=
        fun he => hlt2.ne (hnthinj (he.trans (hcount q hqprime).symm))
      have hpm : Nat.Prime (Nat.nth Nat.Prime (Nat.count Nat.Prime p + 1)) :=
        Nat.nth_mem_of_infinite (p := Nat.Prime) hpinf _
      have hgt : p < Nat.nth Nat.Prime (Nat.count Nat.Prime p + 1) := by
        have hle2 : Nat.nth Nat.Prime (Nat.count Nat.Prime p) ≤
            Nat.nth Nat.Prime (Nat.count Nat.Prime p + 1) := hmono (Nat.le_succ _)
        have hne2 : Nat.nth Nat.Prime (Nat.count Nat.Prime p) ≠
            Nat.nth Nat.Prime (Nat.count Nat.Prime p + 1) :=
          fun he2 => (Nat.succ_ne_self (Nat.count Nat.Prime p)) (hnthinj he2)
        rw [hpq] at hle2 hne2
        exact lt_of_le_of_ne hle2 hne2
      exact hconsec _ hpm hgt (lt_of_le_of_ne hle hne)
    have hcountq : Nat.count Nat.Prime q = Nat.count Nat.Prime p + 1 := by omega
    have hq : Nat.nth Nat.Prime (Nat.count Nat.Prime p + 1) = q := by
      rw [← hcountq]; exact hcount q hqprime
    rw [hq, ← hpq]
    exact hgap
  exact Set.Infinite.mono himg (h.image_of_injOn hinj)

/-- THE FRAME THEOREM. Given the three named inputs, the rank-4 companion
estimate, the kernel-checked deduction, and the 262 discharged obligations:
`Bound 182`. -/
theorem h1_182_of (h1 : Kloosterman3Bound) (h2 : Kloosterman2CorrelationBound)
    (hK4 : IncidenceRankFourBounds182) (h3 : TypeIIILocalFourier)
    (hd : Deduction182) (S : TrialSource182) (C : TrialCerts182)
    (hobs : PhysicalSourceBounds182Mirror S C) :
    BigOSpeedrun.PrimeGaps.Bound 182 :=
  frequently_gap182_of_infinite_consecutive_pairs (hd S C hobs h1 h2 hK4 h3)

#print axioms h1_182_of
#print axioms frequently_gap182_of_infinite_consecutive_pairs

end Pg182Frame
