import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Polynomial.Splits

/-!
# The last mile of the Kloosterman bound: `|tr Frob| ≤ rank · q^{1/2}`

This file isolates the elementary step that turns the two cohomological facts

* `rank(Kl_3) ≤ 3` (the rank of the Kloosterman sheaf), and
* every eigenvalue of Frobenius on the stalk `Kl_{3,a}` has complex absolute value
  `q ^ (1/2)` (purity of weight `1`, from `LAdicSheaf.weightBound`, Tag 03VH),

into the numerical bound `|Kl_3(a; q)| ≤ 3 q^{1/2}`. The arithmetic input is that the trace
of Frobenius is the sum of the eigenvalues, and that a sum of `n` complex numbers of absolute
value `r` has absolute value at most `n r`.

Nothing here is specific to the Kloosterman sheaf: the same lemma discharges the `n`-th
Kloosterman bound `|Kl_n| ≤ n q^{(n-1)/2}` (with `rank = n` and weight `n - 1`) and every
other "purity plus rank gives a bound on a trace" step. The Kloosterman-specific content is
the two cohomological inputs, stated as `KloostermanRank` and `KloostermanPurity` in
`KLOOSTERMAN_SHEAF.lean`.

## Main results

* `Kloosterman.norm_multiset_sum_le_card_mul`: a sum of `n` complex numbers of absolute value
  `r` has absolute value at most `n r`.
* `Kloosterman.norm_trace_le_of_monic_charpoly_pure`: for a monic complex polynomial of degree
  at most `n` all of whose roots have absolute value `r`, the absolute value of the sum of the
  roots is at most `n r`.
* `Kloosterman.kloosterman_bound`: the `n = 3` instance, `|Kl_3(a; q)| ≤ 3 q^{1/2}`.
-/

namespace Kloosterman

open Polynomial

/-- **A sum of `n` complex numbers of absolute value `r` has absolute value at most `n r`.**

This is the triangle inequality together with `‖z‖ = r` for every `z ∈ s`. -/
theorem norm_multiset_sum_le_card_mul (s : Multiset ℂ) {r : ℝ} (h : ∀ z ∈ s, ‖z‖ = r) :
    ‖s.sum‖ ≤ (s.card : ℝ) * r := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have ha : ‖a‖ = r := h a (Multiset.mem_cons_self a s)
    have hs : ∀ z ∈ s, ‖z‖ = r := fun z hz => h z (Multiset.mem_cons_of_mem hz)
    have ih' := ih hs
    rw [Multiset.sum_cons, Multiset.card_cons, Nat.cast_add, Nat.cast_one]
    calc ‖a + s.sum‖ ≤ ‖a‖ + ‖s.sum‖ := norm_add_le a s.sum
      _ ≤ r + (s.card : ℝ) * r := by
        rw [ha]
        exact add_le_add_right ih' r
      _ = ((s.card : ℝ) + 1) * r := by ring

/-- **The trace bound from purity.** Let `p` be the monic characteristic polynomial of a
`ℚ_ℓ`-linear Frobenius of rank at most `n`, with every root of absolute value `r ≥ 0`. Then the
sum of the roots — the trace of Frobenius — has absolute value at most `n r`. -/
theorem norm_trace_le_of_monic_charpoly_pure {p : ℂ[X]} (hsplits : p.Splits) {n : ℕ}
    (hdeg : p.natDegree ≤ n) {r : ℝ} (hr : 0 ≤ r) (hpure : ∀ z ∈ p.roots, ‖z‖ = r) :
    ‖p.roots.sum‖ ≤ (n : ℝ) * r := by
  have hcard : p.roots.card ≤ n := by
    rw [← hsplits.natDegree_eq_card_roots]
    exact hdeg
  have hsum := norm_multiset_sum_le_card_mul p.roots hpure
  calc ‖p.roots.sum‖ ≤ (p.roots.card : ℝ) * r := hsum
    _ ≤ (n : ℝ) * r := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hr

/-- **The Kloosterman bound for `n = 3`**: if the characteristic polynomial of the Frobenius on
the stalk `Kl_{3,a}` is monic of degree at most `3` with every root of absolute value
`q^{1/2}` — purity of weight `1` at rank at most `3` — then the Kloosterman sum, the trace of
Frobenius, satisfies `|Kl_3(a; q)| ≤ 3 q^{1/2}`. -/
theorem kloosterman_bound {p : ℂ[X]} (hsplits : p.Splits) (hdeg : p.natDegree ≤ 3) {q : ℕ}
    (hpure : ∀ z ∈ p.roots, ‖z‖ = Real.sqrt q) :
    ‖p.roots.sum‖ ≤ 3 * Real.sqrt q :=
  norm_trace_le_of_monic_charpoly_pure hsplits hdeg (Real.sqrt_nonneg q) hpure

/-- **The unnormalized form consumed by `PrimeGap186.kloosterman3_bound`** (Katz 1988 Thm
4.1.1(1)–(2) at `n = 3`, `bᵢ = 1`, trivial `χᵢ`): purity of **weight `2`** on a rank-`3` sheaf
over `𝔽_p` gives `|Σ_{x₁x₂x₃=c} e_p(x₁+x₂+x₃)| ≤ 3 p`, which after the `1/p` normalization of
`normalizedKloosterman3` is `≤ 3`. Same lemma, `r = p` instead of `r = √p`. -/
theorem kloosterman_bound_unnormalized {p : ℂ[X]} (hsplits : p.Splits) (hdeg : p.natDegree ≤ 3)
    {q : ℕ} (hpure : ∀ z ∈ p.roots, ‖z‖ = (q : ℝ)) : ‖p.roots.sum‖ ≤ 3 * (q : ℝ) :=
  norm_trace_le_of_monic_charpoly_pure hsplits hdeg (Nat.cast_nonneg q) hpure

end Kloosterman
