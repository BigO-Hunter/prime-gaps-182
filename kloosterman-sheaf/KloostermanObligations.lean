import KloostermanTraceBound

/-!
# The Kloosterman packaging: what has to be proved, and what follows once it is

`Kl_3` is the rank-three ℓ-adic sheaf on `𝔾_m` that Laumon's Fourier transform attaches to the
additive-line family computed in `StacksFrontier`'s `Trace/LaumonFourier*` modules: the family
sheaf `pr₁^*ℱ_{σ₁} ⊗ L_ψ'(a xⁿ + x t)` on `Spec k'[x][t]` with the trivial `σ₁`, pushed forward
with compact support along `t`. Its lisseness on the open where `R¹pr₂!` is locally constant is
`Stacks.EtaleCohomology.isLisse_laumonFourierFamilySheaf`; its rank, its purity, and the
identification of its stalk trace with the Kloosterman sum are the three packaging obligations
recorded in `KLOOSTERMAN_SHEAF.lean`.

This file records what those obligations are worth: **they are sufficient**, and the last step is
proved here. `Kl3Package` bundles exactly the data a completed packaging has to deliver —

* a rank bound `rank ≤ 3`;
* the characteristic polynomial of Frobenius on the stalk, monic (it is the charpoly of an
  endomorphism), split (over `ℂ`), of degree at most the rank;
* its root sum is the Kloosterman sum (the trace of Frobenius — the sheaf-function
  correspondence at `a`);
* and purity of weight `1`: every root has absolute value `q^{1/2}`;

— and `Kl3Package.norm_kl3_le` concludes `‖Kl_3(a; q)‖ ≤ 3 q^{1/2}`.

Nothing in this file assumes anything: the imlication from a completed packaging to the bound is
proved, so the packaging obligations are the only remaining work, and they are stated positively
(what has to be *constructed*), not as an axiom.
-/

namespace Kloosterman

open Polynomial

/-- **The data a completed `Kl_3` packaging must deliver.** Every field except `rank_le` and
`pure` is bookkeeping about the characteristic polynomial of the geometric Frobenius on the stalk
`Kl_{3,a}`; `rank_le` is the rank bound and `pure` is Deligne's weight-`1` purity. -/
structure Kl3Package (q : ℕ) where
  /-- the rank of the Kloosterman sheaf at `a` -/
  rank : ℕ
  /-- the rank bound: `Kl_3` is rank three -/
  rank_le : rank ≤ 3
  /-- the Kloosterman sum `Kl_3(a; q)`, i.e. the trace of the geometric Frobenius on the stalk -/
  kl3 : ℂ
  /-- the characteristic polynomial of the geometric Frobenius on the stalk `Kl_{3,a}` -/
  charpoly : ℂ[X]
  /-- a characteristic polynomial of an endomorphism is monic -/
  charpoly_monic : charpoly.Monic
  /-- over `ℂ` every polynomial splits -/
  charpoly_splits : charpoly.Splits
  /-- the degree of the charpoly is the rank -/
  natDegree_le_rank : charpoly.natDegree ≤ rank
  /-- the trace of Frobenius is the sum of the eigenvalues -/
  trace_eq : charpoly.roots.sum = kl3
  /-- purity of weight `1`: every eigenvalue has complex absolute value `q^{1/2}` -/
  pure : ∀ z ∈ charpoly.roots, ‖z‖ = Real.sqrt q

/-- **The Kloosterman bound from a completed packaging**: `‖Kl_3(a; q)‖ ≤ 3 q^{1/2}`. -/
theorem Kl3Package.norm_kl3_le {q : ℕ} (P : Kl3Package q) : ‖P.kl3‖ ≤ 3 * Real.sqrt q := by
  have hdeg : P.charpoly.natDegree ≤ 3 := le_trans P.natDegree_le_rank P.rank_le
  have h := kloosterman_bound P.charpoly_splits hdeg P.pure
  simpa [P.trace_eq] using h

/-- **The normalized form used by the program**: `‖Kl_3(a; q)‖ / q^{1/2} ≤ 3`. -/
theorem Kl3Package.norm_kl3_div_sqrt_le {q : ℕ} (P : Kl3Package q) (hq : 0 < q) :
    ‖P.kl3‖ / Real.sqrt q ≤ 3 := by
  have hsqrt : 0 < Real.sqrt q := Real.sqrt_pos.mpr (by exact_mod_cast hq)
  rw [div_le_iff₀ hsqrt]
  exact P.norm_kl3_le

end Kloosterman
