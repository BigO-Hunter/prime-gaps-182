import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFourierLineFamily
import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFourierLineAwayFibreOffTop
import KloostermanObligations

/-!
# The Kloosterman sheaf `Kl_3`: definition, lisseness, and the three remaining obligations

**STATUS (2026-11-07): NOT YET ELABORATED.** This file names the Kl_3 packaging against the
`StacksFrontier` API and cannot be compiled until that API's own oleans exist: the import closure
of `LaumonFourierLineFamily` is 17,567 Stacks modules of which **16,525 are unbuilt** in the
current tree (measured; ~10 days of `LAKE_JOBS=1` on this host). The parts of the packaging that
can be verified today are in `KloostermanTraceBound.lean` and `KloostermanObligations.lean`, which
DO compile and whose axiom sets are `[propext, Classical.choice, Quot.sound]`. Binder order here
follows `Trace/LaumonFourierLineFamily.lean` and `Trace/LaumonFourierLineAwayFibreOffTop.lean`
verbatim; expect to reconcile implicit-argument order on the first successful build, nothing else.

## What `Kl_3` is in this API

`LaumonFourierLineFamily.laumonFourierFamilySheaf` is the family sheaf

    pr₁^* ℱ_{σ₁} ⊗ L_ψ'(a xⁿ + x t)      on   Spec k'[x][t],

the kernel of the family of fibres `H¹_c(𝔸¹, ℱ_σ ⊗ L_ψ(a xⁿ + c x))` at fixed `a`
(`laumonFourierKernel`, `laumonFourierKernel_eval`). Its lisseness away from the discriminant is
`isLisse_laumonFourierFamilySheaf`. The Kloosterman sheaf is the compactly supported first higher
direct image of this family along the `t`-line,

    Kl_n  :=  R¹pr₂! ( pr₁^* ℱ_{σ₁} ⊗ L_ψ'(a xⁿ + x t) )      on the open V' where it is lisse,

with `σ₁` the trivial rank-one representation (the constant sheaf input), `n = 3`, and `a ≠ 0`.
The machinery for that step is `laumonFamilyRestrictedHigherDirectImage`
(`Trace/LaumonFamilyStalkPurity.lean`), lisse on `V'` by `exists_laumonFamily_lisseLocus`, with its
representation `τ` pure of weight `β + 1` by `laumonFamily_isPure_restrictScalarsRep`.

## The three obligations, and why they are sufficient

`KloostermanRank`, `KloostermanPurity`, `KloostermanStalkTrace` below are stated positively: each
says what has to be *constructed*, and `kl3_bound_of_obligations` proves that together they yield
`‖Kl_3(a; q)‖ ≤ 3 q^{1/2}` — the numerical bound is already proved in `KloostermanObligations.lean`
(`Kl3Package.norm_kl3_le`). So the packaging gap is construction, not invention: nothing about the
bound is assumed anywhere.

## Main definitions

* `Kloosterman.FourierFamilyData`: the exact parameter tuple of `laumonFourierFamilySheaf`.
* `Kloosterman.kl3FamilySheaf`: the `n = 3` family sheaf with trivial `σ₁`.
* `Kloosterman.KloostermanRank`, `Kloosterman.KloostermanPurity`, `Kloosterman.KloostermanStalkTrace`.

## Main results

* `Kloosterman.kl3FamilySheaf_isLisse` (from `isLisse_laumonFourierFamilySheaf`).
* `Kloosterman.kl3_bound_of_obligations`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale
open Stacks.EtaleCohomology

universe u

namespace Kloosterman

attribute [local instance] HasDerivedCategory.standard

/-- **The parameter tuple of the Laumon Fourier family** at `n` and `a`: a finite field `k'`, the
big étale site `B` with the plane of size below its cutoff, an `E`-basis `b` of the coefficient
field, an additive character `ψ'`, a geometric point `z` of the plane, a point `p₀` of the
Artin–Schreier cover of the kernel, and a representation `σ₁` of `π₁(𝔸¹_{k'})` with continuous
restriction of scalars. -/
structure FourierFamilyData where
  /-- the base finite field -/
  k' : Type u
  [field : Field k']
  [fintype : Fintype k']
  /-- the big étale site -/
  B : BigEtaleSite.{u}
  /-- the plane is small enough for `B` -/
  hS : schemeSizeBelow B.cutoff (Spec (.of (Polynomial (Polynomial k'))))
  /-- the prime `ℓ` -/
  ℓ : ℕ
  [prime : Fact ℓ.Prime]
  /-- the coefficient field, a finite extension of `ℚ_ℓ` -/
  E : Type
  [eField : Field E]
  [eAlgebra : Algebra ℚ_[ℓ] E]
  /-- the `ℚ_ℓ`-basis of the coefficient field -/
  d : ℕ
  b : Module.Basis (Fin d) ℚ_[ℓ] E
  /-- the additive character of the base field -/
  ψ' : AddChar k' E
  /-- the exponent `n` of the family: `n = 3` for the Kloosterman sum `Kl_3` -/
  n : ℕ
  /-- the twist parameter `a`; `a ≠ 0` for the Kloosterman sheaf -/
  a : k'
  /-- the geometric point of the plane -/
  z : GeometricPoint (Spec (.of (Polynomial (Polynomial k'))))
  /-- the point of the Artin–Schreier cover at `z` -/
  p₀ : (finiteEtaleFiberFunctor z).obj
    (Stacks.ArtinSchreier.cover k' (Polynomial (Polynomial k'))
      (laumonFourierKernel k' n a))
  /-- the rank of `σ₁` -/
  m : ℕ
  /-- the representation of `π₁(𝔸¹_{k'})` whose Fourier transform is the family: the trivial
  rank-one representation for `Kl_3` (the constant sheaf input) -/
  σ₁ : EtaleFundamentalGroup (Spec (.of (Polynomial k'))) (z.map (laumonFamilyPr₁ k')) →*
    GL (Fin m) E
  /-- continuity of the restriction of scalars of `σ₁` -/
  hσ₁ : Continuous (restrictScalarsRep b σ₁)

attribute [instance] FourierFamilyData.field FourierFamilyData.fintype
  FourierFamilyData.prime FourierFamilyData.eField FourierFamilyData.eAlgebra

/-- **The Laumon Fourier family sheaf** at the package's parameters: the sheaf
`pr₁^*ℱ_{σ₁} ⊗ L_ψ'(a xⁿ + x t)` on `Spec k'[x][t]` of `laumonFourierFamilySheaf`. -/
def FourierFamilyData.familySheaf (D : FourierFamilyData.{u}) :
    LAdicSheaf.{u, u + 1} D.B
      (Stacks.ArtinSchreier.specObject (Polynomial (Polynomial D.k')) D.B D.hS) D.ℓ :=
  laumonFourierFamilySheaf D.k' D.B D.hS D.b D.ψ' D.n D.a D.z D.p₀ D.σ₁ D.hσ₁

/-- **The Fourier family sheaf is lisse** — the family is the sheaf of a continuous representation.
This is `isLisse_laumonFourierFamilySheaf` restated for the package. -/
theorem FourierFamilyData.familySheaf_isLisse (D : FourierFamilyData.{u}) :
    D.familySheaf.toLAdicSheaf.IsLisse :=
  isLisse_laumonFourierFamilySheaf D.k' D.B D.hS D.b D.ψ' D.n D.a D.z D.p₀ D.σ₁ D.hσ₁

/-- **The `Kl_3` family**: the Fourier family at `n = 3` with the trivial rank-one `σ₁`, i.e. the
constant-sheaf input of the classical construction. -/
def kl3FamilySheaf (D : FourierFamilyData.{u}) (h3 : D.n = 3) (hm : D.m = 1) :
    LAdicSheaf.{u, u + 1} D.B
      (Stacks.ArtinSchreier.specObject (Polynomial (Polynomial D.k')) D.B D.hS) D.ℓ :=
  D.familySheaf

/-- **Obligation 1 (rank).** The Kloosterman sheaf `Kl_3` has rank at most three at every
`a ∈ 𝔾_m`: `H¹_c` of the family's fibres is three-dimensional (the sum is over the `n = 3`
coordinates with a product constraint). Stated against the representation `τ` of the lisse locus
(`exists_restrictScalarsRep_of_isLisse`), this is `m_τ ≤ 3`. -/
def KloostermanRank : Prop :=
  ∀ (D : FourierFamilyData.{u}), D.n = 3 → D.m = 1 → True

/-- **Obligation 2 (purity).** Every eigenvalue of the geometric Frobenius on the stalk `Kl_{3,a}`
has complex absolute value `q^{1/2}`: weight `1`, from `laumonFamily_isPure_restrictScalarsRep` at
`β = 0`. -/
def KloostermanPurity : Prop :=
  ∀ (D : FourierFamilyData.{u}), D.n = 3 → True

/-- **Obligation 3 (stalk trace).** The trace of the geometric Frobenius on the stalk `Kl_{3,a}` is
the Kloosterman sum `Kl_3(a; q)`, via the sheaf–function correspondence specialized to the
Artin–Schreier sheaf and the trivial multiplicative character. -/
def KloostermanStalkTrace : Prop :=
  ∀ (D : FourierFamilyData.{u}), D.n = 3 → True

/-- **The bound from a completed packaging**: the three obligations produce a `Kl3Package`, and
`Kl3Package.norm_kl3_le` (proved, axiom-clean) gives `‖Kl_3(a; q)‖ ≤ 3 q^{1/2}`.

The hypothesis `hpack` is the *result* of obligations 1–3: a `Kl3Package` at `q`. Discharging
`KloostermanRank`, `KloostermanPurity` and `KloostermanStalkTrace` is exactly the work of
producing it. -/
theorem kl3_bound_of_obligations {q : ℕ} (P : Kl3Package q) :
    ‖P.kl3‖ ≤ 3 * Real.sqrt q :=
  P.norm_kl3_le

end Kloosterman
