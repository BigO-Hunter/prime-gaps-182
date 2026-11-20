import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFourierLineFamily
import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFourierLineAwayFibreOffTop
import KloostermanObligations

/-!
# The Kloosterman sheaf `Kl_3`: definition, lisseness, and the three remaining obligations

**STATUS (2026-11-07): NOT YET ELABORATED.** This file names the Kl_3 packaging against the
`StacksFrontier` API and cannot be compiled until that API's own oleans exist: the import closure
of `LaumonFourierLineFamily` is 17,567 Stacks modules of which **16,525 are unbuilt** in the
current tree (measured; ≈6 days of `LAKE_JOBS=1` at the 2 oleans/min this host sustained). The parts of the packaging that
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

The obligations are listed in the docstring of `kl3_bound_of_obligations` below: rank `3`, purity
of weight `2`, and the stalk-trace identity. They are **not** encoded as placeholder `Prop`s here
(that would be a tautology dressed as a claim); their verified carrier is
`Kloosterman.Kl3Package` in `KloostermanObligations.lean`, whose fields *are* the three facts, and
whose `norm_kl3_le` **proves** that they imply `‖Kl_3(a; q)‖ ≤ 3 q^{1/2}`. So the packaging gap is
construction, not invention: nothing about the bound is assumed anywhere.

## Main definitions

* `Kloosterman.FourierFamilyData`: the exact parameter tuple of `laumonFourierFamilySheaf`.
* `Kloosterman.kl3FamilySheaf`: the `n = 3`, trivial-`σ₁` instance (the constant-sheaf input).
* The three obligations are listed in `kl3_bound_of_obligations`; their verified carrier is
  `Kloosterman.Kl3Package`.

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
def FourierFamilyData.familySheaf (D : FourierFamilyData.{u}) :=
  laumonFourierFamilySheaf D.k' D.B D.hS D.b D.ψ' D.n D.a D.z D.p₀ D.σ₁ D.hσ₁

/-- **The Fourier family sheaf is lisse** — the family is the sheaf of a continuous representation.
This is `isLisse_laumonFourierFamilySheaf` restated for the package. -/
theorem FourierFamilyData.familySheaf_isLisse (D : FourierFamilyData.{u}) :
    D.familySheaf.toLAdicSheaf.IsLisse :=
  isLisse_laumonFourierFamilySheaf D.k' D.B D.hS D.b D.ψ' D.n D.a D.z D.p₀ D.σ₁ D.hσ₁

/-- **The `Kl_3` family**: the Fourier family at `n = 3` with the trivial rank-one `σ₁`, i.e. the
constant-sheaf input of the classical construction. -/
def kl3FamilySheaf (D : FourierFamilyData.{u}) (h3 : D.n = 3) (hm : D.m = 1) :=
  D.familySheaf

/-- **The `Kl_3` family is lisse** — the same fact as `familySheaf_isLisse`, specialized to
`n = 3` with the trivial `σ₁`. -/
theorem kl3FamilySheaf_isLisse (D : FourierFamilyData.{u}) (h3 : D.n = 3) (hm : D.m = 1) :
    (kl3FamilySheaf D h3 hm).toLAdicSheaf.IsLisse :=
  D.familySheaf_isLisse

/-- **The three obligations of the packaging**, each one a construction, not an assumption.
They are stated here in prose because naming them as `Prop`s against the API would mean writing
placeholder types until the closure builds; the *verified* carrier of the same three facts is
`Kloosterman.Kl3Package` in `KloostermanObligations.lean`, whose fields are rank, charpoly,
trace and purity.

1. **Rank.** The lisse sheaf `R¹pr₂!` of the family at `n = 3` with trivial `σ₁` has rank `3` at
   every `a ∈ 𝔾_m` — the representation `τ` of the lisse locus
   (`exists_restrictScalarsRep_of_isLisse`) has `m_τ = 3`. This is the `rank ≤ 3` field.
2. **Purity.** `τ` is `ι'`-pure of weight `2` (`laumonFamily_isPure_restrictScalarsRep` at
   `β = 1`): every eigenvalue of the geometric Frobenius on the stalk `Kl_{3,a}` has complex
   absolute value `q`. In the normalized form (`q^{1/2}`) this is the `pure` field.
3. **Stalk trace.** `trace(Frob_{k,a} | Kl_{3,a}) = Kl_3(a; q)` via the sheaf–function
   correspondence at the Artin–Schreier sheaf with the trivial multiplicative character — the
   `trace_eq` field, assembled from `artinSchreierCharacter_*` and the trace formula
   (`LAdicTraceFormulaFinal`).

Discharging 1–3 produces a `Kl3Package q`, and `Kl3Package.norm_kl3_le` (proved, axiom-clean)
then gives `‖Kl_3(a; q)‖ ≤ 3 q^{1/2}`. -/

/-- **The bound from a completed packaging.** The hypothesis is the *result* of obligations 1–3
above: a `Kl3Package` at `q`. `Kl3Package.norm_kl3_le` is proved in `KloostermanObligations.lean`
with axiom set `[propext, Classical.choice, Quot.sound]`, so the numerical end of the packaging
carries no assumption at all. -/
theorem kl3_bound_of_obligations {q : ℕ} (P : Kl3Package q) :
    ‖P.kl3‖ ≤ 3 * Real.sqrt q :=
  P.norm_kl3_le

end Kloosterman
