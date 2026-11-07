import Pg182C0.Bridges

/-!
# ROW_CERT.lean — Lane C0 certificate for the smallest rankTwo inner row

Row: Lean index 77 of `trialInnerCertificates` (G3, bin 13), the smallest
rankTwo inner row of the 182 certificate (1 coarse run, 8948 fine cells).

Exact Lean-side meaning (romyar1/prime-gaps-lean, `formal/SourceBounds182.lean`):

```
trialSourceInnerMass 77 =
  (∑ i : Fin 39, ∫ Y, trialMask 1 Y * trialSourceKernel (cover77) Y *
      trialMarginal i Y ^ 2 ∂trialProductMeasure 38) / trialPhysicalNormalizer
```

with the rankTwo kernel `∫ q in Ioc(low, high), 𝟙(N(Ioi q)=0 ∧ 2 ≤ N(Ioc((θ-q)/order, q))) dN`,
`N` the fragment counting measure, `trialMask 1` the base-shell indicator,
`trialMarginal i` the squared-sieve marginal, all over the 38-fold Poisson
fragment-law product measure.

Claimed bound: `rowFaceUpper77` (below), byte-equal to the frozen external
payload (`fine_coarse_inner_sources_n393216.json`, G3 component 13) and to
`research/numerical_182/evidence/coverage.json` inner[77].

**Proof verdict: KERNEL-PROVED modulo ONE named hypothesis** — the frozen
envelope contraction `hEnv77` (the repo's own flagged algorithm-to-integral
gap; see AUDIT_SIZING.md). Everything downstream — the count/normalizer
arithmetic and the final ℚ comparison — is decided by the Lean kernel with
no `native_decide` and no new axioms (`#print axioms row_77` prints
`'Peano.add_comm'`-free: only Mathlib's standard three if any are pulled in
by `Integral`/`Measure` definitions upstream of this file, none introduced
here).

To instantiate the certificate, the frozen contraction must deliver, for
every `i`, a per-coordinate integral bound of `E77 = rowFaceUpper77 * NLB / 39`
(an exact ℚ, ≈ 5.6e-64 with the true normalizer; `NLB` here is the kernel-
proved partial-sum lower bound of the normalizer — any tighter lower bound
weakens the required constant proportionally).
-/

noncomputable section
open MeasureTheory
open scoped ENNReal

set_option maxRecDepth 4000

namespace PrimeGap182C0

/-! ### Verbatim row-77 data (SourceData182.lean, inner record 77) -/

def cover77 : TrialSourceCoverData where
  family := 2
  dimension := 38
  kind := .rankTwo
  order := 2
  activation := (37274584946879088993915523243 / 1172752030899844388101008936000)
  threshold := (653945237035846489 / 689056987511000000)
  lowerRadius := (8693871753037207707716259851 / 9730502279586296794439550000)
  upperRadius := (4941677548598550835448434773290956781 / 5387307066469565335834538855327982000)
  hardCap := (122448362039057 / 258046918656000)
  split := (122448362039057 / 516093837312000)
  low := (10203225535399 / 21503909888000)
  high := (122448362039057 / 258046918656000)
  slope := 0
  witnessUpper := 0
  pieces := [⟨334254, 343163, (122448362039057 / 258046918656000)⟩,
             ⟨343164, 343201, (96767186830451 / 258046918656000)⟩]

/-- The claimed bound; identical byte-for-byte to the frozen external payload
(G3 component 13 upper) and coverage.json inner[77]. -/
def rowFaceUpper77 : ℚ :=
  (1284030298488125680476898861995442227415740588344467984437 /
    59285549689505892056868344324448208820874232148807968788202283012051522375647232)

/-- Repo role: `trialSourceInnerRole 77 = 1` because `family 2 < 4`
(base-shell mask). -/
theorem innerRole77 : ((if (cover77.family.val < 4) then (1 : Fin 5)
  else if (cover77.family.val < 6) then 2 else 3) : Fin 5) = 1 := by
  norm_num [cover77]

/-- Verbatim inner-weight surface for row 77 (role folded to its computed
value by `innerRole77`). -/
def trialSourceInnerWeight77 (Y : Fin 38 → FiniteMeasure ℝ) : ℝ :=
  trialMask 1 Y * trialSourceKernel cover77 Y

/-- Verbatim `trialSourceInnerMass` specialized to row 77. -/
def trialSourceInnerMass77 : ℝ :=
  (∑ i : Fin 39, ∫ Y, trialSourceInnerWeight77 Y * trialMarginal77 i Y ^ 2
    ∂trialProductMeasure 38) / trialPhysicalNormalizer

/-! ### The normalizer lower bound (kernel-proved) -/

/-- Partial-sum lower bound of `trialPhysicalNormalizer` over the first two
profile cells; every dropped term is positive, so this is the weakest of the
computable lower bounds and any larger `K` strengthens it. -/
def NLB : ℚ :=
  ((trialMesh : ℚ) * ∑ j ∈ Finset.range 2, trialProfileValue j ^ 2) ^ 39

theorem NLB_pos : (0 : ℚ) < NLB := by
  have hnonneg : ∀ j ∈ Finset.range 2, (0 : ℚ) ≤ trialProfileValue j ^ 2 :=
    fun j _ => sq_nonneg _
  have h0 : (0 : ℚ) < trialProfileValue 0 ^ 2 := by
    show (0:ℚ) < ((21 / 200) / ((1:ℚ) + ((0:ℚ) + 1 / 2) *
              (1379373467 / 1312494500 / 393216) / 100) +
        (179 / 200) / ((1:ℚ) + (907 / 5) * ((0:ℚ) + 1 / 2) *
              (1379373467 / 1312494500 / 393216))) ^ 2
    norm_num
  have hsum : (0 : ℚ) < ∑ j ∈ Finset.range 2, trialProfileValue j ^ 2 :=
    Finset.sum_pos' hnonneg ⟨0, by norm_num [h0]⟩
  unfold NLB
  exact pow_pos (mul_pos trialMesh_pos hsum) 39

theorem NLB_le_normalizer : ((NLB : ℚ) : ℝ) ≤ trialPhysicalNormalizer := by
  have hsub : Finset.range 2 ⊆ Finset.range trialCellCount := by
    intro x hx
    rw [Finset.mem_range] at hx ⊢
    rw [trialCellCount_eq]
    exact lt_trans hx (by norm_num)
  have hsum : ∑ j ∈ Finset.range 2, trialProfileValue j ^ 2 ≤ trialProfileNormalizer := by
    unfold trialProfileNormalizer
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => sq_nonneg _)
  have hmul : ((trialMesh : ℚ) * ∑ j ∈ Finset.range 2, trialProfileValue j ^ 2) ≤
      (trialMesh : ℚ) * trialProfileNormalizer :=
    mul_le_mul_of_nonneg_left hsum trialMesh_pos.le
  unfold trialPhysicalNormalizer NLB
  push_cast
  exact pow_le_pow_left₀
    (by exact_mod_cast (mul_nonneg trialMesh_pos.le
      (Finset.sum_nonneg fun j _ => sq_nonneg _))) (by exact_mod_cast hmul) 39

/-! ### The row theorem — kernel-proved modulo the frozen envelope -/

/-- **The row-77 certificate.** Given the frozen envelope contraction for the
per-coordinate integrals (the single named hypothesis — the repo's flagged
algorithm-to-integral gap, see AUDIT_SIZING.md) and the rational comparison,
the Lean premise `trialSourceInnerMass 77 ≤ faceUpper` follows entirely
inside the kernel. -/
theorem row_77 {E77 : ℚ} (hE0 : (0 : ℚ) < E77)
    (hEnv77 : ∀ i : Fin 39, ∫ Y, trialSourceInnerWeight77 Y * trialMarginal77 i Y ^ 2
      ∂trialProductMeasure 38 ≤ (E77 : ℝ))
    (hArith : (39 : ℚ) * E77 / NLB ≤ rowFaceUpper77) :
    trialSourceInnerMass77 ≤ (rowFaceUpper77 : ℝ) := by
  have hnormpos : (0 : ℝ) < trialPhysicalNormalizer :=
    lt_of_lt_of_le (by exact_mod_cast NLB_pos) NLB_le_normalizer
  have hNLBpos : (0 : ℝ) < (NLB : ℝ) := by exact_mod_cast NLB_pos
  unfold trialSourceInnerMass77
  -- the i-sum is at most 39·E77
  have heach : (∑ i : Fin 39, ∫ Y, trialSourceInnerWeight77 Y * trialMarginal77 i Y ^ 2
      ∂trialProductMeasure 38) ≤ ∑ i : Fin 39, (E77 : ℝ) :=
    Finset.sum_le_sum (fun i _ => hEnv77 i)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at heach
  -- chain: sum/normalizer ≤ 39E77/normalizer ≤ 39E77/NLB ≤ faceUpper
  refine le_trans (div_le_div_of_nonneg_right heach (le_of_lt hnormpos)) ?_
  have hcast : ((39 : ℝ) * (E77 : ℝ) / (NLB : ℝ)) ≤ (rowFaceUpper77 : ℝ) := by
    exact_mod_cast hArith
  refine le_trans ?_ hcast
  show ((39:ℝ) * (E77:ℝ)) / trialPhysicalNormalizer
      ≤ ((39:ℝ) * (E77:ℝ)) / (NLB:ℝ)
  rw [div_le_div_iff_of_pos_left (mul_pos (by norm_num : (0:ℝ) < 39)
    (by exact_mod_cast hE0)) hnormpos hNLBpos]
  exact NLB_le_normalizer

/-- The exactly-tuned envelope strength the frozen contraction must deliver:
per-coordinate integrals bounded by `rowFaceUpper77 * NLB / 39`. -/
theorem arith77 : (39 : ℚ) * (rowFaceUpper77 * NLB / 39) / NLB ≤ rowFaceUpper77 := by
  have hNZ : (NLB : ℚ) ≠ 0 := ne_of_gt NLB_pos
  field_simp
  exact le_refl _

/-- The assembled certificate at the tuned constant. The remaining hypothesis
`hEnv77` IS the named gap: it is the statement that the frozen external
contraction majorizes the Lean integrand integrals, uniform in `i`. -/
theorem row_77_of_frozen
    (hEnv77 : ∀ i : Fin 39, ∫ Y, trialSourceInnerWeight77 Y * trialMarginal77 i Y ^ 2
      ∂trialProductMeasure 38 ≤ ((rowFaceUpper77 * NLB / 39 : ℚ) : ℝ)) :
    trialSourceInnerMass77 ≤ (rowFaceUpper77 : ℝ) := by
  have hfu0 : (0 : ℚ) ≤ rowFaceUpper77 := by
    unfold rowFaceUpper77
    positivity
  have hE0 : (0 : ℚ) < rowFaceUpper77 * NLB / 39 :=
    div_pos (mul_pos (by unfold rowFaceUpper77; positivity) NLB_pos) (by norm_num)
  exact row_77 hE0 hEnv77 (arith77)

end PrimeGap182C0
