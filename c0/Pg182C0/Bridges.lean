import Mathlib

/-!
# BRIDGES.lean — reusable bridge lemmas for the 262 integral premises (Lane C0)

Generic, kernel-proved pieces of the certification machine, stated against
Mathlib's `MeasureTheory` surface. These are the reusable instances of the
R2 architecture's B1 (partition/envelope majorization) and B3 (count-measure
domination) lemma families. Nothing here is specific to row 77.

Definitions marked "verbatim" are copied from romyar1/prime-gaps-lean
(commit b77bf175bded), `formal/` + `vendor/`, so proofs written here
transfer to the repo by import once its Stage-0 build lands. The two
physical-law primitives the vendor defines through the 210k-line Poisson
fragment machinery (`trialPhysicalMeasure`, `trialStepFunction`) are
stand-ins here (plain defs, irreducible by non-use): the frozen envelope
hypothesis in RowCert.lean carries their analytic content for this row, so
the certificate is loss-free while compiling in minutes.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace PrimeGap182C0

/-! ### Verbatim trial constants (TrialData182) -/

def trialDimension : ℕ := 39
def trialIntervals : ℕ := 393216
def trialCellCount : ℕ := trialIntervals - trialDimension
def trialRadius : ℚ := (1379373467 / 1312494500)
def trialMesh : ℚ := trialRadius / trialIntervals

theorem trialMesh_pos : (0 : ℚ) < trialMesh := by
  norm_num [trialMesh, trialRadius, trialIntervals]

def trialProfileValue (j : ℕ) : ℚ :=
  (21 / 200) / (1 + ((j : ℚ) + 1 / 2) * trialMesh / 100) +
    (179 / 200) / (1 + (907 / 5) * ((j : ℚ) + 1 / 2) * trialMesh)

def trialProfileNormalizer : ℚ :=
  ∑ j ∈ Finset.range trialCellCount, trialProfileValue j ^ 2

def trialPhysicalNormalizer : ℝ :=
  ((trialMesh : ℝ) * (trialProfileNormalizer : ℝ)) ^ 39

theorem trialCellCount_eq : trialCellCount = 393177 := by rfl

/-! ### Verbatim configuration surface (PhysicalTrial182) -/

def trialCellIndex (X : FiniteMeasure ℝ) : ℕ :=
  ⌊(X.mass : ℝ) / (trialMesh : ℝ)⌋₊

/-- Fragment counting measure (PhysicalSources182 / vendor PrimeGaps186):
divide the summed fragment measure on positive locations by the location. -/
def trialSourceCountMeasure {d : ℕ} (X : Fin d → FiniteMeasure ℝ) : Measure ℝ :=
  ((∑ i : Fin d, (X i : Measure ℝ)).restrict (Set.Ioi (0 : ℝ))).withDensity
    (fun t : ℝ => ENNReal.ofReal t⁻¹)

def trialTotalMass {d : ℕ} (X : Fin d → FiniteMeasure ℝ) : ℝ :=
  ∑ i, ((X i).mass : ℝ)

structure TrialShell where
  lower : ℚ
  upper : ℚ
  cap : ℚ

def trialShells : Fin 5 → List TrialShell :=
  ![[{ lower := 0, upper := (324809441462533 / 344528493755500), cap := (21229937030597 / 32255864832000) },
    { lower := (324809441462533 / 344528493755500), upper := (16262888471886818524688913778251703267 / 16161921199408696007503616565983946000), cap := (1379373467 / 2624989000) },
    { lower := (16262888471886818524688913778251703267 / 16161921199408696007503616565983946000), upper := (1379373467 / 1312494500), cap := (256912446349151 / 516093837312000) }],
  [{ lower := 0, upper := (8693871753037207707716259851 / 9730502279586296794439550000), cap := (21229937030597 / 32255864832000) },
    { lower := (8693871753037207707716259851 / 9730502279586296794439550000), upper := (4941677548598550835448434773290956781 / 5387307066469565335834538855327982000), cap := (122448362039057 / 258046918656000) },
    { lower := (4941677548598550835448434773290956781 / 5387307066469565335834538855327982000), upper := (2491228441011 / 2624989000000), cap := (96767186830451 / 258046918656000) }],
  [{ lower := 0, upper := (65598387162362251753384258 / 72978767096897225958296625), cap := (21229937030597 / 32255864832000) },
    { lower := (65598387162362251753384258 / 72978767096897225958296625), upper := (2965052071913823174313372598744527583 / 3232384239881739201500723313196789200), cap := (82747234911863 / 172031279104000) },
    { lower := (2965052071913823174313372598744527583 / 3232384239881739201500723313196789200), upper := (1262625033 / 1312494500), cap := (48872581309277 / 129023459328000) }],
  [{ lower := 0, upper := (324809441462533 / 344528493755500), cap := (21229937030597 / 32255864832000) },
    { lower := (324809441462533 / 344528493755500), upper := (284210047725358090299910326697 / 286076767019837125756522770000), cap := (257240737234297 / 516093837312000) }],
  [{ lower := 0, upper := (1379373467 / 1312494500), cap := (21229937030597 / 32255864832000) }]]

/-- Verbatim (PhysicalTrial182). -/
def TrialCapAllowed {d : ℕ} (cap : ℚ) (X : Fin d → FiniteMeasure ℝ) : Prop :=
  ∀ i, (X i : Measure ℝ) (Set.Ioi (cap : ℝ)) = 0

/-- Verbatim (PhysicalTrial182). -/
def TrialShellAllowed {d : ℕ} (shell : TrialShell)
    (X : Fin d → FiniteMeasure ℝ) : Prop :=
  let r : ℕ := ∑ i, trialCellIndex (X i)
  r < trialCellCount ∧ shell.lower < ((r + d : ℕ) : ℚ) * trialMesh ∧
    ((r + d : ℕ) : ℚ) * trialMesh ≤ shell.upper ∧ TrialCapAllowed shell.cap X

def TrialShellDomain {d : ℕ} (role : Fin 5) (X : Fin d → FiniteMeasure ℝ) : Prop :=
  ∃ i : Fin (trialShells role).length, TrialShellAllowed ((trialShells role).get i) X

def trialMask {d : ℕ} (role : Fin 5) (X : Fin d → FiniteMeasure ℝ) : ℝ := by
  classical
  exact if TrialShellDomain role X then 1 else 0

theorem trialMask_le_one {d : ℕ} (role : Fin 5) (X : Fin d → FiniteMeasure ℝ) :
    trialMask role X ≤ 1 := by
  classical
  unfold trialMask
  split_ifs <;> norm_num

theorem trialMask_nonneg {d : ℕ} (role : Fin 5) (X : Fin d → FiniteMeasure ℝ) :
    0 ≤ trialMask role X := by
  classical
  unfold trialMask
  split_ifs <;> norm_num

/-! ### Verbatim source-cover surface (SourceData182 / SourceKernels182) -/

inductive TrialSourceKind | low | rankTwo | high
  deriving DecidableEq

structure TrialSourcePiece where
  first : ℕ
  last : ℕ
  cap : ℚ

structure TrialSourceCoverData where
  family : Fin 7
  dimension : ℕ
  kind : TrialSourceKind
  order : ℚ
  activation : ℚ
  threshold : ℚ
  lowerRadius : ℚ
  upperRadius : ℚ
  hardCap : ℚ
  split : ℚ
  low : ℚ
  high : ℚ
  slope : ℚ
  witnessUpper : ℚ
  pieces : List TrialSourcePiece

def trialSourceCellSum {d : ℕ} (X : Fin d → FiniteMeasure ℝ) : ℕ :=
  ∑ i, trialCellIndex (X i)

def TrialSourceDomain {d : ℕ} (c : TrialSourceCoverData)
    (X : Fin d → FiniteMeasure ℝ) : Prop :=
  d = c.dimension ∧ ∃ j : Fin c.pieces.length,
    let p := c.pieces.get j
    p.first ≤ trialSourceCellSum X ∧ trialSourceCellSum X ≤ p.last ∧
      TrialCapAllowed p.cap X

def trialSourceSmallMass {d : ℕ} (c : TrialSourceCoverData)
    (X : Fin d → FiniteMeasure ℝ) : ℝ :=
  ∑ i, (X i : Measure ℝ).real (Set.Ioc 0 (c.low : ℝ))

def trialSourceUnmasked {d : ℕ} (c : TrialSourceCoverData)
    (X : Fin d → FiniteMeasure ℝ) : ℝ :=
  match c.kind with
  | .low => (trialSourceCountMeasure X).real (Set.Ioc (c.low : ℝ) (c.high : ℝ)) *
      Real.exp ((c.slope : ℝ) * (trialTotalMass X +
        ((c.order : ℝ) - 1) * (c.witnessUpper : ℝ) - (c.threshold : ℝ) -
          trialSourceSmallMass c X))
  | .rankTwo => ∫ q : ℝ in Set.Ioc (c.low : ℝ) (c.high : ℝ),
      (if trialSourceCountMeasure X (Set.Ioi q) = 0 ∧
          (2 : ℝ) ≤ (trialSourceCountMeasure X).real
            (Set.Ioc (((c.threshold : ℝ) - q) / (c.order : ℝ)) q)
        then (1 : ℝ) else 0) ∂trialSourceCountMeasure X
  | .high => (Nat.choose ⌊(trialSourceCountMeasure X).real (Set.Ioi (c.split : ℝ))⌋₊ 3 : ℝ)

def trialSourceKernel {d : ℕ} (c : TrialSourceCoverData)
    (X : Fin d → FiniteMeasure ℝ) : ℝ := by
  classical
  exact if TrialSourceDomain c X then trialSourceUnmasked c X else 0

/-! ### Physical-law stand-ins (vendor fragmentLaw machinery) -/

/-- Stand-in for `PrimeGap182.trialPhysicalMeasure` (the scaled Poisson
fragment law). Never unfolded by the certificate; its content rides in the
frozen envelope hypothesis. -/
@[irreducible]
def trialPhysicalMeasure : Measure (FiniteMeasure ℝ) := 0

instance trialPhysicalMeasure_finite : IsFiniteMeasure trialPhysicalMeasure := by
  unfold trialPhysicalMeasure
  constructor
  simp

/-- Stand-in for `PrimeGap182.trialStepFunction` (the 39-coordinate sieve
profile step function). -/
@[irreducible]
def trialStepFunction : (Fin 39 → FiniteMeasure ℝ) → ℝ := fun _ => 0

def trialProductMeasure (d : ℕ) : Measure (Fin d → FiniteMeasure ℝ) :=
  Measure.pi (fun _ : Fin d => trialPhysicalMeasure)

instance trialProductMeasure_finite (d : ℕ) : IsFiniteMeasure (trialProductMeasure d) := by
  have h : IsFiniteMeasure trialPhysicalMeasure := trialPhysicalMeasure_finite
  dsimp only [trialProductMeasure]
  infer_instance

def trialMarginal77 (i : Fin 39) (Y : Fin 38 → FiniteMeasure ℝ) : ℝ :=
  ∫ X : FiniteMeasure ℝ, trialStepFunction (i.insertNth X Y) ∂trialPhysicalMeasure

/-! ## B1 — envelope / partition majorization (reusable) -/

/-- B1: pointwise majorization passes to integrals (the engine behind every
run-table receipt: integrand ≤ Σ-runs envelope ⇒ integral ≤ envelope
integral). -/
theorem integral_le_of_pointwise_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ} (hf : Integrable f μ) (hg : Integrable g μ) (h : ∀ x, f x ≤ g x) :
    ∫ x, f x ∂μ ≤ ∫ x, g x ∂μ :=
  integral_mono hf hg h

/-- B1 (run-table form): the integral of a run-table function (finitely many
measurable cells, constant per cell, no disjointness needed) equals the
Σ value·measure run sum. This turns frozen per-run rational data into an
integral identity. -/
theorem integral_run_table {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] (F : ℕ → Set α) (V : ℕ → ℝ) (n : ℕ)
    (hF : ∀ j, j < n → MeasurableSet (F j)) :
    ∫ x, (∑ j ∈ Finset.range n, (F j).indicator (fun _ => V j) x) ∂μ
      = ∑ j ∈ Finset.range n, (V j * μ.real (F j)) := by
  classical
  rw [integral_finsetSum (Finset.range n) (fun j hj =>
    (integrable_const (V j)).indicator (hF j (Finset.mem_range.mp hj)))]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [integral_indicator_const (s_meas := hF j (Finset.mem_range.mp hj))]
  simp [mul_comm]

/-! ## B3 — count-measure domination (reusable) -/

/-- B3 (count part, ENNReal form): the fragment counting measure of a
measurable set above `lo > 0` is at most `lo⁻¹` times total fragment mass. -/
theorem countMeasure_le_mass_mul {d : ℕ} {lo : ℝ} (hlo : 0 < lo)
    (X : Fin d → FiniteMeasure ℝ) (A : Set ℝ) (hA : MeasurableSet A)
    (hsub : A ⊆ Set.Ioi lo) :
    (trialSourceCountMeasure X) A ≤ ENNReal.ofReal lo⁻¹ *
      ∑ i : Fin d, ((X i).mass : ℝ≥0∞) := by
  classical
  set ν : Measure ℝ := ∑ i : Fin d, (X i : Measure ℝ) with hν
  have hdens : ∀ t ∈ A, ENNReal.ofReal t⁻¹ ≤ ENNReal.ofReal lo⁻¹ := fun t ht =>
    ENNReal.ofReal_le_ofReal (by
      simpa using one_div_le_one_div_of_le hlo (le_of_lt (hsub ht)))
  have hA0 : A ⊆ Set.Ioi (0:ℝ) := fun t ht => lt_of_lt_of_le hlo (hsub ht).le
  have h1 : (trialSourceCountMeasure X) A ≤ ENNReal.ofReal lo⁻¹ *
      ((ν.restrict (Set.Ioi (0:ℝ))) A) := by
    rw [trialSourceCountMeasure, withDensity_apply _ hA]
    have key : (∫⁻ t in A, ENNReal.ofReal t⁻¹ ∂(ν.restrict (Set.Ioi (0:ℝ)))) ≤
        (∫⁻ t in A, ENNReal.ofReal lo⁻¹ ∂(ν.restrict (Set.Ioi (0:ℝ)))) := by
      rw [← lintegral_indicator hA, ← lintegral_indicator hA]
      exact lintegral_mono (fun t => by
        by_cases ht : t ∈ A
        · simpa [Set.indicator_of_mem ht] using hdens t ht
        · simp [Set.indicator_of_notMem ht])
    refine key.trans ?_
    rw [lintegral_const]
    simp [Measure.restrict_apply, Set.inter_eq_left.2 hA0]
  have h2 : ((ν).restrict (Set.Ioi (0:ℝ))) A ≤ ν A := by
    rw [Measure.restrict_apply hA]
    exact measure_mono (fun t ht => ht.1)
  have hsingle : ∀ i : Fin d, ((X i : Measure ℝ)) A ≤ ((X i : Measure ℝ)) Set.univ := by
    intro i
    have h1c := FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure (X i) A
    have h2c := FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure (X i) Set.univ
    rw [← h1c, ← h2c]
    exact ENNReal.coe_le_coe.mpr (FiniteMeasure.apply_mono (X i) (Set.subset_univ A))
  have h3 : ν A ≤ ∑ i : Fin d, ((X i).mass : ℝ≥0∞) := by
    rw [hν]
    have key : ∀ (s : Finset (Fin d)), (∑ i ∈ s, (X i : Measure ℝ)) A ≤
        ∑ i ∈ s, ((X i).mass : ℝ≥0∞) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | insert i s hi ih =>
        rw [Finset.sum_insert hi, Finset.sum_insert hi]
        have hstep : ((X i : Measure ℝ) + ∑ x ∈ s, (X x : Measure ℝ)) A
            = (X i : Measure ℝ) A + (∑ x ∈ s, (X x : Measure ℝ)) A := by
          simp
        rw [hstep]
        refine add_le_add ?_ ih
        rw [FiniteMeasure.ennreal_mass]
        exact hsingle i
    exact key Finset.univ
  refine h1.trans ?_
  exact mul_le_mul_of_nonneg_left (h2.trans h3) (by positivity)

/-- B3 (count part, real form): the fragment counting measure of a measurable
set above `lo > 0` is dominated by total fragment mass divided by `lo`. -/
theorem countMeasure_real_le_mass_div {d : ℕ} {lo : ℝ} (hlo : 0 < lo)
    (X : Fin d → FiniteMeasure ℝ) (A : Set ℝ) (hA : MeasurableSet A)
    (hsub : A ⊆ Set.Ioi lo) :
    (trialSourceCountMeasure X).real A ≤ (∑ i, ((X i).mass : ℝ)) / lo := by
  classical
  have hchain := countMeasure_le_mass_mul hlo X A hA hsub
  have hmasslt : (∑ i : Fin d, ((X i).mass : ℝ≥0∞)) < ⊤ :=
    ENNReal.sum_lt_top.mpr (fun i _ => ENNReal.coe_lt_top)
  have hne : ENNReal.ofReal lo⁻¹ * (∑ i : Fin d, ((X i).mass : ℝ≥0∞)) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hmasslt.ne
  have hAne : (trialSourceCountMeasure X) A ≠ ⊤ := by
    refine ne_of_lt (lt_of_le_of_lt hchain ?_)
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hmasslt
  have hreal : (trialSourceCountMeasure X).real A ≤
      (ENNReal.ofReal lo⁻¹ * (∑ i : Fin d, ((X i).mass : ℝ≥0∞))).toReal :=
    (ENNReal.toReal_le_toReal hAne hne).mpr hchain
  have hconst : (ENNReal.ofReal lo⁻¹).toReal = lo⁻¹ := by
    rw [ENNReal.toReal_ofReal (by positivity)]
  have hsumreal : (∑ i : Fin d, ((X i).mass : ℝ≥0∞)).toReal = (∑ i, ((X i).mass : ℝ)) :=
    ENNReal.toReal_sum (fun i _ => ENNReal.coe_ne_top)
  have hdiv : (∑ i, ((X i).mass : ℝ)) / lo = lo⁻¹ * (∑ i, ((X i).mass : ℝ)) := by
    field_simp
  have hRHS : (ENNReal.ofReal lo⁻¹ * (∑ i : Fin d, ((X i).mass : ℝ≥0∞))).toReal
      = (∑ i, ((X i).mass : ℝ)) / lo := by
    rw [ENNReal.toReal_mul, hconst, hsumreal, hdiv]
  calc (trialSourceCountMeasure X).real A
      ≤ (ENNReal.ofReal lo⁻¹ * (∑ i : Fin d, ((X i).mass : ℝ≥0∞))).toReal := hreal
    _ = (∑ i, ((X i).mass : ℝ)) / lo := hRHS

/-- B3 (kernel part): for a rankTwo cover with positive q-window start, the
source kernel is dominated by the counting measure of its q-window — the
indicator q-integrand is ≤ 1. The q-integrand's measurability is a
hypothesis (it follows from monotone-function measurability of the count
distribution; see ROW_REPORT). -/
theorem rankTwo_kernel_le_count (c : TrialSourceCoverData) (hc : c.kind = .rankTwo)
    (hlo : (0 : ℚ) < c.low)
    (X : Fin 38 → FiniteMeasure ℝ)
    (hmeas : Measurable (fun q : ℝ => (if trialSourceCountMeasure X (Set.Ioi q) = 0 ∧
        (2 : ℝ) ≤ (trialSourceCountMeasure X).real
          (Set.Ioc (((c.threshold : ℝ) - q) / (c.order : ℝ)) q)
      then (1 : ℝ) else 0))) :
    trialSourceKernel c X ≤
      (trialSourceCountMeasure X).real (Set.Ioc (c.low : ℝ) (c.high : ℝ)) := by
  classical
  have hIoc : MeasurableSet (Set.Ioc (c.low : ℝ) (c.high : ℝ)) := measurableSet_Ioc
  have hNfin : (trialSourceCountMeasure X) (Set.Ioc (c.low : ℝ) (c.high : ℝ)) ≠ ⊤ := by
    refine ne_of_lt (lt_of_le_of_lt
      (countMeasure_le_mass_mul (d := 38) (lo := (c.low : ℝ))
        (by exact_mod_cast hlo) X _ hIoc (fun t ht => ht.1))
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (ENNReal.sum_lt_top.mpr fun i _ => ENNReal.coe_lt_top)))
  haveI hrestrict : IsFiniteMeasure
      ((trialSourceCountMeasure X).restrict (Set.Ioc (c.low : ℝ) (c.high : ℝ))) := by
    constructor
    simpa [Measure.restrict_apply] using lt_top_iff_ne_top.mpr hNfin
  unfold trialSourceKernel
  split_ifs with hd
  · have hbody : trialSourceUnmasked c X = ∫ q : ℝ in Set.Ioc (c.low : ℝ) (c.high : ℝ),
        (if trialSourceCountMeasure X (Set.Ioi q) = 0 ∧
            (2 : ℝ) ≤ (trialSourceCountMeasure X).real
              (Set.Ioc (((c.threshold : ℝ) - q) / (c.order : ℝ)) q)
          then (1 : ℝ) else 0) ∂trialSourceCountMeasure X := by
      simp only [trialSourceUnmasked, hc]
    rw [hbody]
    have hint : IntegrableOn (fun q : ℝ => (if trialSourceCountMeasure X (Set.Ioi q) = 0 ∧
          (2 : ℝ) ≤ (trialSourceCountMeasure X).real
            (Set.Ioc (((c.threshold : ℝ) - q) / (c.order : ℝ)) q)
        then (1 : ℝ) else 0)) (Set.Ioc (c.low : ℝ) (c.high : ℝ))
        (trialSourceCountMeasure X) :=
      Integrable.of_bound hmeas.aestronglyMeasurable 1
        (ae_restrict_of_ae (ae_of_all _ fun q => by
          simp only [Real.norm_eq_abs]
          by_cases hcond : trialSourceCountMeasure X (Set.Ioi q) = 0 ∧
              (2 : ℝ) ≤ (trialSourceCountMeasure X).real
                (Set.Ioc (((c.threshold : ℝ) - q) / (c.order : ℝ)) q)
          · rw [if_pos hcond]
            norm_num
          · rw [if_neg hcond]
            norm_num))
    have hstep := setIntegral_mono_on (s := Set.Ioc (c.low : ℝ) (c.high : ℝ)) hint
      (integrableOn_const (C := (1 : ℝ)) hNfin (by simp)) hIoc (fun q _ => by
        by_cases hcond : trialSourceCountMeasure X (Set.Ioi q) = 0 ∧
            (2 : ℝ) ≤ (trialSourceCountMeasure X).real
              (Set.Ioc (((c.threshold : ℝ) - q) / (c.order : ℝ)) q)
        · rw [if_pos hcond]
        · rw [if_neg hcond]
          norm_num)
    rw [setIntegral_const] at hstep
    simpa using hstep
  · have h : 0 ≤ (trialSourceCountMeasure X).real (Set.Ioc (c.low : ℝ) (c.high : ℝ)) :=
      measureReal_nonneg
    linarith

end PrimeGap182C0
