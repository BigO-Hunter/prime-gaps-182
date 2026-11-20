import Pg182D1.HEnv77

/-!
# HENV77ROW77.lean — the row-77 instantiation of the hEnv77 discharge schema

Row 77 of the C0 certificate (Lean index 77 of `trialInnerCertificates`,
G3 rank_two component 13 of the frozen payload) has ONE coarse run: the
fine-cell window 334254..343201 (8948 cells, sum range
38*334254 .. 38*343201 = 12701652 .. 13041638).

This file plugs the frozen payload's exact numbers into the D1 discharge
schema (`HEnv77.lean`):

* `sigma77` — the frozen per-run integrand envelope (the D3 affine reference
  upper of the row's single prefix), exact rational;
* `p77` — the frozen row mass (`source_mass`, a point interval: lower =
  upper), exact rational;
* `c77max` — the window's maximal sum-cell value, sealing the support.

`row77_integral_le` is the discharge: given C0's kernel-side bounds (the
integrand is dominated by the frozen envelope and vanishes above `c77max`)
and the D1-data window mass bound (stated as the exact sum of per-sum-cell
class masses), the row integral is at most E77.

**Data verdict (receipt/percell_emission.json, machine-decided below).**
The D1-data comparison of the proved Chernoff envelope class against the
frozen masses FAILS at row 77: the certified envelope lower bound
`env38lo77 = 10434910272290039 / 20000000000000000` (at c = c77max, s = 1/4)
exceeds `p77` — `row77_data_gap_is_false` decides this exactly. The gap is
the envelope-class weakness documented in D1C_REPORT.md, not a missing
computation: 0/8948 fine cells and 68/73 rank/high rows pass, while the five
`high` rows (source mass exactly 1) DO pass — see the receipt batch
`receipt/lean/Percell77RunLevel.lean` (5 holds, all decided, axiom-free).
-/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace PrimeGap182D1

/-- Frozen row-77 per-run integrand envelope (D3 affine reference upper,
`fine_coarse_inner_sources_n393216.json`, G3 component_index 13). -/
def sigma77 : ℚ := 24959464591110552161 / 1267650600228229401496703205376

/-- Frozen row-77 mass (`source_mass.upper`; the interval is a point). -/
def p77 : ℚ :=
  253438844523999567461371639857525695995105216506475714569 /
    3213876088517980551083924184682325205044405987565585670602752

/-- Maximal sum-cell value of the row-77 window. -/
def c77max : ℕ := 38 * 343201

/-- The kernel-checked numeric product (norm_num: rational normalization). -/
theorem sigma77_mul_p77_eq :
    sigma77 * p77
      = 6325697865908739665694892373861436812872822358518057247093542087018622133609 /
        4074071952668972172536891376818756322102936787331872501272280898708762599526673412366794752 := by
  norm_num [sigma77, p77]

/-- The certified envelope lower bound at the run's maximal sum cell
(receipt/percell_emission.json; outward-rounded, FAIL direction). -/
def env38lo77 : ℚ := 10434910272290039 / 20000000000000000

/-- The D1-data comparison at row 77: does the frozen mass dominate the
proved Chernoff envelope? -/
def Row77DataGap : Prop := (p77 : ℚ) ≥ env38lo77

/-- Machine verdict: the D1-data comparison FAILS at row 77 (decided
exactly; see receipt/lean/axcheck_percell.txt for the axiom footprint). -/
theorem row77_data_gap_is_false : ¬ Row77DataGap := by
  norm_num [Row77DataGap, p77, env38lo77]

/-- **The row-77 discharge.** The schema of `hEnv77_discharge` instantiated
at the frozen payload: a constant per-run envelope on the window run set,
with the D1-data window mass bound (the exact per-class sum) and the frozen
sum comparison. This is the lemma C0's `RowCert` consumes (uniform in the
profile coordinate i — nothing depends on i). -/
theorem row77_integral_le
    {μ : Measure (FiniteMeasure ℝ)} [IsProbabilityMeasure μ]
    {f : (Fin 38 → FiniteMeasure ℝ) → ℝ}
    (E77 : ℝ)
    (hnn : ∀ Y, 0 ≤ f Y)
    (hsup : ∀ Y, f Y ≤ (sigma77 : ℝ))
    (hzero : ∀ Y, c77max < sumCell Y → f Y = 0)
    (hdata : (∑ c ∈ Finset.range (c77max + 1),
        (Measure.pi fun _ : Fin 38 => μ).real
          {Y : Fin 38 → FiniteMeasure ℝ | sumCell Y = c}) ≤ (p77 : ℝ))
    (hsum : (sigma77 : ℝ) * p77 ≤ E77) :
    (∫ Y, f Y ∂(Measure.pi fun _ : Fin 38 => μ)) ≤ E77 := by
  classical
  have hσpos : 0 ≤ (sigma77 : ℝ) :=
    by exact_mod_cast le_of_lt (show (0 : ℚ) < sigma77 by norm_num [sigma77])
  -- the run envelope: σ77 on the window classes, 0 outside
  set S : (Fin 38 → FiniteMeasure ℝ) → ℝ := fun Y =>
    ∑ c ∈ Finset.range (c77max + 1),
      {Y' : Fin 38 → FiniteMeasure ℝ | sumCell Y' = c}.indicator
        (fun _ => (sigma77 : ℝ)) Y with hSdef
  have hSmeas : Measurable S := measurable_runEnvelope (fun _ => (sigma77 : ℝ))
    (Finset.range (c77max + 1))
  -- termwise facts (mirroring D1Engine's proved block)
  have hterm0 : ∀ (Y : Fin 38 → FiniteMeasure ℝ) (c : ℕ),
      c ∈ Finset.range (c77max + 1) →
      0 ≤ {Y' : Fin 38 → FiniteMeasure ℝ | sumCell Y' = c}.indicator
        (fun _ => (sigma77 : ℝ)) Y := by
    intro Y c hc
    by_cases hYc : sumCell Y = c
    · have hmem : Y ∈ ({Y' : Fin 38 → FiniteMeasure ℝ | sumCell Y' = c} :
        Set (Fin 38 → FiniteMeasure ℝ)) := hYc
      rw [Set.indicator_of_mem hmem]
      exact hσpos
    · have hmem : Y ∉ ({Y' : Fin 38 → FiniteMeasure ℝ | sumCell Y' = c} :
        Set (Fin 38 → FiniteMeasure ℝ)) := fun h => hYc h
      rw [Set.indicator_of_notMem hmem]
  have htermle : ∀ (Y : Fin 38 → FiniteMeasure ℝ) (c : ℕ),
      c ∈ Finset.range (c77max + 1) →
      {Y' : Fin 38 → FiniteMeasure ℝ | sumCell Y' = c}.indicator
        (fun _ => (sigma77 : ℝ)) Y ≤ (sigma77 : ℝ) := by
    intro Y c hc
    by_cases hYc : sumCell Y = c
    · have hmem : Y ∈ ({Y' : Fin 38 → FiniteMeasure ℝ | sumCell Y' = c} :
        Set (Fin 38 → FiniteMeasure ℝ)) := hYc
      rw [Set.indicator_of_mem hmem]
    · have hmem : Y ∉ ({Y' : Fin 38 → FiniteMeasure ℝ | sumCell Y' = c} :
        Set (Fin 38 → FiniteMeasure ℝ)) := fun h => hYc h
      rw [Set.indicator_of_notMem hmem]
      exact hσpos
  have hSint : Integrable S (Measure.pi fun _ : Fin 38 => μ) := by
    refine (integrable_const (∑ c ∈ Finset.range (c77max + 1),
      (sigma77 : ℝ))).mono' hSmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun Y => by
        rw [Real.norm_eq_abs, abs_of_nonneg]
        · exact Finset.sum_le_sum (fun c hc => htermle Y c hc)
        · exact Finset.sum_nonneg (fun c hc => hterm0 Y c hc)))
  have hpt : ∀ Y, f Y ≤ S Y := by
    intro Y
    by_cases hY : sumCell Y ∈ Finset.range (c77max + 1)
    · have hmem : Y ∈ ({Y' : Fin 38 → FiniteMeasure ℝ | sumCell Y' = sumCell Y} :
        Set (Fin 38 → FiniteMeasure ℝ)) := rfl
      calc f Y ≤ (sigma77 : ℝ) := hsup Y
        _ = {Y' : Fin 38 → FiniteMeasure ℝ | sumCell Y' = sumCell Y}.indicator
              (fun _ => (sigma77 : ℝ)) Y :=
              (Set.indicator_of_mem (f := fun _ => (sigma77 : ℝ)) hmem).symm
        _ ≤ S Y := by
            refine Finset.single_le_sum (f := fun c : ℕ =>
              {Y' : Fin 38 → FiniteMeasure ℝ | sumCell Y' = c}.indicator
                (fun _ => (sigma77 : ℝ)) Y) ?_ hY
            intro c hc
            exact hterm0 Y c hc
    · have hzero' : f Y = 0 := hzero Y (by
        have hle : c77max + 1 ≤ sumCell Y := by
          simpa [Finset.mem_range, Nat.not_lt] using hY
        omega)
      rw [hzero']
      exact Finset.sum_nonneg (fun c hc => hterm0 Y c hc)
  have hstep : (∫ Y, f Y ∂(Measure.pi fun _ : Fin 38 => μ))
      ≤ (∫ Y, S Y ∂(Measure.pi fun _ : Fin 38 => μ)) :=
    integral_mono_of_nonneg (Filter.Eventually.of_forall hnn)
      hSint (Filter.Eventually.of_forall hpt)
  -- the envelope integral is σ77 * Σ_{c∈K} μ{sumCell = c}
  have hintK : (∫ Y, S Y ∂(Measure.pi fun _ : Fin 38 => μ))
      ≤ (sigma77 : ℝ) * (∑ c ∈ Finset.range (c77max + 1),
          (Measure.pi fun _ : Fin 38 => μ).real
            {Y : Fin 38 → FiniteMeasure ℝ | sumCell Y = c}) := by
    have hmeasc : ∀ c ∈ Finset.range (c77max + 1), MeasurableSet
      ({Y' : Fin 38 → FiniteMeasure ℝ | sumCell Y' = c} :
        Set (Fin 38 → FiniteMeasure ℝ)) := fun c _ => measurableSet_sumCell c
    have hintc : ∀ c ∈ Finset.range (c77max + 1),
        (∫ Y : Fin 38 → FiniteMeasure ℝ,
          {Y' : Fin 38 → FiniteMeasure ℝ | sumCell Y' = c}.indicator
            (fun _ => (sigma77 : ℝ)) Y ∂(Measure.pi fun _ : Fin 38 => μ))
        = (sigma77 : ℝ) * (Measure.pi fun _ : Fin 38 => μ).real
          {Y : Fin 38 → FiniteMeasure ℝ | sumCell Y = c} := by
      intro c hc
      rw [integral_indicator_const (sigma77 : ℝ) (hmeasc c hc)]
      simp [mul_comm]
    have hSsplit : (∫ Y, S Y ∂(Measure.pi fun _ : Fin 38 => μ))
        = ∑ c ∈ Finset.range (c77max + 1),
          (∫ Y : Fin 38 → FiniteMeasure ℝ,
            {Y' : Fin 38 → FiniteMeasure ℝ | sumCell Y' = c}.indicator
              (fun _ => (sigma77 : ℝ)) Y
          ∂(Measure.pi fun _ : Fin 38 => μ)) := by
      simp only [hSdef]
      exact integral_finsetSum _ (fun c _ =>
        ((integrable_const (sigma77 : ℝ)).indicator (measurableSet_sumCell c)))
    rw [hSsplit, Finset.sum_congr rfl (fun c hc => hintc c hc), ← Finset.mul_sum]
  refine le_trans hstep (le_trans hintK ?_)
  refine le_trans (mul_le_mul_of_nonneg_left hdata hσpos) hsum

end PrimeGap182D1
