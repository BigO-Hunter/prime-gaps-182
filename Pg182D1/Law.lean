import Mathlib

/-!
# LAW.lean — the verbatim fragment-law definitions (Lane D1)

Definitions copied verbatim from romyar1/prime-gaps-lean (commit b77bf175bded),
`vendor/primegaps186/PrimeGaps186.lean` (namespace `PrimeGap186`): the Poisson
fragment law of the 182/186 trial, together with the C0 trial constants of
`Pg182C0/Bridges.lean` (same-commit `formal/TrialData182.lean` shapes).

Everything here is DEFINITION or elementary; the D1 majorant chain builds on
`D1Cell`, `D1Mgf`, `D1Sum`, `D1Engine`.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace PrimeGap182D1

/-! ### Verbatim C0 trial constants (Pg182C0/Bridges.lean, TrialData182) -/

def trialDimension : ℕ := 39
def trialIntervals : ℕ := 393216
def trialCellCount : ℕ := trialIntervals - trialDimension
def trialRadius : ℚ := (1379373467 / 1312494500)
def trialMesh : ℚ := trialRadius / trialIntervals

theorem trialMesh_pos : (0 : ℚ) < trialMesh := by
  norm_num [trialMesh, trialRadius, trialIntervals]

theorem trialCellCount_eq : trialCellCount = 393177 := by rfl

def trialCellIndex (X : FiniteMeasure ℝ) : ℕ :=
  ⌊(X.mass : ℝ) / (trialMesh : ℝ)⌋₊

/-! ### Verbatim fragment-law primitives (PrimeGap186, commit b77bf175bded) -/

/-- Verbatim `PrimeGap186.weightedEmpirical`. -/
noncomputable def weightedEmpirical (n : ℕ) (x : Fin n → ℝ) : FiniteMeasure ℝ :=
  ∑ i : Fin n,
    let atom : FiniteMeasure ℝ := ⟨Measure.dirac (x i), inferInstance⟩
    (x i).toNNReal • atom

/-- Verbatim `PrimeGap186.finitePoissonLaw`. -/
noncomputable def finitePoissonLaw (μ : FiniteMeasure ℝ) : Measure (FiniteMeasure ℝ) :=
  Measure.map
    (fun p : ℕ × (ℕ → ℝ) =>
      weightedEmpirical p.1 (fun i : Fin p.1 => p.2 i.val))
    ((ProbabilityTheory.poissonMeasure μ.mass).prod
      (Measure.infinitePi (fun _ : ℕ => (μ.normalize : Measure ℝ))))

/-- Verbatim `PrimeGap186.cappedDyadicIntensity`. -/
noncomputable def cappedDyadicIntensity (ζ : ℝ) (k : ℤ) : FiniteMeasure ℝ :=
  ⟨((volume.restrict (Set.Ioc (0 : ℝ) ζ)).withDensity
      (fun u : ℝ => ENNReal.ofReal (1 / u))).restrict
      (Set.Ioc ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1))), by
    rw [restrict_withDensity measurableSet_Ioc]
    apply isFiniteMeasure_withDensity
    apply ne_of_lt
    calc
      (∫⁻ u, ENNReal.ofReal (1 / u)
          ∂((volume.restrict (Set.Ioc (0 : ℝ) ζ)).restrict
            (Set.Ioc ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1)))))
        ≤ ∫⁻ _u, ENNReal.ofReal (1 / (2 : ℝ) ^ k)
            ∂((volume.restrict (Set.Ioc (0 : ℝ) ζ)).restrict
              (Set.Ioc ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1)))) := by
          apply lintegral_mono_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
          exact ENNReal.ofReal_le_ofReal
            (one_div_le_one_div_of_le (zpow_pos (by norm_num) k) hu.1.le)
      _ < ∞ := by
        rw [lintegral_const]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)⟩

/-- Verbatim `PrimeGap186.finiteFragments`. -/
noncomputable def finiteFragments (ω : ℤ → FiniteMeasure ℝ) : FiniteMeasure ℝ := by
  classical
  exact if h : IsFiniteMeasure (Measure.sum (fun k : ℤ => (ω k : Measure ℝ))) then
      ⟨Measure.sum (fun k : ℤ => (ω k : Measure ℝ)), h⟩
    else 0

/-- Verbatim `PrimeGap186.fragmentLaw`: the probability law of the finite
weighted fragment measure (the paper's `ν_ζ` is `exp(γ) · ζ` times this). -/
noncomputable def fragmentLaw (ζ : ℝ) : Measure (FiniteMeasure ℝ) :=
  Measure.map finiteFragments
    (Measure.infinitePi (fun k : ℤ => finitePoissonLaw (cappedDyadicIntensity ζ k)))

/-! ### Elementary facts: mass and cell measurability -/

theorem measurable_mass : Measurable (fun X : FiniteMeasure ℝ => (X.mass : ℝ)) :=
  ((Measure.measurable_coe MeasurableSet.univ).comp
    measurable_subtype_coe).ennreal_toReal

theorem measurable_cellIndex : Measurable (fun X : FiniteMeasure ℝ => trialCellIndex X) := by
  refine Measurable.nat_floor ?_
  exact measurable_mass.div (by fun_prop)

/-- The floor law: a sample in cell `n` has mass `< (n+1) · mesh`. -/
theorem cell_mass_lt {X : FiniteMeasure ℝ} {n : ℕ} (h : trialCellIndex X = n) :
    (X.mass : ℝ) < ((n : ℝ) + 1) * (trialMesh : ℝ) := by
  rw [trialCellIndex] at h
  have h1 := Nat.lt_floor_add_one ((X.mass : ℝ) / (trialMesh : ℝ))
  rw [h] at h1
  have hmesh : (0 : ℝ) < (trialMesh : ℝ) := by exact_mod_cast trialMesh_pos
  have h2 : ((X.mass : ℝ) / (trialMesh : ℝ)) * (trialMesh : ℝ)
      < ((n : ℝ) + 1) * (trialMesh : ℝ) := mul_lt_mul_of_pos_right h1 hmesh
  rw [div_mul_cancel₀ _ (ne_of_gt hmesh)] at h2
  exact h2

/-- The floor law (lower side): a sample in cell `n` has mass `≥ n · mesh`. -/
theorem mass_le_of_cellIndex {X : FiniteMeasure ℝ} {n : ℕ} (h : trialCellIndex X = n) :
    ((n : ℝ) * (trialMesh : ℝ)) ≤ (X.mass : ℝ) := by
  have hmesh : (0 : ℝ) < (trialMesh : ℝ) := by exact_mod_cast trialMesh_pos
  have hquot : (0 : ℝ) ≤ (X.mass : ℝ) / (trialMesh : ℝ) :=
    div_nonneg X.mass.coe_nonneg hmesh.le
  have h1 : ((n : ℝ)) ≤ (X.mass : ℝ) / (trialMesh : ℝ) := by
    rw [← h]
    exact Nat.floor_le hquot
  have h2 : ((n : ℝ) * (trialMesh : ℝ)) ≤ ((X.mass : ℝ) / (trialMesh : ℝ)) * (trialMesh : ℝ) :=
    mul_le_mul_of_nonneg_right h1 hmesh.le
  rw [div_mul_cancel₀ _ (ne_of_gt hmesh)] at h2
  exact h2

end PrimeGap182D1
