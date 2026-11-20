import Pg182D2.BandAssembly
import Pg182D2.HeadTail
import Pg182D2.TableData
import Pg182Frame.Frame

/-!
# COMPOSITION.lean — `h1_182_of`, with the data side discharged

The frame theorem (`Pg182Frame/Frame.lean`) takes the 262 source-bound rows as the hypothesis
`hobs : PhysicalSourceBounds182Mirror S C` and returns `Bound 182` from Katz, FKM, the rank-four
companion, Type III and the kernel-checked deduction.  This file builds `hobs` from this lane's
proved data side, so `h1_182_of` below runs with **no analytic input left on the data side**.

## What the data side now supplies

`(N1)` — the charFun identity of the fragment mass law — is a theorem
(`Pg182D2.BandAssembly.charFun_mass_fragmentLaw`), so the payload `cell_measure_le_hq_of_charFun'`
no longer has a named input:

    cell_measure_le_hq_final : convPow fragmentMassLaw 38 (cell n) ≤ ofReal hq

That is the *envelope layer* of all 137 inner rows (Layer M of the ledger: `HasLocalBound` at
`1/ζ`, via the Fejér smoothing lemma, the modulus identity, the `Cin` bounds and `∫_0^R e^{-38 Cin}
≤ 38/39 < 4/π`).

## The certificate table is now Lean data, not an abstract carrier

`Pg182D2.TableData` transcribes the frozen source table: the 137 inner rows
(`faceUpper`/`coefficientUpper`/`normalizedB`/`witnessUpper`) and the 60 outer rows
(`rootUpper`/`faceUpper`), plus the five cap rationals and the shared normalisation constants.
So `C : TrialCerts182` — an arbitrary record of 197 abstract reals — is *gone* from the statement
below: the certificate side is the definite table `certTable`.

The distinct numeric fact the transcription *proves* is the Layer-I margin on the 73
`rankTwo`/`high` rows (`TableData.witness_margin`, one `norm_num` theorem per row): the cover's
`witnessUpper` is the integrand envelope there, and `witnessUpper j * hq ≤ faceUpper j`.

For the 64 `.low` rows no envelope is recorded in the table (the frozen `witnessUpper` misses
those certificates by 19–27 orders of magnitude — see `TABLE_TRANSCRIPTION_REPORT.md`), so the
row inequality keeps its Layer-I form.  `certEnvelope` below is the *weakest sufficient* choice of
envelope, which is what lets `hmargin` be absorbed entirely (`h1_182_of_certEnvelope`).
-/

noncomputable section
namespace PrimeGap182D2

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- The `d = 38` sum law of the fragment masses at the 182 period. -/
abbrev fragmentMassLaw : Measure ℝ :=
  (PrimeGap182D1.fragmentLaw zeta).map (fun X : FiniteMeasure ℝ => (X.mass : ℝ))

instance fragmentLaw_isProbabilityMeasure : IsProbabilityMeasure (PrimeGap182D1.fragmentLaw zeta) :=
  PrimeGap182D1.fragmentLaw_isProbabilityMeasure zeta

instance fragmentMassLaw_isProbabilityMeasure : IsProbabilityMeasure fragmentMassLaw :=
  inferInstance

/-- **The cell bound, unconditional.**  The payload of the data side: every cell of the `d = 38`
sum law has mass `≤ hq`, with `(N1)`, `(N2)`, the modulus identity and the `Cin` bounds all
discharged as theorems. -/
theorem cell_measure_le_hq_final (n : ℕ) :
    convPow fragmentMassLaw 38 (Set.Ioc ((n : ℝ) * mesh) ((n : ℝ) * mesh + mesh))
      ≤ ENNReal.ofReal hq :=
  cell_measure_le_hq_of_charFun' (fun t => charFun_mass_fragmentLaw zeta_pos t) n

/-! ### The certificate table as the frame's carrier -/

/-- The frozen certificate table, as the frame's `TrialCerts182`: the 197 certificate rationals are
read off `Pg182D2.TableData` instead of being an abstract record. -/
def certTable : Pg182Frame.TrialCerts182 where
  rootUpper j := (TableData.outerRootUpper j : ℝ)
  faceUpper j := (TableData.outerFaceUpper j : ℝ)
  innerFaceUpper j := (TableData.innerFaceUpper j : ℝ)

@[simp] theorem certTable_rootUpper (j : Fin 60) :
    certTable.rootUpper j = (TableData.outerRootUpper j : ℝ) := rfl

@[simp] theorem certTable_faceUpper (j : Fin 60) :
    certTable.faceUpper j = (TableData.outerFaceUpper j : ℝ) := rfl

@[simp] theorem certTable_innerFaceUpper (j : Fin 137) :
    certTable.innerFaceUpper j = (TableData.innerFaceUpper j : ℝ) := rfl

/-! ### The Layer-I margin as a proved table fact (73 rows)

For the `rankTwo`/`high` rows the cover's `witnessUpper` is the integrand envelope, and the
certificate margin is a `norm_num` fact about the transcribed table
(`TableData.witness_margin_<j>`, lifted from `ℚ` to `ℝ` here). -/

/-- The proved Layer-I margin, in the `ℝ` form the composition consumes, for every non-`low` row. -/
theorem witness_margin_real (j : Fin 137) (h : TableData.isLow j = false) :
    (TableData.innerWitnessUpper j : ℝ) * hq ≤ (TableData.innerFaceUpper j : ℝ) := by
  have hq_eq : ((TableData.hqQ : ℚ) : ℝ) = hq := by
    norm_num [TableData.hqQ, TableData.zetaQ, hq, mesh, zeta, cellCount]
  have h' : (TableData.innerWitnessUpper j : ℝ) * ((TableData.hqQ : ℚ) : ℝ)
      ≤ (TableData.innerFaceUpper j : ℝ) := by
    exact_mod_cast TableData.witness_margin j h
  rwa [hq_eq] at h'

/-! ### The Layer-I envelope at its certificate maximum

`certEnvelope` takes the largest envelope the certificate permits, `faceUpper / hq`.  That is the
*weakest* sufficient hypothesis on the row inequality, and it makes the margin an identity — the
only irreducible Layer-I content left is `hrow` itself. -/

/-- The certificate-implied Layer-I envelope. -/
def certEnvelope (j : Fin 137) : ℝ := (TableData.innerFaceUpper j : ℝ) / hq

theorem certEnvelope_nonneg (j : Fin 137) : 0 ≤ certEnvelope j :=
  le_of_lt (div_pos (by exact_mod_cast TableData.innerFaceUpper_pos j) hq_pos)

theorem certEnvelope_margin (j : Fin 137) :
    certEnvelope j * hq ≤ (TableData.innerFaceUpper j : ℝ) := by
  rw [certEnvelope, div_mul_cancel₀]
  exact ne_of_gt hq_pos

/-! ### The composition theorems -/

/-- **THE COMPOSITION — `h1_182_of`.**  The frame theorem with `hobs` built from the discharged
data side: the 137 inner rows are the proved cell bound (`cell_measure_le_hq_final`) times the
Layer-I envelope, against the **transcribed** certificate table (`certTable`).

Every hypothesis below is either a campaign-level deep input (Katz, FKM, rank-four, Type III), the
kernel-checked deduction, or the Layer-I row inequality.  The 197 certificate rationals are now
literal Lean data, not hypotheses. -/
theorem h1_182_of (h1 : Pg182Frame.Kloosterman3Bound)
    (h2 : Pg182Frame.Kloosterman2CorrelationBound)
    (hK4 : Pg182Frame.IncidenceRankFourBounds182)
    (h3 : Pg182Frame.TypeIIILocalFourier)
    (hd : Pg182Frame.Deduction182)
    (S : Pg182Frame.TrialSource182)
    -- the 5 cap rows and the 120 outer rows: frozen source data against the transcribed table
    (hcap : Pg182Frame.CapBounds182 S)
    (hroot : ∀ j : Fin 60, S.outerRoot j ≤ (TableData.outerRootUpper j : ℝ))
    (hface : ∀ j : Fin 60, S.outerFace j ≤ (TableData.outerFaceUpper j : ℝ))
    -- the 137 inner rows: Layer I (envelope) against the proved cell bound
    (cellOf : Fin 137 → ℕ) (envSup : Fin 137 → ℝ)
    (henv : ∀ j : Fin 137, 0 ≤ envSup j)
    (hrow : ∀ j : Fin 137, S.innerMass j ≤ envSup j * (convPow fragmentMassLaw 38
      (Set.Ioc ((cellOf j : ℝ) * mesh) ((cellOf j : ℝ) * mesh + mesh))).toReal)
    (hmargin : ∀ j : Fin 137, envSup j * hq ≤ (TableData.innerFaceUpper j : ℝ)) :
    BigOSpeedrun.PrimeGaps.Bound 182 := by
  refine Pg182Frame.h1_182_of h1 h2 hK4 h3 hd S certTable
    ⟨hcap, hroot, hface, fun j => ?_⟩
  simp only [certTable_innerFaceUpper]
  have hcell : (convPow fragmentMassLaw 38 (Set.Ioc ((cellOf j : ℝ) * mesh)
      ((cellOf j : ℝ) * mesh + mesh))).toReal ≤ hq := by
    have h := ENNReal.toReal_mono (ENNReal.ofReal_ne_top) (cell_measure_le_hq_final (cellOf j))
    rwa [ENNReal.toReal_ofReal hq_pos.le] at h
  calc S.innerMass j ≤ envSup j * (convPow fragmentMassLaw 38 (Set.Ioc ((cellOf j : ℝ) * mesh)
        ((cellOf j : ℝ) * mesh + mesh))).toReal := hrow j
    _ ≤ envSup j * hq := mul_le_mul_of_nonneg_left hcell (henv j)
    _ ≤ (TableData.innerFaceUpper j : ℝ) := hmargin j

/-- **THE COMPOSITION, with the Layer-I margin absorbed.**  Substituting the certificate-implied
envelope `certEnvelope` discharges `hmargin` outright (`certEnvelope_margin`), leaving the row
inequality as the single Layer-I input — in its weakest sufficient form. -/
theorem h1_182_of_certEnvelope (h1 : Pg182Frame.Kloosterman3Bound)
    (h2 : Pg182Frame.Kloosterman2CorrelationBound)
    (hK4 : Pg182Frame.IncidenceRankFourBounds182)
    (h3 : Pg182Frame.TypeIIILocalFourier)
    (hd : Pg182Frame.Deduction182)
    (S : Pg182Frame.TrialSource182)
    (hcap : Pg182Frame.CapBounds182 S)
    (hroot : ∀ j : Fin 60, S.outerRoot j ≤ (TableData.outerRootUpper j : ℝ))
    (hface : ∀ j : Fin 60, S.outerFace j ≤ (TableData.outerFaceUpper j : ℝ))
    (cellOf : Fin 137 → ℕ)
    (hrow : ∀ j : Fin 137, S.innerMass j ≤ certEnvelope j * (convPow fragmentMassLaw 38
      (Set.Ioc ((cellOf j : ℝ) * mesh) ((cellOf j : ℝ) * mesh + mesh))).toReal) :
    BigOSpeedrun.PrimeGaps.Bound 182 :=
  h1_182_of h1 h2 hK4 h3 hd S hcap hroot hface cellOf certEnvelope certEnvelope_nonneg
    hrow certEnvelope_margin

end PrimeGap182D2
