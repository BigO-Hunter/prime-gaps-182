import Pg182D2.TableData
import SourceData182

/-!
# CrossCheck.lean — kernel proof that the transcription is faithful

The vendored frozen modules are `formal/TrialData182.lean` and
`formal/SourceData182.lean` from romyar1/prime-gaps-lean release
`external-numerics-20260909` (byte digests in `receipt/transcription_fidelity.txt`).

Each theorem below is a `decide +kernel` equality between a column of
`Pg182D2.TableData` and the corresponding projection of the frozen module.  Any
mis-parsed rational, any shifted row, any transposed column breaks these — they
are the transcription's proof of fidelity, not a restatement of it.
-/

set_option maxRecDepth 8192 in
theorem innerFaceUpper_eq : ∀ j : Fin 137,
    PrimeGap182D2.TableData.innerFaceUpper j
      = (PrimeGap182.trialInnerCertificates j).faceUpper := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem innerCoefficientUpper_eq : ∀ j : Fin 137,
    PrimeGap182D2.TableData.innerCoefficientUpper j
      = (PrimeGap182.trialInnerCertificates j).coefficientUpper := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem innerNormalizedB_eq : ∀ j : Fin 137,
    PrimeGap182D2.TableData.innerNormalizedB j
      = (PrimeGap182.trialInnerCertificates j).normalizedB := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem innerWitnessUpper_eq : ∀ j : Fin 137,
    PrimeGap182D2.TableData.innerWitnessUpper j
      = (PrimeGap182.trialInnerCertificates j).cover.witnessUpper := by
  decide +kernel

set_option maxRecDepth 8192 in
/-- `isLow` is the frozen `kind = .low`. -/

theorem isLow_eq : ∀ j : Fin 137,
    PrimeGap182D2.TableData.isLow j
      = ((PrimeGap182.trialInnerCertificates j).cover.kind == PrimeGap182.TrialSourceKind.low) := by
  decide +kernel

set_option maxRecDepth 8192 in
/-- `innerFamily` is the frozen cover's `family`. -/

theorem innerFamily_eq : ∀ j : Fin 137,
    (PrimeGap182D2.TableData.innerFamily j).val
      = (PrimeGap182.trialInnerCertificates j).cover.family.val := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem outerRootUpper_eq : ∀ j : Fin 60,
    PrimeGap182D2.TableData.outerRootUpper j
      = (PrimeGap182.trialOuterCertificates j).rootUpper := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem outerFaceUpper_eq : ∀ j : Fin 60,
    PrimeGap182D2.TableData.outerFaceUpper j
      = (PrimeGap182.trialOuterCertificates j).faceUpper := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem rhoStarQ_eq :
    PrimeGap182D2.TableData.rhoStarQ = PrimeGap182.trialRhoStar := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem denominatorLowerQ_eq :
    PrimeGap182D2.TableData.denominatorLowerQ = PrimeGap182.trialDenominatorLower := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem cap_caps_eq :
    PrimeGap182D2.TableData.denominatorUpperQ = PrimeGap182.trialDenominatorUpper
  ∧ PrimeGap182D2.TableData.j0LowerQ = PrimeGap182.trialJ0Lower
  ∧ PrimeGap182D2.TableData.jPlusLowerQ = PrimeGap182.trialJPlusLower
  ∧ PrimeGap182D2.TableData.tailUpperQ = PrimeGap182.trialTailUpper := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem innerTotalUpperQ_eq :
    PrimeGap182D2.TableData.innerTotalUpperQ = PrimeGap182.trialSourceInnerTotalUpper := by
  decide +kernel

#print axioms innerFaceUpper_eq
#print axioms innerCoefficientUpper_eq
#print axioms innerNormalizedB_eq
#print axioms innerWitnessUpper_eq
#print axioms isLow_eq
#print axioms innerFamily_eq
#print axioms outerRootUpper_eq
#print axioms outerFaceUpper_eq
#print axioms rhoStarQ_eq
#print axioms denominatorLowerQ_eq
#print axioms cap_caps_eq
#print axioms innerTotalUpperQ_eq
