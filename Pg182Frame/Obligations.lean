import Mathlib.Basic.Real.Basic

/-!
# The 262 integral obligations of the 182 row

Exact 1:1 handles for the 262 scalar numerical premises consumed by
`PhysicalSourceBounds182` (romyar1/prime-gaps-lean @ b77bf175bded,
formal/SourceBounds182.lean:138-142: 5 cap + 60 outerRoot + 60 outerFace +
137 innerMass).

The carriers below are ABSTRACT mirrors: their fields are named for, and
documented as, the exact frozen quantities of the romyar1 kernel
(`trialSourceOuterRoot` etc. over the fragment-law configuration space
`Fin 39 → FiniteMeasure ℝ` against the recorded exact rationals of
formal/SourceData182.lean and formal/TrialData182.lean). The exact defining
expressions live in that kernel context; this frame does not vendor them.

The 262 obligations are stubbed (`sorry`) — the honest inventory. The C0 row
machine discharges them against the kernel instantiation; each name is stable
and wired 1:1 into `PhysicalSourceBounds182Mirror` (see Frame.lean).
-/

noncomputable section

namespace Pg182Frame

/-- Abstract mirror of the five cap integrals and their five exact rational
enclosure targets (formal/PhysicalTrial182.lean:165-170; exact rationals in
formal/TrialData182.lean, e.g. trialDenominatorLower =
9900316613656518642800593/664613997892457936451903530140172288). -/
structure TrialSource182 where
  squareIntegral : ℝ       -- trialSquareIntegral
  baseIntegral : ℝ         -- trialBaseIntegral
  enlargementIntegral : ℝ  -- trialEnlargementIntegral
  tailIntegral : ℝ         -- trialTailIntegral
  denominatorLower : ℝ     -- (trialDenominatorLower : ℝ), exact Q in TrialData182.lean
  denominatorUpper : ℝ     -- (trialDenominatorUpper : ℝ)
  j0Lower : ℝ              -- (trialJ0Lower : ℝ)
  jPlusLower : ℝ           -- (trialJPlusLower : ℝ)
  tailUpper : ℝ            -- (trialTailUpper : ℝ)
  outerRoot : Fin 60 → ℝ   -- j ↦ trialSourceOuterRoot j (SourceBounds182.lean:58+)
  outerFace : Fin 60 → ℝ   -- j ↦ trialSourceOuterFace j
  innerMass : Fin 137 → ℝ  -- j ↦ trialSourceInnerMass j

/-- Abstract mirror of the recorded certificate rationals
(formal/SourceData182.lean, 197 records: 60 outer rootUpper, 60 outer faceUpper,
137 inner faceUpper). -/
structure TrialCerts182 where
  rootUpper : Fin 60 → ℝ       -- (trialOuterCertificates j).rootUpper
  faceUpper : Fin 60 → ℝ       -- (trialOuterCertificates j).faceUpper
  innerFaceUpper : Fin 137 → ℝ -- (trialInnerCertificates j).faceUpper

/-- The five cap inequalities, packed (mirror of `PhysicalCapBounds182`,
formal/PhysicalTrial182.lean:165-170). -/
def CapBounds182 (S : TrialSource182) : Prop :=
  S.denominatorLower ≤ S.squareIntegral ∧ S.squareIntegral ≤ S.denominatorUpper ∧
    S.j0Lower ≤ S.baseIntegral ∧ S.jPlusLower ≤ S.enlargementIntegral ∧
    S.tailIntegral ≤ S.tailUpper

/-- Mirror of `PhysicalSourceBounds182` (formal/SourceBounds182.lean:138-142):
5 cap + 60 + 60 + 137 = 262 inequalities. -/
def PhysicalSourceBounds182Mirror (S : TrialSource182) (C : TrialCerts182) : Prop :=
  CapBounds182 S ∧
  (∀ j : Fin 60, S.outerRoot j ≤ C.rootUpper j) ∧
  (∀ j : Fin 60, S.outerFace j ≤ C.faceUpper j) ∧
  (∀ j : Fin 137, S.innerMass j ≤ C.innerFaceUpper j)

/-! ## The five cap obligations (stubbed; C0 discharges) -/

/-- STUB. `cap.denominator_lower : (trialDenominatorLower : ℝ) ≤ trialSquareIntegral`
(formal/PhysicalTrial182.lean:166). -/
theorem integral_le_cap_denominator_lower (S : TrialSource182) :
    S.denominatorLower ≤ S.squareIntegral := sorry

/-- STUB. `cap.denominator_upper : trialSquareIntegral ≤ (trialDenominatorUpper : ℝ)`
(formal/PhysicalTrial182.lean:167). -/
theorem integral_le_cap_denominator_upper (S : TrialSource182) :
    S.squareIntegral ≤ S.denominatorUpper := sorry

/-- STUB. `cap.base_lower : (trialJ0Lower : ℝ) ≤ trialBaseIntegral`
(formal/PhysicalTrial182.lean:168). -/
theorem integral_le_cap_base_lower (S : TrialSource182) :
    S.j0Lower ≤ S.baseIntegral := sorry

/-- STUB. `cap.enlargement_lower : (trialJPlusLower : ℝ) ≤ trialEnlargementIntegral`
(formal/PhysicalTrial182.lean:169). -/
theorem integral_le_cap_enlargement_lower (S : TrialSource182) :
    S.jPlusLower ≤ S.enlargementIntegral := sorry

/-- STUB. `cap.tail_upper : trialTailIntegral ≤ (trialTailUpper : ℝ)`
(formal/PhysicalTrial182.lean:170). -/
theorem integral_le_cap_tail_upper (S : TrialSource182) :
    S.tailIntegral ≤ S.tailUpper := sorry

/-! ## The 120 outer obligations (stubbed; C0 discharges) -/

/-- STUB. `outerRoot (0) : trialSourceOuterRoot ⟨0, _⟩ ≤ (trialOuterCertificates ⟨0, _⟩).rootUpper`
(formal/SourceBounds182.lean:140). -/
theorem integral_le_outer_root_000 (S : TrialSource182) (C : TrialCerts182) :
    S.outerRoot ⟨0, by omega⟩ ≤ C.rootUpper ⟨0, by omega⟩ := sorry

/-- STUB. `outerRoot (1) : trialSourceOuterRoot ⟨1, _⟩ ≤ (trialOuterCertificates ⟨1, _⟩).rootUpper`
(formal/SourceBounds182.lean:140). -/
theorem integral_le_outer_root_001 (S : TrialSource182) (C : TrialCerts182) :
    S.outerRoot ⟨1, by omega⟩ ≤ C.rootUpper ⟨1, by omega⟩ := sorry

/-- STUB. `outerRoot (2) : trialSourceOuterRoot ⟨2, _⟩ ≤ (trialOuterCertificates ⟨2, _⟩).rootUpper`
(formal/SourceBounds182.lean:140). -/
theorem integral_le_outer_root_002 (S : TrialSource182) (C : TrialCerts182) :
    S.outerRoot ⟨2, by omega⟩ ≤ C.rootUpper ⟨2, by omega⟩ := sorry

/-- STUB. `outerRoot (3) : trialSourceOuterRoot ⟨3, _⟩ ≤ (trialOuterCertificates ⟨3, _⟩).rootUpper`
(formal/SourceBounds182.lean:140). -/
theorem integral_le_outer_root_003 (S : TrialSource182) (C : TrialCerts182) :
    S.outerRoot ⟨3, by omega⟩ ≤ C.rootUpper ⟨3, by omega⟩ := sorry

/-- STUB. `outerRoot (4) : trialSourceOuterRoot ⟨4, _⟩ ≤ (trialOuterCertificates ⟨4, _⟩).rootUpper`
(formal/SourceBounds182.lean:140). -/
theorem integral_le_outer_root_004 (S : TrialSource182) (C : TrialCerts182) :
    S.outerRoot ⟨4, by omega⟩ ≤ C.rootUpper ⟨4, by omega⟩ := sorry

/-- STUB. `outerRoot (5) : trialSourceOuterRoot ⟨5, _⟩ ≤ (trialOuterCertificates ⟨5, _⟩).rootUpper`
(formal/SourceBounds182.lean:140). -/
theorem integral_le_outer_root_005 (S : TrialSource182) (C : TrialCerts182) :
    S.outerRoot ⟨5, by omega⟩ ≤ C.rootUpper ⟨5, by omega⟩ := sorry

/-- STUB. `outerRoot (6) : trialSourceOuterRoot ⟨6, _⟩ ≤ (trialOuterCertificates ⟨6, _⟩).rootUpper`
(formal/SourceBounds182.lean:140). -/
theorem integral_le_outer_root_006 (S : TrialSource182) (C : TrialCerts182) :
    S.outerRoot ⟨6, by omega⟩ ≤ C.rootUpper ⟨6, by omega⟩ := sorry

/-- STUB. `outerRoot (7) : trialSourceOuterRoot ⟨7, _⟩ ≤ (trialOuterCertificates ⟨7, _⟩).rootUpper`
(formal/SourceBounds182.lean:140). -/
theorem integral_le_outer_root_007 (S : TrialSource182) (C : TrialCerts182) :
    S.outerRoot ⟨7, by omega⟩ ≤ C.rootUpper ⟨7, by omega⟩ := sorry

/-- STUB. `outerRoot (8) : trialSourceOuterRoot ⟨8, _⟩ ≤ (trialOuterCertificates ⟨8, _⟩).rootUpper`
(formal/SourceBounds182.lean:140). -/
theorem integral_le_outer_root_008 (S : TrialSource182) (C : TrialCerts182) :
    S.outerRoot ⟨8, by omega⟩ ≤ C.rootUpper ⟨8, by omega⟩ := sorry

/-- STUB. `outerRoot (9) : trialSourceOuterRoot ⟨9, _⟩ ≤ (trialOuterCertificates ⟨9, _⟩).rootUpper`
(formal/SourceBounds182.lean:140). -/
theorem integral_le_outer_root_009 (S : TrialSource182) (C : TrialCerts182) :
    S.outerRoot ⟨9, by omega⟩ ≤ C.rootUpper ⟨9, by omega⟩ := sorry

/-- STUB. `outerRoot (10) : trialSourceOuterRoot ⟨10, _⟩ ≤ (trialOuterCertificates ⟨10, _⟩).rootUpper`
(formal/SourceBounds182.lean:140). -/
theorem integral_le_outer_root_010 (S : TrialSource182) (C : TrialCerts182) :
    S.outerRoot ⟨10, by omega⟩ ≤ C.rootUpper ⟨10, by omega⟩ := sorry

/-- STUB. `outerRoot (11) : trialSourceOuterRoot ⟨11, _⟩ ≤ (trialOuterCertificates ⟨11, _⟩).rootUpper`
(formal/SourceBounds182.lean:140). -/
theorem integral_le_outer_root_011 (S : TrialSource182) (C : TrialCerts182) :
    S.outerRoot ⟨11, by omega⟩ ≤ C.rootUpper ⟨11, by omega⟩ := sorry

/-- STUB. `outerRoot (12) : trialSourceOuterRoot ⟨12, _⟩ ≤ (trialOuterCertificates ⟨12, _⟩).rootUpper`
(formal/SourceBounds182.lean:140). -/
theorem integral_le_outer_root_012 (S : TrialSource182) (C : TrialCerts182) :
    S.outerRoot ⟨12, by omega⟩ ≤ C.rootUpper ⟨12, by omega⟩ := sorry

/-- STUB. `outerRoot (13) : trialSourceOuterRoot ⟨13, _⟩ ≤ (trialOuterCertificates ⟨13, _⟩).rootUpper`
(formal/SourceBounds182.lean:140). -/
theorem integral_le_outer_root_013 (S : TrialSource182) (C : TrialCerts182) :
    S.outerRoot ⟨13, by omega⟩ ≤ C.rootUpper ⟨13, by omega⟩ := sorry

/-- STUB. `outerRoot (14) : trialSourceOuterRoot ⟨14, _⟩ ≤ (trialOuterCertificates ⟨14, _⟩).rootUpper`
(formal/SourceBounds182.lean:140). -/
theorem integral_le_outer_root_014 (S : TrialSource182) (C : TrialCerts182) :
    S.outerRoot ⟨14, by omega⟩ ≤ C.rootUpper ⟨14, by omega⟩ := sorry

/-- STUB. `outerRoot (15) : trialSourceOuterRoot ⟨15, _⟩ ≤ (trialOuterCertificates ⟨15, _⟩).rootUpper`
(formal/SourceBounds182.lean:140). -/
theorem integral_le_outer_root_015 (S : TrialSource182) (C : TrialCerts182) :
    S.outerRoot ⟨15, by omega⟩ ≤ C.rootUpper ⟨15, by omega⟩ := sorry

/-- STUB. `outerRoot (16) : trialSourceOuterRoot ⟨16, _⟩ ≤ (trialOuterCertificates ⟨16, _⟩).rootUpper`
(formal/SourceBounds182.lean:140). -/
theorem integral_le_outer_root_016 (S : TrialSource182) (C : TrialCerts182) :
    S.outerRoot ⟨16, by omega⟩ ≤ C.rootUpper ⟨16, by omega⟩ := sorry

/-- STUB. `outerRoot (17) : trialSourceOuterRoot ⟨17, _⟩ ≤ (trialOuterCertificates ⟨17, _⟩).rootUpper`
(formal/SourceBounds182.lean:140). -/
theorem integral_le_outer_root_017 (S : TrialSource182) (C : TrialCerts182) :
    S.outerRoot ⟨17, by omega⟩ ≤ C.rootUpper ⟨17, by omega⟩ := sorry

/-- STUB. `outerRoot (18) : trialSourceOuterRoot ⟨18, _⟩ ≤ (trialOuterCertificates ⟨18, _⟩).rootUpper`
(formal/SourceBounds182.lean:140). -/
theorem integral_le_outer_root_018 (S : TrialSource182) (C : TrialCerts182) :
    S.outerRoot ⟨18, by omega⟩ ≤ C.rootUpper ⟨18, by omega⟩ := sorry

/-- STUB. `outerRoot (19) : trialSourceOuterRoot ⟨19, _⟩ ≤ (trialOuterCertificates ⟨19, _⟩).rootUpper`
(formal/SourceBounds182.lean:140). -/
theorem integral_le_outer_root_019 (S : TrialSource182) (C : TrialCerts182) :
    S.outerRoot ⟨19, by omega⟩ ≤ C.rootUpper ⟨19, by omega⟩ := sorry

/-- STUB. `outerRoot (20) : trialSourceOuterRoot ⟨20, _⟩ ≤ (trialOuterCertificates ⟨20, _⟩).rootUpper`
(formal/SourceBounds182.lean:140). -/
theorem integral_le_outer_root_020 (S : TrialSource182) (C : TrialCerts182) :
    S.outerRoot ⟨20, by omega⟩ ≤ C.rootUpper ⟨20, by omega⟩ := sorry

/-- STUB. `outerRoot (21) : trialSourceOuterRoot ⟨21, _⟩ ≤ (trialOuterCertificates ⟨21, _⟩).rootUpper`
(formal/SourceBounds182.lean:140). -/
theorem integral_le_outer_root_021 (S : TrialSource182) (C : TrialCerts182) :
    S.outerRoot ⟨21, by omega⟩ ≤ C.rootUpper ⟨21, by omega⟩ := sorry

/-- STUB. `outerRoot (22) : trialSourceOuterRoot ⟨22, _⟩ ≤ (trialOuterCertificates ⟨22, _⟩).rootUpper`
(formal/SourceBounds182.lean:140). -/
theorem integral_le_outer_root_022 (S : TrialSource182) (C : TrialCerts182) :
    S.outerRoot ⟨22, by omega⟩ ≤ C.rootUpper ⟨22, by omega⟩ := sorry

/-- STUB. `outerRoot (23) : trialSourceOuterRoot ⟨23, _⟩ ≤ (trialOuterCertificates ⟨23, _⟩).rootUpper`
(formal/SourceBounds182.lean:140). -/
theorem integral_le_outer_root_023 (S : TrialSource182) (C : TrialCerts182) :
    S.outerRoot ⟨23, by omega⟩ ≤ C.rootUpper ⟨23, by omega⟩ := sorry

/-- STUB. `outerRoot (24) : trialSourceOuterRoot ⟨24, _⟩ ≤ (trialOuterCertificates ⟨24, _⟩).rootUpper`
(formal/SourceBounds182.lean:140). -/
theorem integral_le_outer_root_024 (S : TrialSource182) (C : TrialCerts182) :
    S.outerRoot ⟨24, by omega⟩ ≤ C.rootUpper ⟨24, by omega⟩ := sorry

/-- STUB. `outerRoot (25) : trialSourceOuterRoot ⟨25, _⟩ ≤ (trialOuterCertificates ⟨25, _⟩).rootUpper`
(formal/SourceBounds182.lean:140). -/
theorem integral_le_outer_root_025 (S : TrialSource182) (C : TrialCerts182) :
    S.outerRoot ⟨25, by omega⟩ ≤ C.rootUpper ⟨25, by omega⟩ := sorry

/-- STUB. `outerRoot (26) : trialSourceOuterRoot ⟨26, _⟩ ≤ (trialOuterCertificates ⟨26, _⟩).rootUpper`
(formal/SourceBounds182.lean:140). -/
theorem integral_le_outer_root_026 (S : TrialSource182) (C : TrialCerts182) :
    S.outerRoot ⟨26, by omega⟩ ≤ C.rootUpper ⟨26, by omega⟩ := sorry

/-- STUB. `outerRoot (27) : trialSourceOuterRoot ⟨27, _⟩ ≤ (trialOuterCertificates ⟨27, _⟩).rootUpper`
(formal/SourceBounds182.lean:140). -/
theorem integral_le_outer_root_027 (S : TrialSource182) (C : TrialCerts182) :
    S.outerRoot ⟨27, by omega⟩ ≤ C.rootUpper ⟨27, by omega⟩ := sorry

/-- STUB. `outerRoot (28) : trialSourceOuterRoot ⟨28, _⟩ ≤ (trialOuterCertificates ⟨28, _⟩).rootUpper`
(formal/SourceBounds182.lean:140). -/
theorem integral_le_outer_root_028 (S : TrialSource182) (C : TrialCerts182) :
    S.outerRoot ⟨28, by omega⟩ ≤ C.rootUpper ⟨28, by omega⟩ := sorry

/-- STUB. `outerRoot (29) : trialSourceOuterRoot ⟨29, _⟩ ≤ (trialOuterCertificates ⟨29, _⟩).rootUpper`
(formal/SourceBounds182.lean:140). -/
theorem integral_le_outer_root_029 (S : TrialSource182) (C : TrialCerts182) :
    S.outerRoot ⟨29, by omega⟩ ≤ C.rootUpper ⟨29, by omega⟩ := sorry

/-- STUB. `outerRoot (30) : trialSourceOuterRoot ⟨30, _⟩ ≤ (trialOuterCertificates ⟨30, _⟩).rootUpper`
(formal/SourceBounds182.lean:140). -/
theorem integral_le_outer_root_030 (S : TrialSource182) (C : TrialCerts182) :
    S.outerRoot ⟨30, by omega⟩ ≤ C.rootUpper ⟨30, by omega⟩ := sorry

/-- STUB. `outerRoot (31) : trialSourceOuterRoot ⟨31, _⟩ ≤ (trialOuterCertificates ⟨31, _⟩).rootUpper`
(formal/SourceBounds182.lean:140). -/
theorem integral_le_outer_root_031 (S : TrialSource182) (C : TrialCerts182) :
    S.outerRoot ⟨31, by omega⟩ ≤ C.rootUpper ⟨31, by omega⟩ := sorry

/-- STUB. `outerRoot (32) : trialSourceOuterRoot ⟨32, _⟩ ≤ (trialOuterCertificates ⟨32, _⟩).rootUpper`
(formal/SourceBounds182.lean:140). -/
theorem integral_le_outer_root_032 (S : TrialSource182) (C : TrialCerts182) :
    S.outerRoot ⟨32, by omega⟩ ≤ C.rootUpper ⟨32, by omega⟩ := sorry

/-- STUB. `outerRoot (33) : trialSourceOuterRoot ⟨33, _⟩ ≤ (trialOuterCertificates ⟨33, _⟩).rootUpper`
(formal/SourceBounds182.lean:140). -/
theorem integral_le_outer_root_033 (S : TrialSource182) (C : TrialCerts182) :
    S.outerRoot ⟨33, by omega⟩ ≤ C.rootUpper ⟨33, by omega⟩ := sorry

/-- STUB. `outerRoot (34) : trialSourceOuterRoot ⟨34, _⟩ ≤ (trialOuterCertificates ⟨34, _⟩).rootUpper`
(formal/SourceBounds182.lean:140). -/
theorem integral_le_outer_root_034 (S : TrialSource182) (C : TrialCerts182) :
    S.outerRoot ⟨34, by omega⟩ ≤ C.rootUpper ⟨34, by omega⟩ := sorry

/-- STUB. `outerRoot (35) : trialSourceOuterRoot ⟨35, _⟩ ≤ (trialOuterCertificates ⟨35, _⟩).rootUpper`
(formal/SourceBounds182.lean:140). -/
theorem integral_le_outer_root_035 (S : TrialSource182) (C : TrialCerts182) :
    S.outerRoot ⟨35, by omega⟩ ≤ C.rootUpper ⟨35, by omega⟩ := sorry

/-- STUB. `outerRoot (36) : trialSourceOuterRoot ⟨36, _⟩ ≤ (trialOuterCertificates ⟨36, _⟩).rootUpper`
(formal/SourceBounds182.lean:140). -/
theorem integral_le_outer_root_036 (S : TrialSource182) (C : TrialCerts182) :
    S.outerRoot ⟨36, by omega⟩ ≤ C.rootUpper ⟨36, by omega⟩ := sorry

/-- STUB. `outerRoot (37) : trialSourceOuterRoot ⟨37, _⟩ ≤ (trialOuterCertificates ⟨37, _⟩).rootUpper`
(formal/SourceBounds182.lean:140). -/
theorem integral_le_outer_root_037 (S : TrialSource182) (C : TrialCerts182) :
    S.outerRoot ⟨37, by omega⟩ ≤ C.rootUpper ⟨37, by omega⟩ := sorry

/-- STUB. `outerRoot (38) : trialSourceOuterRoot ⟨38, _⟩ ≤ (trialOuterCertificates ⟨38, _⟩).rootUpper`
(formal/SourceBounds182.lean:140). -/
theorem integral_le_outer_root_038 (S : TrialSource182) (C : TrialCerts182) :
    S.outerRoot ⟨38, by omega⟩ ≤ C.rootUpper ⟨38, by omega⟩ := sorry

/-- STUB. `outerRoot (39) : trialSourceOuterRoot ⟨39, _⟩ ≤ (trialOuterCertificates ⟨39, _⟩).rootUpper`
(formal/SourceBounds182.lean:140). -/
theorem integral_le_outer_root_039 (S : TrialSource182) (C : TrialCerts182) :
    S.outerRoot ⟨39, by omega⟩ ≤ C.rootUpper ⟨39, by omega⟩ := sorry

/-- STUB. `outerRoot (40) : trialSourceOuterRoot ⟨40, _⟩ ≤ (trialOuterCertificates ⟨40, _⟩).rootUpper`
(formal/SourceBounds182.lean:140). -/
theorem integral_le_outer_root_040 (S : TrialSource182) (C : TrialCerts182) :
    S.outerRoot ⟨40, by omega⟩ ≤ C.rootUpper ⟨40, by omega⟩ := sorry

/-- STUB. `outerRoot (41) : trialSourceOuterRoot ⟨41, _⟩ ≤ (trialOuterCertificates ⟨41, _⟩).rootUpper`
(formal/SourceBounds182.lean:140). -/
theorem integral_le_outer_root_041 (S : TrialSource182) (C : TrialCerts182) :
    S.outerRoot ⟨41, by omega⟩ ≤ C.rootUpper ⟨41, by omega⟩ := sorry

/-- STUB. `outerRoot (42) : trialSourceOuterRoot ⟨42, _⟩ ≤ (trialOuterCertificates ⟨42, _⟩).rootUpper`
(formal/SourceBounds182.lean:140). -/
theorem integral_le_outer_root_042 (S : TrialSource182) (C : TrialCerts182) :
    S.outerRoot ⟨42, by omega⟩ ≤ C.rootUpper ⟨42, by omega⟩ := sorry

/-- STUB. `outerRoot (43) : trialSourceOuterRoot ⟨43, _⟩ ≤ (trialOuterCertificates ⟨43, _⟩).rootUpper`
(formal/SourceBounds182.lean:140). -/
theorem integral_le_outer_root_043 (S : TrialSource182) (C : TrialCerts182) :
    S.outerRoot ⟨43, by omega⟩ ≤ C.rootUpper ⟨43, by omega⟩ := sorry

/-- STUB. `outerRoot (44) : trialSourceOuterRoot ⟨44, _⟩ ≤ (trialOuterCertificates ⟨44, _⟩).rootUpper`
(formal/SourceBounds182.lean:140). -/
theorem integral_le_outer_root_044 (S : TrialSource182) (C : TrialCerts182) :
    S.outerRoot ⟨44, by omega⟩ ≤ C.rootUpper ⟨44, by omega⟩ := sorry

/-- STUB. `outerRoot (45) : trialSourceOuterRoot ⟨45, _⟩ ≤ (trialOuterCertificates ⟨45, _⟩).rootUpper`
(formal/SourceBounds182.lean:140). -/
theorem integral_le_outer_root_045 (S : TrialSource182) (C : TrialCerts182) :
    S.outerRoot ⟨45, by omega⟩ ≤ C.rootUpper ⟨45, by omega⟩ := sorry

/-- STUB. `outerRoot (46) : trialSourceOuterRoot ⟨46, _⟩ ≤ (trialOuterCertificates ⟨46, _⟩).rootUpper`
(formal/SourceBounds182.lean:140). -/
theorem integral_le_outer_root_046 (S : TrialSource182) (C : TrialCerts182) :
    S.outerRoot ⟨46, by omega⟩ ≤ C.rootUpper ⟨46, by omega⟩ := sorry

/-- STUB. `outerRoot (47) : trialSourceOuterRoot ⟨47, _⟩ ≤ (trialOuterCertificates ⟨47, _⟩).rootUpper`
(formal/SourceBounds182.lean:140). -/
theorem integral_le_outer_root_047 (S : TrialSource182) (C : TrialCerts182) :
    S.outerRoot ⟨47, by omega⟩ ≤ C.rootUpper ⟨47, by omega⟩ := sorry

/-- STUB. `outerRoot (48) : trialSourceOuterRoot ⟨48, _⟩ ≤ (trialOuterCertificates ⟨48, _⟩).rootUpper`
(formal/SourceBounds182.lean:140). -/
theorem integral_le_outer_root_048 (S : TrialSource182) (C : TrialCerts182) :
    S.outerRoot ⟨48, by omega⟩ ≤ C.rootUpper ⟨48, by omega⟩ := sorry

/-- STUB. `outerRoot (49) : trialSourceOuterRoot ⟨49, _⟩ ≤ (trialOuterCertificates ⟨49, _⟩).rootUpper`
(formal/SourceBounds182.lean:140). -/
theorem integral_le_outer_root_049 (S : TrialSource182) (C : TrialCerts182) :
    S.outerRoot ⟨49, by omega⟩ ≤ C.rootUpper ⟨49, by omega⟩ := sorry

/-- STUB. `outerRoot (50) : trialSourceOuterRoot ⟨50, _⟩ ≤ (trialOuterCertificates ⟨50, _⟩).rootUpper`
(formal/SourceBounds182.lean:140). -/
theorem integral_le_outer_root_050 (S : TrialSource182) (C : TrialCerts182) :
    S.outerRoot ⟨50, by omega⟩ ≤ C.rootUpper ⟨50, by omega⟩ := sorry

/-- STUB. `outerRoot (51) : trialSourceOuterRoot ⟨51, _⟩ ≤ (trialOuterCertificates ⟨51, _⟩).rootUpper`
(formal/SourceBounds182.lean:140). -/
theorem integral_le_outer_root_051 (S : TrialSource182) (C : TrialCerts182) :
    S.outerRoot ⟨51, by omega⟩ ≤ C.rootUpper ⟨51, by omega⟩ := sorry

/-- STUB. `outerRoot (52) : trialSourceOuterRoot ⟨52, _⟩ ≤ (trialOuterCertificates ⟨52, _⟩).rootUpper`
(formal/SourceBounds182.lean:140). -/
theorem integral_le_outer_root_052 (S : TrialSource182) (C : TrialCerts182) :
    S.outerRoot ⟨52, by omega⟩ ≤ C.rootUpper ⟨52, by omega⟩ := sorry

/-- STUB. `outerRoot (53) : trialSourceOuterRoot ⟨53, _⟩ ≤ (trialOuterCertificates ⟨53, _⟩).rootUpper`
(formal/SourceBounds182.lean:140). -/
theorem integral_le_outer_root_053 (S : TrialSource182) (C : TrialCerts182) :
    S.outerRoot ⟨53, by omega⟩ ≤ C.rootUpper ⟨53, by omega⟩ := sorry

/-- STUB. `outerRoot (54) : trialSourceOuterRoot ⟨54, _⟩ ≤ (trialOuterCertificates ⟨54, _⟩).rootUpper`
(formal/SourceBounds182.lean:140). -/
theorem integral_le_outer_root_054 (S : TrialSource182) (C : TrialCerts182) :
    S.outerRoot ⟨54, by omega⟩ ≤ C.rootUpper ⟨54, by omega⟩ := sorry

/-- STUB. `outerRoot (55) : trialSourceOuterRoot ⟨55, _⟩ ≤ (trialOuterCertificates ⟨55, _⟩).rootUpper`
(formal/SourceBounds182.lean:140). -/
theorem integral_le_outer_root_055 (S : TrialSource182) (C : TrialCerts182) :
    S.outerRoot ⟨55, by omega⟩ ≤ C.rootUpper ⟨55, by omega⟩ := sorry

/-- STUB. `outerRoot (56) : trialSourceOuterRoot ⟨56, _⟩ ≤ (trialOuterCertificates ⟨56, _⟩).rootUpper`
(formal/SourceBounds182.lean:140). -/
theorem integral_le_outer_root_056 (S : TrialSource182) (C : TrialCerts182) :
    S.outerRoot ⟨56, by omega⟩ ≤ C.rootUpper ⟨56, by omega⟩ := sorry

/-- STUB. `outerRoot (57) : trialSourceOuterRoot ⟨57, _⟩ ≤ (trialOuterCertificates ⟨57, _⟩).rootUpper`
(formal/SourceBounds182.lean:140). -/
theorem integral_le_outer_root_057 (S : TrialSource182) (C : TrialCerts182) :
    S.outerRoot ⟨57, by omega⟩ ≤ C.rootUpper ⟨57, by omega⟩ := sorry

/-- STUB. `outerRoot (58) : trialSourceOuterRoot ⟨58, _⟩ ≤ (trialOuterCertificates ⟨58, _⟩).rootUpper`
(formal/SourceBounds182.lean:140). -/
theorem integral_le_outer_root_058 (S : TrialSource182) (C : TrialCerts182) :
    S.outerRoot ⟨58, by omega⟩ ≤ C.rootUpper ⟨58, by omega⟩ := sorry

/-- STUB. `outerRoot (59) : trialSourceOuterRoot ⟨59, _⟩ ≤ (trialOuterCertificates ⟨59, _⟩).rootUpper`
(formal/SourceBounds182.lean:140). -/
theorem integral_le_outer_root_059 (S : TrialSource182) (C : TrialCerts182) :
    S.outerRoot ⟨59, by omega⟩ ≤ C.rootUpper ⟨59, by omega⟩ := sorry

/-- STUB. `outerFace (0)` (formal/SourceBounds182.lean:141). -/
theorem integral_le_outer_face_000 (S : TrialSource182) (C : TrialCerts182) :
    S.outerFace ⟨0, by omega⟩ ≤ C.faceUpper ⟨0, by omega⟩ := sorry

/-- STUB. `outerFace (1)` (formal/SourceBounds182.lean:141). -/
theorem integral_le_outer_face_001 (S : TrialSource182) (C : TrialCerts182) :
    S.outerFace ⟨1, by omega⟩ ≤ C.faceUpper ⟨1, by omega⟩ := sorry

/-- STUB. `outerFace (2)` (formal/SourceBounds182.lean:141). -/
theorem integral_le_outer_face_002 (S : TrialSource182) (C : TrialCerts182) :
    S.outerFace ⟨2, by omega⟩ ≤ C.faceUpper ⟨2, by omega⟩ := sorry

/-- STUB. `outerFace (3)` (formal/SourceBounds182.lean:141). -/
theorem integral_le_outer_face_003 (S : TrialSource182) (C : TrialCerts182) :
    S.outerFace ⟨3, by omega⟩ ≤ C.faceUpper ⟨3, by omega⟩ := sorry

/-- STUB. `outerFace (4)` (formal/SourceBounds182.lean:141). -/
theorem integral_le_outer_face_004 (S : TrialSource182) (C : TrialCerts182) :
    S.outerFace ⟨4, by omega⟩ ≤ C.faceUpper ⟨4, by omega⟩ := sorry

/-- STUB. `outerFace (5)` (formal/SourceBounds182.lean:141). -/
theorem integral_le_outer_face_005 (S : TrialSource182) (C : TrialCerts182) :
    S.outerFace ⟨5, by omega⟩ ≤ C.faceUpper ⟨5, by omega⟩ := sorry

/-- STUB. `outerFace (6)` (formal/SourceBounds182.lean:141). -/
theorem integral_le_outer_face_006 (S : TrialSource182) (C : TrialCerts182) :
    S.outerFace ⟨6, by omega⟩ ≤ C.faceUpper ⟨6, by omega⟩ := sorry

/-- STUB. `outerFace (7)` (formal/SourceBounds182.lean:141). -/
theorem integral_le_outer_face_007 (S : TrialSource182) (C : TrialCerts182) :
    S.outerFace ⟨7, by omega⟩ ≤ C.faceUpper ⟨7, by omega⟩ := sorry

/-- STUB. `outerFace (8)` (formal/SourceBounds182.lean:141). -/
theorem integral_le_outer_face_008 (S : TrialSource182) (C : TrialCerts182) :
    S.outerFace ⟨8, by omega⟩ ≤ C.faceUpper ⟨8, by omega⟩ := sorry

/-- STUB. `outerFace (9)` (formal/SourceBounds182.lean:141). -/
theorem integral_le_outer_face_009 (S : TrialSource182) (C : TrialCerts182) :
    S.outerFace ⟨9, by omega⟩ ≤ C.faceUpper ⟨9, by omega⟩ := sorry

/-- STUB. `outerFace (10)` (formal/SourceBounds182.lean:141). -/
theorem integral_le_outer_face_010 (S : TrialSource182) (C : TrialCerts182) :
    S.outerFace ⟨10, by omega⟩ ≤ C.faceUpper ⟨10, by omega⟩ := sorry

/-- STUB. `outerFace (11)` (formal/SourceBounds182.lean:141). -/
theorem integral_le_outer_face_011 (S : TrialSource182) (C : TrialCerts182) :
    S.outerFace ⟨11, by omega⟩ ≤ C.faceUpper ⟨11, by omega⟩ := sorry

/-- STUB. `outerFace (12)` (formal/SourceBounds182.lean:141). -/
theorem integral_le_outer_face_012 (S : TrialSource182) (C : TrialCerts182) :
    S.outerFace ⟨12, by omega⟩ ≤ C.faceUpper ⟨12, by omega⟩ := sorry

/-- STUB. `outerFace (13)` (formal/SourceBounds182.lean:141). -/
theorem integral_le_outer_face_013 (S : TrialSource182) (C : TrialCerts182) :
    S.outerFace ⟨13, by omega⟩ ≤ C.faceUpper ⟨13, by omega⟩ := sorry

/-- STUB. `outerFace (14)` (formal/SourceBounds182.lean:141). -/
theorem integral_le_outer_face_014 (S : TrialSource182) (C : TrialCerts182) :
    S.outerFace ⟨14, by omega⟩ ≤ C.faceUpper ⟨14, by omega⟩ := sorry

/-- STUB. `outerFace (15)` (formal/SourceBounds182.lean:141). -/
theorem integral_le_outer_face_015 (S : TrialSource182) (C : TrialCerts182) :
    S.outerFace ⟨15, by omega⟩ ≤ C.faceUpper ⟨15, by omega⟩ := sorry

/-- STUB. `outerFace (16)` (formal/SourceBounds182.lean:141). -/
theorem integral_le_outer_face_016 (S : TrialSource182) (C : TrialCerts182) :
    S.outerFace ⟨16, by omega⟩ ≤ C.faceUpper ⟨16, by omega⟩ := sorry

/-- STUB. `outerFace (17)` (formal/SourceBounds182.lean:141). -/
theorem integral_le_outer_face_017 (S : TrialSource182) (C : TrialCerts182) :
    S.outerFace ⟨17, by omega⟩ ≤ C.faceUpper ⟨17, by omega⟩ := sorry

/-- STUB. `outerFace (18)` (formal/SourceBounds182.lean:141). -/
theorem integral_le_outer_face_018 (S : TrialSource182) (C : TrialCerts182) :
    S.outerFace ⟨18, by omega⟩ ≤ C.faceUpper ⟨18, by omega⟩ := sorry

/-- STUB. `outerFace (19)` (formal/SourceBounds182.lean:141). -/
theorem integral_le_outer_face_019 (S : TrialSource182) (C : TrialCerts182) :
    S.outerFace ⟨19, by omega⟩ ≤ C.faceUpper ⟨19, by omega⟩ := sorry

/-- STUB. `outerFace (20)` (formal/SourceBounds182.lean:141). -/
theorem integral_le_outer_face_020 (S : TrialSource182) (C : TrialCerts182) :
    S.outerFace ⟨20, by omega⟩ ≤ C.faceUpper ⟨20, by omega⟩ := sorry

/-- STUB. `outerFace (21)` (formal/SourceBounds182.lean:141). -/
theorem integral_le_outer_face_021 (S : TrialSource182) (C : TrialCerts182) :
    S.outerFace ⟨21, by omega⟩ ≤ C.faceUpper ⟨21, by omega⟩ := sorry

/-- STUB. `outerFace (22)` (formal/SourceBounds182.lean:141). -/
theorem integral_le_outer_face_022 (S : TrialSource182) (C : TrialCerts182) :
    S.outerFace ⟨22, by omega⟩ ≤ C.faceUpper ⟨22, by omega⟩ := sorry

/-- STUB. `outerFace (23)` (formal/SourceBounds182.lean:141). -/
theorem integral_le_outer_face_023 (S : TrialSource182) (C : TrialCerts182) :
    S.outerFace ⟨23, by omega⟩ ≤ C.faceUpper ⟨23, by omega⟩ := sorry

/-- STUB. `outerFace (24)` (formal/SourceBounds182.lean:141). -/
theorem integral_le_outer_face_024 (S : TrialSource182) (C : TrialCerts182) :
    S.outerFace ⟨24, by omega⟩ ≤ C.faceUpper ⟨24, by omega⟩ := sorry

/-- STUB. `outerFace (25)` (formal/SourceBounds182.lean:141). -/
theorem integral_le_outer_face_025 (S : TrialSource182) (C : TrialCerts182) :
    S.outerFace ⟨25, by omega⟩ ≤ C.faceUpper ⟨25, by omega⟩ := sorry

/-- STUB. `outerFace (26)` (formal/SourceBounds182.lean:141). -/
theorem integral_le_outer_face_026 (S : TrialSource182) (C : TrialCerts182) :
    S.outerFace ⟨26, by omega⟩ ≤ C.faceUpper ⟨26, by omega⟩ := sorry

/-- STUB. `outerFace (27)` (formal/SourceBounds182.lean:141). -/
theorem integral_le_outer_face_027 (S : TrialSource182) (C : TrialCerts182) :
    S.outerFace ⟨27, by omega⟩ ≤ C.faceUpper ⟨27, by omega⟩ := sorry

/-- STUB. `outerFace (28)` (formal/SourceBounds182.lean:141). -/
theorem integral_le_outer_face_028 (S : TrialSource182) (C : TrialCerts182) :
    S.outerFace ⟨28, by omega⟩ ≤ C.faceUpper ⟨28, by omega⟩ := sorry

/-- STUB. `outerFace (29)` (formal/SourceBounds182.lean:141). -/
theorem integral_le_outer_face_029 (S : TrialSource182) (C : TrialCerts182) :
    S.outerFace ⟨29, by omega⟩ ≤ C.faceUpper ⟨29, by omega⟩ := sorry

/-- STUB. `outerFace (30)` (formal/SourceBounds182.lean:141). -/
theorem integral_le_outer_face_030 (S : TrialSource182) (C : TrialCerts182) :
    S.outerFace ⟨30, by omega⟩ ≤ C.faceUpper ⟨30, by omega⟩ := sorry

/-- STUB. `outerFace (31)` (formal/SourceBounds182.lean:141). -/
theorem integral_le_outer_face_031 (S : TrialSource182) (C : TrialCerts182) :
    S.outerFace ⟨31, by omega⟩ ≤ C.faceUpper ⟨31, by omega⟩ := sorry

/-- STUB. `outerFace (32)` (formal/SourceBounds182.lean:141). -/
theorem integral_le_outer_face_032 (S : TrialSource182) (C : TrialCerts182) :
    S.outerFace ⟨32, by omega⟩ ≤ C.faceUpper ⟨32, by omega⟩ := sorry

/-- STUB. `outerFace (33)` (formal/SourceBounds182.lean:141). -/
theorem integral_le_outer_face_033 (S : TrialSource182) (C : TrialCerts182) :
    S.outerFace ⟨33, by omega⟩ ≤ C.faceUpper ⟨33, by omega⟩ := sorry

/-- STUB. `outerFace (34)` (formal/SourceBounds182.lean:141). -/
theorem integral_le_outer_face_034 (S : TrialSource182) (C : TrialCerts182) :
    S.outerFace ⟨34, by omega⟩ ≤ C.faceUpper ⟨34, by omega⟩ := sorry

/-- STUB. `outerFace (35)` (formal/SourceBounds182.lean:141). -/
theorem integral_le_outer_face_035 (S : TrialSource182) (C : TrialCerts182) :
    S.outerFace ⟨35, by omega⟩ ≤ C.faceUpper ⟨35, by omega⟩ := sorry

/-- STUB. `outerFace (36)` (formal/SourceBounds182.lean:141). -/
theorem integral_le_outer_face_036 (S : TrialSource182) (C : TrialCerts182) :
    S.outerFace ⟨36, by omega⟩ ≤ C.faceUpper ⟨36, by omega⟩ := sorry

/-- STUB. `outerFace (37)` (formal/SourceBounds182.lean:141). -/
theorem integral_le_outer_face_037 (S : TrialSource182) (C : TrialCerts182) :
    S.outerFace ⟨37, by omega⟩ ≤ C.faceUpper ⟨37, by omega⟩ := sorry

/-- STUB. `outerFace (38)` (formal/SourceBounds182.lean:141). -/
theorem integral_le_outer_face_038 (S : TrialSource182) (C : TrialCerts182) :
    S.outerFace ⟨38, by omega⟩ ≤ C.faceUpper ⟨38, by omega⟩ := sorry

/-- STUB. `outerFace (39)` (formal/SourceBounds182.lean:141). -/
theorem integral_le_outer_face_039 (S : TrialSource182) (C : TrialCerts182) :
    S.outerFace ⟨39, by omega⟩ ≤ C.faceUpper ⟨39, by omega⟩ := sorry

/-- STUB. `outerFace (40)` (formal/SourceBounds182.lean:141). -/
theorem integral_le_outer_face_040 (S : TrialSource182) (C : TrialCerts182) :
    S.outerFace ⟨40, by omega⟩ ≤ C.faceUpper ⟨40, by omega⟩ := sorry

/-- STUB. `outerFace (41)` (formal/SourceBounds182.lean:141). -/
theorem integral_le_outer_face_041 (S : TrialSource182) (C : TrialCerts182) :
    S.outerFace ⟨41, by omega⟩ ≤ C.faceUpper ⟨41, by omega⟩ := sorry

/-- STUB. `outerFace (42)` (formal/SourceBounds182.lean:141). -/
theorem integral_le_outer_face_042 (S : TrialSource182) (C : TrialCerts182) :
    S.outerFace ⟨42, by omega⟩ ≤ C.faceUpper ⟨42, by omega⟩ := sorry

/-- STUB. `outerFace (43)` (formal/SourceBounds182.lean:141). -/
theorem integral_le_outer_face_043 (S : TrialSource182) (C : TrialCerts182) :
    S.outerFace ⟨43, by omega⟩ ≤ C.faceUpper ⟨43, by omega⟩ := sorry

/-- STUB. `outerFace (44)` (formal/SourceBounds182.lean:141). -/
theorem integral_le_outer_face_044 (S : TrialSource182) (C : TrialCerts182) :
    S.outerFace ⟨44, by omega⟩ ≤ C.faceUpper ⟨44, by omega⟩ := sorry

/-- STUB. `outerFace (45)` (formal/SourceBounds182.lean:141). -/
theorem integral_le_outer_face_045 (S : TrialSource182) (C : TrialCerts182) :
    S.outerFace ⟨45, by omega⟩ ≤ C.faceUpper ⟨45, by omega⟩ := sorry

/-- STUB. `outerFace (46)` (formal/SourceBounds182.lean:141). -/
theorem integral_le_outer_face_046 (S : TrialSource182) (C : TrialCerts182) :
    S.outerFace ⟨46, by omega⟩ ≤ C.faceUpper ⟨46, by omega⟩ := sorry

/-- STUB. `outerFace (47)` (formal/SourceBounds182.lean:141). -/
theorem integral_le_outer_face_047 (S : TrialSource182) (C : TrialCerts182) :
    S.outerFace ⟨47, by omega⟩ ≤ C.faceUpper ⟨47, by omega⟩ := sorry

/-- STUB. `outerFace (48)` (formal/SourceBounds182.lean:141). -/
theorem integral_le_outer_face_048 (S : TrialSource182) (C : TrialCerts182) :
    S.outerFace ⟨48, by omega⟩ ≤ C.faceUpper ⟨48, by omega⟩ := sorry

/-- STUB. `outerFace (49)` (formal/SourceBounds182.lean:141). -/
theorem integral_le_outer_face_049 (S : TrialSource182) (C : TrialCerts182) :
    S.outerFace ⟨49, by omega⟩ ≤ C.faceUpper ⟨49, by omega⟩ := sorry

/-- STUB. `outerFace (50)` (formal/SourceBounds182.lean:141). -/
theorem integral_le_outer_face_050 (S : TrialSource182) (C : TrialCerts182) :
    S.outerFace ⟨50, by omega⟩ ≤ C.faceUpper ⟨50, by omega⟩ := sorry

/-- STUB. `outerFace (51)` (formal/SourceBounds182.lean:141). -/
theorem integral_le_outer_face_051 (S : TrialSource182) (C : TrialCerts182) :
    S.outerFace ⟨51, by omega⟩ ≤ C.faceUpper ⟨51, by omega⟩ := sorry

/-- STUB. `outerFace (52)` (formal/SourceBounds182.lean:141). -/
theorem integral_le_outer_face_052 (S : TrialSource182) (C : TrialCerts182) :
    S.outerFace ⟨52, by omega⟩ ≤ C.faceUpper ⟨52, by omega⟩ := sorry

/-- STUB. `outerFace (53)` (formal/SourceBounds182.lean:141). -/
theorem integral_le_outer_face_053 (S : TrialSource182) (C : TrialCerts182) :
    S.outerFace ⟨53, by omega⟩ ≤ C.faceUpper ⟨53, by omega⟩ := sorry

/-- STUB. `outerFace (54)` (formal/SourceBounds182.lean:141). -/
theorem integral_le_outer_face_054 (S : TrialSource182) (C : TrialCerts182) :
    S.outerFace ⟨54, by omega⟩ ≤ C.faceUpper ⟨54, by omega⟩ := sorry

/-- STUB. `outerFace (55)` (formal/SourceBounds182.lean:141). -/
theorem integral_le_outer_face_055 (S : TrialSource182) (C : TrialCerts182) :
    S.outerFace ⟨55, by omega⟩ ≤ C.faceUpper ⟨55, by omega⟩ := sorry

/-- STUB. `outerFace (56)` (formal/SourceBounds182.lean:141). -/
theorem integral_le_outer_face_056 (S : TrialSource182) (C : TrialCerts182) :
    S.outerFace ⟨56, by omega⟩ ≤ C.faceUpper ⟨56, by omega⟩ := sorry

/-- STUB. `outerFace (57)` (formal/SourceBounds182.lean:141). -/
theorem integral_le_outer_face_057 (S : TrialSource182) (C : TrialCerts182) :
    S.outerFace ⟨57, by omega⟩ ≤ C.faceUpper ⟨57, by omega⟩ := sorry

/-- STUB. `outerFace (58)` (formal/SourceBounds182.lean:141). -/
theorem integral_le_outer_face_058 (S : TrialSource182) (C : TrialCerts182) :
    S.outerFace ⟨58, by omega⟩ ≤ C.faceUpper ⟨58, by omega⟩ := sorry

/-- STUB. `outerFace (59)` (formal/SourceBounds182.lean:141). -/
theorem integral_le_outer_face_059 (S : TrialSource182) (C : TrialCerts182) :
    S.outerFace ⟨59, by omega⟩ ≤ C.faceUpper ⟨59, by omega⟩ := sorry

/-! ## The 137 inner obligations (stubbed; C0 discharges) -/

/-- STUB. `innerMass (0)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_000 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨0, by omega⟩ ≤ C.innerFaceUpper ⟨0, by omega⟩ := sorry

/-- STUB. `innerMass (1)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_001 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨1, by omega⟩ ≤ C.innerFaceUpper ⟨1, by omega⟩ := sorry

/-- STUB. `innerMass (2)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_002 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨2, by omega⟩ ≤ C.innerFaceUpper ⟨2, by omega⟩ := sorry

/-- STUB. `innerMass (3)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_003 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨3, by omega⟩ ≤ C.innerFaceUpper ⟨3, by omega⟩ := sorry

/-- STUB. `innerMass (4)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_004 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨4, by omega⟩ ≤ C.innerFaceUpper ⟨4, by omega⟩ := sorry

/-- STUB. `innerMass (5)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_005 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨5, by omega⟩ ≤ C.innerFaceUpper ⟨5, by omega⟩ := sorry

/-- STUB. `innerMass (6)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_006 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨6, by omega⟩ ≤ C.innerFaceUpper ⟨6, by omega⟩ := sorry

/-- STUB. `innerMass (7)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_007 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨7, by omega⟩ ≤ C.innerFaceUpper ⟨7, by omega⟩ := sorry

/-- STUB. `innerMass (8)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_008 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨8, by omega⟩ ≤ C.innerFaceUpper ⟨8, by omega⟩ := sorry

/-- STUB. `innerMass (9)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_009 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨9, by omega⟩ ≤ C.innerFaceUpper ⟨9, by omega⟩ := sorry

/-- STUB. `innerMass (10)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_010 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨10, by omega⟩ ≤ C.innerFaceUpper ⟨10, by omega⟩ := sorry

/-- STUB. `innerMass (11)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_011 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨11, by omega⟩ ≤ C.innerFaceUpper ⟨11, by omega⟩ := sorry

/-- STUB. `innerMass (12)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_012 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨12, by omega⟩ ≤ C.innerFaceUpper ⟨12, by omega⟩ := sorry

/-- STUB. `innerMass (13)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_013 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨13, by omega⟩ ≤ C.innerFaceUpper ⟨13, by omega⟩ := sorry

/-- STUB. `innerMass (14)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_014 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨14, by omega⟩ ≤ C.innerFaceUpper ⟨14, by omega⟩ := sorry

/-- STUB. `innerMass (15)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_015 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨15, by omega⟩ ≤ C.innerFaceUpper ⟨15, by omega⟩ := sorry

/-- STUB. `innerMass (16)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_016 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨16, by omega⟩ ≤ C.innerFaceUpper ⟨16, by omega⟩ := sorry

/-- STUB. `innerMass (17)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_017 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨17, by omega⟩ ≤ C.innerFaceUpper ⟨17, by omega⟩ := sorry

/-- STUB. `innerMass (18)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_018 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨18, by omega⟩ ≤ C.innerFaceUpper ⟨18, by omega⟩ := sorry

/-- STUB. `innerMass (19)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_019 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨19, by omega⟩ ≤ C.innerFaceUpper ⟨19, by omega⟩ := sorry

/-- STUB. `innerMass (20)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_020 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨20, by omega⟩ ≤ C.innerFaceUpper ⟨20, by omega⟩ := sorry

/-- STUB. `innerMass (21)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_021 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨21, by omega⟩ ≤ C.innerFaceUpper ⟨21, by omega⟩ := sorry

/-- STUB. `innerMass (22)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_022 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨22, by omega⟩ ≤ C.innerFaceUpper ⟨22, by omega⟩ := sorry

/-- STUB. `innerMass (23)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_023 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨23, by omega⟩ ≤ C.innerFaceUpper ⟨23, by omega⟩ := sorry

/-- STUB. `innerMass (24)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_024 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨24, by omega⟩ ≤ C.innerFaceUpper ⟨24, by omega⟩ := sorry

/-- STUB. `innerMass (25)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_025 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨25, by omega⟩ ≤ C.innerFaceUpper ⟨25, by omega⟩ := sorry

/-- STUB. `innerMass (26)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_026 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨26, by omega⟩ ≤ C.innerFaceUpper ⟨26, by omega⟩ := sorry

/-- STUB. `innerMass (27)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_027 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨27, by omega⟩ ≤ C.innerFaceUpper ⟨27, by omega⟩ := sorry

/-- STUB. `innerMass (28)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_028 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨28, by omega⟩ ≤ C.innerFaceUpper ⟨28, by omega⟩ := sorry

/-- STUB. `innerMass (29)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_029 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨29, by omega⟩ ≤ C.innerFaceUpper ⟨29, by omega⟩ := sorry

/-- STUB. `innerMass (30)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_030 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨30, by omega⟩ ≤ C.innerFaceUpper ⟨30, by omega⟩ := sorry

/-- STUB. `innerMass (31)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_031 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨31, by omega⟩ ≤ C.innerFaceUpper ⟨31, by omega⟩ := sorry

/-- STUB. `innerMass (32)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_032 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨32, by omega⟩ ≤ C.innerFaceUpper ⟨32, by omega⟩ := sorry

/-- STUB. `innerMass (33)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_033 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨33, by omega⟩ ≤ C.innerFaceUpper ⟨33, by omega⟩ := sorry

/-- STUB. `innerMass (34)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_034 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨34, by omega⟩ ≤ C.innerFaceUpper ⟨34, by omega⟩ := sorry

/-- STUB. `innerMass (35)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_035 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨35, by omega⟩ ≤ C.innerFaceUpper ⟨35, by omega⟩ := sorry

/-- STUB. `innerMass (36)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_036 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨36, by omega⟩ ≤ C.innerFaceUpper ⟨36, by omega⟩ := sorry

/-- STUB. `innerMass (37)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_037 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨37, by omega⟩ ≤ C.innerFaceUpper ⟨37, by omega⟩ := sorry

/-- STUB. `innerMass (38)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_038 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨38, by omega⟩ ≤ C.innerFaceUpper ⟨38, by omega⟩ := sorry

/-- STUB. `innerMass (39)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_039 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨39, by omega⟩ ≤ C.innerFaceUpper ⟨39, by omega⟩ := sorry

/-- STUB. `innerMass (40)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_040 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨40, by omega⟩ ≤ C.innerFaceUpper ⟨40, by omega⟩ := sorry

/-- STUB. `innerMass (41)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_041 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨41, by omega⟩ ≤ C.innerFaceUpper ⟨41, by omega⟩ := sorry

/-- STUB. `innerMass (42)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_042 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨42, by omega⟩ ≤ C.innerFaceUpper ⟨42, by omega⟩ := sorry

/-- STUB. `innerMass (43)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_043 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨43, by omega⟩ ≤ C.innerFaceUpper ⟨43, by omega⟩ := sorry

/-- STUB. `innerMass (44)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_044 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨44, by omega⟩ ≤ C.innerFaceUpper ⟨44, by omega⟩ := sorry

/-- STUB. `innerMass (45)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_045 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨45, by omega⟩ ≤ C.innerFaceUpper ⟨45, by omega⟩ := sorry

/-- STUB. `innerMass (46)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_046 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨46, by omega⟩ ≤ C.innerFaceUpper ⟨46, by omega⟩ := sorry

/-- STUB. `innerMass (47)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_047 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨47, by omega⟩ ≤ C.innerFaceUpper ⟨47, by omega⟩ := sorry

/-- STUB. `innerMass (48)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_048 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨48, by omega⟩ ≤ C.innerFaceUpper ⟨48, by omega⟩ := sorry

/-- STUB. `innerMass (49)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_049 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨49, by omega⟩ ≤ C.innerFaceUpper ⟨49, by omega⟩ := sorry

/-- STUB. `innerMass (50)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_050 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨50, by omega⟩ ≤ C.innerFaceUpper ⟨50, by omega⟩ := sorry

/-- STUB. `innerMass (51)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_051 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨51, by omega⟩ ≤ C.innerFaceUpper ⟨51, by omega⟩ := sorry

/-- STUB. `innerMass (52)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_052 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨52, by omega⟩ ≤ C.innerFaceUpper ⟨52, by omega⟩ := sorry

/-- STUB. `innerMass (53)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_053 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨53, by omega⟩ ≤ C.innerFaceUpper ⟨53, by omega⟩ := sorry

/-- STUB. `innerMass (54)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_054 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨54, by omega⟩ ≤ C.innerFaceUpper ⟨54, by omega⟩ := sorry

/-- STUB. `innerMass (55)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_055 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨55, by omega⟩ ≤ C.innerFaceUpper ⟨55, by omega⟩ := sorry

/-- STUB. `innerMass (56)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_056 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨56, by omega⟩ ≤ C.innerFaceUpper ⟨56, by omega⟩ := sorry

/-- STUB. `innerMass (57)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_057 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨57, by omega⟩ ≤ C.innerFaceUpper ⟨57, by omega⟩ := sorry

/-- STUB. `innerMass (58)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_058 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨58, by omega⟩ ≤ C.innerFaceUpper ⟨58, by omega⟩ := sorry

/-- STUB. `innerMass (59)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_059 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨59, by omega⟩ ≤ C.innerFaceUpper ⟨59, by omega⟩ := sorry

/-- STUB. `innerMass (60)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_060 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨60, by omega⟩ ≤ C.innerFaceUpper ⟨60, by omega⟩ := sorry

/-- STUB. `innerMass (61)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_061 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨61, by omega⟩ ≤ C.innerFaceUpper ⟨61, by omega⟩ := sorry

/-- STUB. `innerMass (62)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_062 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨62, by omega⟩ ≤ C.innerFaceUpper ⟨62, by omega⟩ := sorry

/-- STUB. `innerMass (63)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_063 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨63, by omega⟩ ≤ C.innerFaceUpper ⟨63, by omega⟩ := sorry

/-- STUB. `innerMass (64)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_064 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨64, by omega⟩ ≤ C.innerFaceUpper ⟨64, by omega⟩ := sorry

/-- STUB. `innerMass (65)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_065 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨65, by omega⟩ ≤ C.innerFaceUpper ⟨65, by omega⟩ := sorry

/-- STUB. `innerMass (66)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_066 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨66, by omega⟩ ≤ C.innerFaceUpper ⟨66, by omega⟩ := sorry

/-- STUB. `innerMass (67)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_067 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨67, by omega⟩ ≤ C.innerFaceUpper ⟨67, by omega⟩ := sorry

/-- STUB. `innerMass (68)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_068 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨68, by omega⟩ ≤ C.innerFaceUpper ⟨68, by omega⟩ := sorry

/-- STUB. `innerMass (69)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_069 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨69, by omega⟩ ≤ C.innerFaceUpper ⟨69, by omega⟩ := sorry

/-- STUB. `innerMass (70)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_070 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨70, by omega⟩ ≤ C.innerFaceUpper ⟨70, by omega⟩ := sorry

/-- STUB. `innerMass (71)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_071 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨71, by omega⟩ ≤ C.innerFaceUpper ⟨71, by omega⟩ := sorry

/-- STUB. `innerMass (72)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_072 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨72, by omega⟩ ≤ C.innerFaceUpper ⟨72, by omega⟩ := sorry

/-- STUB. `innerMass (73)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_073 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨73, by omega⟩ ≤ C.innerFaceUpper ⟨73, by omega⟩ := sorry

/-- STUB. `innerMass (74)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_074 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨74, by omega⟩ ≤ C.innerFaceUpper ⟨74, by omega⟩ := sorry

/-- STUB. `innerMass (75)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_075 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨75, by omega⟩ ≤ C.innerFaceUpper ⟨75, by omega⟩ := sorry

/-- STUB. `innerMass (76)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_076 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨76, by omega⟩ ≤ C.innerFaceUpper ⟨76, by omega⟩ := sorry

/-- STUB. `innerMass (77)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_077 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨77, by omega⟩ ≤ C.innerFaceUpper ⟨77, by omega⟩ := sorry

/-- STUB. `innerMass (78)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_078 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨78, by omega⟩ ≤ C.innerFaceUpper ⟨78, by omega⟩ := sorry

/-- STUB. `innerMass (79)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_079 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨79, by omega⟩ ≤ C.innerFaceUpper ⟨79, by omega⟩ := sorry

/-- STUB. `innerMass (80)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_080 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨80, by omega⟩ ≤ C.innerFaceUpper ⟨80, by omega⟩ := sorry

/-- STUB. `innerMass (81)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_081 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨81, by omega⟩ ≤ C.innerFaceUpper ⟨81, by omega⟩ := sorry

/-- STUB. `innerMass (82)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_082 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨82, by omega⟩ ≤ C.innerFaceUpper ⟨82, by omega⟩ := sorry

/-- STUB. `innerMass (83)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_083 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨83, by omega⟩ ≤ C.innerFaceUpper ⟨83, by omega⟩ := sorry

/-- STUB. `innerMass (84)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_084 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨84, by omega⟩ ≤ C.innerFaceUpper ⟨84, by omega⟩ := sorry

/-- STUB. `innerMass (85)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_085 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨85, by omega⟩ ≤ C.innerFaceUpper ⟨85, by omega⟩ := sorry

/-- STUB. `innerMass (86)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_086 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨86, by omega⟩ ≤ C.innerFaceUpper ⟨86, by omega⟩ := sorry

/-- STUB. `innerMass (87)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_087 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨87, by omega⟩ ≤ C.innerFaceUpper ⟨87, by omega⟩ := sorry

/-- STUB. `innerMass (88)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_088 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨88, by omega⟩ ≤ C.innerFaceUpper ⟨88, by omega⟩ := sorry

/-- STUB. `innerMass (89)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_089 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨89, by omega⟩ ≤ C.innerFaceUpper ⟨89, by omega⟩ := sorry

/-- STUB. `innerMass (90)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_090 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨90, by omega⟩ ≤ C.innerFaceUpper ⟨90, by omega⟩ := sorry

/-- STUB. `innerMass (91)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_091 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨91, by omega⟩ ≤ C.innerFaceUpper ⟨91, by omega⟩ := sorry

/-- STUB. `innerMass (92)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_092 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨92, by omega⟩ ≤ C.innerFaceUpper ⟨92, by omega⟩ := sorry

/-- STUB. `innerMass (93)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_093 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨93, by omega⟩ ≤ C.innerFaceUpper ⟨93, by omega⟩ := sorry

/-- STUB. `innerMass (94)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_094 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨94, by omega⟩ ≤ C.innerFaceUpper ⟨94, by omega⟩ := sorry

/-- STUB. `innerMass (95)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_095 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨95, by omega⟩ ≤ C.innerFaceUpper ⟨95, by omega⟩ := sorry

/-- STUB. `innerMass (96)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_096 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨96, by omega⟩ ≤ C.innerFaceUpper ⟨96, by omega⟩ := sorry

/-- STUB. `innerMass (97)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_097 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨97, by omega⟩ ≤ C.innerFaceUpper ⟨97, by omega⟩ := sorry

/-- STUB. `innerMass (98)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_098 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨98, by omega⟩ ≤ C.innerFaceUpper ⟨98, by omega⟩ := sorry

/-- STUB. `innerMass (99)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_099 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨99, by omega⟩ ≤ C.innerFaceUpper ⟨99, by omega⟩ := sorry

/-- STUB. `innerMass (100)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_100 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨100, by omega⟩ ≤ C.innerFaceUpper ⟨100, by omega⟩ := sorry

/-- STUB. `innerMass (101)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_101 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨101, by omega⟩ ≤ C.innerFaceUpper ⟨101, by omega⟩ := sorry

/-- STUB. `innerMass (102)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_102 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨102, by omega⟩ ≤ C.innerFaceUpper ⟨102, by omega⟩ := sorry

/-- STUB. `innerMass (103)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_103 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨103, by omega⟩ ≤ C.innerFaceUpper ⟨103, by omega⟩ := sorry

/-- STUB. `innerMass (104)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_104 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨104, by omega⟩ ≤ C.innerFaceUpper ⟨104, by omega⟩ := sorry

/-- STUB. `innerMass (105)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_105 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨105, by omega⟩ ≤ C.innerFaceUpper ⟨105, by omega⟩ := sorry

/-- STUB. `innerMass (106)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_106 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨106, by omega⟩ ≤ C.innerFaceUpper ⟨106, by omega⟩ := sorry

/-- STUB. `innerMass (107)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_107 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨107, by omega⟩ ≤ C.innerFaceUpper ⟨107, by omega⟩ := sorry

/-- STUB. `innerMass (108)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_108 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨108, by omega⟩ ≤ C.innerFaceUpper ⟨108, by omega⟩ := sorry

/-- STUB. `innerMass (109)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_109 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨109, by omega⟩ ≤ C.innerFaceUpper ⟨109, by omega⟩ := sorry

/-- STUB. `innerMass (110)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_110 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨110, by omega⟩ ≤ C.innerFaceUpper ⟨110, by omega⟩ := sorry

/-- STUB. `innerMass (111)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_111 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨111, by omega⟩ ≤ C.innerFaceUpper ⟨111, by omega⟩ := sorry

/-- STUB. `innerMass (112)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_112 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨112, by omega⟩ ≤ C.innerFaceUpper ⟨112, by omega⟩ := sorry

/-- STUB. `innerMass (113)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_113 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨113, by omega⟩ ≤ C.innerFaceUpper ⟨113, by omega⟩ := sorry

/-- STUB. `innerMass (114)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_114 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨114, by omega⟩ ≤ C.innerFaceUpper ⟨114, by omega⟩ := sorry

/-- STUB. `innerMass (115)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_115 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨115, by omega⟩ ≤ C.innerFaceUpper ⟨115, by omega⟩ := sorry

/-- STUB. `innerMass (116)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_116 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨116, by omega⟩ ≤ C.innerFaceUpper ⟨116, by omega⟩ := sorry

/-- STUB. `innerMass (117)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_117 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨117, by omega⟩ ≤ C.innerFaceUpper ⟨117, by omega⟩ := sorry

/-- STUB. `innerMass (118)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_118 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨118, by omega⟩ ≤ C.innerFaceUpper ⟨118, by omega⟩ := sorry

/-- STUB. `innerMass (119)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_119 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨119, by omega⟩ ≤ C.innerFaceUpper ⟨119, by omega⟩ := sorry

/-- STUB. `innerMass (120)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_120 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨120, by omega⟩ ≤ C.innerFaceUpper ⟨120, by omega⟩ := sorry

/-- STUB. `innerMass (121)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_121 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨121, by omega⟩ ≤ C.innerFaceUpper ⟨121, by omega⟩ := sorry

/-- STUB. `innerMass (122)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_122 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨122, by omega⟩ ≤ C.innerFaceUpper ⟨122, by omega⟩ := sorry

/-- STUB. `innerMass (123)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_123 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨123, by omega⟩ ≤ C.innerFaceUpper ⟨123, by omega⟩ := sorry

/-- STUB. `innerMass (124)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_124 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨124, by omega⟩ ≤ C.innerFaceUpper ⟨124, by omega⟩ := sorry

/-- STUB. `innerMass (125)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_125 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨125, by omega⟩ ≤ C.innerFaceUpper ⟨125, by omega⟩ := sorry

/-- STUB. `innerMass (126)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_126 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨126, by omega⟩ ≤ C.innerFaceUpper ⟨126, by omega⟩ := sorry

/-- STUB. `innerMass (127)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_127 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨127, by omega⟩ ≤ C.innerFaceUpper ⟨127, by omega⟩ := sorry

/-- STUB. `innerMass (128)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_128 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨128, by omega⟩ ≤ C.innerFaceUpper ⟨128, by omega⟩ := sorry

/-- STUB. `innerMass (129)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_129 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨129, by omega⟩ ≤ C.innerFaceUpper ⟨129, by omega⟩ := sorry

/-- STUB. `innerMass (130)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_130 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨130, by omega⟩ ≤ C.innerFaceUpper ⟨130, by omega⟩ := sorry

/-- STUB. `innerMass (131)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_131 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨131, by omega⟩ ≤ C.innerFaceUpper ⟨131, by omega⟩ := sorry

/-- STUB. `innerMass (132)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_132 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨132, by omega⟩ ≤ C.innerFaceUpper ⟨132, by omega⟩ := sorry

/-- STUB. `innerMass (133)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_133 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨133, by omega⟩ ≤ C.innerFaceUpper ⟨133, by omega⟩ := sorry

/-- STUB. `innerMass (134)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_134 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨134, by omega⟩ ≤ C.innerFaceUpper ⟨134, by omega⟩ := sorry

/-- STUB. `innerMass (135)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_135 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨135, by omega⟩ ≤ C.innerFaceUpper ⟨135, by omega⟩ := sorry

/-- STUB. `innerMass (136)` (formal/SourceBounds182.lean:142). -/
theorem integral_le_inner_mass_136 (S : TrialSource182) (C : TrialCerts182) :
    S.innerMass ⟨136, by omega⟩ ≤ C.innerFaceUpper ⟨136, by omega⟩ := sorry

end Pg182Frame
