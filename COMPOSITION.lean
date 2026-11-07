import Pg182D2.BandAssembly
import Pg182D2.HeadTail
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
≤ 38/39 < 4/π`).  The two objects that remain and are NOT analytic:

* **Layer I** — the frozen affine-prefix / retained-maximum envelope `envSup` and the row-to-cell
  map `cellOf` (audit item 3, D3 data).  Its content is the inequality chain
  `S.innerMass j ≤ envSup j * (cell mass)` (`hrow`), which is kernel/table data, not mathematics.
* **the certificate margin** `envSup j * hq ≤ C.innerFaceUpper j` (`hmargin`), the frozen numeric
  table of `formal/SourceData182.lean` read against `pg182-d2/num/`.

The 5 cap rows and the 120 outer rows are `D1`-independent (`OBLIGATION_MAP.md` §2): they carry no
per-cell law mass and are consumed as hypotheses of the same frozen shape (`hcap`, `hroot`,
`hface`).

## The final named-input list

**Katz** (`Kloosterman3Bound`), **FKM** (`Kloosterman2CorrelationBound`), **rank-four**
(`IncidenceRankFourBounds182`), **Type III** (`TypeIIILocalFourier`), the **kernel-checked
deduction** (`Deduction182`), and the **frozen numeric/certificate table**.  No smoothing lemma, no
integral estimate, no modulus computation, no charFun identity: the analytic-support half is empty.
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

/-- **THE COMPOSITION — `h1_182_of`.**  The frame theorem with `hobs` built from the discharged
data side: the 137 inner rows are the proved cell bound (`cell_measure_le_hq_final`) times the
frozen Layer-I envelope, against the frozen certificate margin.

Every hypothesis below is either a campaign-level deep input (Katz, FKM, rank-four, Type III), the
kernel-checked deduction, or frozen numeric/certificate data.  None is analytic, and none is a
Mathlib gap. -/
theorem h1_182_of (h1 : Pg182Frame.Kloosterman3Bound)
    (h2 : Pg182Frame.Kloosterman2CorrelationBound)
    (hK4 : Pg182Frame.IncidenceRankFourBounds182)
    (h3 : Pg182Frame.TypeIIILocalFourier)
    (hd : Pg182Frame.Deduction182)
    (S : Pg182Frame.TrialSource182) (C : Pg182Frame.TrialCerts182)
    -- the 5 cap rows and the 120 outer rows: D1-independent frozen data
    (hcap : Pg182Frame.CapBounds182 S)
    (hroot : ∀ j : Fin 60, S.outerRoot j ≤ C.rootUpper j)
    (hface : ∀ j : Fin 60, S.outerFace j ≤ C.faceUpper j)
    -- the 137 inner rows: Layer I (frozen envelope) against the proved cell bound
    (cellOf : Fin 137 → ℕ) (envSup : Fin 137 → ℝ)
    (henv : ∀ j : Fin 137, 0 ≤ envSup j)
    (hrow : ∀ j : Fin 137, S.innerMass j ≤ envSup j * (convPow fragmentMassLaw 38
      (Set.Ioc ((cellOf j : ℝ) * mesh) ((cellOf j : ℝ) * mesh + mesh))).toReal)
    (hmargin : ∀ j : Fin 137, envSup j * hq ≤ C.innerFaceUpper j) :
    BigOSpeedrun.PrimeGaps.Bound 182 := by
  refine Pg182Frame.h1_182_of h1 h2 hK4 h3 hd S C ⟨hcap, hroot, hface, fun j => ?_⟩
  have hcell : (convPow fragmentMassLaw 38 (Set.Ioc ((cellOf j : ℝ) * mesh)
      ((cellOf j : ℝ) * mesh + mesh))).toReal ≤ hq := by
    have h := ENNReal.toReal_mono (ENNReal.ofReal_ne_top) (cell_measure_le_hq_final (cellOf j))
    rwa [ENNReal.toReal_ofReal hq_pos.le] at h
  calc S.innerMass j ≤ envSup j * (convPow fragmentMassLaw 38 (Set.Ioc ((cellOf j : ℝ) * mesh)
        ((cellOf j : ℝ) * mesh + mesh))).toReal := hrow j
    _ ≤ envSup j * hq := mul_le_mul_of_nonneg_left hcell (henv j)
    _ ≤ C.innerFaceUpper j := hmargin j

end PrimeGap182D2
