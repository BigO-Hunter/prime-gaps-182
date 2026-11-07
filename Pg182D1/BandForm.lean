import Pg182D1.Support

/-!
# BANDFORM.lean — the per-band closed form of the mass MGF (numeric refinement)

The structural exp-sandwich (`D1Mgf.mgf_fragmentLaw_le_finset`) is what the D1
chain consumes; this module adds the computable closed form the frozen data
checks consume. For every dyadic band `k` the per-band MGF is exactly

    E_k(s) = exp( - ∫_{(2^k, 2^{k+1}] ∩ (0,ζ]} (1 - e^{-s·u}) / u du ),

kernel-proved by instantiating the vendored EReal Poisson-MGF machinery
(`lintegral_exp_neg_finitePoissonLaw`) on the band intensity measure. The
exponent `b_k := ∫_band (1 - e^{-su})/u` is the certified quantity the
per-cell envelope data bounds below (see receipt/percell_gen.py).
-/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace PrimeGap182D1

/-- The band window of the `k`-th dyadic band inside the trial support. -/
def bandWindow (ζ : ℝ) (k : ℤ) : Set ℝ :=
  Set.Ioc ((2:ℝ)^k) ((2:ℝ)^(k+1)) ∩ Set.Ioc (0:ℝ) ζ

theorem bandWindow_pos {ζ : ℝ} {k : ℤ} {u : ℝ} (hu : u ∈ bandWindow ζ k) : (0:ℝ) < u := by
  exact (zpow_pos (by norm_num : (0:ℝ) < 2) k).trans hu.1.1

theorem mem_bandWindow {ζ : ℝ} {k : ℤ} {u : ℝ} (hu : u ∈ bandWindow ζ k) :
    (2:ℝ)^k < u ∧ 0 < u ∧ u ≤ ζ := by
  have h1 : (2:ℝ)^k < u := hu.1.1
  have h2 : (0:ℝ) < (2:ℝ)^k := zpow_pos (by norm_num) k
  exact ⟨h1, h2.trans h1, hu.2.2⟩

theorem measurableSet_bandWindow (ζ : ℝ) (k : ℤ) : MeasurableSet (bandWindow ζ k) :=
  (measurableSet_Ioc).inter measurableSet_Ioc

/-- The per-band closed form: the MGF of the mass under the Poisson law of the
`k`-th dyadic band is the exponential of minus the band's intensity integral. -/
theorem bandMgf_eq (ζ s : ℝ) (k : ℤ) (hs : 0 ≤ s) :
    (∫ X : FiniteMeasure ℝ, Real.exp (-s * (X.mass : ℝ))
        ∂(finitePoissonLaw (cappedDyadicIntensity ζ k)))
      = Real.exp (- (∫ u in bandWindow ζ k, (1 - Real.exp (-s * u)) / u)) := by
  haveI hprob : IsProbabilityMeasure
      (finitePoissonLaw (cappedDyadicIntensity ζ k)) :=
    finitePoissonLaw_isProbabilityMeasure _
  have hAmeas : MeasurableSet (bandWindow ζ k) := measurableSet_bandWindow ζ k
  have hmassm : Measurable (fun c : FiniteMeasure ℝ => (c.mass : ℝ)) := measurable_mass
  -- integrability of the real MGF integrand
  have hleftInt : Integrable
      (fun c : FiniteMeasure ℝ => Real.exp (-s * (c.mass : ℝ)))
      (finitePoissonLaw (cappedDyadicIntensity ζ k)) := by
    refine (integrable_const (1 : ℝ)).mono'
      (measurable_const.mul hmassm).exp.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun c => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs) c.mass.coe_nonneg)
  -- the EReal survival lemma per coordinate
  have hinner : ∀ u : ℝ, 0 ≤ u →
      EReal.exp (-((ENNReal.ofReal u * ENNReal.ofReal s : ℝ≥0∞) : EReal)) =
        ENNReal.ofReal (Real.exp (-s * u)) := by
    intro u hu
    rw [mul_comm (ENNReal.ofReal u) (ENNReal.ofReal s),
      ← ENNReal.ofReal_mul hs, EReal.coe_ennreal_ofReal,
      max_eq_left (mul_nonneg hs hu),
      ← EReal.coe_neg, EReal.exp_coe]
    simp only [neg_mul]
  -- the band measure, raw
  have hWcoe : ((cappedDyadicIntensity ζ k : FiniteMeasure ℝ) : Measure ℝ)
      = ((volume.restrict (Set.Ioc (0:ℝ) ζ)).withDensity
          (fun u : ℝ => ENNReal.ofReal (1 / u))).restrict
          (Set.Ioc ((2:ℝ)^k) ((2:ℝ)^(k+1))) := by
    simp only [cappedDyadicIntensity, FiniteMeasure.toMeasure_mk]
  -- the band intensity integral unwraps to the real integral over the band window
  have hintensity : (∫⁻ u, 1 - EReal.exp
        (-((ENNReal.ofReal u * ENNReal.ofReal s : ℝ≥0∞) : EReal))
      ∂((cappedDyadicIntensity ζ k : FiniteMeasure ℝ) : Measure ℝ))
      = ENNReal.ofReal (∫ u in bandWindow ζ k, (1 - Real.exp (-s * u)) / u) := by
    rw [hWcoe]
    have hhmeas : Measurable (fun u : ℝ => ENNReal.ofReal (1 / u)) :=
      (measurable_const.div measurable_id).ennreal_ofReal
    have hφmeas : Measurable (fun u : ℝ => 1 - EReal.exp
        (-((ENNReal.ofReal u * ENNReal.ofReal s : ℝ≥0∞) : EReal))) :=
      measurable_const.sub
        ((measurable_id.ennreal_ofReal.mul measurable_const).coe_ereal_ennreal.neg.ereal_exp)
    have hbound : ∀ u ∈ bandWindow ζ k, 0 ≤ (1 - Real.exp (-s * u)) / u ∧
        (1 - Real.exp (-s * u)) / u ≤ s := by
      intro u hu
      have hu0 := bandWindow_pos hu
      constructor
      · exact div_nonneg
          (sub_nonneg.mpr (Real.exp_le_one_iff.mpr
            (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs) hu0.le))) hu0.le
      · apply (div_le_iff₀ hu0).2
        linarith [Real.add_one_le_exp (-s * u)]
    have hAfin : IsFiniteMeasure (volume.restrict (bandWindow ζ k)) := by
      refine ⟨?_⟩
      have hsub : bandWindow ζ k ⊆ Set.Ioc ((2:ℝ)^k) ((2:ℝ)^(k+1)) :=
        fun u hu => hu.1
      have hle : ((volume.restrict (bandWindow ζ k)) Set.univ)
          ≤ volume (Set.Ioc ((2:ℝ)^k) ((2:ℝ)^(k+1))) := by
        have hcoe : ((volume.restrict (bandWindow ζ k)) Set.univ)
            = volume (bandWindow ζ k) := by
          simp [Measure.restrict_apply]
        rw [hcoe]
        exact measure_mono hsub
      simp only [Real.volume_Ioc] at hle
      exact lt_of_le_of_lt hle ENNReal.coe_lt_top
    have hkerInt : Integrable
        (fun u : ℝ => (1 - Real.exp (-s * u)) / u)
        (volume.restrict (bandWindow ζ k)) := by
      have hb : ∀ u ∈ bandWindow ζ k, ‖(1 - Real.exp (-s * u)) / u‖ ≤ s :=
        fun u hu => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hbound u hu).1]
          exact (hbound u hu).2
      refine (integrable_const s).mono'
        ((measurable_const.sub (measurable_const.mul measurable_id).exp).div
          measurable_id).aestronglyMeasurable
        (ae_restrict_of_forall_mem hAmeas hb)
    show (∫⁻ u in Set.Ioc ((2:ℝ)^k) ((2:ℝ)^(k+1)),
        1 - EReal.exp (-((ENNReal.ofReal u * ENNReal.ofReal s : ℝ≥0∞) : EReal))
      ∂((volume.restrict (Set.Ioc (0:ℝ) ζ)).withDensity
          (fun u : ℝ => ENNReal.ofReal (1 / u)))) = _
    rw [setLIntegral_withDensity_eq_setLIntegral_mul
      (volume.restrict (Set.Ioc (0:ℝ) ζ)) hhmeas hφmeas
      (measurableSet_Ioc : MeasurableSet (Set.Ioc ((2:ℝ)^k) ((2:ℝ)^(k+1))))]
    rw [Measure.restrict_restrict
      (measurableSet_Ioc : MeasurableSet (Set.Ioc ((2:ℝ)^k) ((2:ℝ)^(k+1))))]
    rw [ofReal_integral_eq_lintegral_ofReal hkerInt
      (ae_restrict_of_forall_mem hAmeas (fun u hu => (hbound u hu).1))]
    simp only [bandWindow]
    have hpt : ∀ u ∈ bandWindow ζ k,
        ((fun u : ℝ => ENNReal.ofReal (1 / u)) *
            (fun u : ℝ => 1 - EReal.exp
              (-((ENNReal.ofReal u * ENNReal.ofReal s : ℝ≥0∞) : EReal)))) u
          = ENNReal.ofReal ((1 - Real.exp (-s * u)) / u) := by
      intro u hu
      have hu0 := bandWindow_pos hu
      change ENNReal.ofReal (1 / u) *
          (1 - EReal.exp (-((ENNReal.ofReal u * ENNReal.ofReal s : ℝ≥0∞) : EReal))) =
        ENNReal.ofReal ((1 - Real.exp (-s * u)) / u)
      rw [hinner u hu0.le, ← ENNReal.ofReal_one,
        ← ENNReal.ofReal_sub 1 (Real.exp_nonneg _),
        ← ENNReal.ofReal_mul (div_nonneg zero_le_one hu0.le)]
      congr 1
      ring
    refine lintegral_congr_ae ?_
    filter_upwards [ae_restrict_of_forall_mem hAmeas (fun u hu => hpt u hu)] with u hu
    exact hu
  -- the per-point identity on the MGF
  have hpoint (c : FiniteMeasure ℝ) :
      EReal.exp (-((∫⁻ _u, ENNReal.ofReal s ∂(c : Measure ℝ)) : EReal)) =
        ENNReal.ofReal (Real.exp (-s * (c.mass : ℝ))) := by
    simpa only [lintegral_const, ← FiniteMeasure.ennreal_mass,
      ENNReal.ofReal_coe_nnreal, mul_comm] using hinner (c.mass : ℝ) c.mass.coe_nonneg
  have hmain := lintegral_exp_neg_finitePoissonLaw (cappedDyadicIntensity ζ k)
    (fun _ => ENNReal.ofReal s) measurable_const
  simp_rw [hpoint] at hmain
  rw [← ofReal_integral_eq_lintegral_ofReal hleftInt
      (Filter.Eventually.of_forall fun _ => Real.exp_nonneg _)] at hmain
  have hI0 : (0:ℝ) ≤ ∫ u in bandWindow ζ k, (1 - Real.exp (-s * u)) / u := by
    refine setIntegral_nonneg hAmeas fun u hu => ?_
    have hu0 := bandWindow_pos hu
    exact div_nonneg
      (sub_nonneg.mpr (Real.exp_le_one_iff.mpr
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs) hu0.le))) hu0.le
  rw [hintensity, EReal.coe_ennreal_ofReal, max_eq_left hI0,
    ← EReal.coe_neg, EReal.exp_coe] at hmain
  exact (ENNReal.ofReal_eq_ofReal_iff
    (integral_nonneg fun _ => Real.exp_nonneg _) (Real.exp_nonneg _)).1 hmain

/-- The band exponent is nonnegative, so the per-band MGF is at most 1. -/
theorem bandMgf_le_one (ζ s : ℝ) (k : ℤ) (hs : 0 ≤ s) :
    (∫ X : FiniteMeasure ℝ, Real.exp (-s * (X.mass : ℝ))
        ∂(finitePoissonLaw (cappedDyadicIntensity ζ k))) ≤ 1 := by
  rw [bandMgf_eq ζ s k hs]
  refine Real.exp_le_one_iff.mpr (neg_nonpos.mpr ?_)
  refine setIntegral_nonneg (measurableSet_bandWindow ζ k) fun u hu => ?_
  have hu0 := bandWindow_pos hu
  exact div_nonneg (sub_nonneg.mpr (Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs) hu0.le))) hu0.le

end PrimeGap182D1
