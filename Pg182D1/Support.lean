import Pg182D1.Law

/-!
# SUPPORT.lean — verbatim vendor helper slice (PrimeGap186, b77bf175bded)

The small lemma chain the fragment law stands on, copied verbatim from
`vendor/primegaps186/PrimeGaps186.lean` and renamed into `PrimeGap182D1`.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal
open scoped NNReal

namespace PrimeGap182D1

theorem coe_weightedEmpirical (n : ℕ) (x : Fin n → ℝ) :
    (weightedEmpirical n x : Measure ℝ) =
      ∑ i : Fin n, ENNReal.ofReal (x i) • Measure.dirac (x i) := by
  unfold weightedEmpirical
  rw [FiniteMeasure.toMeasure_sum]
  rfl

theorem measurable_weightedEmpirical (n : ℕ) : Measurable (weightedEmpirical n) := by
  have hm : Measurable (fun x : Fin n → ℝ => (weightedEmpirical n x : Measure ℝ)) := by
    apply Measure.measurable_of_measurable_coe
    intro s hs
    simp only [coe_weightedEmpirical, Measure.finsetSum_apply, Measure.smul_apply,
      smul_eq_mul, Measure.dirac_apply' _ hs]
    fun_prop
  exact hm.subtype_mk

theorem measurable_weightedEmpirical_sample :
    Measurable (fun p : ℕ × (ℕ → ℝ) =>
      weightedEmpirical p.1 (fun i : Fin p.1 => p.2 i.val)) := by
  refine measurable_from_prod_countable_right fun n => ?_
  exact (measurable_weightedEmpirical n).comp (by fun_prop)

theorem coe_eq_mass_smul_normalize (μ : FiniteMeasure ℝ) :
    (μ : Measure ℝ) = (μ.mass : ℝ≥0∞) • (μ.normalize : Measure ℝ) :=
  congrArg (fun ν : FiniteMeasure ℝ => (ν : Measure ℝ)) μ.self_eq_mass_smul_normalize

theorem lintegral_finitePoissonLaw_normalized
    (μ : FiniteMeasure ℝ) (F : FiniteMeasure ℝ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ c, F c ∂(finitePoissonLaw μ) =
      ∫⁻ n, ∫⁻ x : Fin n → ℝ, F (weightedEmpirical n x)
        ∂(Measure.pi (fun _ : Fin n => (μ.normalize : Measure ℝ)))
        ∂(ProbabilityTheory.poissonMeasure μ.mass) := by
  unfold finitePoissonLaw
  rw [lintegral_map hF measurable_weightedEmpirical_sample,
    lintegral_prod (fun p : ℕ × (ℕ → ℝ) =>
      F (weightedEmpirical p.1 (fun i => p.2 i)))
      (hF.comp measurable_weightedEmpirical_sample).aemeasurable]
  apply lintegral_congr
  intro n
  rw [← Measure.infinitePi_eq_pi,
    ← Measure.map_infinitePi_infinitePi_of_inj
      (P := fun _ : ℕ => (μ.normalize : Measure ℝ)) (f := fun i : Fin n => i.val)
      Fin.val_injective,
    lintegral_map (f := fun x => F (weightedEmpirical n x))
      (hF.comp (measurable_weightedEmpirical n)) (by fun_prop)]

theorem lintegral_weightedEmpirical_pi (μ : FiniteMeasure ℝ) (n : ℕ)
    (h : ℝ → ℝ≥0∞) (hh : Measurable h) :
    (∫⁻ x : Fin n → ℝ, ∫⁻ u, h u ∂(weightedEmpirical n x : Measure ℝ)
      ∂(Measure.pi (fun _ : Fin n => (μ.normalize : Measure ℝ)))) =
      (n : ℝ≥0∞) * ∫⁻ u, ENNReal.ofReal u * h u ∂(μ.normalize : Measure ℝ) := by
  simp_rw [coe_weightedEmpirical, lintegral_finsetSum_measure, lintegral_smul_measure,
    lintegral_dirac, smul_eq_mul]
  rw [lintegral_finsetSum Finset.univ (by fun_prop)]
  simpa using Finset.sum_eq_card_nsmul (s := Finset.univ) (fun i _ =>
    (measurePreserving_eval (fun _ : Fin n => (μ.normalize : Measure ℝ)) i).lintegral_comp
      (measurable_id.ennreal_ofReal.mul hh))

theorem poisson_singleton_succ (r : ℝ≥0) (n : ℕ) :
    ((n + 1 : ℕ) : ℝ≥0∞) * ProbabilityTheory.poissonMeasure r {n + 1} =
      (r : ℝ≥0∞) * ProbabilityTheory.poissonMeasure r {n} := by
  have hreal : ((n + 1 : ℕ) : ℝ) *
      (Real.exp (-(r : ℝ)) * (r : ℝ) ^ (n + 1) / (n + 1).factorial) =
      (r : ℝ) * (Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / n.factorial) := by
    rw [Nat.factorial_succ, Nat.cast_mul, pow_succ]
    field_simp
  simpa only [ENNReal.ofReal_mul (by positivity : 0 ≤ ((n + 1 : ℕ) : ℝ)),
    ENNReal.ofReal_mul r.coe_nonneg, ENNReal.ofReal_natCast, ENNReal.ofReal_coe_nnreal,
    ProbabilityTheory.poissonMeasure_singleton] using congrArg ENNReal.ofReal hreal

theorem lintegral_poisson_id (r : ℝ≥0) :
    ∫⁻ n : ℕ, (n : ℝ≥0∞) ∂(ProbabilityTheory.poissonMeasure r) = (r : ℝ≥0∞) := by
  have hsum : ∑' n : ℕ, ProbabilityTheory.poissonMeasure r {n} = 1 := by
    simpa using (lintegral_countable' (μ := ProbabilityTheory.poissonMeasure r)
      (fun _ : ℕ => (1 : ℝ≥0∞))).symm
  rw [lintegral_countable', tsum_eq_zero_add' ENNReal.summable]
  simp only [Nat.cast_zero, zero_mul, zero_add, poisson_singleton_succ]
  rw [ENNReal.tsum_mul_left, hsum, mul_one]

theorem lintegral_weighted_finitePoissonLaw
    (μ : FiniteMeasure ℝ) (h : ℝ → ℝ≥0∞) (hh : Measurable h) :
    (∫⁻ c, ∫⁻ u, h u ∂(c : Measure ℝ) ∂(finitePoissonLaw μ)) =
      ∫⁻ u, ENNReal.ofReal u * h u ∂(μ : Measure ℝ) := by
  rw [lintegral_finitePoissonLaw_normalized μ
    (fun c => ∫⁻ u, h u ∂(c : Measure ℝ))
    ((Measure.measurable_lintegral hh).comp measurable_subtype_coe)]
  simp_rw [lintegral_weightedEmpirical_pi μ _ h hh]
  rw [lintegral_mul_const _ (by fun_prop), lintegral_poisson_id,
    coe_eq_mass_smul_normalize μ, lintegral_smul_measure, smul_eq_mul]

theorem finitePoissonLaw_isProbabilityMeasure (μ : FiniteMeasure ℝ) :
    IsProbabilityMeasure (finitePoissonLaw μ) := by
  unfold finitePoissonLaw
  infer_instance

theorem measurable_fragment_sum :
    Measurable (fun ω : ℤ → FiniteMeasure ℝ =>
      Measure.sum (fun k : ℤ => (ω k : Measure ℝ))) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  simp only [Measure.sum_apply _ hs]
  exact Measurable.tsum fun k => (Measure.measurable_coe hs).comp
    (measurable_subtype_coe.comp (measurable_pi_apply k))

theorem measurable_finiteFragments : Measurable finiteFragments := by
  classical
  have hg : Measurable (fun ω : {ω : ℤ → FiniteMeasure ℝ |
      IsFiniteMeasure (Measure.sum (fun k : ℤ => (ω k : Measure ℝ)))} =>
      (⟨Measure.sum (fun k : ℤ => (ω.val k : Measure ℝ)), ω.property⟩ : FiniteMeasure ℝ)) :=
    (measurable_fragment_sum.comp measurable_subtype_coe).subtype_mk
  unfold finiteFragments
  exact hg.dite (g := fun _ => (0 : FiniteMeasure ℝ)) measurable_const
    (FiniteMeasure.measurableSet_isFiniteMeasure.preimage measurable_fragment_sum)

theorem dyadic_bands_disjoint :
    Pairwise (fun i j : ℤ => Disjoint
      (Set.Ioc ((2 : ℝ) ^ i) ((2 : ℝ) ^ (i + 1)))
      (Set.Ioc ((2 : ℝ) ^ j) ((2 : ℝ) ^ (j + 1)))) :=
  (zpow_right_mono₀ (by norm_num : (1 : ℝ) ≤ 2)).pairwise_disjoint_on_Ioc_succ

theorem iUnion_dyadic_bands :
    (⋃ k : ℤ, Set.Ioc ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1))) = Set.Ioi 0 := by
  ext u
  simp only [Set.mem_iUnion, Set.mem_Ioi]
  constructor
  · rintro ⟨k, hk⟩
    exact (zpow_pos (by norm_num) k).trans hk.1
  · exact fun hu => exists_mem_Ioc_zpow hu (by norm_num : (1 : ℝ) < 2)

theorem sum_cappedDyadicIntensity (ζ : ℝ) :
    Measure.sum (fun k : ℤ => (cappedDyadicIntensity ζ k : Measure ℝ)) =
      (volume.restrict (Set.Ioc (0 : ℝ) ζ)).withDensity
        (fun u : ℝ => ENNReal.ofReal (1 / u)) := by
  change Measure.sum (fun k : ℤ =>
    ((volume.restrict (Set.Ioc (0 : ℝ) ζ)).withDensity
      (fun u : ℝ => ENNReal.ofReal (1 / u))).restrict
      (Set.Ioc ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1)))) = _
  rw [← Measure.restrict_iUnion dyadic_bands_disjoint (fun _ => measurableSet_Ioc),
    iUnion_dyadic_bands, restrict_withDensity measurableSet_Ioi,
    Measure.restrict_restrict measurableSet_Ioi,
    Set.inter_eq_right.mpr (fun _ hu => hu.1)]

theorem lintegral_fragment_sum (ζ : ℝ) (h : ℝ → ℝ≥0∞) (hh : Measurable h) :
    (∫⁻ ω, ∫⁻ u, h u ∂(Measure.sum (fun k : ℤ => (ω k : Measure ℝ)))
      ∂(Measure.infinitePi (fun k : ℤ =>
        finitePoissonLaw (cappedDyadicIntensity ζ k)))) =
      ∫⁻ u in Set.Ioc (0 : ℝ) ζ, h u ∂volume := by
  let : ∀ k : ℤ, IsProbabilityMeasure (finitePoissonLaw (cappedDyadicIntensity ζ k)) :=
    fun k => finitePoissonLaw_isProbabilityMeasure _
  have hm : Measurable (fun c : FiniteMeasure ℝ => ∫⁻ u, h u ∂(c : Measure ℝ)) :=
    (Measure.measurable_lintegral hh).comp measurable_subtype_coe
  simp_rw [lintegral_sum_measure]
  rw [lintegral_tsum (f := fun k : ℤ => fun ω : ℤ → FiniteMeasure ℝ =>
    ∫⁻ u, h u ∂(ω k : Measure ℝ))
    (fun k => (hm.comp (measurable_pi_apply k)).aemeasurable)]
  have he (k : ℤ) := (measurePreserving_eval_infinitePi
      (fun j : ℤ => finitePoissonLaw (cappedDyadicIntensity ζ j)) k).lintegral_comp hm
  simp_rw [he, lintegral_weighted_finitePoissonLaw _ h hh]
  rw [← lintegral_sum_measure, sum_cappedDyadicIntensity,
    lintegral_withDensity_eq_lintegral_mul _
      (f := fun u : ℝ => ENNReal.ofReal (1 / u))
      (g := fun u : ℝ => ENNReal.ofReal u * h u) (by fun_prop) (by fun_prop)]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
  have hu0 : 0 < u := hu.1
  change ENNReal.ofReal (1 / u) * (ENNReal.ofReal u * h u) = h u
  rw [← mul_assoc, ← ENNReal.ofReal_mul (le_of_lt (one_div_pos.mpr hu0)),
    one_div_mul_cancel hu0.ne', ENNReal.ofReal_one, one_mul]

theorem ae_isFiniteMeasure_fragment_sum (ζ : ℝ) :
    ∀ᵐ ω ∂(Measure.infinitePi (fun k : ℤ =>
      finitePoissonLaw (cappedDyadicIntensity ζ k))),
      IsFiniteMeasure (Measure.sum (fun k : ℤ => (ω k : Measure ℝ))) := by
  have hm : Measurable (fun ω : ℤ → FiniteMeasure ℝ =>
      (Measure.sum (fun k : ℤ => (ω k : Measure ℝ))) Set.univ) :=
    (Measure.measurable_coe MeasurableSet.univ).comp measurable_fragment_sum
  have he := lintegral_fragment_sum ζ (fun _ => 1) measurable_const
  simp only [lintegral_one, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero] at he
  filter_upwards [ae_lt_top hm (by rw [he]; exact ENNReal.ofReal_ne_top)] with ω hω
  exact ⟨hω⟩

theorem fragmentLaw_isProbabilityMeasure (ζ : ℝ) : IsProbabilityMeasure (fragmentLaw ζ) := by
  let : ∀ k : ℤ, IsProbabilityMeasure (finitePoissonLaw (cappedDyadicIntensity ζ k)) :=
    fun k => finitePoissonLaw_isProbabilityMeasure _
  unfold fragmentLaw
  infer_instance

end PrimeGap182D1
