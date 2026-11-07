import Pg182D2.HasLocalBound

/-! # axcheck — Lane D3 (`HasLocalBound.lean`)

Every theorem of the smoothing-lemma file, by `#print axioms`.  Expected output for all:
`[propext, Classical.choice, Quot.sound]` (no `sorryAx`, no `native_decide`).
-/

open PrimeGap182D2

#print axioms fejerKernel_nonneg
#print axioms fejerKernel_zero
#print axioms fejerKernel_of_ne
#print axioms fejerKernel_le
#print axioms hasDerivAt_sinc_antideriv
#print axioms sinc_mul_eq
#print axioms fejerKernel_eq_integral
#print axioms fejerKernel_ge
#print axioms integral_charFun_re_Icc
#print axioms norm_charFun_shift
#print axioms integral_sinc_shift
#print axioms abs_integral_sinc_le
#print axioms integral_fejerKernel_eq
#print axioms integral_neg_eq_two
#print axioms integral_fejerKernel_le
#print axioms hasLocalBound_of_charFun_bound
#print axioms hasLocalBound_of_integrable_charFun
#print axioms hasLocalBound_one_div_zeta
#print axioms cell_measure_le_hq_of_charFun
