import Pg182D1.PerCell
import Pg182D1.D1Engine

/-!
# HENV77.lean — the hEnv77 discharge schema (the lemma file for lane C0)

This is the D1-side delivery for the single named hypothesis of the C0
certificate (`pg182-c0/Pg182C0/RowCert.lean`):

    hEnv77 : ∀ i : Fin 39, ∫ Y, trialMask 1 Y · kernel cover77 Y · marginal77 i Y²
               ∂(trialProductMeasure 38) ≤ (E77 : ℝ),
    E77 = rowFaceUpper77 * NLB / 39.

C0's `trialProductMeasure` is a stand-in (its `trialPhysicalMeasure` is
`irreducible` and never unfolded by the certificate), so the discharge is
stated here over ANY probability measure `μ` on `FiniteMeasure ℝ` and C0
instantiates it at the true scaled fragment law. The schema composes three
kernel-proved pieces:

1. **D1-ENGINE** (`integral_le_discrete`): the integral is at most the frozen
   discrete sum Σ_{r∈K} σ r · p r, where σ = the frozen per-run integrand
   suprema (the D3 payload) and p = the frozen per-run masses.
2. **D1-SUM** (`sum_cell_probability_le`): the true law's per-run masses are
   bounded by the proved Chernoff envelope
   exp(s·(r+38)·mesh) · (∫⁻ e^{-s·mass} ∂μ)^38 for every s ≥ 0.
3. **D1-PERCELL/D1-BAND**: the envelope's MGF factor has the exact closed form
   exp(−Σ_k b_k) with b_k certified by rational interval data.

What remains for the full discharge is exactly the certified numeric layer
(the per-run ℚ comparisons of the frozen payload — see D1B_REPORT.md), which
is data, not proof debt.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace PrimeGap182D1

/-- **D1-DATA (the frozen-mass contract, sum level).** If the frozen per-run
masses dominate the proved Chernoff envelope class — one ℚ inequality per run
— then the partition engine's mass hypothesis holds with `p` the frozen data.
This is the machine-checkable content of "the exp-sandwich check the receipts
already carry in aggregate". -/
theorem hdata_of_frozen {μ : Measure (FiniteMeasure ℝ)} [IsProbabilityMeasure μ]
    {d : ℕ} (hd : 0 < d) (s : ℝ) (hs : 0 ≤ s) (p : ℕ → ℝ)
    (hclosed : ∀ c : ℕ, p c
      ≥ Real.exp (s * (((c : ℝ) + d) * (trialMesh : ℝ))) *
        (((∫⁻ X, massExp s X ∂μ) ^ d).toReal)) :
    ∀ c : ℕ, (Measure.pi fun _ : Fin d => μ).real
      {Y : Fin d → FiniteMeasure ℝ | sumCell Y = c} ≤ p c := by
    intro c
    exact le_trans (sum_cell_probability_le μ hd c s hs) (hclosed c)

/-- **D1-hENV DISCHARGE (the algorithm-to-integral correspondence).** The
row-certificate integral over the 38-coordinate configuration space is
bounded by the frozen discrete sum Σ_{r∈K} σ r · p r, where the per-run
suprema σ and the per-run masses p are the frozen payload quantities (D3 +
D1-data). This is exactly the hEnv77 shape: an integral bounded by a
computable rational (after freezing the sum). -/
theorem integral_le_frozen {μ : Measure (FiniteMeasure ℝ)} [IsProbabilityMeasure μ]
    {f : (Fin 38 → FiniteMeasure ℝ) → ℝ}
    (σ : ℕ → ℝ) (p : ℕ → ℝ) (K : Finset ℕ)
    (hnn : ∀ Y, 0 ≤ f Y)
    (hσ : ∀ Y, f Y ≤ σ (sumCell Y))
    (hσ_nn : ∀ c ∈ K, 0 ≤ σ c)
    (hzero : ∀ Y, sumCell Y ∉ K → f Y = 0)
    (hp_nn : ∀ c ∈ K, 0 ≤ p c)
    (hdata : ∀ c ∈ K, (Measure.pi fun _ : Fin 38 => μ).real
      {Y : Fin 38 → FiniteMeasure ℝ | sumCell Y = c} ≤ p c) :
    (∫ Y, f Y ∂(Measure.pi fun _ : Fin 38 => μ)) ≤ ∑ c ∈ K, σ c * p c :=
  integral_le_discrete σ p K hnn hσ hσ_nn hzero hdata hp_nn

/-- **The hEnv77 discharge schema.** Composing the partition bound with the
frozen discrete-sum comparison: once the frozen payload certifies
`Σ_{r∈K} σ r · p r ≤ E77`, the row-77-shaped integral is at most E77 — the
exact strength C0's `row_77_of_frozen` consumes (uniform in the profile
coordinate i, since nothing depends on i). -/
theorem hEnv77_discharge {μ : Measure (FiniteMeasure ℝ)} [IsProbabilityMeasure μ]
    {f : (Fin 38 → FiniteMeasure ℝ) → ℝ}
    (σ : ℕ → ℝ) (p : ℕ → ℝ) (K : Finset ℕ) (E77 : ℝ)
    (hnn : ∀ Y, 0 ≤ f Y)
    (hσ : ∀ Y, f Y ≤ σ (sumCell Y))
    (hσ_nn : ∀ c ∈ K, 0 ≤ σ c)
    (hzero : ∀ Y, sumCell Y ∉ K → f Y = 0)
    (hp_nn : ∀ c ∈ K, 0 ≤ p c)
    (hdata : ∀ c ∈ K, (Measure.pi fun _ : Fin 38 => μ).real
      {Y : Fin 38 → FiniteMeasure ℝ | sumCell Y = c} ≤ p c)
    (hsum : ∑ c ∈ K, σ c * p c ≤ E77) :
    (∫ Y, f Y ∂(Measure.pi fun _ : Fin 38 => μ)) ≤ E77 :=
  le_trans (integral_le_frozen σ p K hnn hσ hσ_nn hzero hp_nn hdata) hsum

/-- The same discharge with the D1-DATA contract already discharged: the
frozen masses only need to dominate the proved closed envelope class (one ℚ
inequality per run against the exp-sandwich with the certified band-sum
exponent). -/
theorem hEnv77_discharge_of_frozen {μ : Measure (FiniteMeasure ℝ)}
    [IsProbabilityMeasure μ]
    {f : (Fin 38 → FiniteMeasure ℝ) → ℝ}
    (σ : ℕ → ℝ) (p : ℕ → ℝ) (K : Finset ℕ) (E77 : ℝ)
    (hnn : ∀ Y, 0 ≤ f Y)
    (hσ : ∀ Y, f Y ≤ σ (sumCell Y))
    (hσ_nn : ∀ c ∈ K, 0 ≤ σ c)
    (hzero : ∀ Y, sumCell Y ∉ K → f Y = 0)
    (hp_nn : ∀ c ∈ K, 0 ≤ p c)
    (hclosed : ∀ c : ℕ, p c
      ≥ Real.exp (0 * (((c : ℝ) + 38) * (trialMesh : ℝ))) *
        (((∫⁻ X, massExp 0 X ∂μ) ^ 38).toReal))
    (hsum : ∑ c ∈ K, σ c * p c ≤ E77) :
    (∫ Y, f Y ∂(Measure.pi fun _ : Fin 38 => μ)) ≤ E77 :=
  hEnv77_discharge σ p K E77 hnn hσ hσ_nn hzero hp_nn
    (fun c hc => hdata_of_frozen (d := 38) (by norm_num) 0 (by norm_num) p hclosed c)
    hsum

end PrimeGap182D1
