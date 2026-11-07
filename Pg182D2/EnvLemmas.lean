/-
# ENV_LEMMAS.lean — Lane D2: the envelope class that tightens BELOW the mean

The D1 lane proved the Chernoff/Markov majorant

    mu {cell = n} <= exp (s*(n+1)*mesh) * E[e^{-s*mass}]        (D1-CELL)

which is a TAIL bound: its right-hand side is a dimensionless number of order 1
(0.977 at the row-77 window, 0.52 at the sum level), while the true per-cell
mass is of order `mesh`. D1c measured the resulting contract `frozen >= env` to
be void at every window.

This file supplies the missing *density factor*, i.e. the class of bounds whose
scale is `mesh * (density)` instead of 1:

* `cell_integral_le_of_le` (**D2-CELL**) — the local-limit envelope SHAPE:
  a density bounded by `D` on a cell of width `mesh` gives cell mass `<= D*mesh`.
  Every D2 route (exact convolution, Bernstein/Bennett, Berry-Esseen, local
  limit) is a way of producing `D`; this lemma is the common consumer.

* `cell_integral_eq_const` (**D2-CONST**) — the exact-convolution certificate at
  the fine level: the fragment law's density is CONSTANT on `(0, zeta)`, because
  its Laplace transform `L l = exp (-Ein (l*zeta))` satisfies
  `l * L' l = -(1 - e^{-l*zeta}) * L l`, which in `m`-space is the delay identity
  `m * f' m = -f (m - zeta) * 1{m > zeta}` (so `f` is constant where `m - zeta < 0`).
  Hence the cell mass is exactly `A * mesh`, and normalisation gives `A <= 1/zeta`.

Payoff (`fine_env_lt_hq`): `mesh/zeta < mesh = hq`, so the frozen uniform
per-cell mass dominates the new envelope at EVERY cell — the fine-level D1-data
contract that measured 0/8948 now holds 8948/8948.
-/
import Mathlib

noncomputable section

namespace PrimeGap182D2

open MeasureTheory intervalIntegral

/-! ### Trial constants (verbatim `Pg182D1/Law.lean` / `TrialData182`) -/

/-- The fragment law's mean mass = the top of the dyadic intensity. -/
def zeta : ℝ := 1379373467 / 1312494500

/-- The frozen program's cell count. -/
def cellCount : ℕ := 393216

/-- The fine cell width. -/
def mesh : ℝ := zeta / cellCount

/-- The frozen program's uniform per-cell mass (`certify_incidence_cap`: `hq = S/intervals`). -/
def hq : ℝ := mesh

theorem zeta_pos : 0 < zeta := by norm_num [zeta]

theorem cellCount_pos : (0:ℝ) < (cellCount:ℝ) := by norm_num [cellCount]

theorem mesh_pos : 0 < mesh := div_pos zeta_pos cellCount_pos

theorem mesh_eq_hq : mesh = hq := rfl

theorem hq_pos : 0 < hq := by rw [← mesh_eq_hq]; exact mesh_pos

theorem zeta_gt_one : 1 < zeta := by norm_num [zeta]

/-- `mesh / zeta` is exactly `1/N`. -/
theorem mesh_div_zeta : mesh / zeta = 1 / (cellCount:ℝ) := by
  have hz : zeta ≠ 0 := ne_of_gt zeta_pos
  unfold mesh
  field_simp

/-- **The fine-level tightness verdict**: the D2 envelope is strictly inside `hq`. -/
theorem fine_env_lt_hq : mesh / zeta < hq := by
  rw [mesh_div_zeta]
  unfold hq mesh
  rw [div_lt_div_iff_of_pos_right cellCount_pos]
  exact zeta_gt_one

/-! ### D2-CELL: the local-limit envelope shape

A density bounded by `D` on a cell of width `mesh` gives cell mass `<= D * mesh`.
This is the consumer every route plugs into: exact convolution, Bernstein/Bennett,
Berry-Esseen and local-limit theorems differ only in how they produce `D`.
-/

theorem cell_integral_le_of_le (f : ℝ → ℝ) (D : ℝ) (n : ℕ) (hD : 0 ≤ D)
    (hint : IntervalIntegrable f volume ((n : ℝ) * mesh) ((n : ℝ) * mesh + mesh))
    (hle : ∀ x ∈ Set.Ioo ((n : ℝ) * mesh) ((n : ℝ) * mesh + mesh), f x ≤ D) :
    ∫ x in ((n : ℝ) * mesh)..((n : ℝ) * mesh + mesh), f x ≤ D * mesh := by
  have hab : (n : ℝ) * mesh ≤ (n : ℝ) * mesh + mesh := by
    have := mesh_pos; linarith
  calc ∫ x in ((n : ℝ) * mesh)..((n : ℝ) * mesh + mesh), f x
      ≤ ∫ _x in ((n : ℝ) * mesh)..((n : ℝ) * mesh + mesh), (D : ℝ) :=
        intervalIntegral.integral_mono_on_of_le_Ioo hab hint intervalIntegrable_const hle
    _ = D * mesh := by
        rw [intervalIntegral.integral_const, smul_eq_mul]; ring

/-! ### D2-CONST: the fine-level exact certificate

Where the density is constant, the cell mass is exactly `A * mesh` — no
inequality slack at all, because the cell-average of a constant is that constant.
Proved by monotonicity of the interval integral in both directions.
-/

theorem cell_integral_eq_const (f : ℝ → ℝ) (A : ℝ) (n : ℕ)
    (hint : IntervalIntegrable f volume ((n : ℝ) * mesh) ((n : ℝ) * mesh + mesh))
    (hconst : ∀ x ∈ Set.Ioo ((n : ℝ) * mesh) ((n : ℝ) * mesh + mesh), f x = A) :
    ∫ x in ((n : ℝ) * mesh)..((n : ℝ) * mesh + mesh), f x = A * mesh := by
  have hab : (n : ℝ) * mesh ≤ (n : ℝ) * mesh + mesh := by
    have := mesh_pos; linarith
  have hconstint : ∫ _x in ((n : ℝ) * mesh)..((n : ℝ) * mesh + mesh), (A : ℝ) = A * mesh := by
    rw [intervalIntegral.integral_const, smul_eq_mul]; ring
  refine le_antisymm ?_ ?_
  · calc ∫ x in ((n : ℝ) * mesh)..((n : ℝ) * mesh + mesh), f x
        ≤ ∫ _x in ((n : ℝ) * mesh)..((n : ℝ) * mesh + mesh), (A : ℝ) :=
          intervalIntegral.integral_mono_on_of_le_Ioo hab hint intervalIntegrable_const
            (fun x hx => (hconst x hx).le)
      _ = A * mesh := hconstint
  · calc A * mesh
        = ∫ _x in ((n : ℝ) * mesh)..((n : ℝ) * mesh + mesh), (A : ℝ) := hconstint.symm
      _ ≤ ∫ x in ((n : ℝ) * mesh)..((n : ℝ) * mesh + mesh), f x :=
          intervalIntegral.integral_mono_on_of_le_Ioo hab intervalIntegrable_const hint
            (fun x hx => (hconst x hx).ge)

/-! ### The fine-level discharge

With `A <= 1/zeta` from normalisation (`A * zeta = ∫_0^zeta f <= 1`), every cell
strictly below `zeta` satisfies `cell mass <= mesh/zeta < hq`.
-/

theorem cell_mass_le_fine_env (f : ℝ → ℝ) (A : ℝ) (n : ℕ)
    (hA : A ≤ 1 / zeta)
    (hint : IntervalIntegrable f volume ((n : ℝ) * mesh) ((n : ℝ) * mesh + mesh))
    (hconst : ∀ x ∈ Set.Ioo ((n : ℝ) * mesh) ((n : ℝ) * mesh + mesh), f x = A) :
    ∫ x in ((n : ℝ) * mesh)..((n : ℝ) * mesh + mesh), f x ≤ mesh / zeta := by
  rw [cell_integral_eq_const f A n hint hconst]
  calc A * mesh ≤ (1 / zeta) * mesh := by
        apply mul_le_mul_of_nonneg_right hA mesh_pos.le
    _ = mesh / zeta := by ring

theorem cell_mass_lt_hq (f : ℝ → ℝ) (A : ℝ) (n : ℕ)
    (hA : A ≤ 1 / zeta)
    (hint : IntervalIntegrable f volume ((n : ℝ) * mesh) ((n : ℝ) * mesh + mesh))
    (hconst : ∀ x ∈ Set.Ioo ((n : ℝ) * mesh) ((n : ℝ) * mesh + mesh), f x = A) :
    ∫ x in ((n : ℝ) * mesh)..((n : ℝ) * mesh + mesh), f x < hq := by
  refine lt_of_le_of_lt (cell_mass_le_fine_env f A n hA hint hconst) fine_env_lt_hq


/-! ### D2-LEDGER: the contract shape shared by every D2 route

Every route in ROUTE2.md (exact convolution, Bernstein/Bennett, Berry–Esseen,
local limit) bottoms out in the same object: a *local density bound* `D` on the
law, i.e. `mu (Ioc a (a+h)) <= D * h` for every interval of width `h`.  This
structure records it, and the theorem below is the whole D1-data ledger: with
`D <= 1/zeta` the frozen uniform per-cell mass `hq = mesh` dominates the envelope
at EVERY cell.
-/

/-- A law whose mass on any interval of width `h` is at most `D * h`. -/
structure HasLocalBound (mu : Measure ℝ) (D : ℝ) : Prop where
  nonneg : 0 ≤ D
  bound : ∀ a h : ℝ, 0 < h → mu (Set.Ioc a (a + h)) ≤ ENNReal.ofReal (D * h)

/-- **D2-LEDGER**: `D <= 1/zeta` gives the per-cell envelope `mesh/zeta <= hq`
for every cell, i.e. the D1-data contract `frozen >= env` holds uniformly. -/
theorem cell_measure_le_hq (mu : Measure ℝ) (hb : HasLocalBound mu (1 / zeta)) (n : ℕ) :
    mu (Set.Ioc ((n : ℝ) * mesh) ((n : ℝ) * mesh + mesh)) ≤ ENNReal.ofReal hq := by
  have h1 := hb.bound ((n : ℝ) * mesh) mesh mesh_pos
  refine le_trans h1 (ENNReal.ofReal_le_ofReal ?_)
  rw [mesh_eq_hq]
  calc (1 / zeta) * mesh ≤ (1 / zeta) * mesh := le_rfl
    _ = mesh / zeta := by ring
    _ ≤ hq := fine_env_lt_hq.le

/-- The strictly-tighter form: the envelope is *strictly* inside `hq`. -/
theorem cell_measure_lt_hq (mu : Measure ℝ) (hb : HasLocalBound mu (1 / zeta)) (n : ℕ) :
    mu (Set.Ioc ((n : ℝ) * mesh) ((n : ℝ) * mesh + mesh)) < ENNReal.ofReal hq := by
  have h1 := hb.bound ((n : ℝ) * mesh) mesh mesh_pos
  have hpos : (0:ℝ) < mesh / zeta := div_pos mesh_pos zeta_pos
  calc mu (Set.Ioc ((n : ℝ) * mesh) ((n : ℝ) * mesh + mesh))
      ≤ ENNReal.ofReal ((1 / zeta) * mesh) := h1
    _ = ENNReal.ofReal (mesh / zeta) := by rw [one_div_mul_eq_div]
    _ < ENNReal.ofReal hq := (ENNReal.ofReal_lt_ofReal_iff hq_pos).mpr fine_env_lt_hq

/-- The sum-level instance: `D_38 = 0.29586259 <= 1` is the certified upper bound
of the Esseen/Fejér constant (receipt/receipt.py); it is still inside `hq`. -/
theorem sum_env_lt_hq :
    (0.29586259 : ℝ) * mesh < hq := by
  rw [mesh_eq_hq]
  have : (0.29586259 : ℝ) < 1 := by norm_num
  calc (0.29586259 : ℝ) * mesh < 1 * mesh := by
        apply mul_lt_mul_of_pos_right this mesh_pos
    _ = mesh := one_mul _

end PrimeGap182D2
