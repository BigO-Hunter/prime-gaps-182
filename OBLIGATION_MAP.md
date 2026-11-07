# OBLIGATION_MAP.md — the 262 obligations, definitive counts (Lane D2b; data side finalised by N1N2)

Supersedes `pg182-d1/OBLIGATION_MAP.md` on the count table and on the low-row
class. Source of every count here: **the certificate source itself**,
`frozen/.../target/SourceData182.lean` (parsed by `num/window_scan.py`), not the
payload file tree.

## 1. The table

```lean
structure TrialCerts182 where          -- formal/SourceData182.lean
  rootUpper      : Fin 60  → ℝ         -- outerRoot certificates
  faceUpper      : Fin 60  → ℝ         -- outerFace certificates
  innerFaceUpper : Fin 137 → ℝ         -- innerMass certificates
```
plus the 5 cap inequalities of `CapBounds182`. Contract:
`pg182-frame/Pg182Frame/Obligations.lean`, `PhysicalSourceBounds182Mirror`.

| family | obligations | covers (from SourceData182.lean) | D1-data status |
|---|---:|---|---|
| Cap (denominator l/u, J0, Jplus, tail) | 5 | — | **D1-independent** |
| Outer root **and** face | **120** | 60 covers: **28 rankTwo + 30 low + 2 high** | **D1-independent** |
| Inner mass | **137** | 137 covers: **68 rankTwo + 5 high + 64 low** | **D1-data consumers** |
| **total** | **262** | **96 rankTwo + 94 low + 7 high = 197 covers** | |

Each outer cover carries both a `rootUpper` and a `faceUpper`, so 60 outer covers
= 120 outer obligations (28 rankTwo covers → 56, 30 low → 60, 2 high → 4); this
reproduces `pg182-d1/OBLIGATION_MAP.md`'s outer rows (56 rank/high roots+faces,
60 outer low roots+faces) exactly. Each inner cover carries one `faceUpper`, so
137 inner covers = 137 obligations.

Reconciliation of the "94 `.low` rows": **94 covers = 64 inner low + 30 outer
low.** The 30 outer low covers sit in the outer root/face family, which consumes
no per-cell law mass (B1/B3 + D3 chain only), so they are not an envelope-class
problem at all. The 197-cover split `96/94/7` reproduces
`pg182-r2/ARCHITECTURE.md:22`; the 137-inner split `68/5/64` reproduces D1c's map
(73 rank/high + 64 low).

## 2. Per-class verdicts after D2 and D2b

Two layers, and only two, are needed by all 137 inner rows:

* **Layer M (cell masses).** `HasLocalBound mu D` with `D ≤ 1/zeta` (fine,
  R1 exact-convolution: the density is `e^{-γ}/zeta` on the whole period) and
  `D = 0.29586259` (sum, R4 Fejér with the exact `|φ|^38`). Both inside `hq`.
* **Layer I (integrand suprema).** The frozen affine-prefix / retained-maximum
  data (audit item 3, D3). Unchanged by this lane.

| class | n | layer M | layer I | status |
|---|---:|---|---|---|
| inner rankTwo | 68 | **closed** (`cell_measure_le_hq`; the `HasLocalBound` d=38 hypothesis is now the *proved* `hasLocalBound_of_charFun_bound` plus two computations) | D3 data | envelope layer closed |
| inner high | 5 | **closed** | D3 data | envelope layer closed |
| **inner low** | **64** | **closed — tilt cancels** (`tilted_cell_le`, `tilt_cancels`, `untilted_cell_le_hq`) | D3 data | **envelope layer closed; no exp-sandwich owed** |
| outer low | 30 | not consumed | not consumed | D1-independent |
| outer rankTwo / high | 28 / 2 | not consumed | not consumed | D1-independent |

The low-row closure in one line: the `.low` kernel is an untilted fragment mass
times `exp(slope · (affine in the mass))` (`SourceKernels182.lean:41-45`); the
exponential is monotone so its cell supremum sits at the right edge — exactly what
the frozen generator stores as `exponent_upper`. Both sides of `frozen ≥ env`
carry the same factor, it cancels, and what is left is `A ≤ 1/zeta`. Uniform in
`slope`, no MGF product.

## 3. Window placement (why R1 applies to all of them)

`num/window_scan.py`, from `SourceData182.lean`'s `pieces` (the source-cover
window on `r = Σ i, trialCellIndex (X i)`), in mass units `r·hq`:

| family | n | window tops | max | vs `zeta = 1.050956` |
|---|---:|---|---:|---|
| inner low | 64 | 0.89337 … | **0.993372** | 0.9452·zeta, headroom 1.058× |
| inner rankTwo + high | 73 | 0.89337 … | 0.993372 | same |
| outer (all kinds) | 60 | 0.0195 … | 1.0508 | ≤ zeta |

Every window of every one of the 137 inner rows lies strictly inside the single
period `(0, zeta)` where the density is exactly constant — so no inner row touches
the dyadic tail, and R1's per-cell statement applies to every cell of every row.
Pinned in Lean as `inner_window_inside_period`.

## 4. The named inputs: analytic count now ZERO (Lane D3)

**Closed (D3).** `Pg182D2/HasLocalBound.lean` proves the Fejér/Esseen smoothing lemma:
for a finite measure `ν` and any `B` bounding every truncation `∫_0^R ‖charFun ν‖`,

```lean
hasLocalBound_of_charFun_bound : (∀ R, ∫ t in (0)..R, ‖charFun ν t‖ ≤ B) →
    HasLocalBound ν (Real.pi / 4 * B)
hasLocalBound_one_div_zeta :     B ≤ 4/(π*zeta) → HasLocalBound ν (1/zeta)
cell_measure_le_hq_of_charFun :  the payload, per-cell mass ≤ hq
```

So the item D2 named ("Mathlib has no smoothing lemma") no longer exists, and
`D2-LEDGER`'s `D ≤ 1/zeta` obligation becomes a theorem for any law with an
integrable characteristic function — the `d = 38` case, not the `d = 1` case,
where the hypothesis provably fails (`∫‖φ_1‖ = ∞`, the measured 5.724 hq).

**The two computational inputs, after D4 (`Pg182D2/CharFunMod.lean`, `Pg182D2/IntegralBound.lean`).**
Neither is analytic; both are now stated in Lean, and everything between them and `hq` is proved:

| input | status | Lean |
|---|---|---|
| **the modulus identity** `‖φ_ζ(t)‖ = exp(-Cin (t ζ))` | **PROVED** (D4) | `re_charExponent`, `norm_exp_neg_charExponent`, `norm_charFun_exp_exponent`, `integral_norm_charFun_pow` |
| **the truncation chain** | **PROVED** (D4) | `integral_norm_charFun_pow_le`, `hasLocalBound_convPow_of_certified`, `cell_measure_le_hq_of_certified_integral` |
| **the margin** `0.39446770 ≤ 4/π` | **PROVED** (D4, `norm_num`) | `certifiedIntegralBound_le_four_div_pi` (3.23×) |
| (N1) the Poisson bridge `charFun (fragment mass law) t = exp(-charExponent t ζ)` | **prefix PROVED + one named residual** (`Pg182D2/CharFunBridge.lean`): the Bochner mixture `integral_finitePoissonLaw_normalized`, the analytic core `poisson_integral_pow`, the mass split `exp_mass_weightedEmpirical`, the interface `charFun_mass_map`.  Residual = the **band assembly** over `k : ℤ`, named as the Lean prop `N1Residual` / `N1ResidualBand` |
| **the structural `Cin` bounds** (monotone, `Cin π ≥ 1`, `Cin ≥ x²/π²` on `[0,π]`, `Cin (2x) ≥ Cin x + 1/4`, `Cin (4·2^k) ≥ 1 + k/4`) | **PROVED** (D4) | `Pg182D2/CinBounds.lean`, 14 theorems |
| (N2) `∀ R, ∫_0^R e^{-38 Cin} ≤ B` with `B ≤ 4/π` | **PROVED (lane N1N2)** — `∫_0^R e^{-38 Cin} ≤ 38/39 < 4/π` for every `R` | `Pg182D2/HeadTail.lean`: head (Jordan + `integral_gaussian_Ioi`) + mid (`Cin π ≥ 1`) + dyadic tail (`Cin_dyadic` + geometric block sum), `integral_cinDecay_le_four_div_pi` |

So the ledger at `d = 38` reads: `(N1) ⇒ HasLocalBound (μ^{*38}) (1/ζ) ⇒ cell mass ≤ hq`,
with `hq` reached by proved theorems only — and (N2) is no longer on the left-hand side:

```lean
hasLocalBound_convPow_of_charFun  : (∀ t, charFun μ t = exp (-(charExponent t ζ))) →
    HasLocalBound (convPow μ 38) (1 / zeta)                  -- Pg182D2/HeadTail.lean
cell_measure_le_hq_of_charFun'    : ... → cell mass ≤ hq      -- likewise
```

**The FINAL named-input list of the 182 data side (after N1N2).**

| # | input | status |
|---|---|---|
| 1 | **(N1)** the fragment-law charFun identity | prefix proved (`CharFunBridge.lean`); residual = the band assembly over `k : ℤ` |
| — | ~~(N2) the certified integral~~ | **CLOSED** — `Pg182D2/HeadTail.lean`, `38/39 < 4/π` |

The residual's exact blocker is a Mathlib gap, stated in `CharFunBridge.lean` and
`N1N2_REPORT.md` §2: *no Bochner analogue of "the integral of a product family over
`Measure.infinitePi` is the product of the integrals"* (finite index:
`integral_fintype_prod_eq_prod`; nonnegative `∫⁻` index: `lintegral_fragment_sum`).  Three
remaining steps, each named, none needing new mathematics: single band (from the proved
mixture + `poisson_integral_pow`), band product (the gap, plus `HasSum.exp`), and the join
`Σ_k ∫_{band k} = ∫_0^ζ` (available: `integral_iUnion_ae` + `integrable_charExponent_integrand`).

**Campaign-level deep inputs** (not on the data side, not Lean-reachable today):

* **Katz** — `|Kl₃(c)| ≤ 3`, raw rank-four `≤ 4p√p` (Katz Thm 4.1.1; Deligne purity).
* **FKM** — two-Kloosterman correlation `≤ 8p√p` (Fouvry–Kowalski–Michel Prop 2).
* **Type III** — `TypeIII.LocalFourierHypothesis` (no closed proof anywhere).
* **Deduction** — the tuple/admissibility bound-from-tuple step (in `formal/`, romyar1).

So the campaign's final statement is **"182 certified given N1's band assembly + Katz + FKM +
Type III"** — the analytic-support half is empty: no smoothing lemma, no integral estimate,
no modulus computation, no `Cin` bound left as an assumption.
The `d = 1` level remains out of scope as a smoothing input: `∫_0^∞ ‖φ_1‖ = ∞` there
(`e^{-Cin} → e^{-γ}/(t ζ)`), the measured 5.724 hq, and R1's exact-convolution density
constancy is what covers it.

## 5. Axcheck

`receipt/axcheck_headtail.txt` (**N1N2**, 15 theorems — the whole `∫_0^R e^{-38 Cin} ≤ 4/π`
assembly including `integral_exp_neg_Cin_le_four_div_pi`, `hasLocalBound_convPow_of_charFun`,
`cell_measure_le_hq_of_charFun'`) and `receipt/axcheck_charfunbridge.txt` (**N1N2**, 7
theorems — `integral_finitePoissonLaw_normalized`, `poisson_integral_pow`,
`exp_mass_weightedEmpirical`, `charFun_mass_map`, …): `[propext, Classical.choice,
Quot.sound]` only.

`receipt/axcheck_charfunmod.txt` (D4, 9 theorems) and `receipt/axcheck_integralbound.txt`
(D4, 6 theorems): `[propext, Classical.choice, Quot.sound]` only.

`receipt/axcheck_haslocalbound.txt` (D3) — all 20 theorems of `Pg182D2/HasLocalBound.lean`
including `hasLocalBound_of_charFun_bound`, `hasLocalBound_one_div_zeta`,
`cell_measure_le_hq_of_charFun`: `[propext, Classical.choice, Quot.sound]` only.

`receipt/axcheck_lowrows.txt` — `tilted_cell_le`, `tilt_cancels`,
`untilted_cell_le_hq`, `window_measure_le_cells`, `inner_window_inside_period`,
`cellCount_mul_mesh`, `inner_window_top_lt_cellCount_mul_mesh`, plus D2's
`fine_env_lt_hq`, `cell_measure_le_hq`: all on
**[propext, Classical.choice, Quot.sound]** only. No `sorryAx`, no
`native_decide`, no new axioms.
