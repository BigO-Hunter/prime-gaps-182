# FINALSET_REPORT — the 182 data side: what is now computation, and what is not

Lane D4, repo dir `d2/`.  Deliverables: `Pg182D2/CharFunMod.lean`
(item i), `Pg182D2/IntegralBound.lean` (item ii), axchecks in `receipt/`.

## 0. Verdict, per item

| item | verdict |
|---|---|
| **(i) the modulus identity** `‖φ_ζ(t)‖ = exp (-Cin (t ζ))` | **PROVED** — the whole modulus computation: `re_charExponent`, `norm_exp_neg_charExponent`, `norm_charFun_exp_exponent` |
| (i) the *Poisson bridge* `charFun (mass law) t = exp (-Ein (-I t ζ))` | **named** (N1), stated exactly as the hypothesis of `hasLocalBound_convPow_of_certified` |
| **(ii) the certified integral → layer M** | **PROVED** — `hasLocalBound_convPow_of_certified_integral`, `cell_measure_le_hq_of_certified_integral`, plus the margin `certifiedIntegralBound_le_four_div_pi` |
| **(ii) the structural `Cin` bounds** (monotonicity, `Cin π ≥ 1`, `Cin ≥ x²/π²` on `[0,π]`, the dyadic doubling gain) | **PROVED** — `Pg182D2/CinBounds.lean`, 14 theorems |
| (ii) the integral bound itself `∫_0^∞ e^{-38 Cin} ≤ 0.39446770` | **named** (N2), in the hypothesis form `∀ R, ∫_0^R e^{-38 Cin} ≤ B`; its *structural half* is now proved (§5a) and only the tail/head assembly remains (§5b) |

**Named-input count: 2** (was 2).  What changed is that both are now *stated in Lean*, the
data side is a single theorem away from closed, and everything between them and `hq` is proved.

## 1. Item (i) — the identity is the modulus computation

The band is a Poisson process of intensity `du/u` on `(0, ζ]`, so its charFun is the
Skorokhod exponent `φ_ζ(t) = exp (-Ein (-I t ζ))`.  Two facts make the modulus trivial once
they are in Lean, and both are now theorems:

```lean
def Cin (x : ℝ) : ℝ := ∫ u in (0)..x, (1 - Real.cos u) / u
def charExponent (t ζ : ℝ) : ℂ := ∫ u in (0)..ζ, (1 - Complex.exp (I * (t * u))) / u

re_charExponent           : (charExponent t ζ).re = Cin (t * ζ)          -- all t, no sign case
norm_exp_neg_charExponent : ‖exp (-charExponent t ζ)‖ = exp (-Cin (t * ζ))
```

The route deliberately avoids the Ein/Cin *series* (whose even/odd split is the fiddly part
and needs termwise integration of the cosine series):

1. `‖exp z‖ = exp z.re` (`Complex.norm_exp`) — so the modulus is `exp (-Re Φ)`.
2. `Re` commutes with the ℂ interval integral (`Complex.reCLM` + `ContinuousLinearMap.
   integral_comp_comm`).  This needs the integrand to be **absolutely** integrable, which it
   is: `‖1 - e^{I θ}‖ ≤ ‖θ‖ e^{‖θ‖}` gives `‖(1 - e^{Itu})/u‖ ≤ |t| e^{|t| ζ}` on the band
   (`integrable_charExponent_integrand`).  This is the real content of the landmine "the
   complex-modulus arithmetic may need explicit re/im lemmas" — it needs no new lemmas, only
   the integrability bound.
3. `Re (1 - e^{I θ}) = 1 - cos θ` pointwise (`cinExponent_integrand_re`; `Complex.exp_re`
   gives it directly, `exp_ofReal_mul_I` is not needed).
4. The substitution `x = t u` (`integral_comp_mul_left`) converts `∫_0^ζ (1-cos(tu))/u` into
   `Cin (t ζ)` — an identity for **every** `t` (the `t = 0` case is a separate line).

Nothing is assumed about `t ≥ 0`, which is why the power/truncation lemmas
(`integral_norm_charFun_pow`, `integral_norm_charFun_pow_le`) need no interval-sign case:
only `R ≤ 0` is split off (trivially, the integrand being nonnegative).

## 2. Item (ii) — the transcription is now a composition, and the margin is certified

```lean
def certifiedIntegralBound : ℝ := 39446770 / 10 ^ 8
certifiedIntegralBound_le_four_div_pi : certifiedIntegralBound ≤ 4 / Real.pi   -- 3.23x margin
hasLocalBound_convPow_of_integral_le :
    (∀ t, charFun μ t = exp (-charExponent t zeta)) →
    (∀ R, ∫ x in (0)..R, exp (-(38 * Cin x)) ≤ B) → B ≤ 4 / Real.pi →
    HasLocalBound (convPow μ 38) (1 / zeta)
```

so the D2 ledger's layer M at `d = 38` is one hypothesis-pair away from closed.  Note the
generic-constant form: **the receipt's `0.39446770` is not needed as such**.  The margin is
`4/π = 1.27324`, so any bound below it discharges the same line — which is what makes §5's
elementary chain sufficient, and is why the failure of the exact-value transcription would
not have blocked the campaign.

## 3. What is NOT done, exactly

**(N1) the Poisson bridge.**  Needed:

```lean
charFun ((fragmentLaw ζ).map (fun X => (X.mass : ℝ))) t = Complex.exp (-(charExponent t ζ))
```

This is the ℂ-valued counterpart of the vendored real lemma
`lintegral_exp_neg_finitePoissonLaw` (`Pg182D1/Support.lean:220`).  The real proof runs
through `EReal`-valued `lintegral`s and its step `∏ i, g (x i)` has no ℂ analogue in that
machinery, so the ℂ version must be redone with **Bochner** integrals.  Its pieces
(the genuinely absent ones are marked ×):

* `∫ c, (∫ u, e^{I t u} ∂c) ∂(finitePoissonLaw μ) = exp (∫ u, (e^{I t u} - 1) ∂μ)` — needs
  the Poisson series with ℂ terms (`‖ψ‖ ≤ 1` gives absolute convergence; `integral_tsum`);
  × no single Mathlib lemma packages "charFun of a finite Poisson model", but every step
  (`lintegral_finitePoissonLaw_normalized`'s Bochner twin) is standard.
* `exp (Σ'_k c_k) = ∏'_k exp (c_k)` for `Σ ‖c_k‖ < ∞` over `k : ℤ` — `HasSum.exp` exists;
  summability comes from `Σ_k ∫_{band k} ‖e^{Itu}-1‖/u ≤ ∫_0^ζ min(2, |t|u)/u du`.
* the join `Σ_k ∫_{band k} = ∫_0^ζ` — already proved in the real case
  (`lintegral_fragment_sum`, `sum_cappedDyadicIntensity`); the ℂ version is a `tsum` of
  Bochner integrals over the dyadic partition.
* the identification of `∫_0^ζ (1 - e^{Itu})/u` with `Ein (-I t ζ)` — **not needed**:
  `charExponent` is *defined* as that integral, so this step is definitional.

Estimated size: 300–450 lines, mechanical, no new mathematics.

**(N2) the integral bound.**  Two honest routes.

*Transcription of the receipt.*  The receipt's arithmetic is exact rationals, but its
`[0,1] ∪ [1,20]` Darboux grids have `24 000` cells — transcribing them means either 24 000
generated `norm_num` interval lemmas (the `percell_emit.py` pattern) or a Lean-side
interval-integral monotonicity lemma instantiated per cell.  Multi-hundred lines of
generated data; no risk, no insight.

*Elementary bound (§5).*  Cheaper, and sufficient because of the margin.

## 4. Sharpness note (unchanged from D3)

`‖φ_1‖ = e^{-Cin} → e^{-γ}/(t ζ)` so `∫_0^∞ ‖φ_1‖ = ∞`: the `d = 1` level is *not* a
smoothing input at all.  The `d = 38` level is, by four orders of magnitude.  That asymmetry
is a theorem in `Pg182D2/HasLocalBound.lean` §4, not a defect of this lane.

## 5a. The structural half — PROVED (`Pg182D2/CinBounds.lean`)

```lean
Cin_mono        : 0 ≤ a → a ≤ b → Cin a ≤ Cin b
Cin_ge_sq       : 0 ≤ x → x ≤ π → x^2/π^2 ≤ Cin x        -- Jordan, 1 - cos u ≥ 2u²/π²
Cin_pi_ge_one   : 1 ≤ Cin π                              -- weight 1/u ≥ 1/π on (0,π], ∫(1-cos) = π
Cin_ge_one      : π ≤ x → 1 ≤ Cin x
Cin_double      : 4 ≤ x → Cin x + 1/4 ≤ Cin (2*x)        -- weight ≥ 1/(2x), |sin| ≤ 1
Cin_dyadic      : 1 + k/4 ≤ Cin (4 * 2^k)                -- induction from Cin 4 ≥ Cin π ≥ 1
```
plus the integrability of the `Cin` integrand (`integrableOn_cinIntegrand`,
`intervalIntegrable_cinIntegrand`, bounded by `|u|/2` via `one_sub_cos_le_half_sq`).
All 14 on `[propext, Classical.choice, Quot.sound]` (axcheck: `receipt/axcheck_cinbounds.txt`).

## 5b. What remains for (N2): the head/tail assembly

Numerics: head `∫_0^π e^{-38Cin} ≤ ∫_0^∞ e^{-38x²/π²} = (1/2)√(π³/38) = 0.4516`
(`integral_gaussian_Ioi`, `b = 38/π²`); `∫_π^4 ≤ (4-π) e^{-38} ≈ 3e-17`; tail
`∫_4^∞ ≤ Σ_k 4·2^k e^{-38(1+k/4)} = 4e^{-38}Σ_k (2e^{-9.5})^k ≤ 8e^{-38} ≈ 2.5e-16`.
Total `≈ 0.4517 ≤ 1`.  The only non-elementary step is packaging the dyadic sum (a
`tsum`-over-`iUnion`-of-blocks, or the pointwise power majorant
`e^{-38Cin x} ≤ e^{-38}(x/8)^{-13}` plus `integral_Ioi_rpow_of_lt`).

## 6. Reproduction

    LAKE_JOBS=1 LEAN_NUM_THREADS=1 lake build Pg182D2.IntegralBound        # 8927 jobs, 11 s
    LAKE_JOBS=1 LEAN_NUM_THREADS=1 lake env lean receipt/axcheck_charfunmod.lean
    LAKE_JOBS=1 LEAN_NUM_THREADS=1 lake env lean receipt/axcheck_integralbound.lean

## 7. Axcheck

`receipt/axcheck_charfunmod.txt` (9 theorems) and `receipt/axcheck_integralbound.txt`
(6 theorems): **`[propext, Classical.choice, Quot.sound]` only.**  No `sorryAx`, no
`native_decide`, no new axioms, in either file.

## 8. Numeric verification (the two named inputs are about the SAME objects)

Checked in `python3` against `quad` and the receipt's series (2026-11-07):

| quantity | value | check |
|---|---|---|
| `Cin 1` by my integral definition | `0.2398117420` | = the series `Σ (-1)^{m+1} x^{2m}/((2m)(2m)!)` to `1e-10` |
| `Cin π`, `Cin 4`, `Cin 20` | `1.6482776387`, `2.1044917239`, `3.5285281176` | integral = series at each |
| `∫_0^∞ e^{-38 Cin}` (true) | `0.2884887…` | `< 0.39446770` (the receipt's certified upper bound) |
| the margin `4/π ÷ 0.39446770` | `3.2277×` | matches `certifiedIntegralBound_le_four_div_pi` |
| the §5 crude chain | `0.4517 + 3e-17 + 2.5e-16` | `< 1 < 4/π` |

The first row matters: the `Cin` of `CharFunMod.lean` (interval integral) and the `Cin` the
receipt bounds (alternating series) are the same function, so (N2) is a statement about the
object that appears in the modulus identity, not merely a lookalike.
