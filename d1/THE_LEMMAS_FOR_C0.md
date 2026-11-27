# THE_LEMMAS_FOR_C0.md — the exact D1 interface for the C0 lane

Lane C0's certificate (`pg182-c0/Pg182C0/RowCert.lean`) isolates one named
hypothesis:

```lean
hEnv77 : ∀ i : Fin 39,
  ∫ Y, trialMask 1 Y * trialSourceKernel cover77 Y * trialMarginal77 i Y ^ 2
    ∂(trialProductMeasure 38) ≤ (E77 : ℝ)
```

with the kernel-proved required strength `E77 = rowFaceUpper77 * NLB / 39`.

## What D1 delivers to C0 today (all kernel-proved, axcheck-clean)

From `d1/` (project `pg182-d1`, namespace
`PrimeGap182D1`, import `Pg182D1.D1Cell` + `Pg182D1.D1Mgf`):

1. **`cell_probability_le ζ n s hs`** — the per-cell majorant engine:
   for every cell `n`, every `s ≥ 0`,
   `(fragmentLaw ζ).real {X | trialCellIndex X = n} ≤
      exp(s·(n+1)·mesh) * ∫ exp(-s·mass) ∂(fragmentLaw ζ)`.
2. **`mgf_fragmentLaw_le_finset ζ s hs S`** — the structural exp-sandwich:
   `∫⁻ massExp s ∂(fragmentLaw ζ) ≤ ∏_{k∈S} ∫⁻ massExp s ∂(finitePoissonLaw
   (cappedDyadicIntensity ζ k))` for every finite band set `S ⊆ ℤ`.
3. `mass_finiteFragments`, `mass_lt`-style floor laws
   (`cell_mass_lt`, `mass_le_of_cellIndex`), `measurable_massExp`,
   `massExp_le_one` — the glue facts.

### The hEnv77 discharge shape this produces

C0 should instantiate the following 3-step chain (steps 1-2 are D1's; step 3
is C0's existing B1 machinery):

1. Per-coordinate: for the discrete-law envelope
   `env(n) := exp(s·(n+1)·mesh) · B(s)` with
   `B(s) := ∏_{k∈S} E_k` the proved MGF bound (any `s ≥ 0`, any `S`),
   `μ{cell = n} ≤ env(n)` — **proved** (D1Cell + D1Mgf composition).
2. The frozen per-run masses `p^frozen_c` must satisfy
   `p^frozen_c ≥ env(c)` — **D1-data**, one ℚ inequality per cell (the
   exp-sandwich check the receipts already carry in aggregate).
3. The per-run integrand suprema `σ(r)` (frozen affine-prefix data) must
   dominate the integrand per coarse run — **D3** (audit item 3).

Then `hEnv77` follows by B1 partition majorization
(`integral_le_of_pointwise_le` + `integral_run_table`, both already proved in
`pg182-c0/Pg182C0/Bridges.lean`).

### The one lemma still owed to C0 (next D1 session)

The composition of 1+2 into the 38-dim sum-level statement
(`sumCell Y = Σ_j trialCellIndex (Y j)`, coarse runs):

```
μ^{38}{sumCell = c} ≤ exp(s·(c+38)·mesh) · B(s)^38
```

Drafted at `wip/D1Sum.lean` (the mass_lt/floor arithmetic is done; the
remaining work is one measurable-finite-sum lemma and the pi-product MGF
identity `lintegral_massExp_pi`, both sketched in the file), plus the
partition engine `wip/D1Engine.lean` (drafted; mechanical errors remain:
`Measurable.indicator` naming, one `Integrable.mono'` side-condition, the
`single_le_sum` dominating-term shape). Neither is in the build yet.

## Axcheck footprint (receipt/axcheck.txt equivalent)

```
'PrimeGap182D1.cell_probability_le' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'PrimeGap182D1.mgf_fragmentLaw_le_finset' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'PrimeGap182D1.mass_finiteFragments' depends on axioms:
  [propext, Classical.choice, Quot.sound]
```

No `sorryAx`, no `native_decide`, no new axioms. The law definitions are
verbatim from romyar1/prime-gaps-lean @ b77bf175bded
(`vendor/primegaps186/PrimeGaps186.lean`), so C0 proofs transfer by import
once its Stage-0 build lands.
