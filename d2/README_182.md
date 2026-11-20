# The 182 package — a Lean proof that a famous gap bound reduces to six named inputs

**One line.** If six specific mathematical statements are true — three deep estimates about
Kloosterman sums, one Type III Fourier estimate, one deduction theorem formalized elsewhere, and
262 source inequalities from the frozen trial data — then **infinitely often, two consecutive
primes differ by at most 182**. Everything between those six inputs and that conclusion is proved
here, in Lean 4 + Mathlib, kernel-checked, on the standard axioms `[propext, Classical.choice,
Quot.sound]` — no `sorry`, no new axioms, no `native_decide`.

This file is the front door. The details:

| file | what it is |
|---|---|
| `COMPOSITION_STATEMENT.md` | the composition theorem, every hypothesis typed and documented — **read this first** |
| `OBLIGATION_MAP.md` | every obligation of the program, its status (proved / named / instantiate-pending), and the exact Lean declaration that carries it |
| `COMPOSITION.lean` | the composition theorem itself, in Lean |
| `Pg182D2/` | the proved data side (13 modules) |
| `receipt/` | machine-checkable receipts: axiom checks of every theorem, table-fidelity checks |
| `PACKAGE_SHA256SUMS.txt` | sha256 of this package and of every file in it |

---

## 1. What the 182 bound is

The target is the race statement `BigOSpeedrun.PrimeGaps.Bound 182` (verbatim from the
bigospeedrun/verifier statement file):

```lean
def Bound (B : ℕ) : Prop :=
  ∃ᶠ m in Filter.atTop, Nat.nth Nat.Prime (m + 1) - Nat.nth Nat.Prime m ≤ B
```

That is: infinitely often, a prime and the next prime differ by at most 182. Bounded gaps between
primes are known unconditionally since Zhang/Maynard (246, polyscopic improvement to some hundreds);
182 is a *structured* bound — it comes from the trial-based machinery of the romyar1 endpoint
development, whose numerical machinery certifies this particular constant. What this package adds
is the **formal reduction**: a machine-checked theorem that turns six named inputs into that
statement, with the entire analytic data side (the part that used to be the informal half) proved
outright.

## 2. What is PROVED here

Two things, both kernel-checked (axiom receipts in `receipt/`):

**(a) The composition theorem** `PrimeGap182D2.h1_182_of` (`COMPOSITION.lean`):

> the six named inputs ⇒ `Bound 182`.

Formally, from `Kloosterman3Bound`, `Kloosterman2CorrelationBound`, `IncidenceRankFourBounds182`,
`TypeIIILocalFourier`, `Deduction182`, a source record `S` with its 262 inequalities, the theorem
produces `BigOSpeedrun.PrimeGaps.Bound 182`. No hypothesis is hidden: the full typed list is in
`COMPOSITION_STATEMENT.md`.

**(b) The data side** — the analytic half of those 262 inequalities, which is the new mathematics
of this package. For the 137 "inner mass" inequalities, the bound has two layers. The *cell-mass
layer* is fully proved, unconditionally:

```lean
theorem cell_measure_le_hq_final (n : ℕ) :
    convPow fragmentMassLaw 38 (cell n) ≤ ENNReal.ofReal hq
```

— every cell of the 38-fold additive convolution of the "fragment mass law" has measure at most
`hq`. The proof chain, every step a theorem in `Pg182D2/`:

1. the characteristic function of the fragment mass law is `exp(−charExponent t ζ)` — a theorem
   (`BandAssembly.charFun_mass_fragmentLaw`), proved via an infinite-Poisson product decomposition
   and a countable-product integral lemma (`InfinitePiProduct`, upstream as Mathlib PR #45771);
2. its modulus is `exp(−Cin(tζ))`, where `Cin` is the cosine integral (`CharFunMod`);
3. `∫₀ᴿ e^(−38·Cin) ≤ 38/39 < 4/π` for every `R` (`HeadTail`), using only structural bounds on
   `Cin` (`CinBounds`, 14 theorems);
4. the Fejér/Esseen smoothing lemma turns that truncation bound into a local mass bound
   `1/ζ` (`HasLocalBound.hasLocalBound_of_charFun_bound`);
5. the local bound gives the per-cell bound (`EnvLemmas`, `LowRows` — including the tilt
   cancellation that handles the 64 "low" rows uniformly in the tilt slope).

The **certificate table** — 197 certificate rows + 5 caps + shared constants, 546 rational
literals — is transcribed into Lean as `Pg182D2/TableData.lean`, with kernel proofs that the
transcription equals the frozen upstream module (12 `decide +kernel` equalities,
`receipt/transcription_fidelity.txt`). The table is no longer a hypothesis; it is data. On the 73
`rankTwo`/`high` inner rows the certificate margin is additionally a proved `norm_num` fact, and
the composition `h1_182_of_certEnvelope` absorbs the margin on all 137 rows by choosing the
certificate-implied envelope.

**Aggregate axiom receipt:** 15 receipt files, 162 `#print axioms` declarations, every one
`[propext, Classical.choice, Quot.sound]`; zero `sorryAx`, zero `native_decide`. Fresh re-run of
the composition check: `receipt/axcheck_composition_rerun.txt`.

## 3. What is NAMED (the six inputs)

Nothing outside Lean is smuggled in: each input is an explicit typed hypothesis. Exact statements
in `COMPOSITION_STATEMENT.md` §2.

| # | hypothesis (Lean name) | content | status |
|---|---|---|---|
| 1 | `Pg182Frame.Kloosterman3Bound` | ‖Kl₃(c)‖ ≤ 3 over F_p, c ≠ 0 — Katz, *Gauss Sums…*, Thm 4.1.1 | **instantiate-pending** (see §4) |
| 2 | `Pg182Frame.Kloosterman2CorrelationBound` | two-Kloosterman correlation ≤ 8p√p — Fouvry–Kowalski–Michel, Prop 2 | **instantiate-pending** (cohomological core; the sharp constant's p-adic refinement is separate work) |
| 3 | `Pg182Frame.IncidenceRankFourBounds182` | raw rank-4 Kloosterman ≤ 4p√p — the rank-four companion (Katz/Deligne purity) | **instantiate-pending** (same machinery as #1) |
| 4 | `Pg182Frame.TypeIIILocalFourier` | the Type III local Fourier proposition, verbatim from the romyar1 development | **named** — no closed proof exists anywhere, in or out of Lean |
| 5 | `Pg182Frame.Deduction182` | "local inputs + the 262 bounds ⇒ infinitely many consecutive prime pairs ≤ 182" | **named, kernel-checked elsewhere** — a theorem of romyar1/prime-gaps-lean @ b77bf175bded (918 modules, 6,128 declarations, standard axioms), carried here as a hypothesis and mirrored 1:1 by the frame |
| 6 | `hcap`, `hroot`, `hface`, `hrow` | the 262 **source** inequalities: source integral ≤ certified rational (5 caps + 120 outer + 137 inner) | **named** — frozen physical data, the "source direction" of the table; certified offline by the romyar1 kernel. The *reverse* direction (certificate ⇒ usable bound) is what this package proves |

## 4. What the Weil instantiation would change

The deep inputs #1–#3 are exactly the statements that 20th-century arithmetic geometry (Weil I/II,
Deligne purity, the Laumon Fourier transform) exists to prove. A parallel lane audited the Lean
formalization of that machinery (AxiomMath/Weil + official Stacks) and found:

- the estimate engine is present and the **last mile is already a proved, axiom-clean theorem**
  (`KloostermanTraceBound.kloosterman_bound`: rank ≤ 3 + weight-2 purity ⇒ ‖Kl₃‖ ≤ 3, and its `3p`
  raw form) — what remains for #1 is *construction against an existing API* (three packaging
  obligations, priced in weeks, not years);
- the heavyweight `#print axioms` gate on `LAdicSheaf.weightBound` and
  `Weil.satisfiesWeilEstimate` is **PENDING**: those modules need 19.4k Stacks modules built
  (≈ 6.8 days of machine time — the gate is running). Source-level scan across 63k Stacks + 980
  Weil files: zero `sorry`, zero `axiom`, zero `native_decide`.

**If the gate passes**, inputs #1–#3 stop being "named after Katz/FKM" and become "instantiate
from the Weil/Stacks libraries", and the campaign statement tightens from *"182 certified given
Katz + FKM + rank-four + Type III + …"* to *"182 certified given Type III + Kl₃ packaging"*. Type
III (#4) is untouched by all of this — it is the remaining genuinely open analytic input. Two
honest caveats from the audit: axiom-clean ≠ statement-faithful (a human must still read the
sheaf-theoretic definitions before betting the constants), and the packaging is construction, not
a completed proof. Details: `OBLIGATION_MAP.md` §5.

## 5. Honest limits

- The 137 inner inequalities are **not** each individually proved. What is proved is the analytic
  (cell-mass) half for every cell; the remaining half (`hrow`, the affine-prefix integrand
  envelope and the row-to-cell identification) is frozen source data whose content lives in the
  romyar1 kernel. This split is explicit in the theorem: `hrow` is a hypothesis.
- For the 64 "low" rows no numeric envelope is recorded in the table (measured: the stored
  `witnessUpper` overshoots by 4.6e7×–1.8e26×), so their Layer-I content necessarily lives in
  `hrow`. `TABLE_TRANSCRIPTION_REPORT.md` has the measurements.
- The certificate table's fidelity is relative to the vendored upstream modules identified by the
  sha256 digests in `receipt/transcription_fidelity.txt`.
- `Deduction182` is a hypothesis mirroring a kernel-checked theorem **in another repository**; this
  package does not re-prove it, it transports it.

## 6. Checking it yourself

```bash
lake build Pg182D2                      # the data side + the table
lake env lean receipt/axcheck_composition.lean    # the axiom receipt of the composition
```

`lakefile.toml` pins Mathlib (prebuilt), `pg182-frame` and `pg182-d1` by path; `lean-toolchain`
pins the toolchain. Expect the composition axcheck in ~30 s on a warm build. **Path-dep caveat:**
the three dependencies are pinned to sibling directories of this checkout, so a bare tarball does
not build standalone — a recipient needs the pinned `pg182-frame`/`pg182-d1` (one commit each,
both self-contained) and a Mathlib checkout at the pinned revision, or should read the sources and
receipts (which are self-contained). Nothing in this package requires network access, and nothing
here is published anywhere else — this directory is the deliverable.

*Status: data side CLOSED (zero mechanical residue, zero named analytic inputs on the data side);
composition theorem axiom-clean; six named inputs exact; Weil gate pending.*
