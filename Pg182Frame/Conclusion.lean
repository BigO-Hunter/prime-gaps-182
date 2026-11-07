import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# The race target, restated verbatim

`BigOSpeedrun.PrimeGaps.Bound` exactly as pinned in the maintainer's trusted
statement file: github.com/bigospeedrun/verifier,
`challenges/prime-gaps/Statement.lean` @ cb829226510350dc04c7b0c221943ed65daedfed.
Def-equal restatement (same namespace, same body) so the frame theorem targets
the race statement by name.
-/

namespace BigOSpeedrun.PrimeGaps

/-- Race target. Infinitely often, consecutive primes differ by at most `B`. A smaller natural
bound is better. Verbatim from challenges/prime-gaps/Statement.lean @ cb829226. -/
def Bound (B : ℕ) : Prop :=
  ∃ᶠ m in Filter.atTop, Nat.nth Nat.Prime (m + 1) - Nat.nth Nat.Prime m ≤ B

end BigOSpeedrun.PrimeGaps
