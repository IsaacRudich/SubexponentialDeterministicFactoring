module

public import Factoring_aux
public import Mathlib.Data.Nat.Log

/-!
# Deterministic factoring in time `N ^ o(1)`: the proof

The declarations of `Challenge.lean`, with the same names and types, proved.

* `factor`, `FactoringMachine`, `FactoringMachine.FiniteAlphabets`, `FactorsWithin`,
  `FactoringInTime`: from `FactoringAux/Definitions.lean`, a verbatim copy of the Challenge's
  definitions, imported through `Factoring_aux`.
* `subexponentialRate`: proved by one line naming the lemma `Factoring.Aux.subexponentialRate`
  (`FactoringAux/UniMain.lean`).
* `SqrtLogLogConjecture`: the same proposition as in the Challenge, stated and not proved.
-/

@[expose] public section

namespace Factoring

/-- **The result.** One machine factors in time `N ^ o(1)`: for every `k`, the same machine
factors within `C · 2 ^ (n / k)` steps, about `N ^ (1/k)`. -/
theorem subexponentialRate :
    ∃ M : FactoringMachine, ∀ k : ℕ, 1 ≤ k → ∃ C : ℕ,
      FactorsWithin M (fun n => C * 2 ^ (n / k)) :=
  Aux.subexponentialRate

#print axioms subexponentialRate

/-- **The conjecture (not proved).** A faster rate, conjectured by the AI when asked to
conjecture: one machine factors in time `exp(O(log N / √(log log N)))`.  In the bit length `n`
(`n ≈ log₂ N`, so `log log N ≈ log n`) this is `2 ^ O(n / √(log n))`, written here as
`C · 2 ^ (C · n / (⌊√⌊log₂ n⌋⌋ + 1))`: the `C` in the exponent is the constant of the `O(·)`, the
`C` in front covers small inputs, and the `+ 1` only avoids dividing by zero when `n ≤ 3`.
Stated as a proposition, not as a theorem: nothing here claims it is true. -/
def SqrtLogLogConjecture : Prop :=
  ∃ C : ℕ, FactoringInTime (fun n => C * 2 ^ (C * n / (Nat.sqrt (Nat.log 2 n) + 1)))

end Factoring
