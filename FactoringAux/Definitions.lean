module

public import Mathlib.Computability.TuringMachine.Computable
public import Mathlib.Data.Nat.Prime.Defs

/-!
# The definitions of the statement, for the proof

A verbatim copy of the definitions of `Challenge.lean` (`factor`, `FactoringMachine`,
`FactoringMachine.FiniteAlphabets`, `FactorsWithin`, `FactoringInTime`), on which the proof files
build.  `Challenge.lean` cannot be imported by the proof, since it also states the theorem.
Comparator checks that the declarations reached from `Solution.lean` agree with those of
`Challenge.lean`: same names, same types, same values.

Not an audit surface: the audited copy is `Challenge.lean`.
-/

@[expose] public section

namespace Factoring

open Turing Computability

/-! ### The problem -/

/-- Factoring: the smallest prime factor of `N` (Mathlib's `Nat.minFac`; it is `1` for `N = 1`).
Applied repeatedly, it gives the whole factorization. -/
def factor : ℕ → ℕ := Nat.minFac

/-! ### Machines and time -/

/-- A Mathlib machine that computes `factor`, with numbers written in binary on input and output,
together with its running time as a function of the input length. -/
abbrev FactoringMachine := TM2ComputableInTime encodeNat encodeNat factor

/-- Every stack alphabet of the machine is finite, as for a textbook machine. -/
def FactoringMachine.FiniteAlphabets (M : FactoringMachine) : Prop :=
  ∀ k, Finite (M.tm.Γ k)

/-- Machine `M` factors every `N` within `T n` steps, where `n` is the number of bits of `N`. -/
def FactorsWithin (M : FactoringMachine) (T : ℕ → ℕ) : Prop :=
  M.FiniteAlphabets ∧ ∀ n, M.time n ≤ T n

/-- Some machine factors every `N` within `T n` steps. -/
def FactoringInTime (T : ℕ → ℕ) : Prop :=
  ∃ M : FactoringMachine, FactorsWithin M T

end Factoring
