module

public import Mathlib.Computability.TuringMachine.Computable
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Nat.Log

/-!
# Deterministic factoring in time `N ^ o(1)`: the statement

This file is the statement for audit.  It imports Mathlib only.

* **Factoring** is `Nat.minFac`: the smallest prime factor of `N` (it is `1` for `N = 1`).
* **Machines, encodings and time** are Mathlib's: a `Turing.TM2ComputableInTime` machine (a Turing
  machine in Mathlib's `TM2` model, `Turing.FinTM2`, with a time bound), with numbers written in binary by
  `Computability.encodeNat` on input and output.  `n` is the length of the input, which is the
  number of bits of `N`, so `2 ^ n` is about `N`.  Mathlib asks only the input stack's alphabet to
  be finite; `FactoringMachine.FiniteAlphabets` asks it of every stack, as for a textbook machine.

**The result** (`Factoring.subexponentialRate`): one machine factors every `N` within
`C_k · 2 ^ (n / k)` steps, for every `k ≥ 1`, with `C_k` depending only on `k`.  That is time
about `N ^ (1/k)` for every `k`, i.e. time `N ^ o(1)`.

**The conjecture** (`Factoring.SqrtLogLogConjecture`) is stated as a proposition.  It is not
proved, and nothing here claims it is true.

The proof is in `Solution.lean`, which states the same declarations with the same names and types.
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

/-! ### The result -/

/-- **The result.** One machine factors in time `N ^ o(1)`: for every `k`, the same machine
factors within `C · 2 ^ (n / k)` steps, about `N ^ (1/k)`. -/
theorem subexponentialRate :
    ∃ M : FactoringMachine, ∀ k : ℕ, 1 ≤ k → ∃ C : ℕ,
      FactorsWithin M (fun n => C * 2 ^ (n / k)) := by
  sorry

/-! ### The conjecture -/

/-- **The conjecture (not proved).** A faster rate, conjectured by the AI when asked to
conjecture: one machine factors in time `exp(O(log N / √(log log N)))`.  In the bit length `n`
(`n ≈ log₂ N`, so `log log N ≈ log n`) this is `2 ^ O(n / √(log n))`, written here as
`C · 2 ^ (C · n / (⌊√⌊log₂ n⌋⌋ + 1))`: the `C` in the exponent is the constant of the `O(·)`, the
`C` in front covers small inputs, and the `+ 1` only avoids dividing by zero when `n ≤ 3`.
Stated as a proposition, not as a theorem: nothing here claims it is true. -/
def SqrtLogLogConjecture : Prop :=
  ∃ C : ℕ, FactoringInTime (fun n => C * 2 ^ (C * n / (Nat.sqrt (Nat.log 2 n) + 1)))

end Factoring
