/-
The engine's driver: a `Cmd` that, given a counting expression `e` (`BitSpec`), outputs `encodeNat (minFac N)`.

Scalars: `0` = n (input length), `1` loop counter, `2` = k (position), `3` the bit, `4` = 0, `5`, `6` temporaries;
`Ex` scratch from `10`.  Arrays: `0` input, `1` the answer bits `D`, `2` the output.

For `n ≥ 2` the driver runs the search of `Search.lean` from the top position: at position `k` it sets `D[k] := 0`,
evaluates `e` (`1` iff no divisor `≥ 2` of `N` has the high bits `D[k..n)`), and writes the result into `D[k]`.

* `BitSpec e`: what the engine must provide (value and a cost bound `B n`).

Not an audit surface.
-/
module

public import FactoringAux.Ex
public import FactoringAux.DriverMath
public import FactoringAux.Copied.PlibTop

@[expose] public section

namespace Factoring.Aux

open Factoring.Aux.Copied Factoring.Aux.Copied.PLib Finset Computability Factoring.Aux.Trial

/-- The counting expression's contract: variables below `10`, values `0`/`1`, value `1` exactly when no divisor
`d ≥ 2` of `N` (the input, `n = σ 0` cells of array `0` from cell `1`) has `d / 2^k = x`, where `k = σ 2` and
`x` is written by `D[k..n)` (array `1`), provided `D[k] = 0`; and cost at most `B n` when `D` holds bits. -/
structure BitSpec (e : Ex) (B : ℕ → ℕ) : Prop where
  vb : Ex.VB 10 e
  le_one : ∀ σ A, Ex.eval σ A e ≤ 1
  val : ∀ σ A, σ 2 < σ 0 → 2 ≤ numCells (A 0) 1 (σ 0) → A 1 (σ 2) = 0 →
    Ex.eval σ A e = if 0 < cntPre (numCells (A 0) 1 (σ 0)) (σ 2) (numCells (A 1) (σ 2) (σ 0 - σ 2)) then 0 else 1
  cost : ∀ σ A, σ 2 < σ 0 → (∀ j, A 1 j ≤ 1) → Ex.cost σ A e ≤ B (σ 0)

/-- `k = n - 1 - i`. -/
def kEx : Ex := .sub (.sub (.var 0) (.lit 1)) (.var 1)

/-- The output length: positions `j < n` with a one at or above `j`. -/
def lenEx : Ex :=
  .sum 8 (.var 0) (.lit 0) (.ifLt (.lit 0)
    (.sum 9 (.var 0) (.lit 0) (.ifLt (.var 9) (.var 8) (.lit 0) (.rd 1 (.var 9)))) (.lit 1) (.lit 0))

/-- The search body, turn `i`. -/
def body (e : Ex) : Cmd :=
  .seq (Ex.comp kEx 2 10) (.seq (.wr 1 2 0 4) (.seq (Ex.comp e 3 10) (.wr 1 2 0 3)))

/-- The driver. -/
def drv (e : Ex) : Cmd :=
  .seq (.setK 4 0) (.seq (.setK 5 2) (.ifLt 0 5
    (.ifZero 0 (.seq (.setK 6 2) (.seq (.wr 2 4 0 6) (.seq (.setK 6 1) (.wr 2 4 2 6))))
      (.seq (.setK 6 1) (.seq (.wr 2 4 0 6) (.wr 2 4 1 6))))
    (.seq (.loop 0 1 (body e)) (.seq (.loop 0 1 (.seq (.rd 5 1 1 0) (.wr 2 1 1 5)))
      (.seq (Ex.comp lenEx 6 10) (.wr 2 4 0 6))))))

end Factoring.Aux
