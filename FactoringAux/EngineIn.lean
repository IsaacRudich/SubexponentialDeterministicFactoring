/-
Reading the input of the counting expression bit by bit.

The input number `N` and the pattern `x` are far too large to be values of an expression (unary arithmetic: a value
`v` costs about `v` steps).  The engine reads them one bit at a time, and only through the `0/1` test `bitRd`
(`[A a i ≠ 0]`), so its value and cost do not depend on the size of the array cells.

* `bitRd a i`: `1` if cell `i` of array `a` is nonzero, else `0`; `eval_bitRd`.
* `nBit i`: bit `i` of `N = numCells (A 0) 1 n` (`n = var 0`), `0` for `i ≥ n`; `eval_nBit`.
* `xBit j`: bit `j` of `x = numCells (A 1) k (n − k)` (`k = var 2`), `0` for `j ≥ n − k`; `eval_xBit`.

Not an audit surface.
-/
module

public import FactoringAux.EngineNet
public import FactoringAux.DriverMath

@[expose] public section

namespace Factoring.Aux

open Finset

namespace Ex

/-- `[A a i ≠ 0]`. -/
def bitRd (a : ℕ) (i : Ex) : Ex := .ifLt (.lit 0) (.rd a i) (.lit 1) (.lit 0)

/-- Bit `i` of the input number `N` (cells `1 … n` of array `0`, `n = var 0`). -/
def nBit (i : Ex) : Ex := .ifLt i (.var 0) (bitRd 0 (.add i (.lit 1))) (.lit 0)

/-- Bit `j` of the pattern `x` (cells `k … n−1` of array `1`, `k = var 2`). -/
def xBit (j : Ex) : Ex := .ifLt (.add j (.var 2)) (.var 0) (bitRd 1 (.add j (.var 2))) (.lit 0)

variable {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ}

theorem eval_bitRd (a : ℕ) (i : Ex) : eval σ A (bitRd a i) = if A a (eval σ A i) = 0 then 0 else 1 := by
  simp only [bitRd, eval]
  by_cases h : A a (eval σ A i) = 0 <;> simp [h, Nat.pos_iff_ne_zero]

theorem eval_ifLt' (e f u v : Ex) :
    eval σ A (.ifLt e f u v) = if eval σ A e < eval σ A f then eval σ A u else eval σ A v := rfl

theorem eval_nBit (i : Ex) :
    eval σ A (nBit i) = ((numCells (A 0) 1 (σ 0)).testBit (eval σ A i)).toNat := by
  rw [nBit, eval_ifLt', show eval σ A (.var 0) = σ 0 from rfl]
  by_cases h : eval σ A i < σ 0
  · rw [if_pos h, eval_bitRd, testBit_numCells _ _ _ _ h]
    simp only [eval, Nat.add_comm 1]
    by_cases h' : A 0 (eval σ A i + 1) = 0 <;> simp [h']
  · rw [if_neg h, Nat.testBit_lt_two_pow (lt_of_lt_of_le (numCells_lt _ _ _)
      (Nat.pow_le_pow_right (by norm_num) (by omega)))]
    rfl

theorem eval_xBit (j : Ex) :
    eval σ A (xBit j) = ((numCells (A 1) (σ 2) (σ 0 - σ 2)).testBit (eval σ A j)).toNat := by
  rw [xBit, eval_ifLt', show eval σ A (.var 0) = σ 0 from rfl,
    show eval σ A (.add j (.var 2)) = eval σ A j + σ 2 from rfl]
  by_cases h : eval σ A j + σ 2 < σ 0
  · rw [if_pos h, eval_bitRd, testBit_numCells _ _ _ _ (by omega)]
    simp only [eval, Nat.add_comm (eval σ A j)]
    by_cases h' : A 1 (σ 2 + eval σ A j) = 0 <;> simp [h']
  · rw [if_neg h, Nat.testBit_lt_two_pow (lt_of_lt_of_le (numCells_lt _ _ _)
      (Nat.pow_le_pow_right (by norm_num) (by omega)))]
    rfl

end Ex

end Factoring.Aux
