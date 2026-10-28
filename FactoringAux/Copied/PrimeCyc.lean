/-
Adapted from the authors' related work.
Only `div_two_pow_succ`, `mulModV`, `mulModV_eq` (the value of `mulModR`).

Not an audit surface.
-/
module

public import Mathlib.Tactic.Ring
public import Mathlib.Data.Nat.Bits
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace Factoring.Aux.Copied.AKS

theorem div_two_pow_succ (e t : ℕ) :
    e / 2 ^ t = 2 * (e / 2 ^ (t + 1)) + (if e.testBit t then 1 else 0) := by
  have h1 : e / 2 ^ (t + 1) = e / 2 ^ t / 2 := by rw [pow_succ, Nat.div_div_eq_div_mul]
  rw [h1, Nat.testBit_eq_decide_div_mod_eq]
  have := Nat.div_add_mod (e / 2 ^ t) 2
  have h2 := Nat.mod_lt (e / 2 ^ t) (by norm_num : 0 < 2)
  by_cases h : e / 2 ^ t % 2 = 1
  · simp only [h, decide_true, if_true]; omega
  · simp only [h, decide_false, Bool.false_eq_true, if_false]; omega

/-- `a · b mod n` by the bits of `b`, high bit first (`B` bits): `x := 2x mod n`,
then `x := x + a mod n` on a set bit. -/
def mulModV (n a b B : ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => if b.testBit (B - 1 - m) then (2 * mulModV n a b B m % n + a) % n
      else 2 * mulModV n a b B m % n

theorem mulModV_eq (n a b B : ℕ) (hb : b < 2 ^ B) :
    ∀ m, m ≤ B → mulModV n a b B m = a * (b / 2 ^ (B - m)) % n
  | 0, _ => by simp [mulModV, Nat.div_eq_of_lt hb]
  | m + 1, hm => by
      have ih := mulModV_eq n a b B hb m (by omega)
      have ht := div_two_pow_succ b (B - 1 - m)
      rw [show B - 1 - m + 1 = B - m by omega] at ht
      rw [show B - (m + 1) = B - 1 - m by omega, ht, mulModV, ih]
      split_ifs
      · rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
        congr 1; ring
      · rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
        congr 1; ring

end Factoring.Aux.Copied.AKS
