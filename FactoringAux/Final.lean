/-
The final glue of `everyRootRate`: from counting expressions to the rate.

If for every `k ≥ 1` some counting expression `e` (`BitSpec e B`) costs `B n ≤ C · 2^(n/k)`, then for every `k ≥ 1`
some machine factors within `C' · 2^(n/k)` steps: take the expression for `12k`; the driver (`drv_spec`) costs
`200 (n + 1)^3 (B n + 1) ≤ C'' · 2^(n/(6k))`, and `everyRoot_of_src` does the rest.

* `mul_div_mul_le` (`a ⌊n/(ab)⌋ ≤ ⌊n/b⌋`), `succ_cube_le` (`(n + 1)^3 ≤ (d + 1)^3 · 2^(3⌊n/d⌋)`);
  **`everyRoot_of_count`**.

Not an audit surface.
-/
module

public import FactoringAux.DriverOut
public import FactoringAux.Assemble

@[expose] public section

namespace Factoring.Aux

open Factoring.Aux.Copied Factoring.Aux.Copied.PLib Computability

theorem mul_div_mul_le (a b n : ℕ) : a * (n / (a * b)) ≤ n / b := by
  rcases Nat.eq_zero_or_pos b with hb | hb
  · subst hb; simp
  rw [Nat.le_div_iff_mul_le hb]
  calc a * (n / (a * b)) * b = a * b * (n / (a * b)) := by ring
    _ ≤ n := Nat.mul_div_le n (a * b)

theorem succ_cube_le (n d : ℕ) (hd : 0 < d) : (n + 1) ^ 3 ≤ (d + 1) ^ 3 * 2 ^ (3 * (n / d)) := by
  have h1 := le_two_pow_div n d hd
  have h2 : 1 ≤ 2 ^ (n / d) := Nat.one_le_two_pow
  have h3 : n + 1 ≤ (d + 1) * 2 ^ (n / d) := by nlinarith
  calc (n + 1) ^ 3 ≤ ((d + 1) * 2 ^ (n / d)) ^ 3 := Nat.pow_le_pow_left h3 3
    _ = (d + 1) ^ 3 * 2 ^ (3 * (n / d)) := by rw [mul_pow, ← pow_mul, mul_comm (n / d)]

/-- **The final glue**: counting expressions of cost `≤ C · 2^(n/k)` for every `k ≥ 1` give `everyRootRate`'s
statement. -/
theorem everyRoot_of_count
    (H : ∀ k : ℕ, 1 ≤ k → ∃ (e : Ex) (B : ℕ → ℕ) (C : ℕ), BitSpec e B ∧ ∀ n, B n ≤ C * 2 ^ (n / k)) :
    ∀ k : ℕ, 1 ≤ k → ∃ C : ℕ, FactoringInTime (fun n => C * 2 ^ (n / k)) := by
  intro k hk
  obtain ⟨e, B, C, he, hB⟩ := H (12 * k) (by omega)
  obtain ⟨hout, hcost⟩ := drv_spec e B he
  refine everyRoot_of_src k hk (drv e) 2 (200 * (36 * k + 1) ^ 3 * (C + 1)) hout fun xs => ?_
  set n := xs.length
  set P := 2 ^ (n / (12 * k))
  have h1 : B n + 1 ≤ (C + 1) * P := by
    have hb : B n ≤ C * P := hB n
    have : 1 ≤ P := Nat.one_le_two_pow
    nlinarith
  have h2 : (n + 1) ^ 3 ≤ (36 * k + 1) ^ 3 * P := by
    refine le_trans (succ_cube_le n (36 * k) (by omega)) (Nat.mul_le_mul_left _ ?_)
    refine Nat.pow_le_pow_right (by norm_num) ?_
    have := mul_div_mul_le 3 (12 * k) n
    rwa [show 3 * (12 * k) = 36 * k by ring] at this
  have h3 : P * P ≤ 2 ^ (n / (6 * k)) := by
    rw [← pow_add]
    refine Nat.pow_le_pow_right (by norm_num) ?_
    have := mul_div_mul_le 2 (6 * k) n
    rw [show 2 * (6 * k) = 12 * k by ring] at this
    omega
  calc srcCost (drv e) xs ≤ 200 * (n + 1) ^ 3 * (B n + 1) := hcost xs
    _ ≤ 200 * ((36 * k + 1) ^ 3 * P) * ((C + 1) * P) := by gcongr
    _ = 200 * (36 * k + 1) ^ 3 * (C + 1) * (P * P) := by ring
    _ ≤ 200 * (36 * k + 1) ^ 3 * (C + 1) * 2 ^ (n / (6 * k)) := Nat.mul_le_mul_left _ h3

end Factoring.Aux
