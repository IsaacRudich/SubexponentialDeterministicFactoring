/-
The carry chain of the multiplication network: unit carries check `∑ c_j 2^(bj) = N`.

Gate `CARRY[j]` reads the coefficient `c_j` and the incoming carry, accepts iff `(carry + c_j) mod 2^b` is the `j`-th
`b`-bit digit of `N`, and passes on `(carry + c_j) / 2^b`; the last carry must be `0`.  `chainOK_iff`: the chain
accepts exactly when `carry_in + ∑ c_j 2^(bj) = ∑ n_j 2^(bj)`, for digits `n_j < 2^b`.

Not an audit surface.
-/
module

public import Mathlib.Tactic.Ring
public import Mathlib.Order.Basic
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace Factoring.Aux

/-- `∑ x_j 2^(bj)` for a list of digits (least significant first). -/
def digVal (b : ℕ) : List ℕ → ℕ
  | [] => 0
  | x :: xs => x + 2 ^ b * digVal b xs

/-- The carry chain accepts the coefficients `cs` against the digits `ns`, from the incoming carry `cin`. -/
def chainOK (b : ℕ) : List ℕ → List ℕ → ℕ → Prop
  | [], [], cin => cin = 0
  | c :: cs, n :: ns, cin => (cin + c) % 2 ^ b = n ∧ chainOK b cs ns ((cin + c) / 2 ^ b)
  | _, _, _ => False

/-- Uniqueness of the last digit: `r + P u = n + P w` with `r, n < P` forces `r = n` and `u = w`. -/
theorem digit_unique {P r n u w : ℕ} (hr : r < P) (hn : n < P) :
    r + P * u = n + P * w ↔ r = n ∧ u = w := by
  constructor
  · intro h
    have h1 : (r + P * u) % P = (n + P * w) % P := by rw [h]
    rw [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr,
      Nat.mod_eq_of_lt hn] at h1
    subst h1
    have hP : 0 < P := lt_of_le_of_lt (Nat.zero_le _) hr
    exact ⟨rfl, Nat.eq_of_mul_eq_mul_left hP (by omega)⟩
  · rintro ⟨rfl, rfl⟩; rfl

/-- **The carry chain**: it accepts iff `cin + ∑ c_j 2^(bj) = ∑ n_j 2^(bj)`. -/
theorem chainOK_iff (b : ℕ) :
    ∀ (cs ns : List ℕ) (cin : ℕ), cs.length = ns.length → (∀ n ∈ ns, n < 2 ^ b) →
      (chainOK b cs ns cin ↔ cin + digVal b cs = digVal b ns)
  | [], [], cin, _, _ => by simp [chainOK, digVal]
  | c :: cs, n :: ns, cin, hl, hn => by
      have ih := chainOK_iff b cs ns ((cin + c) / 2 ^ b) (by simpa using hl)
        (fun m hm => hn m (List.mem_cons_of_mem _ hm))
      have hn0 : n < 2 ^ b := hn n List.mem_cons_self
      have hr : (cin + c) % 2 ^ b < 2 ^ b := Nat.mod_lt _ (Nat.two_pow_pos b)
      simp only [chainOK, digVal, ih]
      have hdm := Nat.mod_add_div (cin + c) (2 ^ b)
      have key : cin + (c + 2 ^ b * digVal b cs) =
          (cin + c) % 2 ^ b + 2 ^ b * ((cin + c) / 2 ^ b + digVal b cs) := by
        rw [mul_add]; linarith
      rw [key, digit_unique hr hn0]
  | [], _ :: _, _, hl, _ => by simp at hl
  | _ :: _, [], _, hl, _ => by simp at hl

end Factoring.Aux
