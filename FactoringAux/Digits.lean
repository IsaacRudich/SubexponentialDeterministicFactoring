/-
Digits in base `2^b` (for the multiplication network).

* `dgt d i = d / 2^(b i) % 2^b`, the `i`-th digit; `numOf D n = ∑_{i<n} D_i 2^(b i)`.
* `dgt_numOf`, `numOf_dgt`, `dgt_eq_zero_of_lt`: digits and numbers.
* `numOf_mul_numOf`: the product of two numbers with `n` digits is `∑_j cv_j 2^(b j)` over `T ≥ 2n` coefficients.
* `digVal_range`, `chainOK_range`: the carry chain of `Carry.lean` read gate by gate.

Not an audit surface.
-/
module

public import FactoringAux.Carry
public import FactoringAux.Transform

@[expose] public section

namespace Factoring.Aux

open Finset

/-- The `i`-th digit of `d` in base `2^b`. -/
def dgt (b d i : ℕ) : ℕ := d / 2 ^ (b * i) % 2 ^ b

theorem dgt_lt (b d i : ℕ) : dgt b d i < 2 ^ b := Nat.mod_lt _ (Nat.pow_pos (by norm_num))

/-- The number with digits `D 0, …, D (n-1)`. -/
def numOf (b : ℕ) (D : ℕ → ℕ) (n : ℕ) : ℕ := ∑ i ∈ range n, D i * 2 ^ (b * i)

theorem numOf_lt (b : ℕ) (D : ℕ → ℕ) (hD : ∀ i, D i < 2 ^ b) : ∀ n, numOf b D n < 2 ^ (b * n)
  | 0 => by simp [numOf]
  | n + 1 => by
      unfold numOf
      rw [sum_range_succ]
      have ih := numOf_lt b D hD n
      unfold numOf at ih
      have h1 : D n * 2 ^ (b * n) + 2 ^ (b * n) ≤ 2 ^ b * 2 ^ (b * n) := by
        have h := Nat.mul_le_mul_right (2 ^ (b * n)) (Nat.succ_le_of_lt (hD n))
        rwa [Nat.succ_mul] at h
      calc _ < 2 ^ (b * n) + D n * 2 ^ (b * n) := by omega
        _ ≤ 2 ^ b * 2 ^ (b * n) := by omega
        _ = 2 ^ (b * (n + 1)) := by rw [← pow_add]; ring_nf

theorem dgt_zero (b d : ℕ) : dgt b d 0 = d % 2 ^ b := by simp [dgt]

theorem dgt_succ (b d i : ℕ) : dgt b d (i + 1) = dgt b (d / 2 ^ b) i := by
  unfold dgt
  rw [Nat.div_div_eq_div_mul, ← pow_add]
  congr 3; ring

theorem numOf_succ (b : ℕ) (D : ℕ → ℕ) (n : ℕ) :
    numOf b D (n + 1) = D 0 + 2 ^ b * numOf b (fun i => D (i + 1)) n := by
  unfold numOf
  rw [sum_range_succ', mul_sum]
  simp only [mul_zero, pow_zero, mul_one]
  rw [add_comm]
  congr 1
  refine sum_congr rfl fun i _ => ?_
  rw [mul_add, mul_one, pow_add]; ring

theorem dgt_numOf (b : ℕ) :
    ∀ n (D : ℕ → ℕ), (∀ i, D i < 2 ^ b) → ∀ j, dgt b (numOf b D n) j = if j < n then D j else 0 := by
  intro n
  induction n with
  | zero => intro D _ j; simp [numOf, dgt]
  | succ n ih =>
      intro D hD j
      have hb : 0 < 2 ^ b := Nat.pow_pos (by norm_num)
      rw [numOf_succ]
      cases j with
      | zero =>
          rw [dgt_zero, if_pos (by omega), Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hD 0)]
      | succ j =>
          rw [dgt_succ, Nat.add_mul_div_left _ _ hb, Nat.div_eq_of_lt (hD 0), zero_add,
            ih (fun i => D (i + 1)) (fun i => hD _) j]
          by_cases h : j < n
          · rw [if_pos h, if_pos (by omega)]
          · rw [if_neg h, if_neg (by omega)]

theorem dgt_eq_zero_of_lt {b d n j : ℕ} (hd : d < 2 ^ (b * n)) (hj : n ≤ j) : dgt b d j = 0 := by
  unfold dgt
  rw [Nat.div_eq_of_lt (lt_of_lt_of_le hd (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ hj)))]
  simp

theorem numOf_dgt (b : ℕ) : ∀ n d, d < 2 ^ (b * n) → numOf b (dgt b d) n = d := by
  intro n
  induction n with
  | zero => intro d hd; simp [numOf] at hd ⊢; omega
  | succ n ih =>
      intro d hd
      have hb : 0 < 2 ^ b := Nat.pow_pos (by norm_num)
      rw [numOf_succ]
      simp only [dgt_succ]
      rw [ih (d / 2 ^ b) ?_, dgt_zero]
      · exact Nat.mod_add_div d (2 ^ b)
      · rw [Nat.div_lt_iff_lt_mul hb, ← pow_add]
        calc d < 2 ^ (b * (n + 1)) := hd
          _ = 2 ^ (b * n + b) := by ring_nf

/-- **The product of two numbers is the sum of the convolution coefficients**, for digits supported below `n`
and `T ≥ 2n` coefficients. -/
theorem numOf_mul_numOf (b n T : ℕ) (hT : 2 * n ≤ T) (D E : ℕ → ℕ) (hD : ∀ i, n ≤ i → D i = 0)
    (hE : ∀ i, n ≤ i → E i = 0) :
    numOf b D n * numOf b E n = ∑ j ∈ range T, cv T D E j * 2 ^ (b * j) := by
  have step : ∀ i i', (∑ j ∈ range T, (if i + i' = j then D i * E i' else 0) * 2 ^ (b * j)) =
      if i + i' < T then D i * E i' * 2 ^ (b * (i + i')) else 0 := by
    intro i i'
    simp_rw [ite_mul, zero_mul]
    rw [sum_ite_eq]
    simp [mem_range]
  have rhs : ∑ j ∈ range T, cv T D E j * 2 ^ (b * j) =
      ∑ i ∈ range T, ∑ i' ∈ range T, if i + i' < T then D i * E i' * 2 ^ (b * (i + i')) else 0 := by
    unfold cv
    simp_rw [sum_mul]
    rw [sum_comm]
    refine sum_congr rfl fun i _ => ?_
    rw [sum_comm]
    exact sum_congr rfl fun i' _ => step i i'
  rw [rhs]
  unfold numOf
  rw [sum_mul_sum]
  have hsub : range n ⊆ range T := range_subset_range.mpr (by omega)
  symm
  rw [← sum_subset hsub]
  · refine sum_congr rfl fun i hi => ?_
    rw [← sum_subset hsub]
    · refine sum_congr rfl fun i' hi' => ?_
      rw [mem_range] at hi hi'
      rw [if_pos (by omega), mul_add, pow_add]; ring
    · intro i' _ hi'
      rw [mem_range] at hi'
      rw [hE i' (by omega)]; simp
  · intro i _ hi
    rw [mem_range] at hi
    refine sum_eq_zero fun i' _ => ?_
    rw [hD i (by omega)]; simp

/-- The value of a list of digits read off a function. -/
theorem digVal_range' (b : ℕ) (f : ℕ → ℕ) :
    ∀ len s, digVal b ((List.range' s len).map f) = ∑ j ∈ range len, f (s + j) * 2 ^ (b * j)
  | 0, s => by simp [digVal]
  | len + 1, s => by
      rw [List.range'_succ, List.map_cons, digVal, digVal_range' b f len (s + 1), sum_range_succ', mul_sum]
      simp only [add_zero, mul_zero, pow_zero, mul_one]
      rw [add_comm]
      congr 1
      refine sum_congr rfl fun j _ => ?_
      rw [show s + 1 + j = s + (j + 1) by ring, mul_add, mul_one, pow_add]; ring

theorem digVal_range (b : ℕ) (f : ℕ → ℕ) (len : ℕ) :
    digVal b ((List.range len).map f) = ∑ j ∈ range len, f j * 2 ^ (b * j) := by
  rw [List.range_eq_range', digVal_range']
  simp

/-- **The carry chain, gate by gate**: along carries `car (j+1) = (car j + c j) / 2^b`, the chain accepts iff every
gate's digit check holds and the last carry is `0`. -/
theorem chainOK_range (b : ℕ) (c n car : ℕ → ℕ) (hcar : ∀ j, car (j + 1) = (car j + c j) / 2 ^ b) :
    ∀ len s, chainOK b ((List.range' s len).map c) ((List.range' s len).map n) (car s) ↔
      (∀ j, s ≤ j → j < s + len → (car j + c j) % 2 ^ b = n j) ∧ car (s + len) = 0
  | 0, s => by simp only [List.range'_zero, List.map_nil, chainOK, add_zero]; constructor <;> intro h <;> simp_all
  | len + 1, s => by
      rw [List.range'_succ, List.map_cons, List.map_cons, chainOK, ← hcar,
        chainOK_range b c n car hcar len (s + 1)]
      constructor
      · rintro ⟨h0, h1, h2⟩
        refine ⟨fun j hj1 hj2 => ?_, by rwa [show s + (len + 1) = s + 1 + len by ring]⟩
        rcases Nat.eq_or_lt_of_le hj1 with h | h
        · subst h; exact h0
        · exact h1 j h (by omega)
      · rintro ⟨h1, h2⟩
        exact ⟨h1 s le_rfl (by omega), fun j hj1 hj2 => h1 j (by omega) (by omega),
          by rwa [show s + 1 + len = s + (len + 1) by ring]⟩

end Factoring.Aux
