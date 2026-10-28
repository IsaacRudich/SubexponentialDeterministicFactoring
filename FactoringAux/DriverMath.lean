/-
The mathematics of the engine's driver: the search over an array of answer bits, and the binary output.

* `numCells f o n`: the number whose bit `j < n` is "cell `o + j` of `f` is nonzero"; `numCells_succ`.
* `xs c n i`: the state of `search c n` after `i` positions (`xs_spec`: `search c n = searchGo c (n - i) (xs c n i)`).
* `encodeNat_eq_bitsW`, `length_encodeNat_eq`: `encodeNat p` is the first `ℓ` bits of `p`, where
  `ℓ = #{j < n : 2^j ≤ p}` for `0 < p < 2^n`.

Not an audit surface.
-/
module

public import FactoringAux.Search
public import FactoringAux.Trial.Bits
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

namespace Factoring.Aux

open Finset Computability Factoring.Aux.Trial

/-- The number written by the cells `o, …, o + n - 1` of `f` (a cell is a one when nonzero). -/
def numCells (f : ℕ → ℕ) (o n : ℕ) : ℕ := ∑ j ∈ range n, (if f (o + j) = 0 then 0 else 1) * 2 ^ j

theorem numCells_succ (f : ℕ → ℕ) (o n : ℕ) :
    numCells f o (n + 1) = (if f o = 0 then 0 else 1) + 2 * numCells f (o + 1) n := by
  unfold numCells
  rw [sum_range_succ', Finset.mul_sum]
  simp only [add_zero, pow_zero, mul_one]
  rw [add_comm]
  congr 1
  refine sum_congr rfl fun j _ => ?_
  rw [show o + (j + 1) = o + 1 + j by ring, pow_succ]; ring

theorem numCells_congr {f f' : ℕ → ℕ} {o n : ℕ} (h : ∀ j, o ≤ j → j < o + n → f j = f' j) :
    numCells f o n = numCells f' o n :=
  sum_congr rfl fun j hj => by rw [h (o + j) (by omega) (by simp at hj; omega)]

/-- The state of the search after `i` positions. -/
def xs (c : ℕ → ℕ → ℕ) (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => searchStep c (n - 1 - i) (xs c n i)

theorem xs_spec (c : ℕ → ℕ → ℕ) (n : ℕ) : ∀ i, i ≤ n → search c n = searchGo c (n - i) (xs c n i)
  | 0, _ => by simp [search, xs]
  | i + 1, h => by
      rw [xs_spec c n i (by omega), xs, show n - i = (n - 1 - i) + 1 by omega,
        show n - (i + 1) = n - 1 - i by omega]
      rfl

theorem encodeNat_eq_bitsW (p : ℕ) : encodeNat p = bitsW (encodeNat p).length p := by
  have h := (bitsW_valL (encodeNat p)).symm
  rwa [valL_encodeNat] at h

theorem two_pow_length_le (p : ℕ) (hp : 0 < p) : 2 ^ ((encodeNat p).length - 1) ≤ p := by
  induction p using Nat.binaryRec with
  | zero => omega
  | bit b m ih =>
      rw [encodeNat_bit]
      split_ifs with h
      · obtain ⟨rfl, rfl⟩ := h; simp [Nat.bit] at hp
      · rcases Nat.eq_zero_or_pos m with hm | hm
        · subst hm
          have : b = true := by cases b <;> simp_all
          subst this; simp [Nat.bit, (encodeNat_eq_nil_iff 0).mpr rfl]
        · have := ih hm
          simp only [List.length_cons, Nat.add_sub_cancel]
          have hl : 1 ≤ (encodeNat m).length := by
            rcases Nat.eq_zero_or_pos (encodeNat m).length with h0 | h0
            · rw [List.length_eq_zero_iff, encodeNat_eq_nil_iff] at h0; omega
            · exact h0
          calc 2 ^ (encodeNat m).length = 2 * 2 ^ ((encodeNat m).length - 1) := by
                rw [← pow_succ']; congr 1; omega
            _ ≤ 2 * m := Nat.mul_le_mul_left _ this
            _ ≤ Nat.bit b m := by cases b <;> simp [Nat.bit] <;> omega

/-- The length of `encodeNat p` counts the powers of two up to `p`. -/
theorem length_encodeNat_eq (p n : ℕ) (hp : 0 < p) (hn : p < 2 ^ n) :
    (encodeNat p).length = ((range n).filter (fun j => 2 ^ j ≤ p)).card := by
  have h1 := lt_two_pow_length p
  have h2 := two_pow_length_le p hp
  generalize (encodeNat p).length = ℓ at h1 h2 ⊢
  have hℓ : ℓ ≤ n := by
    by_contra h
    have : 2 ^ n ≤ 2 ^ (ℓ - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have : (range n).filter (fun j => 2 ^ j ≤ p) = range ℓ := by
    ext j
    simp only [mem_filter, mem_range]
    constructor
    · rintro ⟨-, hj⟩
      by_contra h
      have : 2 ^ ℓ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    · intro hj
      exact ⟨by omega, le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) h2⟩
  rw [this, card_range]

theorem numCells_lt (f : ℕ → ℕ) (o : ℕ) : ∀ n, numCells f o n < 2 ^ n := by
  intro n
  induction n generalizing o with
  | zero => simp [numCells]
  | succ n ih =>
      rw [numCells_succ, pow_succ]
      have := ih (o + 1)
      split_ifs <;> omega

/-- The bits of `numCells`. -/
theorem testBit_numCells (f : ℕ → ℕ) : ∀ n o i, i < n → (numCells f o n).testBit i = decide (f (o + i) ≠ 0) := by
  intro n
  induction n with
  | zero => intro o i h; omega
  | succ n ih =>
      intro o i hi
      rw [numCells_succ]
      cases i with
      | zero =>
          rw [Nat.testBit_zero]
          split_ifs with h
          · simp [h]
          · simp [h]
      | succ i =>
          rw [Nat.testBit_succ]
          have : ((if f o = 0 then 0 else 1) + 2 * numCells f (o + 1) n) / 2 = numCells f (o + 1) n := by
            split_ifs <;> omega
          rw [this, ih (o + 1) i (by omega), show o + 1 + i = o + (i + 1) by ring]

theorem bitsW_eq_ofFn : ∀ (ℓ p : ℕ), bitsW ℓ p = List.ofFn (fun i : Fin ℓ => p.testBit i)
  | 0, _ => rfl
  | ℓ + 1, p => by
      rw [bitsW_succ, List.ofFn_succ, bitsW_eq_ofFn ℓ (p / 2)]
      congr 1
      · show (p % 2 == 1) = p.testBit 0
        rw [Nat.testBit_zero]; rcases Nat.mod_two_eq_zero_or_one p with h | h <;> simp [h]
      · congr 1; funext i; simp [Nat.testBit_div_two]

/-- `2^j ≤ p` iff some bit at or above `j` (below `n`) is set. -/
theorem two_pow_le_iff (p n j : ℕ) (hp : p < 2 ^ n) :
    2 ^ j ≤ p ↔ ∃ j', j ≤ j' ∧ j' < n ∧ p.testBit j' = true := by
  constructor
  · intro h
    have hne : p / 2 ^ j ≠ 0 := by
      rw [Ne, Nat.div_eq_zero_iff]
      have : 0 < 2 ^ j := Nat.pow_pos (by norm_num)
      omega
    obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero hne
    rw [Nat.testBit_div_two_pow] at hi
    refine ⟨i + j, by omega, ?_, hi⟩
    by_contra hc
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hp (Nat.pow_le_pow_right (by norm_num) (by omega)))] at hi
    exact Bool.false_ne_true hi
  · rintro ⟨j', h1, -, h3⟩
    exact le_trans (Nat.pow_le_pow_right (by norm_num) h1) (Nat.ge_two_pow_of_testBit h3)

end Factoring.Aux
