/-
Codes for the counting engine: the engine sums over settings by running through numbers.

* Mixed radix: `pp n i = ∏_{j<i} n j`, digit `dgx n c i = c / pp n i % n i`; `codeEquiv`: for positive sizes,
  `(∀ i : Fin m, Fin (n i)) ≃ Fin (pp n m)` with digits `dgx`; **`sum_pi_eq`**: a sum over all families is a sum over
  the numbers below `pp n m`.
* Bit strings: `testBit_bnum` (bit `i` of `bnum θ` is `θ i`), `bdec` (the string of a number), `bnum_bdec`,
  `bdec_bnum`; **`bnum_slice`**: the code of a block of `θ` is `bnum θ / 2^o % 2^w`; `sum_bits_eq`.

Not an audit surface.
-/
module

public import FactoringAux.Gates
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

namespace Factoring.Aux

open Finset

/-! ### Mixed radix -/

/-- `∏_{j<i} n j`. -/
def pp (n : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | i + 1 => pp n i * n i

/-- Digit `i` of `c`. -/
def dgx (n : ℕ → ℕ) (c i : ℕ) : ℕ := c / pp n i % n i

theorem pp_pos {n : ℕ → ℕ} : ∀ {i : ℕ}, (∀ j < i, 0 < n j) → 0 < pp n i
  | 0, _ => Nat.one_pos
  | i + 1, h => Nat.mul_pos (pp_pos fun j hj => h j (by omega)) (h i (by omega))

theorem pp_dvd (n : ℕ → ℕ) {i j : ℕ} (h : i ≤ j) : pp n i * n i ∣ pp n j ∨ i = j := by
  induction j with
  | zero => right; omega
  | succ j ih =>
      rcases Nat.lt_or_ge i (j + 1) with hi | hi
      · left
        rcases ih (by omega) with h1 | h1
        · exact Dvd.dvd.mul_right h1 _
        · subst h1; exact dvd_refl _
      · right; omega

theorem dgx_lt {n : ℕ → ℕ} {i : ℕ} (h : 0 < n i) (c : ℕ) : dgx n c i < n i := Nat.mod_lt _ h

/-- A number below `pp n m` is the sum of its digits. -/
theorem expand (n : ℕ → ℕ) : ∀ (m c : ℕ), c < pp n m → c = ∑ i ∈ range m, dgx n c i * pp n i
  | 0, c, h => by simp [pp] at h; simp [h]
  | m + 1, c, h => by
      have hpos : 0 < pp n m := by
        rcases Nat.eq_zero_or_pos (pp n m) with h0 | h0
        · simp [pp, h0] at h
        · exact h0
      have hq : c / pp n m < n m := by
        rw [Nat.div_lt_iff_lt_mul hpos]; simpa [pp, mul_comm] using h
      have hr : c % pp n m < pp n m := Nat.mod_lt _ hpos
      have ih := expand n m (c % pp n m) hr
      rw [sum_range_succ]
      have hlast : dgx n c m = c / pp n m := by unfold dgx; exact Nat.mod_eq_of_lt hq
      have hlow : ∀ i ∈ range m, dgx n c i = dgx n (c % pp n m) i := by
        intro i hi
        have hi' := mem_range.mp hi
        unfold dgx
        rw [← Nat.mod_mul_right_div_self, ← Nat.mod_mul_right_div_self (c % pp n m)]
        rcases pp_dvd n (show i ≤ m by omega) with hd | hd
        · rw [Nat.mod_mod_of_dvd _ hd]
        · omega
      rw [sum_congr rfl fun i hi => by rw [hlow i hi], ← ih, hlast]
      have := Nat.mod_add_div c (pp n m)
      rw [mul_comm] at this
      omega

theorem sum_digits_lt (n : ℕ → ℕ) (f : ℕ → ℕ) : ∀ m, (∀ i < m, f i < n i) → ∑ i ∈ range m, f i * pp n i < pp n m
  | 0, _ => by simp [pp]
  | m + 1, h => by
      rw [sum_range_succ]
      have ih := sum_digits_lt n f m fun i hi => h i (by omega)
      have hf := h m (by omega)
      show _ < pp n m * n m
      have h1 : (f m + 1) * pp n m ≤ n m * pp n m := Nat.mul_le_mul_right _ (by omega)
      rw [Nat.add_mul, one_mul] at h1
      rw [mul_comm (pp n m) (n m)]
      omega

theorem dgx_sum (n : ℕ → ℕ) (f : ℕ → ℕ) (m : ℕ) (h : ∀ i < m, f i < n i) :
    ∀ j < m, dgx n (∑ i ∈ range m, f i * pp n i) j = f j := by
  have hc := sum_digits_lt n f m h
  set c := ∑ i ∈ range m, f i * pp n i with hcdef
  -- uniqueness of digits: compare the two expansions
  have hpos : ∀ j < m, 0 < n j := fun j hj => lt_of_le_of_lt (Nat.zero_le _) (h j hj)
  have key : ∀ k ≤ m, ∀ j < k, dgx n (∑ i ∈ range k, f i * pp n i) j = f j := by
    intro k
    induction k with
    | zero => intro _ j hj; omega
    | succ k ih =>
        intro hk j hj
        have hlt := sum_digits_lt n f k fun i hi => h i (by omega)
        have hpk : 0 < pp n k := pp_pos fun i hi => hpos i (by omega)
        rw [sum_range_succ]
        rcases Nat.lt_or_ge j k with hjk | hjk
        · have ihj := ih (by omega) j hjk
          unfold dgx at ihj ⊢
          rw [← Nat.mod_mul_right_div_self] at ihj ⊢
          rcases pp_dvd n (show j ≤ k by omega) with hd | hd
          · obtain ⟨q, hq⟩ := hd
            rw [show f k * pp n k = pp n j * n j * (q * f k) by rw [hq]; ring, Nat.add_mul_mod_self_left]
            exact ihj
          · omega
        · obtain rfl : j = k := by omega
          unfold dgx
          rw [Nat.add_mul_div_right _ _ hpk, Nat.div_eq_of_lt hlt, zero_add]
          exact Nat.mod_eq_of_lt (h j (by omega))
  exact fun j hj => key m le_rfl j hj

/-- Mixed-radix codes. -/
def codeEquiv (n : ℕ → ℕ) (m : ℕ) (hn : ∀ i < m, 0 < n i) : (∀ i : Fin m, Fin (n i)) ≃ Fin (pp n m) where
  toFun f := ⟨∑ i ∈ range m, (if h : i < m then (f ⟨i, h⟩ : ℕ) else 0) * pp n i,
    sum_digits_lt n _ m fun i hi => by simp [hi]⟩
  invFun c i := ⟨dgx n c i, dgx_lt (hn i i.2) _⟩
  left_inv f := by
    funext i
    apply Fin.ext
    simp only
    rw [dgx_sum n _ m (fun j hj => by simp [hj]) i i.2]
    simp
  right_inv c := by
    apply Fin.ext
    simp only
    conv_rhs => rw [expand n m c c.2]
    refine sum_congr rfl fun i hi => ?_
    simp [mem_range.mp hi]

theorem codeEquiv_symm_apply (n : ℕ → ℕ) (m : ℕ) (hn : ∀ i < m, 0 < n i) (c : Fin (pp n m)) (i : Fin m) :
    ((codeEquiv n m hn).symm c i : ℕ) = dgx n c i := rfl

/-- **A sum over all families is a sum over their codes.** -/
theorem sum_pi_eq {M : Type*} [AddCommMonoid M] (n : ℕ → ℕ) (m : ℕ) (hn : ∀ i < m, 0 < n i)
    (F : (∀ i : Fin m, Fin (n i)) → M) :
    ∑ f, F f = ∑ c ∈ range (pp n m), if h : c < pp n m then F ((codeEquiv n m hn).symm ⟨c, h⟩) else 0 := by
  rw [← (codeEquiv n m hn).symm.sum_comp, Finset.sum_range]
  exact sum_congr rfl fun c _ => by rw [dif_pos c.2]

/-! ### Bit strings -/

theorem finTwo_symm (b : Bool) : ((finTwoEquiv.symm b : Fin 2) : ℕ) = if b then 1 else 0 := by
  cases b <;> rfl

theorem testBit_bnum : ∀ {c : ℕ} (θ : Bits c) (i : ℕ), (bnum θ).testBit i = if h : i < c then θ ⟨i, h⟩ else false
  | 0, θ, i => by simp [bnum, bitsEquiv]
  | c + 1, θ, i => by
      have hb : bnum θ = 2 ^ c * (if θ (Fin.last c) then 1 else 0) + bnum (Fin.init θ) := by
        simp only [bnum, bitsEquiv, Equiv.trans_apply, Equiv.arrowCongr_apply, Equiv.refl_symm,
          Equiv.coe_refl, Function.comp_apply, finFunctionFinEquiv_apply, Fin.sum_univ_castSucc]
        simp only [Fin.init, Fin.val_last, Fin.val_castSucc, Function.comp_def, id]
        cases θ (Fin.last c) <;> simp [mul_comm, add_comm, finTwo_symm]
      have hlt : bnum (Fin.init θ) < 2 ^ c := (bitsEquiv c (Fin.init θ)).2
      rw [hb, Nat.testBit_two_pow_mul_add _ hlt, testBit_bnum (Fin.init θ)]
      by_cases hi : i < c
      · simp [hi, show i < c + 1 by omega, Fin.init]
      · by_cases hic : i = c
        · subst hic
          cases h : θ (Fin.last i) <;> simp [h, Fin.last] <;> exact h
        · have : i - c ≠ 0 := by omega
          simp only [hi, if_false, show ¬ i < c + 1 by omega, dif_neg, not_false_eq_true]
          cases θ (Fin.last c) <;> simp [Nat.testBit_lt_two_pow (Nat.one_lt_two_pow this)]

theorem bnum_lt {c : ℕ} (θ : Bits c) : bnum θ < 2 ^ c := (bitsEquiv c θ).2

/-- The string of a number (its low `c` bits). -/
def bdec (c q : ℕ) : Bits c := fun i => q.testBit i

theorem bdec_bnum {c : ℕ} (θ : Bits c) : bdec c (bnum θ) = θ := by
  funext i; simp [bdec, testBit_bnum]

theorem bnum_bdec {c q : ℕ} (hq : q < 2 ^ c) : bnum (bdec c q) = q := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_bnum]
  split_ifs with h
  · rfl
  · exact (Nat.testBit_lt_two_pow (lt_of_lt_of_le hq (Nat.pow_le_pow_right (by norm_num) (by omega)))).symm

/-- **The code of a block.** -/
theorem bnum_slice {c : ℕ} (θ : Bits c) (o w : ℕ) (h : o + w ≤ c) :
    bnum (fun j : Fin w => θ ⟨o + j, by omega⟩) = bnum θ / 2 ^ o % 2 ^ w := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_bnum, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, testBit_bnum]
  by_cases hi : i < w
  · simp [hi, show i + o < c by omega, Nat.add_comm i o]
    intro h'; omega
  · simp [hi]

/-- A sum over strings is a sum over their codes. -/
theorem sum_bits_eq {M : Type*} [AddCommMonoid M] (c : ℕ) (F : Bits c → M) :
    ∑ θ, F θ = ∑ q ∈ range (2 ^ c), F (bdec c q) := by
  rw [← (bitsEquiv c).symm.sum_comp, Finset.sum_range]
  refine sum_congr rfl fun q _ => ?_
  congr 1
  have : (bitsEquiv c).symm q = bdec c q := by
    apply (bitsEquiv c).injective
    rw [Equiv.apply_symm_apply]
    apply Fin.ext
    exact (bnum_bdec q.2).symm
  exact this

end Factoring.Aux
