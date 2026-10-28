/-
The count of the multiplication network (`mulNet_count`).

* `asm zP zQ`: the setting of every gate forced by the digits `zP`, `zQ` of the input gates (each gate stores what
  its producers send; the carries follow the chain).
* `good_pinned`: a good setting is the forced one (`Good z → z = asm …`).
* `fC_eq_cv`: the coefficient `CARRY[j]` receives is the convolution coefficient of the digits (`ib_mid_fa`), and
  its value is the integer (`val_cv`).
* **`mulNet_value`**: for `1 ≤ N < 2^(L·L)`, the value of `mulNet R s N k x` is the number of divisors `d` of `N`
  with `d / 2^k = x`.

Not an audit surface.
-/
module

public import FactoringAux.MulNet

@[expose] public section

namespace Factoring.Aux

open Finset

section Count

variable (s : ℕ)

theorem pM_le_fw : pM s ≤ 2 ^ fw s := by
  unfold pM fw; rw [pow_succ]; have := Nat.one_le_two_pow (n := pm s); omega

theorem val_lt_fw (a : ZMod (pM s)) : a.val < 2 ^ fw s := lt_of_lt_of_le (ZMod.val_lt a) (pM_le_fw s)

theorem two_le_two_pow_pL : 2 ≤ 2 ^ pL s := by
  have := pL_pos s
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ pL s := Nat.pow_le_pow_right (by norm_num) this

/-- The carry a `CARRY` gate sends is below `2^(m+1)`. -/
theorem carry_lt (c : ℕ) (hc : c < 2 ^ fw s) (a : ZMod (pM s)) : (c + a.val) / 2 ^ pL s < 2 ^ fw s := by
  have h1 := val_lt_fw s a
  have h2 := two_le_two_pow_pL s
  rw [Nat.div_lt_iff_lt_mul (by omega)]
  calc c + a.val < 2 ^ fw s * 2 := by omega
    _ ≤ 2 ^ fw s * 2 ^ pL s := Nat.mul_le_mul_left _ h2

theorem mV_lt : ∀ (i j : MG (pA s)) (z : mS s i), mV s i j z < 2 ^ mC s i j := by
  intro i j z
  cases i <;> cases j <;> simp only [mV, mC, mLink] <;> (try simp) <;> (try exact val_lt_fw s _)
  all_goals (split_ifs <;> first | exact val_lt_fw s _ | exact Nat.one_pos | exact (Fin.isLt _) |
    exact carry_lt s _ (Fin.isLt _) _ | omega)

variable {R : Type*} [CommRing R]

theorem mW_01 (N k x : ℕ) : ∀ i (z : mS s i), mW (R := R) s N k x i z = 0 ∨ mW (R := R) s N k x i z = 1 := by
  intro i z; cases i <;> simp only [mW] <;> (try split_ifs) <;> simp

/-! ### The forced setting -/

/-- Digits of all input gates of one number. -/
abbrev DigS := Fin (pA s) → Fin (ph s) → Fin (2 ^ pL s)

/-- What `MID[k]` receives. -/
def fMid (zP zQ : DigS s) (k : Fin (pA s)) : (Fin (pA s) → ZMod (pM s)) × (Fin (pA s) → ZMod (pM s)) :=
  (fun r => faV s r (zP r) k, fun r => faV s r (zQ r) k)

/-- What `IB[j]` receives. -/
def fIb (zP zQ : DigS s) (j : Fin (pA s)) : Fin (pA s) → ZMod (pM s) := fun k => midV s k (fMid s zP zQ k) j

/-- What `CARRY[j]` receives from `IB[j mod A]`. -/
def fC (zP zQ : DigS s) (j : ℕ) : ZMod (pM s) :=
  ibV s (fIb s zP zQ ⟨j % pA s, Nat.mod_lt _ (pA_pos s)⟩) (j / pA s)

/-- The carries. -/
def carF (zP zQ : DigS s) : ℕ → ℕ
  | 0 => 0
  | j + 1 => (carF zP zQ j + (fC s zP zQ j).val) / 2 ^ pL s

theorem carF_lt (zP zQ : DigS s) : ∀ j, carF s zP zQ j < 2 ^ fw s
  | 0 => by simp [carF]
  | j + 1 => carry_lt s _ (carF_lt zP zQ j) _

/-- The setting forced by the digits of the input gates. -/
def asm (zP zQ : DigS s) : ∀ i, mS s i
  | .faP r => zP r
  | .faQ r => zQ r
  | .mid k => fMid s zP zQ k
  | .ib j => fIb s zP zQ j
  | .carry j => (fC s zP zQ j, ⟨carF s zP zQ j, carF_lt s zP zQ j⟩)

/-- **A good setting is the forced one.** -/
theorem good_pinned [Nontrivial R] (N k x : ℕ) (z : ∀ i, mS s i) (hz : (mulG s R N k x).Good z) :
    z = asm s (fun r => z (.faP r)) (fun r => z (.faQ r)) := by
  obtain ⟨hW, hv⟩ := hz
  have hmid : ∀ k, z (.mid k) = fMid s (fun r => z (.faP r)) (fun r => z (.faQ r)) k := by
    intro k
    refine Prod.ext (funext fun r => ?_) (funext fun r => ?_)
    · have := hv (.faP r) (.mid k) (by intro h; cases h)
      simp only [mulG, mV] at this
      exact (ZMod.val_injective _ this).symm
    · have := hv (.faQ r) (.mid k) (by intro h; cases h)
      simp only [mulG, mV] at this
      exact (ZMod.val_injective _ this).symm
  have hib : ∀ j, z (.ib j) = fIb s (fun r => z (.faP r)) (fun r => z (.faQ r)) j := by
    intro j
    funext k
    have := hv (.mid k) (.ib j) (by intro h; cases h)
    simp only [mulG, mV] at this
    rw [hmid k] at this
    exact (ZMod.val_injective _ this).symm
  have hc1 : ∀ j : Fin (pA s * pA s), (z (.carry j)).1 = fC s (fun r => z (.faP r)) (fun r => z (.faQ r)) j := by
    intro j
    have := hv (.ib ⟨j.val % pA s, Nat.mod_lt _ (pA_pos s)⟩) (.carry j) (by intro h; cases h)
    simp only [mulG, mV, if_true] at this
    rw [hib] at this
    exact (ZMod.val_injective _ this).symm
  have hc2 : ∀ j (hj : j < pA s * pA s),
      ((z (.carry ⟨j, hj⟩)).2 : ℕ) = carF s (fun r => z (.faP r)) (fun r => z (.faQ r)) j := by
    intro j
    induction j with
    | zero =>
        intro hj
        have := hW (.carry ⟨0, hj⟩)
        simp only [mulG, mW] at this
        split_ifs at this with h
        · exact h.2.1 trivial
        · exact absurd this zero_ne_one
    | succ j ih =>
        intro hj
        have := hv (.carry ⟨j, by omega⟩) (.carry ⟨j + 1, hj⟩) (by intro h; cases h)
        simp only [mulG, mV, if_true, show ¬ (j = j + 1 + 1) by omega, if_false] at this
        rw [← this, ih (by omega), hc1]
        rfl
  funext i
  cases i with
  | faP r => rfl
  | faQ r => rfl
  | mid k => exact hmid k
  | ib j => exact hib j
  | carry j => exact Prod.ext (hc1 j) (Fin.ext (hc2 j.val j.isLt))

/-! ### The coefficients -/

theorem div_lt_ph {i : ℕ} (hi : i < pL s) : i / pA s < ph s := by
  rw [Nat.div_lt_iff_lt_mul (pA_pos s), mul_comm, ← pL_eq]; exact hi

/-- The digit sequence of the input gates `zP`: digit `i < L` is slot `i / A` of gate `i mod A`. -/
def digN (zP : DigS s) (i : ℕ) : ℕ :=
  if h : i < pL s then (zP ⟨i % pA s, Nat.mod_lt _ (pA_pos s)⟩ ⟨i / pA s, div_lt_ph s h⟩).val else 0

theorem digN_lt (zP : DigS s) (i : ℕ) : digN s zP i < 2 ^ pL s := by
  unfold digN; split_ifs
  · exact Fin.isLt _
  · exact Nat.pow_pos (by norm_num)

theorem digN_zero (zP : DigS s) (i : ℕ) (hi : pL s ≤ i) : digN s zP i = 0 := by
  unfold digN; rw [dif_neg (by omega)]

theorem digN_slot (zP : DigS s) (r : Fin (pA s)) (i' : Fin (ph s)) :
    digN s zP (r + pA s * i') = (zP r i').val := by
  have hr := r.isLt
  have hi := i'.isLt
  have hlt : (r : ℕ) + pA s * i' < pL s := by
    rw [pL_eq]
    calc (r : ℕ) + pA s * i' < pA s + pA s * i' := by omega
      _ = pA s * (i' + 1) := by ring
      _ ≤ pA s * ph s := Nat.mul_le_mul_left _ hi
  unfold digN
  rw [dif_pos hlt]
  have e1 : ((r : ℕ) + pA s * i') % pA s = r := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
  have e2 : ((r : ℕ) + pA s * i') / pA s = i' := by
    rw [Nat.add_mul_div_left _ _ (pA_pos s), Nat.div_eq_of_lt hr, zero_add]
  congr 3

theorem digZ_eq (zP : DigS s) (r : Fin (pA s)) :
    digZ s (zP r) = fun i' => ((digN s zP (r + pA s * i') : ℕ) : ZMod (pM s)) := by
  funext i'
  unfold digZ ext0
  split_ifs with h
  · have := digN_slot s zP r ⟨i', h⟩
    simp only at this ⊢
    rw [this]
  · rw [digN_zero]
    · simp
    · rw [pL_eq]
      calc pA s * ph s ≤ pA s * i' := Nat.mul_le_mul_left _ (by omega)
        _ ≤ r + pA s * i' := by omega

theorem hatOut_congr (A : ℕ) (ζ : ZMod (pM s)) {a a' : ℕ → ZMod (pM s)} (h : ∀ r < A, a r = a' r) (k : ℕ) :
    hatOut A ζ a k = hatOut A ζ a' k :=
  sum_congr rfl fun r hr => by rw [h r (mem_range.mp hr)]

theorem midOut_congr (A : ℕ) (ω ω' : ZMod (pM s)) (k : ℕ) {a a' b b' : ℕ → ZMod (pM s)}
    (ha : ∀ r < A, a r = a' r) (hb : ∀ r < A, b r = b' r) (j : ℕ) :
    midOut A ω ω' k a b j = midOut A ω ω' k a' b' j := by
  unfold midOut
  rw [funext fun k₂ => hatOut_congr s A ω ha k₂, funext fun k₂ => hatOut_congr s A ω hb k₂]

/-- **`CARRY[j]` receives the convolution coefficient of the digits.** -/
theorem fC_eq_cv (zP zQ : DigS s) (j : ℕ) (hj : j < pA s * pA s) :
    fC s zP zQ j = ((cv (2 ^ (2 * s + 1 + 1)) (digN s zP) (digN s zQ) j : ℕ) : ZMod (pM s)) := by
  rw [cast_cv]
  have hA := pA_sq s
  have h1 : j % pA s < pA s := Nat.mod_lt _ (pA_pos s)
  have h2 : j / pA s < pA s := by rw [Nat.div_lt_iff_lt_mul (pA_pos s)]; exact hj
  have key := ib_mid_fa (pA s) (16 : ZMod (pM s)) (tInv s) (2 * s + 1) (omega16_pow_L s) hA (tInv_mul s)
    (fun i => ((digN s zP i : ℕ) : ZMod (pM s))) (fun i => ((digN s zQ i : ℕ) : ZMod (pM s)))
    (fun i hi => by simp [digN_zero s zP i (by unfold pL; exact hi)])
    (fun i hi => by simp [digN_zero s zQ i (by unfold pL; exact hi)]) (j % pA s) (j / pA s) h1 h2
  rw [Nat.mod_add_div] at key
  rw [← key]
  unfold fC ibV ibOut
  congr 1
  refine hatOut_congr s _ _ (fun r' hr' => ?_) _
  simp only [ext0, dif_pos hr', fIb, midV]
  refine midOut_congr s _ _ _ _ (fun r hr => ?_) (fun r hr => ?_) _
  · simp only [ext0, dif_pos hr, fMid, faV, ω16]
    rw [digZ_eq s zP ⟨r, hr⟩]
  · simp only [ext0, dif_pos hr, fMid, faV, ω16]
    rw [digZ_eq s zQ ⟨r, hr⟩]

theorem val_fC (zP zQ : DigS s) (j : ℕ) (hj : j < pA s * pA s) :
    (fC s zP zQ j).val = cv (2 ^ (2 * s + 1 + 1)) (digN s zP) (digN s zQ) j := by
  rw [fC_eq_cv s zP zQ j hj]
  exact val_cv s _ _ (digN_lt s zP) (digN_lt s zQ) (digN_zero s zP) j

/-! ### The carry chain of the forced setting -/

/-- The checks of every `CARRY` gate on the forced setting. -/
def CarryOK (N : ℕ) (zP zQ : DigS s) : Prop :=
  ∀ j < pA s * pA s, (carF s zP zQ j + (fC s zP zQ j).val) % 2 ^ pL s = dgt (pL s) N j ∧
    (j + 1 = pA s * pA s → carF s zP zQ (j + 1) = 0)

theorem pLL_le (s : ℕ) : pL s * pL s ≤ pL s * (pA s * pA s) := by
  apply Nat.mul_le_mul_left
  rw [pL_eq, pA_eq]; nlinarith [ph_pos s]

/-- **The checks of the `CARRY` gates hold iff the digits multiply to `N`.** -/
theorem carryOK_iff (N : ℕ) (hN : N < 2 ^ (pL s * pL s)) (zP zQ : DigS s) :
    CarryOK s N zP zQ ↔ numOf (pL s) (digN s zP) (pL s) * numOf (pL s) (digN s zQ) (pL s) = N := by
  set T := pA s * pA s with hT
  have hTT : T = 2 ^ (2 * s + 1 + 1) := pA_sq s
  have hTpos : 0 < T := Nat.mul_pos (pA_pos s) (pA_pos s)
  have hch := chainOK_range (pL s) (fun j => (fC s zP zQ j).val) (dgt (pL s) N) (carF s zP zQ)
    (fun j => rfl) T 0
  rw [zero_add, ← List.range_eq_range'] at hch
  have hiff := chainOK_iff (pL s) ((List.range T).map fun j => (fC s zP zQ j).val)
    ((List.range T).map (dgt (pL s) N)) (carF s zP zQ 0) (by simp) (by
      intro n hn; simp only [List.mem_map] at hn; obtain ⟨j, -, rfl⟩ := hn; exact dgt_lt _ _ _)
  rw [hch] at hiff
  have hN' : N < 2 ^ (pL s * T) := lt_of_lt_of_le hN (Nat.pow_le_pow_right (by norm_num) (pLL_le s))
  have hprod : numOf (pL s) (digN s zP) (pL s) * numOf (pL s) (digN s zQ) (pL s) =
      ∑ j ∈ range T, (fC s zP zQ j).val * 2 ^ (pL s * j) := by
    rw [numOf_mul_numOf (pL s) (pL s) T (by rw [hT, pL_eq, pA_eq]; nlinarith [ph_pos s]) _ _
      (digN_zero s zP) (digN_zero s zQ)]
    refine sum_congr rfl fun j hj => ?_
    rw [val_fC s zP zQ j (mem_range.mp hj), hTT]
  rw [hprod, ← digVal_range, show carF s zP zQ 0 = 0 from rfl, zero_add] at *
  have hNd : digVal (pL s) ((List.range T).map (dgt (pL s) N)) = N := by
    rw [digVal_range]; exact numOf_dgt (pL s) T N hN'
  rw [hNd] at hiff
  rw [← hiff]
  unfold CarryOK
  constructor
  · intro h
    refine ⟨fun j _ hj => (h j hj).1, ?_⟩
    obtain ⟨T', hT'⟩ : ∃ T', T = T' + 1 := ⟨T - 1, by omega⟩
    rw [hT']
    exact (h T' (by omega)).2 (by omega)
  · rintro ⟨h1, h2⟩ j hj
    refine ⟨h1 j (Nat.zero_le _) hj, fun he => ?_⟩
    rw [he]; exact h2

/-! ### The pattern -/

/-- The checks of every input gate `faP r`. -/
def FAOK (k x : ℕ) (zP : DigS s) : Prop :=
  ∀ r : Fin (pA s), preOK s k x r (zP r) ∧ (r.val = 0 → x < 2 ^ (pL s * pL s - k))

theorem testBit_numOf (b : ℕ) (D : ℕ → ℕ) (hD : ∀ i, D i < 2 ^ b) (n i t : ℕ) (hi : i < n) (ht : t < b) :
    (numOf b D n).testBit (b * i + t) = (D i).testBit t := by
  have := dgt_numOf b n D hD i
  rw [if_pos hi] at this
  rw [← this]; unfold dgt
  rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  simp [ht, add_comm]

theorem div_eq_iff_bits (p x k B : ℕ) (hp : p < 2 ^ B) :
    ((∀ pos, k ≤ pos → pos < B → p.testBit pos = x.testBit (pos - k)) ∧ x < 2 ^ (B - k)) ↔
      p / 2 ^ k = x := by
  constructor
  · rintro ⟨h1, h2⟩
    apply Nat.eq_of_testBit_eq; intro n
    rw [Nat.testBit_div_two_pow]
    by_cases hn : n + k < B
    · rw [h1 (n + k) (by omega) hn, Nat.add_sub_cancel]
    · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hp (Nat.pow_le_pow_right (by norm_num) (by omega))),
        Nat.testBit_lt_two_pow (lt_of_lt_of_le h2 (Nat.pow_le_pow_right (by norm_num) (by omega)))]
  · rintro rfl
    refine ⟨fun pos h1 _ => ?_, ?_⟩
    · rw [Nat.testBit_div_two_pow, Nat.sub_add_cancel h1]
    · rw [Nat.div_lt_iff_lt_mul (Nat.pow_pos (by norm_num)), ← pow_add]
      exact lt_of_lt_of_le hp (Nat.pow_le_pow_right (by norm_num) (by omega))

theorem slot_lt (r : Fin (pA s)) (i' : Fin (ph s)) : (r : ℕ) + pA s * i' < pL s := by
  have hr := r.isLt
  have hi := i'.isLt
  rw [pL_eq]
  calc (r : ℕ) + pA s * i' < pA s + pA s * i' := by omega
    _ = pA s * (i' + 1) := by ring
    _ ≤ pA s * ph s := Nat.mul_le_mul_left _ hi

/-- **The input checks hold iff the high bits of `p` are `x`.** -/
theorem faOK_iff (k x : ℕ) (zP : DigS s) :
    FAOK s k x zP ↔ numOf (pL s) (digN s zP) (pL s) / 2 ^ k = x := by
  have hp := numOf_lt (pL s) (digN s zP) (digN_lt s zP) (pL s)
  rw [← div_eq_iff_bits _ _ _ _ hp]
  have hbit : ∀ (r : Fin (pA s)) (i' : Fin (ph s)) (t : ℕ), t < pL s →
      (numOf (pL s) (digN s zP) (pL s)).testBit (pL s * (r + pA s * i') + t) = (zP r i').val.testBit t := by
    intro r i' t ht
    rw [testBit_numOf _ _ (digN_lt s zP) _ _ _ (slot_lt s r i') ht, digN_slot]
  constructor
  · intro h
    refine ⟨fun pos h1 h2 => ?_, (h ⟨0, pA_pos s⟩).2 rfl⟩
    have hi : pos / pL s < pL s := by rw [Nat.div_lt_iff_lt_mul (pL_pos s)]; exact h2
    set i := pos / pL s
    set t := pos % pL s
    have ht : t < pL s := Nat.mod_lt _ (pL_pos s)
    let r : Fin (pA s) := ⟨i % pA s, Nat.mod_lt _ (pA_pos s)⟩
    let i' : Fin (ph s) := ⟨i / pA s, div_lt_ph s hi⟩
    have hpos : pL s * (r + pA s * i') + t = pos := by
      simp only [r, i']
      rw [Nat.mod_add_div]; exact Nat.div_add_mod pos (pL s)
    have := (h r).1 i' ⟨t, ht⟩ (by simp only; rw [hpos]; exact h1)
    simp only at this
    rw [← hpos, hbit r i' t ht, this]
  · rintro ⟨h1, h2⟩ r
    refine ⟨fun i' t ht => ?_, fun _ => h2⟩
    have hlt : pL s * (r + pA s * i') + t < pL s * pL s := by
      have := slot_lt s r i'
      have := t.isLt
      calc pL s * (r + pA s * i') + t < pL s * (r + pA s * i') + pL s := by omega
        _ = pL s * (r + pA s * i' + 1) := by ring
        _ ≤ pL s * pL s := Nat.mul_le_mul_left _ (by omega)
    rw [← hbit r i' t t.isLt]
    exact h1 _ ht hlt

/-! ### Agreement and goodness of the forced setting -/

theorem asm_agree (zP zQ : DigS s) :
    ∀ i j, i ≠ j → mV s i j (asm s zP zQ i) = mV s j i (asm s zP zQ j) := by
  intro i j hne
  cases i <;> cases j <;> simp only [mV, asm, fMid, fIb] <;> try rfl
  · rename_i j₁ j
    split_ifs with h
    · have e : (⟨j.val % pA s, Nat.mod_lt _ (pA_pos s)⟩ : Fin (pA s)) = j₁ := Fin.ext h
      subst e; rfl
    · rfl
  · rename_i j j₁
    split_ifs with h
    · have e : (⟨j.val % pA s, Nat.mod_lt _ (pA_pos s)⟩ : Fin (pA s)) = j₁ := Fin.ext h
      subst e; rfl
    · rfl
  · rename_i j j'
    by_cases h1 : j'.val = j.val + 1
    · rw [if_pos h1, if_neg (by omega), if_pos h1]
      rw [h1]; rfl
    · by_cases h2 : j.val = j'.val + 1
      · rw [if_neg h1, if_pos h2, if_pos h2, h2]; rfl
      · rw [if_neg h1, if_neg h2, if_neg h2, if_neg h1]

theorem mW_faP_one [Nontrivial R] (N k x : ℕ) (r : Fin (pA s)) (u : mS s (.faP r)) :
    mW (R := R) s N k x (.faP r) u = 1 ↔ preOK s k x r u ∧ (r.val = 0 → x < 2 ^ (pL s * pL s - k)) := by
  simp only [mW]; split_ifs with h
  · exact iff_of_true rfl h
  · exact iff_of_false zero_ne_one h

theorem mW_carry_one [Nontrivial R] (N k x : ℕ) (j : Fin (pA s * pA s)) (z : mS s (.carry j)) :
    mW (R := R) s N k x (.carry j) z = 1 ↔
      ((z.2.val + z.1.val) % 2 ^ pL s = dgt (pL s) N j ∧ (j.val = 0 → z.2.val = 0) ∧
        (j.val + 1 = pA s * pA s → (z.2.val + z.1.val) / 2 ^ pL s = 0)) := by
  simp only [mW]; split_ifs with h
  · exact iff_of_true rfl h
  · exact iff_of_false zero_ne_one h

theorem good_asm_iff [Nontrivial R] (N k x : ℕ) (zP zQ : DigS s) :
    (mulG s R N k x).Good (asm s zP zQ) ↔ FAOK s k x zP ∧ CarryOK s N zP zQ := by
  unfold GNet.Good
  constructor
  · rintro ⟨hW, -⟩
    refine ⟨fun r => (mW_faP_one s N k x r _).mp (hW (.faP r)), fun j hj => ?_⟩
    have := (mW_carry_one s N k x ⟨j, hj⟩ _).mp (hW (.carry ⟨j, hj⟩))
    exact ⟨this.1, this.2.2⟩
  · rintro ⟨hF, hC⟩
    refine ⟨fun i => ?_, asm_agree s zP zQ⟩
    cases i with
    | faP r => exact (mW_faP_one s N k x r _).mpr (hF r)
    | faQ r => rfl
    | mid k => rfl
    | ib j => rfl
    | carry j =>
        exact (mW_carry_one s N k x j _).mpr
          ⟨(hC j.val j.isLt).1, fun h => by show carF s zP zQ j = 0; rw [h]; rfl, (hC j.val j.isLt).2⟩

/-! ### The count -/

/-- The digits of `d` laid out over the input gates. -/
def dig (d : ℕ) : DigS s := fun r i' => ⟨dgt (pL s) d (r + pA s * i'), dgt_lt _ _ _⟩

theorem digN_dig (d : ℕ) (hd : d < 2 ^ (pL s * pL s)) : digN s (dig s d) = dgt (pL s) d := by
  funext i
  unfold digN
  split_ifs with h
  · simp only [dig]; rw [Nat.mod_add_div]
  · exact (dgt_eq_zero_of_lt hd (by omega)).symm

theorem numOf_dig (d : ℕ) (hd : d < 2 ^ (pL s * pL s)) : numOf (pL s) (digN s (dig s d)) (pL s) = d := by
  rw [digN_dig s d hd]; exact numOf_dgt _ _ _ hd

theorem dig_numOf (zP : DigS s) : dig s (numOf (pL s) (digN s zP) (pL s)) = zP := by
  funext r i'
  apply Fin.ext
  simp only [dig]
  rw [dgt_numOf _ _ _ (digN_lt s zP), if_pos (slot_lt s r i'), digN_slot]

open Classical in
theorem good_card [Nontrivial R] (N k x : ℕ) (hN1 : 1 ≤ N) (hN : N < 2 ^ (pL s * pL s)) :
    (univ.filter (mulG s R N k x).Good).card = (N.divisors.filter (fun d => d / 2 ^ k = x)).card := by
  have hNd : ∀ d, d ∣ N → d < 2 ^ (pL s * pL s) := fun d hd =>
    lt_of_le_of_lt (Nat.le_of_dvd (by omega) hd) hN
  refine card_nbij' (fun z => numOf (pL s) (digN s (fun r => z (.faP r))) (pL s))
    (fun d => asm s (dig s d) (dig s (N / d))) ?_ ?_ ?_ ?_
  · intro z hz
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hz
    have hpin := good_pinned s N k x z hz
    rw [hpin] at hz
    obtain ⟨hF, hC⟩ := (good_asm_iff s N k x _ _).mp hz
    replace hC := (carryOK_iff s N hN _ _).mp hC
    simp only [coe_filter, Nat.mem_divisors, Set.mem_ofPred_eq]
    exact ⟨⟨Dvd.intro _ hC, by omega⟩, (faOK_iff s k x _).mp hF⟩
  · intro d hd
    simp only [coe_filter, Nat.mem_divisors, Set.mem_ofPred_eq] at hd
    obtain ⟨⟨hdN, -⟩, hx⟩ := hd
    simp only [coe_filter, mem_univ, true_and]
    show (mulG s R N k x).Good _
    rw [good_asm_iff, faOK_iff, carryOK_iff s N hN, numOf_dig s d (hNd d hdN),
      numOf_dig s (N / d) (hNd _ (Nat.div_dvd_of_dvd hdN))]
    exact ⟨hx, Nat.mul_div_cancel' hdN⟩
  · intro z hz
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hz
    have hpin := good_pinned s N k x z hz
    have hz' := hz
    rw [hpin] at hz'
    obtain ⟨-, hC⟩ := (good_asm_iff s N k x _ _).mp hz'
    replace hC := (carryOK_iff s N hN _ _).mp hC
    have hp0 : 0 < numOf (pL s) (digN s fun r => z (.faP r)) (pL s) := by
      rcases Nat.eq_zero_or_pos (numOf (pL s) (digN s fun r => z (.faP r)) (pL s)) with h | h
      · rw [h, zero_mul] at hC; omega
      · exact h
    have hq : N / numOf (pL s) (digN s fun r => z (.faP r)) (pL s) =
        numOf (pL s) (digN s fun r => z (.faQ r)) (pL s) := by
      rw [← hC, Nat.mul_div_cancel_left _ hp0]
    show asm s (dig s (numOf (pL s) (digN s (fun r => z (.faP r))) (pL s))) (dig s (N / _)) = z
    rw [hq]
    exact (congrArg₂ (asm s) (dig_numOf s _) (dig_numOf s _)).trans hpin.symm
  · intro d hd
    simp only [coe_filter, Nat.mem_divisors, Set.mem_ofPred_eq] at hd
    show numOf (pL s) (digN s (dig s d)) (pL s) = d
    exact numOf_dig s d (hNd d hd.1.1)

/-- **The value of the multiplication network** is the number of divisors `d` of `N` with `d / 2^k = x`, for
`1 ≤ N < 2^(L·L)`. -/
theorem mulNet_value (N k x : ℕ) (hN1 : 1 ≤ N) (hN : N < 2 ^ (pL s * pL s)) :
    (mulNet s R N k x).value = ((N.divisors.filter (fun d => d / 2 ^ k = x)).card : R) := by
  rcases subsingleton_or_nontrivial R with h | h
  · exact Subsingleton.elim _ _
  · unfold mulNet
    rw [GNet.value_toNet _ _ (mW_01 s N k x) (mV_lt s)]
    congr 1
    convert good_card (R := R) s N k x hN1 hN

end Count

end Factoring.Aux
