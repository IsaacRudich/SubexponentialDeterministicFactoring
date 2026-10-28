/-
The counting expression's value (`BitSpec.val`): the chain modulo every `2 ≤ m ≤ 2M` (`topE`), compared with the
multiplier times the contribution of the divisor `1`, decides whether some divisor `d ≥ 2` has the prescribed high
bits.

* `count_split`: the divisors with high bits `x` are the counted ones (`cntPre`, `d ≥ 2`) and possibly `1`;
* `mlogN`, `deepMult_le`: a bound `deepMult ≤ 2^mlogN` (to choose `M`);
* the expressions `c1E`, `multE`, `dmE`, `mlE`, **`mainE`**, and **`eval_mainE`**.

Not an audit surface.
-/
module

public import FactoringAux.EngineTop
public import FactoringAux.Moduli
public import FactoringAux.Search

@[expose] public section

namespace Factoring.Aux

open Finset Ex

/-! ### Counting -/

theorem count_split (N k x : ℕ) (hN : 1 ≤ N) :
    (N.divisors.filter (fun d => d / 2 ^ k = x)).card = cntPre N k x + if 1 / 2 ^ k = x then 1 else 0 := by
  unfold cntPre
  rw [← Finset.card_filter_add_card_filter_not (s := N.divisors.filter (fun d => d / 2 ^ k = x)) (fun d => 2 ≤ d)]
  congr 1
  · rw [Finset.filter_filter]; congr 1; ext d; simp [and_comm]
  · rw [Finset.filter_filter]
    have : (N.divisors.filter (fun d => d / 2 ^ k = x ∧ ¬ 2 ≤ d)) = if 1 / 2 ^ k = x then {1} else ∅ := by
      ext d
      simp only [Finset.mem_filter, Nat.mem_divisors]
      split_ifs with h
      · simp only [Finset.mem_singleton]
        constructor
        · rintro ⟨⟨hd, hN0⟩, -, h2⟩
          have : d ≠ 0 := fun h0 => by subst h0; simp at hd; omega
          omega
        · rintro rfl; exact ⟨⟨one_dvd _, by omega⟩, h, by omega⟩
      · simp only [Finset.notMem_empty, iff_false]
        rintro ⟨⟨hd, hN0⟩, hx, h2⟩
        have : d ≠ 0 := fun h0 => by subst h0; simp at hd; omega
        exact h (by rw [show d = 1 by omega] at hx; exact hx)
    rw [this]; split_ifs <;> simp

/-! ### A bound on the multiplier -/

theorem nonRects_le (G : ℕ) : nonRects G ≤ G ^ 4 := by
  unfold nonRects
  calc _ ≤ (univ : Finset (Quad G)).card := Finset.card_filter_le _ _
    _ = G ^ 4 := by simp [Fintype.card_prod]; ring

theorem rects_le (G : ℕ) : (rects G).card ≤ G ^ 4 := by
  calc (rects G).card ≤ (univ : Finset (Quad G)).card := Finset.card_le_univ _
    _ = G ^ 4 := by simp [Fintype.card_prod]; ring

theorem mult_le (G L : ℕ) : mult G L ≤ 2 ^ (2 * G ^ 4 * tB L) := by
  unfold mult
  have ht : tB L + 1 ≤ 2 ^ tB L := Nat.lt_two_pow_self
  calc (tB L + 1) ^ nonRects G * 2 ^ (tB L * (rects G).card)
      ≤ (2 ^ tB L) ^ G ^ 4 * 2 ^ (tB L * G ^ 4) := by
        gcongr
        all_goals first | exact ht | exact nonRects_le G | exact rects_le G | exact Nat.one_le_two_pow | norm_num
    _ = 2 ^ (2 * G ^ 4 * tB L) := by rw [← pow_mul, ← pow_add]; congr 1; ring

/-- The exponent bound of the multiplier. -/
def mlogN (K0 : ℕ) : (d L : ℕ) → ℕ
  | 0, _ => 0
  | d + 1, L => 2 * Gs K0 d ^ 4 * tB L + mlogN K0 d (Lnext (Kb K0 d) (Gs K0 d) L)

theorem deepMult_le (K0 : ℕ) : ∀ d L, deepMult K0 d L ≤ 2 ^ mlogN K0 d L
  | 0, _ => by simp [deepMult, mlogN]
  | d + 1, L => by
      simp only [deepMult, mlogN, pow_add]
      exact Nat.mul_le_mul (mult_le _ _) (deepMult_le K0 d _)

/-! ### The expressions -/

namespace Ex

/-- `[k ≥ 1 ∧ x = 0]` (loop variable `8`). -/
def c1E : Ex := .ifLt (.lit 0) (.var 2) (ifEq (nsum 8 (.sub (.var 0) (.var 2)) (xBit (.var 8))) (.lit 0) (.lit 1) (.lit 0))
  (.lit 0)

/-- `mult G L` modulo `m` (`L` in `vL`, loop variable `x`). -/
def multE (G vL vm x : ℕ) : Ex :=
  zmul vm (zprod x (.lit (nonRects G)) vm (.mod (.add (tBE vL) (.lit 1)) (.var vm)))
    (zprod x (.mul (tBE vL) (.lit (rects G).card)) vm (.mod (.lit 2) (.var vm)))

/-- The data of `Lnext` at depth `d`. -/
def lpOf (K0 d vm vL : ℕ) : LP := ⟨0, vm, vL, 0, 0, Kb K0 d, Gs K0 d, .lit 0⟩

/-- `deepMult` modulo `m` (`L` in `vL`, scratch from `b`). -/
def dmE (K0 : ℕ) : (d vL b vm : ℕ) → Ex
  | 0, _, _, _ => .lit 1
  | d + 1, vL, b, vm => zmul vm (multE (Gs K0 d) vL vm b)
      (.lett (b + 1) (LevelEx.LnE (lpOf K0 d vm vL)) (dmE K0 d (b + 1) (b + 2) vm))

/-- `mlogN`. -/
def mlE (K0 : ℕ) : (d vL b : ℕ) → Ex
  | 0, _, _ => .lit 0
  | d + 1, vL, b => .add (.mul (.lit (2 * Gs K0 d ^ 4)) (tBE vL))
      (.lett (b + 1) (LevelEx.LnE (lpOf K0 d 0 vL)) (mlE K0 d (b + 1) (b + 2)))

/-- **The counting expression** (before its block). -/
def mainE (K0 ℓ : ℕ) : Ex :=
  .lett 11 sE (.lett 12 (L0E (Kb K0 ℓ) (Gs K0 ℓ)) (.lett 9 (.add (.add (.var 0) (mlE K0 ℓ 12 30)) (.lit 4))
    (.ifLt (.lit 0) (nsum 10 (.add (.mul (.lit 2) (.var 9)) (.lit 1)) (.ifLt (.var 10) (.lit 2) (.lit 0)
      (ifEq (topE K0 ℓ) (zmul 10 (dmE K0 ℓ 12 30 10) c1E) (.lit 0) (.lit 1)))) (.lit 0) (.lit 1))))

end Ex

variable {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ}

theorem eval_mlE (K0 : ℕ) : ∀ (d vL b L : ℕ) (σ : ℕ → ℕ), vL < b → σ vL = L → eval σ A (mlE K0 d vL b) = mlogN K0 d L
  | 0, _, _, _, _, _, _ => rfl
  | d + 1, vL, b, L, σ, hb, hL => by
      rw [mlE, mlogN, Ex.eval, eval_lett]
      have h1 := LevelEx.eval_LnE (P := lpOf K0 d 0 vL) (A := A) (lam := L) hL
      rw [h1]
      have := eval_mlE K0 d (b + 1) (b + 2) (Lnext (Kb K0 d) (Gs K0 d) L)
        (Function.update σ (b + 1) (Lnext (lpOf K0 d 0 vL).K (lpOf K0 d 0 vL).G L)) (by omega)
        (Function.update_self _ _ _)
      rw [this]
      simp only [Ex.eval, eval_tBE hL]

theorem ZR_dmE {m : ℕ} (hm : 1 < m) (K0 : ℕ) : ∀ (d vL b vm L : ℕ) (σ : ℕ → ℕ), vL < b → vm < b → σ vm = m →
    σ vL = L → ZR m (eval σ A (dmE K0 d vL b vm)) (deepMult K0 d L : ZMod m)
  | 0, _, _, _, _, _, _, _, _, _ => by simp only [dmE, deepMult, Nat.cast_one]; exact ZR_one hm
  | d + 1, vL, b, vm, L, σ, hb, hvb, hm', hL => by
      rw [dmE, deepMult, Nat.cast_mul]
      refine ZR_zmul hm' (by omega) ?_ ?_
      · unfold multE mult
        rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_pow]
        refine ZR_zmul hm' (by omega) ?_ ?_
        · rw [show ((tB L + 1 : ℕ) : ZMod m) ^ nonRects (Gs K0 d) =
              ∏ j ∈ range (nonRects (Gs K0 d)), ((tB L + 1 : ℕ) : ZMod m) by simp]
          refine ZR_zprod hm' hm b rfl _ fun j _ => ?_
          have hv : Function.update σ b j vm = m := by rw [Function.update_of_ne (by omega)]; exact hm'
          have hl : Function.update σ b j vL = L := by rw [Function.update_of_ne (by omega)]; exact hL
          simp only [Ex.eval, eval_tBE hl, hv]
          exact ZR_mod (by omega)
        · rw [show ((2 : ℕ) : ZMod m) ^ (tB L * (rects (Gs K0 d)).card) =
              ∏ j ∈ range (tB L * (rects (Gs K0 d)).card), ((2 : ℕ) : ZMod m) by simp]
          refine ZR_zprod hm' hm b (by simp only [Ex.eval, eval_tBE hL]) _ fun j _ => ?_
          have hv : Function.update σ b j vm = m := by rw [Function.update_of_ne (by omega)]; exact hm'
          simp only [Ex.eval, hv]
          exact ZR_mod (by omega)
      · rw [eval_lett, LevelEx.eval_LnE (P := lpOf K0 d vm vL) (lam := L) hL]
        exact ZR_dmE hm K0 d (b + 1) (b + 2) vm (Lnext (Kb K0 d) (Gs K0 d) L) _ (by omega) (by omega)
          (by rw [Function.update_of_ne (by omega)]; exact hm') (Function.update_self _ _ _)

theorem eval_c1E (hD : A 1 (σ 2) = 0) (hkn : σ 2 < σ 0) :
    eval σ A c1E = if 1 / 2 ^ σ 2 = numCells (A 1) (σ 2) (σ 0 - σ 2) then 1 else 0 := by
  set x := numCells (A 1) (σ 2) (σ 0 - σ 2)
  have hx0 : x.testBit 0 = false := by
    rw [testBit_numCells _ _ _ _ (by omega)]; simp [hD]
  have hxlt : x < 2 ^ (σ 0 - σ 2) := numCells_lt _ _ _
  rw [c1E, eval_ifLt']
  have hk : eval σ A (.var 2) = σ 2 := rfl
  rw [hk, show eval σ A (.lit 0) = 0 from rfl]
  by_cases hk0 : 0 < σ 2
  · rw [if_pos hk0, eval_ifEq, eval_nsum]
    have hdiv : 1 / 2 ^ σ 2 = 0 := Nat.div_eq_of_lt (Nat.one_lt_two_pow (by omega))
    rw [hdiv]
    have hsum : (∑ j ∈ range (eval σ A (.sub (.var 0) (.var 2))), eval (Function.update σ 8 j) A (xBit (.var 8))) =
        eval σ A (.lit 0) ↔ x = 0 := by
      show _ = 0 ↔ _
      simp only [Ex.eval, eval_xBit]
      simp only [Function.update_of_ne (show (0 : ℕ) ≠ 8 by norm_num), Function.update_of_ne (show (2 : ℕ) ≠ 8 by norm_num),
        Function.update_self]
      rw [Finset.sum_eq_zero_iff]
      constructor
      · intro h
        apply Nat.eq_of_testBit_eq
        intro j
        rw [Nat.zero_testBit]
        by_cases hj : j < σ 0 - σ 2
        · exact Bool.toNat_eq_zero.mp (h j (mem_range.mpr hj))
        · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hxlt (Nat.pow_le_pow_right (by norm_num) (by omega)))
      · intro h j _
        simp only [show numCells (A 1) (σ 2) (σ 0 - σ 2) = 0 from h, Nat.zero_testBit]
        rfl
    by_cases hx : x = 0
    · rw [if_pos (hsum.mpr hx), if_pos hx.symm]; rfl
    · rw [if_neg (fun h => hx (hsum.mp h)), if_neg (fun h => hx h.symm)]; rfl
  · rw [if_neg hk0]
    have hk0' : σ 2 = 0 := by omega
    have : ¬ 1 / 2 ^ σ 2 = x := by
      rw [hk0', pow_zero, Nat.div_one]
      intro h; rw [← h] at hx0; simp at hx0
    rw [if_neg this]

theorem two_pow_big (y : ℕ) : 2 * y + 9 ≤ 2 ^ (y + 8) := by
  have := Nat.lt_two_pow_self (n := y)
  calc 2 * y + 9 ≤ 256 * 2 ^ y := by omega
    _ = 2 ^ (y + 8) := by rw [pow_add]; ring

/-- **The value of the counting expression.** -/
theorem eval_mainE (K0 ℓ : ℕ) (hK : 2 ≤ K0) (hkn : σ 2 < σ 0) (hN : 2 ≤ numCells (A 0) 1 (σ 0))
    (hD : A 1 (σ 2) = 0) :
    eval σ A (mainE K0 ℓ) = if 0 < cntPre (numCells (A 0) 1 (σ 0)) (σ 2) (numCells (A 1) (σ 2) (σ 0 - σ 2))
      then 0 else 1 := by
  set n := σ 0
  set k := σ 2
  set N := numCells (A 0) 1 n
  set x := numCells (A 1) k (n - k)
  set c := cntPre N k x
  set c1 : ℕ := if 1 / 2 ^ k = x then 1 else 0
  set L := Ltop (Kb K0 ℓ) (Gs K0 ℓ) (sOf n)
  set D := deepMult K0 ℓ L
  set M := n + mlogN K0 ℓ L + 4
  have hsplit := count_split N k x (by omega)
  rw [mainE, eval_lett, eval_sE, eval_lett, eval_L0E (s := sOf n) (by simp; rfl), eval_lett]
  set σ3 := Function.update (Function.update (Function.update σ 11 (sOf n)) 12 L) 9
    (eval (Function.update (Function.update σ 11 (sOf n)) 12 L) A (.add (.add (.var 0) (mlE K0 ℓ 12 30)) (.lit 4)))
  have hM : σ3 9 = M := by
    simp only [σ3, Function.update_self, Ex.eval]
    rw [eval_mlE K0 ℓ 12 30 L _ (by norm_num) (by simp)]
    simp; rfl
  -- the summand at a modulus
  have hbody : ∀ m, eval (Function.update σ3 10 m) A (.ifLt (.var 10) (.lit 2) (.lit 0)
      (ifEq (topE K0 ℓ) (zmul 10 (dmE K0 ℓ 12 30 10) c1E) (.lit 0) (.lit 1))) =
      if 2 ≤ m ∧ ¬ m ∣ D * c then 1 else 0 := by
    intro m
    set σm := Function.update σ3 10 m
    have e10 : σm 10 = m := by simp [σm]
    have e0 : σm 0 = n := by show Function.update σ3 10 m 0 = σ 0; simp [σ3]
    have e2 : σm 2 = k := by show Function.update σ3 10 m 2 = σ 2; simp [σ3]
    rw [eval_ifLt', show eval σm A (.var 10) = m from e10, show eval σm A (.lit 2) = 2 from rfl]
    by_cases hm2 : m < 2
    · rw [if_pos hm2, if_neg (by omega)]; rfl
    rw [if_neg hm2, eval_ifEq]
    have hm : 1 < m := by omega
    have hV := top_rep (σ := σm) (A := A) K0 ℓ hK hm e10 e0 e2 hkn.le (by omega)
    have hR : ZR m (eval σm A (zmul 10 (dmE K0 ℓ 12 30 10) c1E)) ((D : ZMod m) * (c1 : ZMod m)) := by
      refine ZR_zmul e10 (by omega) (ZR_dmE hm K0 ℓ 12 30 10 L σm (by norm_num) (by norm_num) e10
        (by simp [σm, σ3])) ?_
      rw [eval_c1E (by rw [e2]; exact hD) (by rw [e2, e0]; exact hkn), e2, e0]
      exact ⟨by split_ifs <;> omega, rfl⟩
    have key : eval σm A (topE K0 ℓ) = eval σm A (zmul 10 (dmE K0 ℓ 12 30 10) c1E) ↔ m ∣ D * c := by
      rw [← ZMod.natCast_eq_zero_iff, Nat.cast_mul]
      constructor
      · intro h
        have := hV.2.symm.trans ((congrArg (fun v : ℕ => (v : ZMod m)) h).trans hR.2)
        rw [hsplit, Nat.cast_add] at this
        linear_combination this
      · intro h
        have h1 : ((D : ZMod m) * ((N.divisors.filter (fun d => d / 2 ^ k = x)).card : ZMod m)) = D * c1 := by
          rw [hsplit, Nat.cast_add]; linear_combination h
        have h2 := hV.2.trans (h1.trans hR.2.symm)
        rw [← ZMod.val_natCast_of_lt hV.1, h2, ZMod.val_natCast_of_lt hR.1]
    by_cases hd : m ∣ D * c
    · rw [if_pos (key.mpr hd), if_neg (fun h => h.2 hd)]; rfl
    · rw [if_neg (fun h => hd (key.mp h)), if_pos ⟨by omega, hd⟩]; rfl
  rw [eval_ifLt', eval_nsum, show eval σ3 A (.add (.mul (.lit 2) (.var 9)) (.lit 1)) = 2 * M + 1 by
    simp only [Ex.eval, hM]]
  simp only [hbody]
  rw [show eval σ3 A (.lit 0) = 0 from rfl, show eval σ3 A (.lit 1) = 1 from rfl]
  have hD0 : 0 < D := deepMult_pos K0 ℓ L
  by_cases hc : c = 0
  · have hz : ∑ m ∈ range (2 * M + 1), (if 2 ≤ m ∧ ¬ m ∣ D * c then 1 else 0) = 0 :=
      Finset.sum_eq_zero fun m _ => by rw [if_neg (fun h => h.2 (by rw [hc, mul_zero]; exact dvd_zero m))]
    rw [hz, if_neg (lt_irrefl 0), if_neg (by omega)]
  · rw [if_pos (Nat.pos_of_ne_zero hc)]
    refine if_pos (Nat.pos_of_ne_zero fun hs => ?_)
    rw [Finset.sum_eq_zero_iff] at hs
    have hall : ∀ m, 1 ≤ m → m ≤ 2 * M → m ∣ D * c := by
      intro m h1 h2
      rcases Nat.lt_or_ge m 2 with h | h
      · rw [show m = 1 by omega]; exact one_dvd _
      · by_contra hnd
        have := hs m (mem_range.mpr (by omega))
        rw [if_pos ⟨h, hnd⟩] at this
        exact one_ne_zero this
    have hcN : c ≤ N := le_trans (Finset.card_le_card (Finset.filter_subset _ _)) (Nat.card_divisors_le_self N)
    have hNn : N < 2 ^ n := numCells_lt _ _ _
    have hDl : D ≤ 2 ^ mlogN K0 ℓ L := deepMult_le K0 ℓ L
    have hlt : (2 * M + 1) * (D * c) < 4 ^ M := by
      have h1 : D * c < 2 ^ (n + mlogN K0 ℓ L) := by
        rw [pow_add]
        calc D * c ≤ 2 ^ mlogN K0 ℓ L * N := Nat.mul_le_mul hDl hcN
          _ < 2 ^ mlogN K0 ℓ L * 2 ^ n := Nat.mul_lt_mul_of_pos_left hNn (by positivity)
          _ = 2 ^ n * 2 ^ mlogN K0 ℓ L := by ring
      have h2 := two_pow_big (n + mlogN K0 ℓ L)
      calc (2 * M + 1) * (D * c) < (2 * M + 1) * 2 ^ (n + mlogN K0 ℓ L) :=
            Nat.mul_lt_mul_of_pos_left h1 (by omega)
        _ ≤ 2 ^ (n + mlogN K0 ℓ L + 8) * 2 ^ (n + mlogN K0 ℓ L) :=
            Nat.mul_le_mul_right _ (by simp only [M]; omega)
        _ = 4 ^ M := by
            rw [← pow_add, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]; congr 1; simp only [M]; ring
    have h0 := eq_zero_of_all_dvd (by omega) hall hlt
    rcases Nat.mul_eq_zero.mp h0 with h | h
    · omega
    · exact hc h

theorem mainE_le_one (K0 ℓ : ℕ) (σ : ℕ → ℕ) (A : ℕ → ℕ → ℕ) : eval σ A (mainE K0 ℓ) ≤ 1 := by
  rw [mainE, eval_lett, eval_lett, eval_lett, eval_ifLt']
  split_ifs <;> simp [Ex.eval]

end Factoring.Aux
