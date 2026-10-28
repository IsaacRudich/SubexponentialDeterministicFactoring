/-
The multiplication network as expressions: value bounds and variables.

* Generic `Bdd` lemmas for the constructors (`B_ifLt`, `B_pow2`, `B_nprodK`, `B_nprod01`, `B_nsum`, `B_sum_mod`,
  `B_prod_mod`).
* With `P = 2^L`: every value met is at most `P^(16 A) = 2^(16 L A)` (`mulV`).
* **`mul_bdd`**, **`mul_vb`** (binders below `u + 7`), **`mul_fv`**.

Not an audit surface.
-/
module

public import FactoringAux.EngineMulRep

@[expose] public section

namespace Factoring.Aux

open Finset Ex MulEx

/-! ### Generic bounds -/

section Gen

variable {V : ℕ} {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ}

theorem B_ifLt {e f a b : Ex} (h1 : Bdd V σ A e) (h2 : Bdd V σ A f) (h3 : eval σ A e < eval σ A f → Bdd V σ A a)
    (h4 : ¬ eval σ A e < eval σ A f → Bdd V σ A b) : Bdd V σ A (.ifLt e f a b) := by
  refine ⟨h1, h2, ?_⟩
  split_ifs with h
  · exact h3 h
  · exact h4 h

theorem B_ifEq {e f a b : Ex} (h1 : Bdd V σ A e) (h2 : Bdd V σ A f) (h3 : Bdd V σ A a) (h4 : Bdd V σ A b) :
    Bdd V σ A (ifEq e f a b) :=
  B_ifLt h1 h2 (fun _ => h4) (fun _ => B_ifLt h2 h1 (fun _ => h4) (fun _ => h3))

theorem B_eqE {e f : Ex} (h1 : Bdd V σ A e) (h2 : Bdd V σ A f) (hV : 1 ≤ V) : Bdd V σ A (eqE e f) :=
  B_ifLt h1 h2 (fun _ => Nat.zero_le V) (fun _ => B_ifLt h2 h1 (fun _ => Nat.zero_le V) (fun _ => hV))

theorem eqE_le (e f : Ex) : eval σ A (eqE e f) ≤ 1 := by rw [eval_eqE]; split_ifs <;> omega

theorem B_pow2 {x : ℕ} {e : Ex} (he : Bdd V σ A e) (h2 : 2 ≤ V) (hV : 2 ^ eval σ A e ≤ V) :
    Bdd V σ A (pow2 x e) := by
  refine ⟨he, Nat.zero_le V, fun _ _ => h2, fun j hj => ?_⟩
  change foldProd (fun _ => 2) 0 j ≤ V
  rw [foldProd_zero, pp_const]
  exact le_trans (Nat.pow_le_pow_right (by norm_num) hj) hV

theorem B_nprodK {x : ℕ} {n b : Ex} {c : ℕ} (hn : Bdd V σ A n)
    (hb : ∀ j < eval σ A n, Bdd V (Function.update σ x j) A b ∧ eval (Function.update σ x j) A b = c)
    (hc : 1 ≤ c) (hV : c ^ eval σ A n ≤ V) : Bdd V σ A (nprod x n b) := by
  refine ⟨hn, Nat.zero_le V, fun j hj => (hb j hj).1, fun j hj => ?_⟩
  change foldProd _ 0 j ≤ V
  rw [foldProd_zero, pp_congr (f' := fun _ => c) (fun i hi => (hb i (by omega)).2), pp_const]
  exact le_trans (Nat.pow_le_pow_right hc hj) hV

theorem pp_le_one {f : ℕ → ℕ} : ∀ {n : ℕ}, (∀ i < n, f i ≤ 1) → pp f n ≤ 1
  | 0, _ => le_rfl
  | n + 1, h => by
      have h1 := pp_le_one (n := n) fun i hi => h i (by omega)
      have h2 := h n (by omega)
      simp only [pp]
      exact le_trans (Nat.mul_le_mul h1 h2) (by norm_num)

theorem B_nprod01 {x : ℕ} {n b : Ex} (hn : Bdd V σ A n)
    (hb : ∀ j < eval σ A n, Bdd V (Function.update σ x j) A b ∧ eval (Function.update σ x j) A b ≤ 1)
    (hV : 1 ≤ V) : Bdd V σ A (nprod x n b) := by
  refine ⟨hn, Nat.zero_le V, fun j hj => (hb j hj).1, fun j hj => ?_⟩
  change foldProd _ 0 j ≤ V
  rw [foldProd_zero]
  exact le_trans (pp_le_one fun i hi => (hb i (by omega)).2) hV

theorem B_nsum {x : ℕ} {n b : Ex} (hn : Bdd V σ A n) (hb : ∀ j < eval σ A n, Bdd V (Function.update σ x j) A b)
    (hV : ∑ i ∈ range (eval σ A n), eval (Function.update σ x i) A b ≤ V) : Bdd V σ A (nsum x n b) := by
  refine ⟨hn, Nat.zero_le V, hb, fun j hj => ?_⟩
  change foldSum _ 0 j ≤ V
  rw [foldSum_zero]
  exact le_trans (sum_le_sum_of_subset (range_subset_range.mpr hj)) hV

theorem B_sum_mod {x : ℕ} {n m b : Ex} (hn : Bdd V σ A n) (hm : Bdd V σ A m) (hM : 0 < eval σ A m)
    (hMV : eval σ A m ≤ V) (hb : ∀ j < eval σ A n, Bdd V (Function.update σ x j) A b) :
    Bdd V σ A (.sum x n m b) := by
  refine ⟨hn, hm, hb, fun j _ => ?_⟩
  rw [foldSum_eq]
  exact le_trans (Nat.mod_lt _ hM).le hMV

theorem B_prod_mod {x : ℕ} {n m b : Ex} (hn : Bdd V σ A n) (hm : Bdd V σ A m) (hM : 0 < eval σ A m)
    (hMV : eval σ A m ≤ V) (h1 : 1 ≤ V) (hb : ∀ j < eval σ A n, Bdd V (Function.update σ x j) A b) :
    Bdd V σ A (.prod x n m b) := by
  refine ⟨hn, hm, hb, fun j _ => ?_⟩
  rcases Nat.eq_zero_or_pos j with h0 | h0
  · subst h0; exact h1
  · rw [foldProd_eq _ _ _ h0]
    exact le_trans (Nat.mod_lt _ hM).le hMV

theorem B_xBit {j : Ex} (hj : Bdd V σ A j) (h2 : σ 2 ≤ V) (h0 : σ 0 ≤ V) (hjV : eval σ A j + σ 2 ≤ V)
    (hA : ∀ a i, A a i ≤ 1) (h1 : 1 ≤ V) : Bdd V σ A (xBit j) :=
  B_ifLt ⟨hj, h2, hjV⟩ h0
    (fun _ => B_ifLt (Nat.zero_le V) ⟨⟨hj, h2, hjV⟩, le_trans (hA _ _) h1⟩ (fun _ => h1) (fun _ => Nat.zero_le V))
    (fun _ => Nat.zero_le V)

theorem B_nBit {i : Ex} (hi : Bdd V σ A i) (h0 : σ 0 ≤ V) (hiV : eval σ A i + 1 ≤ V)
    (hA : ∀ a i, A a i ≤ 1) (h1 : 1 ≤ V) : Bdd V σ A (nBit i) :=
  B_ifLt hi h0
    (fun _ => B_ifLt (Nat.zero_le V) ⟨⟨hi, h1, hiV⟩, le_trans (hA _ _) h1⟩ (fun _ => h1) (fun _ => Nat.zero_le V))
    (fun _ => Nat.zero_le V)

theorem nBit_le (i : Ex) : eval σ A (nBit i) ≤ 1 := by
  rw [eval_nBit]; cases Nat.testBit _ _ <;> simp

end Gen

/-! ### Sizes, with `P = 2^L` -/

section Num

variable (s : ℕ)

theorem two_le_pA : 2 ≤ pA s := by
  unfold pA; calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ (s + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem pA_le_pL : pA s ≤ pL s := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem ph_le_pA : ph s ≤ pA s := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem s_lt_pL : s < pL s := lt_of_lt_of_le (Nat.lt_two_pow_self) (Nat.pow_le_pow_right (by norm_num) (by omega))

theorem pL_lt_P : pL s < 2 ^ pL s := Nat.lt_two_pow_self

theorem four_le_P : 4 ≤ 2 ^ pL s := by
  have : 2 ≤ pL s := le_trans (two_le_pA s) (pA_le_pL s)
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ _ := Nat.pow_le_pow_right (by norm_num) this

theorem one_le_P : 1 ≤ 2 ^ pL s := by have := four_le_P s; omega

theorem P_mono {x a b : ℕ} (h : x ≤ (2 ^ pL s) ^ a) (hab : a ≤ b) : x ≤ (2 ^ pL s) ^ b :=
  le_trans h (Nat.pow_le_pow_right (one_le_P s) hab)

theorem P_mul {x y a b : ℕ} (hx : x ≤ (2 ^ pL s) ^ a) (hy : y ≤ (2 ^ pL s) ^ b) :
    x * y ≤ (2 ^ pL s) ^ (a + b) := by
  rw [pow_add]; exact Nat.mul_le_mul hx hy

theorem P_add {x y a : ℕ} (hx : x ≤ (2 ^ pL s) ^ a) (hy : y ≤ (2 ^ pL s) ^ a) :
    x + y ≤ (2 ^ pL s) ^ (a + 1) := by
  rw [pow_succ]; have := four_le_P s; nlinarith

theorem P_one {x : ℕ} (hx : x ≤ 2 ^ pL s) : x ≤ (2 ^ pL s) ^ 1 := by rw [pow_one]; exact hx

theorem pA_P : pA s ≤ (2 ^ pL s) ^ 1 := P_one s (le_trans (pA_le_pL s) (pL_lt_P s).le)
theorem pL_P : pL s ≤ (2 ^ pL s) ^ 1 := P_one s (pL_lt_P s).le
theorem ph_P : ph s ≤ (2 ^ pL s) ^ 1 := P_mono s (pA_P s) le_rfl |>.trans' (ph_le_pA s)
theorem s_P : s ≤ (2 ^ pL s) ^ 1 := le_trans (s_lt_pL s).le (pL_P s)
theorem small_P {c : ℕ} (hc : c ≤ 4) : c ≤ (2 ^ pL s) ^ 1 := le_trans hc (by rw [pow_one]; exact four_le_P s)

theorem nodes_P : mulNodes s ≤ (2 ^ pL s) ^ 4 := by
  unfold mulNodes
  have h1 := pA_P s
  have h4 := small_P s (c := 4) le_rfl
  have : pA s + (pA s + (pA s + (pA s + pA s * pA s))) = 4 * pA s + pA s * pA s := by ring
  rw [this]
  exact P_mono s (P_add s (P_mul s h4 h1) (P_mul s h1 h1)) (by norm_num)

theorem pM_P : pM s ≤ (2 ^ pL s) ^ 5 := by
  have h1 : pM s ≤ 2 ^ (pm s + 1) := by simp only [pM, pow_succ]; have : 1 ≤ 2 ^ pm s := Nat.one_le_two_pow; omega
  refine le_trans h1 ?_
  rw [← pow_mul]; exact Nat.pow_le_pow_right (by norm_num) (by unfold pm; have := pL_pos s; omega)

theorem fw_pow_P : 2 ^ fw s ≤ (2 ^ pL s) ^ 5 := by
  rw [← pow_mul]; exact Nat.pow_le_pow_right (by norm_num) (by unfold fw pm; have := pL_pos s; omega)

theorem fw_P : fw s ≤ (2 ^ pL s) ^ 5 := le_trans Nat.lt_two_pow_self.le (fw_pow_P s)

theorem pZ_P : pZ s ≤ (2 ^ pL s) ^ (5 * pA s) := by
  rw [pZ, pp_const, pow_mul]; exact Nat.pow_le_pow_left (pM_P s) _

theorem pD_P : pD s ≤ (2 ^ pL s) ^ pA s := by
  rw [pD, pp_const]; exact Nat.pow_le_pow_right (one_le_P s) (ph_le_pA s)

theorem fourL_P : 4 * pL s ≤ (2 ^ pL s) ^ 2 := P_mul s (small_P s le_rfl) (pL_P s)

end Num

/-! ### Constants and residues -/

section Cst

variable {V s u vs : ℕ} {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ}

theorem PV (hV : (2 ^ pL s) ^ (16 * pA s) ≤ V) {x a : ℕ} (hx : x ≤ (2 ^ pL s) ^ a) (ha : a ≤ 32) : x ≤ V :=
  le_trans (P_mono s hx (by have := two_le_pA s; omega)) hV

variable (hV : (2 ^ pL s) ^ (16 * pA s) ≤ V)
include hV

theorem V_ge {c : ℕ} (hc : c ≤ 4) : c ≤ V := PV hV (small_P s hc) (by norm_num)
theorem V_ge16 : 16 ≤ V := PV hV (a := 2) (by have := four_le_P s; nlinarith) (by norm_num)

theorem pM_le_V : pM s ≤ V := PV hV (pM_P s) (by norm_num)

theorem MM_le : pM s * pM s ≤ V := PV hV (P_mul s (pM_P s) (pM_P s)) (by norm_num)

variable (h : σ vs = s)
include h

theorem B_vs : Bdd V σ A (.var vs) := show σ vs ≤ V by rw [h]; exact PV hV (s_P s) (by norm_num)

theorem B_hE : Bdd V σ A (hE u vs) :=
  B_pow2 (B_vs hV h) (V_ge hV (by norm_num)) (by show 2 ^ σ vs ≤ V; rw [h]; exact PV hV (ph_P s) (by norm_num))

theorem B_AE : Bdd V σ A (AE u vs) :=
  B_pow2 ⟨B_vs hV h, V_ge hV (by norm_num), by
      show σ vs + 1 ≤ V; rw [h]; exact PV hV (P_add s (s_P s) (small_P s (by norm_num))) (by norm_num)⟩
    (V_ge hV (by norm_num)) (by show 2 ^ (σ vs + 1) ≤ V; rw [h]; exact PV hV (pA_P s) (by norm_num))

theorem B_LLE : Bdd V σ A (LLE u vs) :=
  B_pow2 ⟨⟨V_ge hV (by norm_num), B_vs hV h, by
      show 2 * σ vs ≤ V; rw [h]; exact PV hV (P_mul s (small_P s (by norm_num)) (s_P s)) (by norm_num)⟩,
    V_ge hV (by norm_num), by
      show 2 * σ vs + 1 ≤ V; rw [h]
      exact PV hV (P_add s (P_mul s (small_P s (by norm_num)) (s_P s)) (P_mono s (small_P s (c := 1) (by norm_num))
        (by norm_num))) (by norm_num)⟩
    (V_ge hV (by norm_num)) (by show 2 ^ (2 * σ vs + 1) ≤ V; rw [h]; exact PV hV (pL_P s) (by norm_num))

theorem B_fwE : Bdd V σ A (fwE u vs) :=
  ⟨⟨V_ge hV le_rfl, B_LLE hV h, by rw [eval_LLE h]; exact PV hV (fourL_P s) (by norm_num)⟩, V_ge hV (by norm_num),
    by simp only [Ex.eval, eval_LLE h]; exact PV hV (fw_P s) (by norm_num)⟩

theorem B_ME : Bdd V σ A (ME u vs) :=
  ⟨B_pow2 ⟨V_ge hV le_rfl, B_LLE hV h, by rw [eval_LLE h]; exact PV hV (fourL_P s) (by norm_num)⟩
      (V_ge hV (by norm_num)) (by
        simp only [Ex.eval, eval_LLE h]; exact le_trans (by simp only [pM, pm]; omega) (pM_le_V hV)),
    V_ge hV (by norm_num), by
      have := eval_ME (A := A) (u := u) h; simp only [ME, Ex.eval] at this ⊢; rw [this]; exact pM_le_V hV⟩

theorem B_TLE : Bdd V σ A (TLE u vs) :=
  B_pow2 (B_LLE hV h) (V_ge hV (by norm_num)) (by rw [eval_LLE h]; exact PV hV (P_one s le_rfl) (by norm_num))

theorem B_PfE : Bdd V σ A (PfE u vs) :=
  B_pow2 (B_fwE hV h) (V_ge hV (by norm_num)) (by rw [eval_fwE h]; exact PV hV (fw_pow_P s) (by norm_num))

theorem B_kA {c : ℕ} (hc : c ≤ 4) : Bdd V σ A (kA u vs c) :=
  ⟨V_ge hV hc, B_AE hV h, by rw [eval_AE h]; exact PV hV (P_mul s (small_P s hc) (pA_P s)) (by norm_num)⟩

theorem B_PZE (hvs : vs < u) : Bdd V σ A (PZE u vs) :=
  B_nprodK (B_AE hV h) (fun j _ => ⟨B_ME hV (upd_vs h (by omega) j), eval_ME (upd_vs h (by omega) j)⟩)
    (one_lt_pM s).le (by
      rw [eval_AE h, ← pp_const]
      exact le_trans (pZ_P s) (le_trans (Nat.pow_le_pow_right (one_le_P s) (by omega)) hV))

theorem B_PDE (hvs : vs < u) : Bdd V σ A (PDE u vs) :=
  B_nprodK (B_hE hV h) (fun j _ => ⟨B_TLE hV (upd_vs h (by omega) j), eval_TLE (upd_vs h (by omega) j)⟩)
    Nat.one_le_two_pow (by
      rw [eval_hE h, ← pp_const]; exact le_trans (pD_P s) (le_trans (Nat.pow_le_pow_right (one_le_P s)
        (by have := two_le_pA s; omega)) hV))

theorem B_mM {e f : Ex} (he : Bdd V σ A e) (hf : Bdd V σ A f) (he' : eval σ A e < pM s) (hf' : eval σ A f < pM s) :
    Bdd V σ A (mM u vs e f) :=
  ⟨⟨he, hf, le_trans (Nat.mul_le_mul he'.le hf'.le) (MM_le hV)⟩, B_ME hV h⟩

theorem B_sM {x : ℕ} {n b : Ex} (hn : Bdd V σ A n) (hb : ∀ j < eval σ A n, Bdd V (Function.update σ x j) A b) :
    Bdd V σ A (sM u vs x n b) :=
  B_sum_mod hn (B_ME hV h) (by rw [eval_ME h]; positivity) (by rw [eval_ME h]; exact pM_le_V hV) hb

theorem B_pw {b : ℕ} {e : Ex} (he : Bdd V σ A e) (hb : b ≤ V) : Bdd V σ A (pw u vs b e) :=
  B_prod_mod he (B_ME hV h) (by rw [eval_ME h]; positivity) (by rw [eval_ME h]; exact pM_le_V hV)
    (V_ge hV (by norm_num)) (fun _ _ => hb)

theorem B_pwi {e : Ex} {a : ℕ} (he : Bdd V σ A e) (hE : eval σ A e ≤ (2 ^ pL s) ^ a) (ha : a ≤ 30) :
    Bdd V σ A (pwi u vs e) :=
  B_pw hV h ⟨⟨⟨B_AE hV h, B_AE hV h, by rw [eval_AE h]; exact PV hV (P_mul s (pA_P s) (pA_P s)) (by norm_num)⟩,
      V_ge hV (by norm_num)⟩, he, by
      simp only [Ex.eval, eval_AE h]
      exact PV hV (P_mul s (le_trans (Nat.sub_le _ _) (P_mul s (pA_P s) (pA_P s))) hE) (by omega)⟩ (V_ge16 hV)

theorem B_tE : Bdd V σ A (tE u vs) :=
  B_pw hV h ⟨⟨⟨V_ge hV (by norm_num), ⟨V_ge hV le_rfl, B_LLE hV h, by
        rw [eval_LLE h]; exact PV hV (fourL_P s) (by norm_num)⟩, by
        simp only [Ex.eval, eval_LLE h]; exact PV hV (P_mul s (small_P s (by norm_num)) (fourL_P s)) (by norm_num)⟩,
      V_ge hV (by norm_num)⟩,
    ⟨⟨V_ge hV (by norm_num), B_vs hV h, by
        show 2 * σ vs ≤ V; rw [h]; exact PV hV (P_mul s (small_P s (by norm_num)) (s_P s)) (by norm_num)⟩,
      V_ge hV (by norm_num), by
        show 2 * σ vs + 2 ≤ V; rw [h]
        exact PV hV (P_add s (P_mul s (small_P s (by norm_num)) (s_P s)) (P_mono s (small_P s (c := 2) (by norm_num))
          (by norm_num))) (by norm_num)⟩, by
      simp only [Ex.eval, eval_LLE h, h]
      exact PV hV (P_mul s (le_trans (Nat.sub_le _ _) (P_mul s (small_P s (by norm_num)) (fourL_P s)))
        (P_add s (P_mul s (small_P s (by norm_num)) (s_P s)) (P_mono s (small_P s (c := 2) (by norm_num))
          (by norm_num)))) (by norm_num)⟩
    (V_ge hV (by norm_num))

theorem B_dD (hvs : vs < u) {z i : Ex} (hz : Bdd V σ A z) (hi : Bdd V σ A i) (hI : eval σ A i ≤ ph s) :
    Bdd V σ A (dD u vs z i) :=
  ⟨⟨hz, B_nprodK hi (fun j _ => ⟨B_TLE hV (upd_vs h (by omega) j), eval_TLE (upd_vs h (by omega) j)⟩)
      Nat.one_le_two_pow (le_trans (Nat.pow_le_pow_right Nat.one_le_two_pow hI)
        (by have := pD_P s; rw [pD, pp_const] at this
            exact le_trans this (le_trans (Nat.pow_le_pow_right (one_le_P s) (by have := two_le_pA s; omega)) hV)))⟩,
    B_TLE hV h⟩

theorem B_dZ (hvs : vs < u) {z i : Ex} (hz : Bdd V σ A z) (hi : Bdd V σ A i) (hI : eval σ A i ≤ pA s) :
    Bdd V σ A (dZ u vs z i) :=
  ⟨⟨hz, B_nprodK hi (fun j _ => ⟨B_ME hV (upd_vs h (by omega) j), eval_ME (upd_vs h (by omega) j)⟩)
      (one_lt_pM s).le (le_trans (Nat.pow_le_pow_right (one_lt_pM s).le hI)
        (by have := pZ_P s; rw [pZ, pp_const] at this
            exact le_trans this (le_trans (Nat.pow_le_pow_right (one_le_P s) (by omega)) hV)))⟩,
    B_ME hV h⟩

theorem B_z1E (hvs : vs < u) (hz : σ (u + 2) ≤ V) : Bdd V σ A (z1E u vs) :=
  ⟨⟨hz, B_PZE hV h hvs⟩, B_PZE hV h hvs⟩
theorem B_z2E (hvs : vs < u) (hz : σ (u + 2) ≤ V) : Bdd V σ A (z2E u vs) := ⟨hz, B_PZE hV h hvs⟩
theorem B_cyE (hz : σ (u + 2) ≤ V) : Bdd V σ A (cyE u vs) := ⟨⟨hz, B_PfE hV h⟩, B_ME hV h⟩
theorem B_ccE (hz : σ (u + 2) ≤ V) : Bdd V σ A (ccE u vs) := ⟨hz, B_PfE hV h⟩

omit hV in
theorem lt_mM {e f : Ex} : eval σ A (mM u vs e f) < pM s := by
  simp only [mM, Ex.eval, eval_ME h]; exact Nat.mod_lt _ (by positivity)

omit hV in
theorem lt_sM {x : ℕ} {n b : Ex} : eval σ A (sM u vs x n b) < pM s := by
  simp only [sM, Ex.eval, eval_ME h, foldSum_eq]; exact Nat.mod_lt _ (by positivity)

omit hV in
theorem lt_pw {b : ℕ} {e : Ex} : eval σ A (pw u vs b e) < pM s := by
  simp only [pw, Ex.eval, eval_ME h]
  rcases Nat.eq_zero_or_pos (eval σ A e) with h0 | h0
  · rw [h0]; exact one_lt_pM s
  · rw [foldProd_eq _ _ _ h0]; exact Nat.mod_lt _ (by positivity)

omit hV in
theorem lt_dZ (hvs : vs < u) {z i : Ex} : eval σ A (dZ u vs z i) < pM s := by
  rw [eval_dZ h hvs rfl]; exact Nat.mod_lt _ (by positivity)

omit hV in
theorem lt_dD (hvs : vs < u) {z i : Ex} : eval σ A (dD u vs z i) < 2 ^ pL s := by
  rw [eval_dD h hvs rfl]; exact Nat.mod_lt _ (by positivity)

omit hV in
theorem lt_cyE : eval σ A (cyE u vs) < pM s := by rw [eval_cyE h]; exact Nat.mod_lt _ (by positivity)

omit hV in
theorem lt_ccE : eval σ A (ccE u vs) < 2 ^ fw s := by rw [eval_ccE h]; exact Nat.mod_lt _ (by positivity)

end Cst

/-! ### The messages -/

section MsgB

variable {V s u vs : ℕ} {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ}
variable (hV : (2 ^ pL s) ^ (16 * pA s) ≤ V) (h : σ vs = s) (hvs : vs < u)
include hV h hvs

theorem B_sel {v : ℕ} {e0 e1 e2 e3 e4 : Ex} (hv : σ v < mulNodes s) (B0 : σ v < pA s → Bdd V σ A e0)
    (B1 : pA s ≤ σ v → σ v < 2 * pA s → Bdd V σ A e1) (B2 : 2 * pA s ≤ σ v → σ v < 3 * pA s → Bdd V σ A e2)
    (B3 : 3 * pA s ≤ σ v → σ v < 4 * pA s → Bdd V σ A e3) (B4 : 4 * pA s ≤ σ v → Bdd V σ A e4) :
    Bdd V σ A (sel u vs v e0 e1 e2 e3 e4) := by
  have Bv : Bdd V σ A (.var v) := show σ v ≤ V from PV hV (le_trans hv.le (nodes_P s)) (by norm_num)
  have ek : ∀ c, eval σ A (kA u vs c) = c * pA s := fun c => eval_kA h c
  unfold sel
  refine B_ifLt Bv (B_kA hV h (by norm_num)) (fun h1 => B0 ?_) (fun h1 => B_ifLt Bv (B_kA hV h (by norm_num))
    (fun h2 => B1 ?_ ?_) (fun h2 => B_ifLt Bv (B_kA hV h (by norm_num)) (fun h3 => B2 ?_ ?_)
      (fun h3 => B_ifLt Bv (B_kA hV h (by norm_num)) (fun h4 => B3 ?_ ?_) (fun h4 => B4 ?_)))) <;>
    simp only [Ex.eval, ek] at * <;> omega

theorem B_hat {zE iE : Ex} {a : ℕ} (ha : a ≤ 26)
    (hz : ∀ r < pA s, Bdd V (Function.update σ (u + 6) r) A zE)
    (hi : ∀ r < pA s, Bdd V (Function.update σ (u + 6) r) A iE ∧
      eval (Function.update σ (u + 6) r) A iE ≤ (2 ^ pL s) ^ a) :
    Bdd V σ A (hat u vs zE iE) := by
  refine B_sM hV h (B_AE hV h) fun r hr => ?_
  rw [eval_AE h] at hr
  have h' := upd_vs h (show vs < u + 6 by omega) r
  have e6 : Function.update σ (u + 6) r (u + 6) = r := Function.update_self ..
  have Br : Bdd V (Function.update σ (u + 6) r) A (.var (u + 6)) :=
    show _ ≤ V by rw [e6]; exact PV hV (le_trans hr.le (pA_P s)) (by norm_num)
  refine B_mM hV h' (B_dZ hV h' hvs (hz r hr) Br (by simp only [Ex.eval, e6]; omega))
    (B_pw hV h' ⟨⟨B_AE hV h', Br, ?_⟩, (hi r hr).1, ?_⟩ (V_ge16 hV)) (lt_dZ h' hvs) (lt_pw h')
  · simp only [Ex.eval, eval_AE h', e6]; exact PV hV (P_mul s (pA_P s) (le_trans hr.le (pA_P s))) (by norm_num)
  · simp only [Ex.eval, eval_AE h', e6]
    exact PV hV (P_mul s (P_mul s (pA_P s) (le_trans hr.le (pA_P s))) (hi r hr).2) (by omega)

theorem B_faMsg {va vb : ℕ} (hvb : vb < u + 4) (ha : σ va < mulNodes s) (hb : σ vb < mulNodes s)
    (hz : σ (u + 2) ≤ V) : Bdd V σ A (faMsg u vs va vb) := by
  have hG := nodes_P s
  refine B_mM hV h (B_pw hV h ⟨⟨PV hV (le_trans ha.le hG) (by norm_num), B_AE hV h⟩,
    ⟨PV hV (le_trans hb.le hG) (by norm_num), B_kA hV h (by norm_num)⟩, ?_⟩ (V_ge16 hV)) ?_ (lt_pw h) (lt_sM h)
  · simp only [Ex.eval, eval_AE h, eval_kA h]
    exact PV hV (P_mul s (le_trans (Nat.mod_le _ _) (le_trans ha.le hG))
      (le_trans (Nat.sub_le _ _) (le_trans hb.le hG))) (by norm_num)
  · refine B_sM hV h (B_AE hV h) fun j hj => ?_
    rw [eval_AE h] at hj
    have h' := upd_vs h (show vs < u + 5 by omega) j
    have e5 : Function.update σ (u + 5) j (u + 5) = j := Function.update_self ..
    have eb : Function.update σ (u + 5) j vb = σ vb := upd_lt _ (by omega)
    have ez : Function.update σ (u + 5) j (u + 2) = σ (u + 2) := upd_lt _ (by omega)
    have Bj : Bdd V (Function.update σ (u + 5) j) A (.var (u + 5)) :=
      show _ ≤ V by rw [e5]; exact PV hV (le_trans hj.le (pA_P s)) (by norm_num)
    refine B_mM hV h' (B_ifLt Bj (B_hE hV h') (fun hlt => B_dD hV h' hvs (show _ ≤ V by rw [ez]; exact hz) Bj
        (by rw [eval_hE h'] at hlt; exact hlt.le)) (fun _ => Nat.zero_le V))
      (B_pw hV h' ⟨⟨B_AE hV h', Bj, ?_⟩, ⟨(show _ ≤ V by rw [eb]; exact PV hV (le_trans hb.le hG) (by norm_num)),
        B_kA hV h' (by norm_num)⟩, ?_⟩ (V_ge16 hV)) ?_ (lt_pw h')
    · simp only [Ex.eval, eval_AE h', e5]; exact PV hV (P_mul s (pA_P s) (le_trans hj.le (pA_P s))) (by norm_num)
    · simp only [Ex.eval, eval_AE h', eval_kA h', e5, eb]
      exact PV hV (P_mul s (P_mul s (pA_P s) (le_trans hj.le (pA_P s)))
        (le_trans (Nat.sub_le _ _) (le_trans hb.le hG))) (by norm_num)
    · rw [eval_ifLt']; split_ifs
      · exact lt_trans (lt_dD h' hvs) (two_pow_pL_lt_pM s)
      · show 0 < pM s; positivity

theorem B_midMsg {va vb : ℕ} (hva : va < u + 4) (hvb : vb < u + 4) (ha : σ va < mulNodes s)
    (hb : σ vb < mulNodes s) (hz : σ (u + 2) ≤ V) : Bdd V σ A (midMsg u vs va vb) := by
  have hG := nodes_P s
  refine B_mM hV h (B_pwi hV h (a := 8) ⟨⟨PV hV (le_trans ha.le hG) (by norm_num), B_kA hV h (by norm_num)⟩,
    ⟨PV hV (le_trans hb.le hG) (by norm_num), B_kA hV h (by norm_num)⟩, ?_⟩ ?_ (by norm_num)) ?_ (lt_pw h) (lt_sM h)
  · simp only [Ex.eval, eval_kA h]
    exact PV hV (P_mul s (le_trans (Nat.sub_le _ _) (le_trans ha.le hG))
      (le_trans (Nat.sub_le _ _) (le_trans hb.le hG))) (by norm_num)
  · simp only [Ex.eval, eval_kA h]
    exact P_mul s (le_trans (Nat.sub_le _ _) (le_trans ha.le hG)) (le_trans (Nat.sub_le _ _) (le_trans hb.le hG))
  · refine B_sM hV h (B_AE hV h) fun i hi => ?_
    rw [eval_AE h] at hi
    have h' := upd_vs h (show vs < u + 5 by omega) i
    have e5 : Function.update σ (u + 5) i (u + 5) = i := Function.update_self ..
    have eb : Function.update σ (u + 5) i vb = σ vb := upd_lt _ (by omega)
    have Bi : Bdd V (Function.update σ (u + 5) i) A (.var (u + 5)) :=
      show _ ≤ V by rw [e5]; exact PV hV (le_trans hi.le (pA_P s)) (by norm_num)
    have Bvb : Bdd V (Function.update σ (u + 5) i) A (.var vb) :=
      show _ ≤ V by rw [eb]; exact PV hV (le_trans hb.le hG) (by norm_num)
    have hz6 : ∀ r, Function.update (Function.update σ (u + 5) i) (u + 6) r (u + 2) ≤ V := fun r => by
      rw [upd_lt _ (by omega), upd_lt _ (by omega)]; exact hz
    have hi6 : ∀ r < pA s, Bdd V (Function.update (Function.update σ (u + 5) i) (u + 6) r) A (.var (u + 5)) ∧
        eval (Function.update (Function.update σ (u + 5) i) (u + 6) r) A (.var (u + 5)) ≤ (2 ^ pL s) ^ 1 := by
      intro r _
      have : Function.update (Function.update σ (u + 5) i) (u + 6) r (u + 5) = i := by
        rw [upd_lt _ (by omega), e5]
      exact ⟨(show _ ≤ V by rw [this]; exact PV hV (le_trans hi.le (pA_P s)) (by norm_num)),
        by simp only [Ex.eval, this]; exact le_trans hi.le (pA_P s)⟩
    refine B_mM hV h' (B_mM hV h'
        (B_hat hV h' hvs (by norm_num) (fun r _ => B_z1E hV (upd_vs h' (by omega) r) hvs (hz6 r)) hi6)
        (B_hat hV h' hvs (by norm_num) (fun r _ => B_z2E hV (upd_vs h' (by omega) r) hvs (hz6 r)) hi6)
        (lt_sM h') (lt_sM h'))
      (B_pwi hV h' (a := 6) ⟨⟨B_AE hV h', Bi, ?_⟩, ⟨Bvb, B_kA hV h' (by norm_num)⟩, ?_⟩ ?_ (by norm_num)) (lt_mM h') (lt_pw h')
    · simp only [Ex.eval, eval_AE h', e5]; exact PV hV (P_mul s (pA_P s) (le_trans hi.le (pA_P s))) (by norm_num)
    · simp only [Ex.eval, eval_AE h', eval_kA h', e5, eb]
      exact PV hV (P_mul s (P_mul s (pA_P s) (le_trans hi.le (pA_P s)))
        (le_trans (Nat.sub_le _ _) (le_trans hb.le hG))) (by norm_num)
    · simp only [Ex.eval, eval_AE h', eval_kA h', e5, eb]
      exact P_mul s (P_mul s (pA_P s) (le_trans hi.le (pA_P s))) (le_trans (Nat.sub_le _ _) (le_trans hb.le hG))

theorem B_ibMsg {j2 : Ex} (hz : σ (u + 2) ≤ V)
    (hj : ∀ r < pA s, Bdd V (Function.update σ (u + 6) r) A j2 ∧
      eval (Function.update σ (u + 6) r) A j2 ≤ (2 ^ pL s) ^ 4) :
    Bdd V σ A (ibMsg u vs j2) := by
  refine B_mM hV h (B_tE hV h) (B_sM hV h (B_AE hV h) fun r hr => ?_) (lt_pw h) (lt_sM h)
  rw [eval_AE h] at hr
  have h' := upd_vs h (show vs < u + 6 by omega) r
  have e6 : Function.update σ (u + 6) r (u + 6) = r := Function.update_self ..
  have Br : Bdd V (Function.update σ (u + 6) r) A (.var (u + 6)) :=
    show _ ≤ V by rw [e6]; exact PV hV (le_trans hr.le (pA_P s)) (by norm_num)
  refine B_mM hV h' (B_dZ hV h' hvs (show _ ≤ V by rw [upd_lt _ (by omega)]; exact hz) Br
      (by simp only [Ex.eval, e6]; omega))
    (B_pwi hV h' (a := 6) ⟨⟨B_AE hV h', Br, ?_⟩, (hj r hr).1, ?_⟩ ?_ (by norm_num)) (lt_dZ h' hvs) (lt_pw h')
  · simp only [Ex.eval, eval_AE h', e6]; exact PV hV (P_mul s (pA_P s) (le_trans hr.le (pA_P s))) (by norm_num)
  · simp only [Ex.eval, eval_AE h', e6]
    exact PV hV (P_mul s (P_mul s (pA_P s) (le_trans hr.le (pA_P s))) (hj r hr).2) (by norm_num)
  · simp only [Ex.eval, eval_AE h', e6]
    exact P_mul s (P_mul s (pA_P s) (le_trans hr.le (pA_P s))) (hj r hr).2

end MsgB

/-! ### The five expressions -/

section Five

variable {V s u vs : ℕ} {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ}
variable (hV : (2 ^ pL s) ^ (16 * pA s) ≤ V) (h : σ vs = s) (hvs : vs < u)
include hV h hvs

theorem B_msg {va vb : ℕ} (hva : va < u + 4) (hvb : vb < u + 4) (ha : σ va < mulNodes s)
    (hb : σ vb < mulNodes s) (hz : σ (u + 2) ≤ V) : Bdd V σ A (msg u vs va vb) := by
  have hG := nodes_P s
  have Bva : Bdd V σ A (.var va) := show σ va ≤ V from PV hV (le_trans ha.le hG) (by norm_num)
  have Bvb : Bdd V σ A (.var vb) := show σ vb ≤ V from PV hV (le_trans hb.le hG) (by norm_num)
  have ek : ∀ c, eval σ A (kA u vs c) = c * pA s := fun c => eval_kA h c
  have B1 : Bdd V σ A (.lit 1) := V_ge hV (by norm_num)
  unfold msg
  refine B_sel hV h hvs ha (fun _ => ?_) (fun _ _ => ?_) (fun _ _ => ?_) (fun _ _ => ?_) (fun _ => ?_)
  · exact B_sel hV h hvs hb (fun _ => Nat.zero_le V) (fun _ _ => Nat.zero_le V)
      (fun _ _ => B_faMsg hV h hvs hvb ha hb hz) (fun _ _ => Nat.zero_le V) (fun _ => Nat.zero_le V)
  · exact B_sel hV h hvs hb (fun _ => Nat.zero_le V) (fun _ _ => Nat.zero_le V)
      (fun _ _ => B_faMsg hV h hvs hvb ha hb hz) (fun _ _ => Nat.zero_le V) (fun _ => Nat.zero_le V)
  · refine B_sel hV h hvs hb (fun hb0 => B_dZ hV h hvs (B_z1E hV h hvs hz) Bvb (by show σ vb ≤ pA s; omega))
      (fun _ hb2 => B_dZ hV h hvs (B_z2E hV h hvs hz) ⟨Bvb, B_kA hV h (by norm_num)⟩
        (by simp only [Ex.eval, ek]; omega)) (fun _ _ => Nat.zero_le V)
      (fun _ _ => B_midMsg hV h hvs hva hvb ha hb hz) (fun _ => Nat.zero_le V)
  · refine B_sel hV h hvs hb (fun _ => Nat.zero_le V) (fun _ _ => Nat.zero_le V)
      (fun _ hb3 => B_dZ hV h hvs hz ⟨Bvb, B_kA hV h (by norm_num)⟩ (by simp only [Ex.eval, ek]; omega))
      (fun _ _ => Nat.zero_le V) (fun _ => B_ifEq ⟨⟨Bvb, B_kA hV h (by norm_num)⟩, B_AE hV h⟩
        ⟨Bva, B_kA hV h (by norm_num)⟩ (B_ibMsg hV h hvs hz fun r _ => ?_) (Nat.zero_le V))
    have h' := upd_vs h (show vs < u + 6 by omega) r
    have eb : Function.update σ (u + 6) r vb = σ vb := upd_lt _ (by omega)
    refine ⟨⟨⟨show _ ≤ V by rw [eb]; exact Bvb, B_kA hV h' (by norm_num)⟩, B_AE hV h'⟩, ?_⟩
    simp only [Ex.eval, eb]
    exact le_trans (Nat.div_le_self _ _) (le_trans (Nat.sub_le _ _) (le_trans hb.le hG))
  · have hcc := lt_ccE (A := A) (u := u) h
    have hcy := lt_cyE (A := A) (u := u) h
    refine B_sel hV h hvs hb (fun _ => Nat.zero_le V) (fun _ _ => Nat.zero_le V) (fun _ _ => Nat.zero_le V)
      (fun _ _ => B_ifEq ⟨⟨Bva, B_kA hV h (by norm_num)⟩, B_AE hV h⟩ ⟨Bvb, B_kA hV h (by norm_num)⟩
        (B_cyE hV h hz) (Nat.zero_le V))
      (fun _ => B_ifEq ⟨Bvb, B_kA hV h (by norm_num)⟩ ⟨⟨Bva, B_kA hV h (by norm_num)⟩, B1, ?_⟩
        ⟨⟨B_ccE hV h hz, B_cyE hV h hz, ?_⟩, B_TLE hV h⟩
        (B_ifEq ⟨Bva, B_kA hV h (by norm_num)⟩ ⟨⟨Bvb, B_kA hV h (by norm_num)⟩, B1, ?_⟩ (B_ccE hV h hz)
          (Nat.zero_le V)))
    · simp only [Ex.eval, ek]
      exact PV hV (P_add s (le_trans (Nat.sub_le _ _) (le_trans ha.le hG)) (P_mono s (small_P s (c := 1)
        (by norm_num)) (by norm_num))) (by norm_num)
    · exact PV hV (P_add s (le_trans hcc.le (fw_pow_P s)) (le_trans hcy.le (pM_P s))) (by norm_num)
    · simp only [Ex.eval, ek]
      exact PV hV (P_add s (le_trans (Nat.sub_le _ _) (le_trans hb.le hG)) (P_mono s (small_P s (c := 1)
        (by norm_num)) (by norm_num))) (by norm_num)

theorem B_lnk (ha : σ u < mulNodes s) (hb : σ (u + 1) < mulNodes s) : Bdd V σ A (lnk u vs) := by
  have hG := nodes_P s
  have Ba : Bdd V σ A (.var u) := show σ u ≤ V from PV hV (le_trans ha.le hG) (by norm_num)
  have Bb : Bdd V σ A (.var (u + 1)) := show σ (u + 1) ≤ V from PV hV (le_trans hb.le hG) (by norm_num)
  have ek : ∀ c, eval σ A (kA u vs c) = c * pA s := fun c => eval_kA h c
  have B1 : Bdd V σ A (.lit 1) := V_ge hV (by norm_num)
  have Z : Bdd V σ A (.lit 0) := Nat.zero_le V
  unfold lnk
  refine B_sel hV h hvs ha (fun _ => ?_) (fun _ _ => ?_) (fun _ _ => ?_) (fun _ _ => ?_) (fun _ => ?_)
  · exact B_sel hV h hvs hb (fun _ => Z) (fun _ _ => Z) (fun _ _ => B1) (fun _ _ => Z) (fun _ => Z)
  · exact B_sel hV h hvs hb (fun _ => Z) (fun _ _ => Z) (fun _ _ => B1) (fun _ _ => Z) (fun _ => Z)
  · exact B_sel hV h hvs hb (fun _ => B1) (fun _ _ => B1) (fun _ _ => Z) (fun _ _ => B1) (fun _ => Z)
  · exact B_sel hV h hvs hb (fun _ => Z) (fun _ _ => Z) (fun _ _ => B1) (fun _ _ => Z)
      (fun _ => B_eqE ⟨⟨Bb, B_kA hV h (by norm_num)⟩, B_AE hV h⟩ ⟨Ba, B_kA hV h (by norm_num)⟩ B1)
  · refine B_sel hV h hvs hb (fun _ => Z) (fun _ _ => Z) (fun _ _ => Z)
      (fun _ _ => B_eqE ⟨⟨Ba, B_kA hV h (by norm_num)⟩, B_AE hV h⟩ ⟨Bb, B_kA hV h (by norm_num)⟩ B1)
      (fun _ => B_ifEq ⟨Bb, B_kA hV h (by norm_num)⟩ ⟨⟨Ba, B_kA hV h (by norm_num)⟩, B1, ?_⟩ B1
        (B_eqE ⟨Ba, B_kA hV h (by norm_num)⟩ ⟨⟨Bb, B_kA hV h (by norm_num)⟩, B1, ?_⟩ B1))
    · simp only [Ex.eval, ek]
      exact PV hV (P_add s (le_trans (Nat.sub_le _ _) (le_trans ha.le hG)) (P_mono s (small_P s (c := 1)
        (by norm_num)) (by norm_num))) (by norm_num)
    · simp only [Ex.eval, ek]
      exact PV hV (P_add s (le_trans (Nat.sub_le _ _) (le_trans hb.le hG)) (P_mono s (small_P s (c := 1)
        (by norm_num)) (by norm_num))) (by norm_num)

theorem eval_cE_le (ha : σ u < mulNodes s) (hb : σ (u + 1) < mulNodes s) : eval σ A (cE u vs) ≤ fw s := by
  have e1 : σ u = MG.enum (pA s) ((MG.enum (pA s)).symm ⟨σ u, ha⟩) := by rw [Equiv.apply_symm_apply]
  have e2 : σ (u + 1) = MG.enum (pA s) ((MG.enum (pA s)).symm ⟨σ (u + 1), hb⟩) := by rw [Equiv.apply_symm_apply]
  rw [cE_val h _ _ e1 e2, mC]; split_ifs <;> omega

theorem B_cE (ha : σ u < mulNodes s) (hb : σ (u + 1) < mulNodes s) : Bdd V σ A (cE u vs) :=
  ⟨B_lnk hV h hvs ha hb, B_fwE hV h, by
    have := eval_cE_le (A := A) hV h hvs ha hb
    simp only [cE, Ex.eval] at this
    exact le_trans this (PV hV (fw_P s) (by norm_num))⟩

theorem B_lr {va vb : ℕ} (hva : va < u + 4) (hvb : vb < u + 4) (ha : σ va < mulNodes s)
    (hb : σ vb < mulNodes s) (ha' : σ u < mulNodes s) (hb' : σ (u + 1) < mulNodes s) (hz : σ (u + 2) ≤ V)
    (hq : σ (u + 3) ≤ V) :
    Bdd V σ A (eqE (msg u vs va vb) (.mod (.var (u + 3)) (pow2 (u + 4) (cE u vs)))) :=
  B_eqE (B_msg hV h hvs hva hvb ha hb hz) ⟨hq, B_pow2 (B_cE hV h hvs ha' hb') (V_ge hV (by norm_num))
    (le_trans (Nat.pow_le_pow_right (by norm_num) (eval_cE_le hV h hvs ha' hb'))
      (PV hV (fw_pow_P s) (by norm_num)))⟩ (V_ge hV (by norm_num))

theorem B_szE {vm : ℕ} (ha : σ u < mulNodes s) : Bdd V σ A (mulNEx u vm vs).sz := by
  have h5 : (2 ^ pL s) ^ (5 * pA s + 5 * pA s) ≤ V :=
    le_trans (Nat.pow_le_pow_right (one_le_P s) (by omega)) hV
  exact B_sel hV h hvs ha (fun _ => B_PDE hV h hvs) (fun _ _ => B_PDE hV h hvs)
    (fun _ _ => ⟨B_PZE hV h hvs, B_PZE hV h hvs, by
      rw [eval_PZE h hvs]; exact le_trans (P_mul s (pZ_P s) (pZ_P s)) h5⟩) (fun _ _ => B_PZE hV h hvs)
    (fun _ => ⟨B_ME hV h, B_PfE hV h, by
      rw [eval_ME h, eval_PfE h]; exact PV hV (P_mul s (pM_P s) (fw_pow_P s)) (by norm_num)⟩)

end Five

/-! ### The weights -/

theorem n_P {s n : ℕ} (hnL : n ≤ pL s * pL s) : n ≤ (2 ^ pL s) ^ 2 :=
  le_trans hnL (by rw [pow_two]; exact Nat.mul_le_mul (pL_lt_P s).le (pL_lt_P s).le)

theorem ifEq01_le {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ} {e f a b : Ex} (ha' : eval σ A a ≤ 1) (hb' : eval σ A b ≤ 1) :
    eval σ A (ifEq e f a b) ≤ 1 := by
  rw [eval_ifEq]; split_ifs <;> assumption

section WB

variable {V s u vs n k : ℕ} {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ}
variable (hV : (2 ^ pL s) ^ (16 * pA s) ≤ V) (h : σ vs = s) (hvs : vs < u) (h2u : 2 < u)
  (h0 : σ 0 = n) (h2 : σ 2 = k) (hkn : k ≤ n) (hnL : n ≤ pL s * pL s) (hA : ∀ a j, A a j ≤ 1)
  (ha : σ u < mulNodes s) (hz : σ (u + 2) ≤ V)
include hV h hvs h2u h0 h2 hkn hnL hA ha hz

theorem B_faW : Bdd V σ A (faW u vs) := by
  have hG := nodes_P s
  have hn := n_P hnL
  have B1 : ∀ σ', Bdd V σ' A (.lit 1) := fun _ => V_ge hV (by norm_num)
  refine B_nprod01 (B_hE hV h) (fun i hi => ?_) (V_ge hV (by norm_num))
  rw [eval_hE h] at hi
  have h' := upd_vs h (show vs < u + 5 by omega) i
  have body : ∀ t < pL s, Bdd V (Function.update (Function.update σ (u + 5) i) (u + 6) t) A
      (.ifLt (posE u vs) (.var 2) (.lit 1)
        (eqE (.mod (.div (dD u vs (zv u) (.var (u + 5))) (pow2 (u + 4) (.var (u + 6)))) (.lit 2))
          (xBit (.sub (posE u vs) (.var 2))))) ∧
      eval (Function.update (Function.update σ (u + 5) i) (u + 6) t) A
      (.ifLt (posE u vs) (.var 2) (.lit 1)
        (eqE (.mod (.div (dD u vs (zv u) (.var (u + 5))) (pow2 (u + 4) (.var (u + 6)))) (.lit 2))
          (xBit (.sub (posE u vs) (.var 2))))) ≤ 1 := by
    intro t ht
    set σ2 := Function.update (Function.update σ (u + 5) i) (u + 6) t
    have h'' : σ2 vs = s := upd_vs h' (by omega) t
    have e5 : σ2 (u + 5) = i := by simp [σ2]
    have e6 : σ2 (u + 6) = t := by simp [σ2]
    have eu : σ2 u = σ u := by simp only [σ2]; rw [upd_lt _ (by omega), upd_lt _ (by omega)]
    have e0 : σ2 0 = n := by simp only [σ2]; rw [upd_lt _ (by omega), upd_lt _ (by omega), h0]
    have e2 : σ2 2 = k := by simp only [σ2]; rw [upd_lt _ (by omega), upd_lt _ (by omega), h2]
    have ez : σ2 (u + 2) = σ (u + 2) := by simp only [σ2]; rw [upd_lt _ (by omega), upd_lt _ (by omega)]
    have hiP : i ≤ (2 ^ pL s) ^ 1 := le_trans hi.le (ph_P s)
    have htP : t ≤ (2 ^ pL s) ^ 1 := le_trans ht.le (pL_P s)
    have Bi : Bdd V σ2 A (.var (u + 5)) := show _ ≤ V by rw [e5]; exact PV hV hiP (by norm_num)
    have Bt : Bdd V σ2 A (.var (u + 6)) := show _ ≤ V by rw [e6]; exact PV hV htP (by norm_num)
    have Bu : Bdd V σ2 A (.var u) := show _ ≤ V by rw [eu]; exact PV hV (le_trans ha.le hG) (by norm_num)
    have Bk : Bdd V σ2 A (.var 2) := show _ ≤ V by rw [e2]; exact PV hV (le_trans hkn hn) (by norm_num)
    have hAi : pA s * i ≤ (2 ^ pL s) ^ 4 := P_mono s (P_mul s (pA_P s) hiP) (by norm_num)
    have hpos : eval σ2 A (posE u vs) ≤ (2 ^ pL s) ^ 7 := by
      simp only [posE, Ex.eval, eval_LLE h'', eval_AE h'', e5, e6, eu]
      exact P_mono s (P_add s (P_mul s (pL_P s) (P_add s (le_trans ha.le hG) hAi)) (P_mono s htP (by norm_num)))
        (by norm_num)
    have Bpos : Bdd V σ2 A (posE u vs) := by
      refine ⟨⟨B_LLE hV h'', ⟨Bu, ⟨B_AE hV h'', Bi, ?_⟩, ?_⟩, ?_⟩, Bt, le_trans hpos (PV hV le_rfl (by norm_num))⟩
      · simp only [Ex.eval, eval_AE h'', e5]; exact PV hV hAi (by norm_num)
      · simp only [Ex.eval, eval_AE h'', e5, eu]; exact PV hV (P_add s (le_trans ha.le hG) hAi) (by norm_num)
      · simp only [Ex.eval, eval_AE h'', eval_LLE h'', e5, eu]
        exact PV hV (P_mul s (pL_P s) (P_add s (le_trans ha.le hG) hAi)) (by norm_num)
    refine ⟨B_ifLt Bpos Bk (fun _ => B1 _) (fun _ => B_eqE ⟨⟨B_dD hV h'' hvs (show _ ≤ V by rw [ez]; exact hz) Bi
        (by show σ2 (u + 5) ≤ ph s; omega), B_pow2 Bt (V_ge hV (by norm_num)) ?_⟩, V_ge hV (by norm_num)⟩
        (B_xBit ⟨Bpos, Bk⟩ (by rw [e2]; exact PV hV (le_trans hkn hn) (by norm_num))
          (by rw [e0]; exact PV hV hn (by norm_num)) ?_ hA (V_ge hV (by norm_num))) (V_ge hV (by norm_num))), ?_⟩
    · show 2 ^ σ2 (u + 6) ≤ V
      rw [e6]; exact le_trans (Nat.pow_le_pow_right (by norm_num) ht.le) (PV hV (P_one s le_rfl) (by norm_num))
    · simp only [Ex.eval, e2]
      exact PV hV (P_add s (le_trans (Nat.sub_le _ _) hpos) (P_mono s (le_trans hkn hn) (by norm_num)))
        (by norm_num)
    · rw [eval_ifLt']; split_ifs
      · exact le_rfl
      · exact eqE_le _ _
  refine ⟨B_nprod01 (B_LLE hV h') (fun t ht => body t (by rwa [eval_LLE h'] at ht)) (V_ge hV (by norm_num)), ?_⟩
  rw [eval_nprod]
  exact pp_le_one fun t ht => (body t (by rwa [eval_LLE h'] at ht)).2

theorem B_dgE : Bdd V σ A (dgE u vs) := by
  have hG := nodes_P s
  have hn := n_P hnL
  have hj : ∀ σ', σ' vs = s → σ' u = σ u → Bdd V σ' A (jE u vs) ∧ eval σ' A (jE u vs) ≤ (2 ^ pL s) ^ 4 :=
    fun σ' hs' hu' => ⟨⟨show _ ≤ V by rw [hu']; exact PV hV (le_trans ha.le hG) (by norm_num), B_kA hV hs' (by norm_num)⟩,
      by simp only [jE, Ex.eval, hu']; exact le_trans (Nat.sub_le _ _) (le_trans ha.le hG)⟩
  have body : ∀ t < pL s, Bdd V (Function.update σ (u + 5) t) A
      (.mul (nBit (.add (.mul (LLE u vs) (jE u vs)) (.var (u + 5)))) (pow2 (u + 4) (.var (u + 5)))) ∧
      eval (Function.update σ (u + 5) t) A
      (.mul (nBit (.add (.mul (LLE u vs) (jE u vs)) (.var (u + 5)))) (pow2 (u + 4) (.var (u + 5)))) ≤ 2 ^ pL s := by
    intro t ht
    have h' := upd_vs h (show vs < u + 5 by omega) t
    have e5 : Function.update σ (u + 5) t (u + 5) = t := Function.update_self ..
    have eu : Function.update σ (u + 5) t u = σ u := upd_lt _ (by omega)
    have e0 : Function.update σ (u + 5) t 0 = n := by rw [upd_lt _ (by omega), h0]
    have htP : t ≤ (2 ^ pL s) ^ 1 := le_trans ht.le (pL_P s)
    have Bt : Bdd V (Function.update σ (u + 5) t) A (.var (u + 5)) :=
      show _ ≤ V by rw [e5]; exact PV hV htP (by norm_num)
    obtain ⟨Bj, hjv⟩ := hj _ h' eu
    have hLj : eval (Function.update σ (u + 5) t) A (.mul (LLE u vs) (jE u vs)) ≤ (2 ^ pL s) ^ 5 := by
      simp only [Ex.eval, eval_LLE h']; exact P_mul s (pL_P s) hjv
    have hi : eval (Function.update σ (u + 5) t) A (.add (.mul (LLE u vs) (jE u vs)) (.var (u + 5))) ≤
        (2 ^ pL s) ^ 6 := by
      simp only [Ex.eval] at hLj ⊢; rw [e5]; exact P_add s hLj (P_mono s htP (by norm_num))
    have hpow : eval (Function.update σ (u + 5) t) A (pow2 (u + 4) (.var (u + 5))) ≤ 2 ^ pL s := by
      rw [eval_pow2]; simp only [Ex.eval, e5]; exact Nat.pow_le_pow_right (by norm_num) ht.le
    refine ⟨⟨B_nBit ⟨⟨B_LLE hV h', Bj, PV hV hLj (by norm_num)⟩, Bt, PV hV hi (by norm_num)⟩
        (by rw [e0]; exact PV hV hn (by norm_num))
        (PV hV (P_add s hi (P_mono s (small_P s (c := 1) (by norm_num)) (by norm_num))) (by norm_num)) hA
        (V_ge hV (by norm_num)),
      B_pow2 Bt (V_ge hV (by norm_num)) (by
        have := le_trans hpow (PV hV (P_one s le_rfl) (by norm_num)); rwa [eval_pow2] at this), ?_⟩, ?_⟩
    · exact le_trans (Nat.mul_le_mul (nBit_le _) hpow) (by rw [one_mul]; exact PV hV (P_one s le_rfl) (by norm_num))
    · simp only [Ex.eval]
      exact le_trans (Nat.mul_le_mul (nBit_le _) hpow) (by rw [one_mul])
  refine B_nsum (B_LLE hV h) (fun t ht => (body t (by rwa [eval_LLE h] at ht)).1) ?_
  rw [eval_LLE h]
  refine le_trans (sum_le_card_mul fun t ht => (body t ht).2) ?_
  exact PV hV (P_mul s (pL_P s) (P_one s le_rfl)) (by norm_num)

theorem B_cW (ha4 : 4 * pA s ≤ σ u) : Bdd V σ A (cW u vs) := by
  have hG := nodes_P s
  have B1 : Bdd V σ A (.lit 1) := V_ge hV (by norm_num)
  have Z : Bdd V σ A (.lit 0) := Nat.zero_le V
  have Bj : Bdd V σ A (jE u vs) :=
    ⟨show σ u ≤ V from PV hV (le_trans ha.le hG) (by norm_num), B_kA hV h (by norm_num)⟩
  have hcc := lt_ccE (A := A) (u := u) h
  have hcy := lt_cyE (A := A) (u := u) h
  have Badd : Bdd V σ A (.add (ccE u vs) (cyE u vs)) := ⟨B_ccE hV h hz, B_cyE hV h hz,
    PV hV (P_add s (le_trans hcc.le (fw_pow_P s)) (le_trans hcy.le (pM_P s))) (by norm_num)⟩
  have Bif1 : Bdd V σ A (ifEq (jE u vs) (.lit 0) (eqE (ccE u vs) (.lit 0)) (.lit 1)) :=
    B_ifEq Bj Z (B_eqE (B_ccE hV h hz) Z (V_ge hV (by norm_num))) B1
  have Bif2 : Bdd V σ A (ifEq (.add (jE u vs) (.lit 1)) (.mul (AE u vs) (AE u vs))
      (eqE (.div (.add (ccE u vs) (cyE u vs)) (TLE u vs)) (.lit 0)) (.lit 1)) := by
    refine B_ifEq ⟨Bj, B1, ?_⟩ ⟨B_AE hV h, B_AE hV h, ?_⟩ (B_eqE ⟨Badd, B_TLE hV h⟩ Z (V_ge hV (by norm_num))) B1
    · simp only [jE, Ex.eval, eval_kA h]
      exact PV hV (P_add s (le_trans (Nat.sub_le _ _) (le_trans ha.le hG)) (P_mono s (small_P s (c := 1)
        (by norm_num)) (by norm_num))) (by norm_num)
    · rw [eval_AE h]; exact PV hV (P_mul s (pA_P s) (pA_P s)) (by norm_num)
  have l1 := ifEq01_le (σ := σ) (A := A) (e := jE u vs) (f := .lit 0) (a := eqE (ccE u vs) (.lit 0))
    (b := .lit 1) (eqE_le _ _) (show eval σ A (.lit 1) ≤ 1 from le_refl 1)
  have l2 := ifEq01_le (σ := σ) (A := A) (e := .add (jE u vs) (.lit 1)) (f := .mul (AE u vs) (AE u vs))
    (a := eqE (.div (.add (ccE u vs) (cyE u vs)) (TLE u vs)) (.lit 0)) (b := .lit 1)
    (eqE_le _ _) (show eval σ A (.lit 1) ≤ 1 from le_refl 1)
  refine ⟨B_eqE ⟨Badd, B_TLE hV h⟩ (B_dgE hV h hvs h2u h0 h2 hkn hnL hA ha hz) (V_ge hV (by norm_num)),
    ⟨Bif1, Bif2, le_trans (Nat.mul_le_mul l1 l2) (V_ge hV (by norm_num))⟩, ?_⟩
  simp only [Ex.eval]
  exact le_trans (Nat.mul_le_mul (eqE_le _ _) (Nat.mul_le_mul l1 l2)) (V_ge hV (by norm_num))

end WB

/-! ### The bounds -/

/-- The value bound: `(m + 2)^2 · 2^(16 L A)`. -/
def mulV (s m : ℕ) : ℕ := (m + 2) ^ 2 * 2 ^ (16 * (pL s * pA s))

theorem mulV_le (s m : ℕ) : mulV s m ≤ (m + 2) ^ 2 * 2 ^ (16 * (pL s * pA s)) := le_rfl

/-- **Every value met by the five expressions is at most `V`.** -/
theorem mul_bdd {m B s n k u vm vs V : ℕ} {σ₀ σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ}
    (_hm : 1 < m) (_h0 : σ₀ vm = m) (hs : σ₀ vs = s) (hn : σ₀ 0 = n) (hk : σ₀ 2 = k) (hkn : k ≤ n)
    (hnL : n ≤ pL s * pL s) (_hvm : vm < B) (hvs : vs < B) (h2 : 2 < B) (hu : B ≤ u)
    (hA : ∀ a j, A a j ≤ 1) (hV : mulV s m ≤ V) (hσ : Ag B σ₀ σ) (ha : σ u < mulNodes s)
    (hb : σ (u + 1) < mulNodes s) (hz : σ (u + 2) ≤ V) (hq : σ (u + 3) ≤ V) :
    Bdd V σ A (mulNEx u vm vs).sz ∧ Bdd V σ A (mulNEx u vm vs).W ∧ Bdd V σ A (mulNEx u vm vs).c ∧
      Bdd V σ A (mulNEx u vm vs).l ∧ Bdd V σ A (mulNEx u vm vs).r := by
  have hV' : (2 ^ pL s) ^ (16 * pA s) ≤ V := by
    refine le_trans ?_ hV
    rw [← pow_mul, mulV, show pL s * (16 * pA s) = 16 * (pL s * pA s) by ring]
    exact Nat.le_mul_of_pos_left _ (by positivity)
  have h : σ vs = s := (hσ vs hvs).trans hs
  have h0 : σ 0 = n := (hσ 0 (by omega)).trans hn
  have h2' : σ 2 = k := (hσ 2 h2).trans hk
  have hvs' : vs < u := by omega
  refine ⟨B_szE hV' h hvs' ha, ?_, B_cE hV' h hvs' ha hb,
    B_lr hV' h hvs' (by omega) (by omega) ha hb ha hb hz hq, B_lr hV' h hvs' (by omega) (by omega) hb ha ha hb hz hq⟩
  exact B_sel hV' h hvs' ha (fun _ => B_faW hV' h hvs' (by omega) h0 h2' hkn hnL hA ha hz)
    (fun _ _ => V_ge hV' (by norm_num)) (fun _ _ => V_ge hV' (by norm_num)) (fun _ _ => V_ge hV' (by norm_num))
    (fun h4 => B_cW hV' h hvs' (by omega) h0 h2' hkn hnL hA ha hz h4)

end Factoring.Aux
