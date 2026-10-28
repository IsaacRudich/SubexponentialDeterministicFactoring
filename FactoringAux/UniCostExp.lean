/-
The cost of the uniform counting command: value bounds of the engine's own expressions.

* `rdT_tbdd`: the table read back from array `3` (`Holds`), values at most `Wv V` when `K ≤ V`, `2^(L K) ≤ V`, `m ≤ V`.
* `kbE_bdd`, `gE_bdd`, `g4E_bdd`, `NcE_bdd`; `lvl_search_bdd` (a level's searches, both orientations).

Not an audit surface.
-/
module

public import FactoringAux.UniCostBase

@[expose] public section

namespace Factoring.Aux

open Factoring.Aux.Copied Factoring.Aux.Copied.PLib Ex Uni Finset SB

namespace UCost

/-! ### The table in array `3` -/

/-- **The table read back** has values at most `Wv V`. -/
theorem rdT_tbdd {V m K L par : ℕ} {A : ℕ → ℕ → ℕ} {T : Clique (ZMod m) K L} (hH : Holds A par T) {σ₀ : ℕ → ℕ}
    (hK : σ₀ 42 = K) (hL : σ₀ 40 = L) (hp : σ₀ 41 = par) (hpar : par < 3) (hm1 : 1 < m) (hm : m ≤ V) (hKV : K ≤ V)
    (hLK : 2 ^ (L * K) ≤ V) : TBdd (Wv V) 60 σ₀ A 60 61 rdT K := by
  intro σ hσ hγ hΘ
  have e42 : σ 42 = K := by rw [hσ 42 (by norm_num), hK]
  have e40 : σ 40 = L := by rw [hσ 40 (by norm_num), hL]
  have e41 : σ 41 = par := by rw [hσ 41 (by norm_num), hp]
  have hW := @le_Wv V
  have hVV := @sq_le_Wv V
  have hK1 : 1 ≤ K := by omega
  have hW16 : 16 ≤ Wv V := by unfold Wv; nlinarith
  have : NeZero m := ⟨by omega⟩
  set P2 := 2 ^ (L * K)
  have hP1 : 1 ≤ P2 := Nat.one_le_two_pow
  have hQ : σ 61 % P2 < P2 := Nat.mod_lt _ (by omega)
  have hKP : K * P2 ≤ V * V := Nat.mul_le_mul hKV hLK
  have hKQ : σ 60 + K * (σ 61 % P2) + 1 ≤ K * P2 := by
    have : K * (σ 61 % P2) + K ≤ K * P2 := by
      have := Nat.mul_le_mul_left K (show σ 61 % P2 + 1 ≤ P2 by omega); rw [mul_add, mul_one] at this; exact this
    omega
  have hLKV : L * K ≤ V := le_trans Nat.lt_two_pow_self.le hLK
  have hLV : L ≤ V := le_trans (Nat.le_mul_of_pos_right _ hK1) hLKV
  have BLK : Bdd (Wv V) σ A (.mul (.var 40) (.var 42)) :=
    B_mul (B_var (by rw [e40]; omega)) (B_var (by rw [e42]; omega)) (by simp only [Ex.eval, e40, e42]; omega)
  have Bp : Bdd (Wv V) σ A (pow2 59 (.mul (.var 40) (.var 42))) :=
    B_pow2 BLK (by omega) (by simp only [Ex.eval, e40, e42]; omega)
  have ep : eval σ A (pow2 59 (.mul (.var 40) (.var 42))) = P2 := by simp only [eval_pow2, Ex.eval, e40, e42]; rfl
  have Bmod : Bdd (Wv V) σ A (.mod (.var 61) (pow2 59 (.mul (.var 40) (.var 42)))) := B_mod (B_var hΘ) Bp
  have em : eval σ A (.mod (.var 61) (pow2 59 (.mul (.var 40) (.var 42)))) = σ 61 % P2 := by
    simp only [Ex.eval]; rw [ep]
  have hKQ' : K * (σ 61 % P2) ≤ K * P2 := Nat.mul_le_mul_left _ hQ.le
  have B1 : Bdd (Wv V) σ A (.mul (.var 42) (.mod (.var 61) (pow2 59 (.mul (.var 40) (.var 42))))) :=
    B_mul (B_var (by rw [e42]; omega)) Bmod (by rw [em]; simp only [Ex.eval, e42]; omega)
  have e1 : eval σ A (.mul (.var 42) (.mod (.var 61) (pow2 59 (.mul (.var 40) (.var 42))))) = K * (σ 61 % P2) := by
    simp only [Ex.eval] at em ⊢; rw [em, e42]
  have B2 : Bdd (Wv V) σ A (.add (.var 60) (.mul (.var 42) (.mod (.var 61) (pow2 59 (.mul (.var 40) (.var 42)))))) :=
    B_add (B_var (by omega)) B1 (by rw [e1]; simp only [Ex.eval]; omega)
  have e2 : eval σ A (.add (.var 60) (.mul (.var 42) (.mod (.var 61) (pow2 59 (.mul (.var 40) (.var 42)))))) =
      σ 60 + K * (σ 61 % P2) := by simp only [Ex.eval] at e1 ⊢; rw [e1]
  have B3 : Bdd (Wv V) σ A (.mul (.lit 3) (.add (.var 60) (.mul (.var 42) (.mod (.var 61)
      (pow2 59 (.mul (.var 40) (.var 42))))))) :=
    B_mul (B_lit (by omega)) B2 (by rw [e2]; simp only [Ex.eval]; unfold Wv; nlinarith)
  have B4 : Bdd (Wv V) σ A (.add (.mul (.lit 3) (.add (.var 60) (.mul (.var 42) (.mod (.var 61)
      (pow2 59 (.mul (.var 40) (.var 42))))))) (.var 41)) :=
    B_add B3 (B_var (by rw [e41]; omega)) (by
      simp only [Ex.eval] at e2 ⊢; rw [e2, e41]; unfold Wv; nlinarith)
  refine ⟨B4, ?_⟩
  simp only [Ex.eval] at e2 ⊢
  rw [e2, e41, hH (σ 60) hγ _ hQ]
  exact le_trans (ZMod.val_lt _).le (le_trans hm hW)

/-! ### Group counts and choice counts -/

theorem Kb_le {d d' : ℕ} (h : d ≤ d') : Kb K0u d ≤ Kb K0u d' := Kb_mono K0u (by norm_num) h

/-- `Kb 48 d` (`d` in `vd`). -/
theorem kbE_bdd {V vd : ℕ} {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ} (hd : σ vd ≤ V) (hK : Kb K0u (σ vd) ≤ V) :
    Bdd V σ A (kbE vd) := by
  have h48 : 48 ≤ V := le_trans (Kb_le (Nat.zero_le _)) hK
  refine ⟨hd, h48, fun j hj => ?_⟩
  have hF : (fun j s => eval (Function.update (Function.update σ 900 j) 901 s) A
      (.mul (.lit 9) (powE 902 (.var 901) 16))) = fun _ s => 9 * s ^ 16 := by
    funext j s
    simp only [Ex.eval]
    rw [eval_powE 902 _ 16 (fun i => by simp [Ex.eval])]
    simp [Ex.eval]
  change Bdd V (Function.update (Function.update σ 900 j) 901 (iterF (fun j s => eval (Function.update
    (Function.update σ 900 j) 901 s) A (.mul (.lit 9) (powE 902 (.var 901) 16))) K0u j)) A _
  rw [hF, iterF_Kb]
  replace hj : j < σ vd := hj
  set σ' := Function.update (Function.update σ 900 j) 901 (Kb K0u j)
  have e1 : σ' 901 = Kb K0u j := by simp [σ']
  have hS : 9 * Kb K0u j ^ 16 ≤ V := by rw [← Kb_succ]; exact le_trans (Kb_le (by omega)) hK
  have hP : ∀ i ≤ 16, Kb K0u j ^ i ≤ V := fun i hi =>
    le_trans (Nat.pow_le_pow_right (by have := Kb_pos j; omega) hi) (by omega)
  have ep : eval σ' A (powE 902 (.var 901) 16) = Kb K0u j ^ 16 := by
    rw [eval_powE 902 _ 16 (fun i => by simp [Ex.eval])]; simp [Ex.eval, e1]
  refine B_mul (B_lit (by omega)) ?_ (by rw [ep]; simp only [Ex.eval]; exact hS)
  exact bdd_nprod_const (x := 902) (n := .lit 16) (b := .var 901) (c := Kb K0u j) (B_lit (by omega))
    (fun i => show _ ≤ V by simp only [Function.update_of_ne (show (901 : ℕ) ≠ 902 by norm_num), e1]; simpa using hP 1 (by omega))
    (fun i => by simp only [Ex.eval, Function.update_of_ne (show (901 : ℕ) ≠ 902 by norm_num), e1])
    (fun i hi => hP i (by simpa [Ex.eval] using hi))

/-- `3 K^8` (`K` in `vK`). -/
theorem gE_bdd {V vK K : ℕ} {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ} (hv : vK ≠ 906) (hK : σ vK = K) (hG : 3 * K ^ 8 ≤ V)
    (h8 : 8 ≤ V) : Bdd V σ A (gE vK) := by
  have hP : ∀ i ≤ 8, K ^ i ≤ V := fun i hi => by
    rcases Nat.eq_zero_or_pos K with h0 | h0
    · subst h0; rcases Nat.eq_zero_or_pos i with h | h
      · subst h; simp; omega
      · rw [zero_pow (by omega)]; omega
    · exact le_trans (Nat.pow_le_pow_right h0 hi) (by omega)
  refine B_mul (B_lit (by omega)) (bdd_nprod_const (x := 906) (n := .lit 8) (b := .var vK) (c := K) (B_lit h8)
    (fun i => show _ ≤ V by rw [Function.update_of_ne hv, hK]; simpa using hP 1 (by omega))
    (fun i => by simp only [Ex.eval, Function.update_of_ne hv, hK])
    (fun i hi => hP i (by simpa [Ex.eval] using hi))) ?_
  show 3 * eval σ A (powE 906 (.var vK) 8) ≤ V
  rw [eval_powE 906 _ 8 (fun i => by simp [Ex.eval, Function.update_of_ne hv])]
  simp only [Ex.eval, hK]; exact hG

/-- `(3 K^8)^4`. -/
theorem g4E_bdd {V vK K : ℕ} {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ} (hv : vK ≠ 906) (hv' : vK ≠ 907) (hK : σ vK = K)
    (hG : (3 * K ^ 8) * (3 * K ^ 8) * ((3 * K ^ 8) * (3 * K ^ 8)) ≤ V) (h8 : 8 ≤ V) : Bdd V σ A (g4E vK) := by
  set G := 3 * K ^ 8
  have hG4 : G ^ 4 ≤ V := by rw [show G ^ 4 = G * G * (G * G) by ring]; exact hG
  have hP : ∀ i ≤ 4, G ^ i ≤ V := fun i hi => by
    rcases Nat.eq_zero_or_pos G with h0 | h0
    · rw [h0]; rcases Nat.eq_zero_or_pos i with h | h
      · subst h; simp; omega
      · rw [zero_pow (by omega)]; omega
    · exact le_trans (Nat.pow_le_pow_right h0 hi) hG4
  have hK' : ∀ i, Function.update σ 907 i vK = K := fun i => by rw [Function.update_of_ne hv', hK]
  exact bdd_nprod_const (x := 907) (n := .lit 4) (b := gE vK) (c := G) (B_lit (by omega))
    (fun i => gE_bdd hv (hK' i) (by simpa using hP 1 (by omega)) h8) (fun i => by rw [eval_gE hv, hK' i])
    (fun i hi => hP i (by simpa [Ex.eval] using hi))

/-- The number of choice codes `Nc` of a level. -/
theorem NcE_bdd {V K lam : ℕ} {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ} (hK : σ 43 = K) (hl : σ 40 = lam)
    (hG : (3 * K ^ 8) * (3 * K ^ 8) * ((3 * K ^ 8) * (3 * K ^ 8)) ≤ V)
    (hC : (tB lam + 1) ^ ((3 * K ^ 8) * (3 * K ^ 8) * ((3 * K ^ 8) * (3 * K ^ 8))) ≤ V) (hl2 : lam + 2 ≤ V)
    (h8 : 8 ≤ V) : Bdd V σ A (NcE 43 40) := by
  set G := 3 * K ^ 8
  have eg : eval σ A (g4E 43) = G * G * (G * G) := by rw [eval_g4E (by norm_num) (by norm_num), hK]; ring
  have hl' : ∀ i, Function.update σ 908 i 40 = lam := fun i => by rw [Function.update_of_ne (by norm_num), hl]
  have ht : tB lam + 1 ≤ V := by unfold tB; have := Nat.div_le_self (lam + 2) 3; omega
  exact bdd_nprod_const (x := 908) (n := g4E 43) (b := .add (tBE 40) (.lit 1)) (c := tB lam + 1)
    (g4E_bdd (by norm_num) (by norm_num) hK hG h8)
    (fun i => B_add (tBE_bdd (hl' i) hl2 (by omega)) (B_lit (by omega))
      (by show eval _ A (tBE 40) + 1 ≤ V; rw [eval_tBE (hl' i)]; exact ht))
    (fun i => by show eval _ A (tBE 40) + 1 = _; rw [eval_tBE (hl' i)])
    (fun i hi => le_trans (Nat.pow_le_pow_right (by omega) (by rw [eg] at hi; exact hi)) hC)

/-! ### A level's searches -/

/-- **A level's search** (row or column) has values at most `V`. -/
theorem lvl_search_bdd {V m BT lam : ℕ} {σ₀ : ℕ → ℕ} {A : ℕ → ℕ → ℕ} {P : LP}
    {Tab : Clique (ZMod m) (P.G * P.G) lam} (H : LevelHyp m BT σ₀ A P lam Tab)
    (hT : TBdd V BT σ₀ A P.vγ P.vΘ P.TE (P.G * P.G)) (R : LevelReq V m P.K P.G lam) (tr : Bool) {cc : ℕ}
    (hcc : cc < (tB lam + 1) ^ (P.G * P.G * (P.G * P.G))) {σ₁ : ℕ → ℕ} (h1 : Ag P.b σ₀ σ₁) (hc : σ₁ P.b = cc)
    (hL : σ₁ (P.b + 1) = Lnext P.K P.G lam) :
    Bdd V σ₁ A (GroupEx.searchE (LevelEx.gs P tr) (P.b + 2) (P.b + 3)) := by
  have hK0 : 0 < P.K := by have := H.hK; omega
  have hg : 0 < P.G := by rw [H.hG]; have := H.hK; positivity
  have hm := H.hm
  have Hg := LevelEx.gridHyp H h1 hc
  have GH := R.grid (le_trans hcc.le R.hC) (LevelEx.gp P) rfl
  obtain ⟨hGG, -, -, -, -, -, -⟩ := GH.facts hg
  have hT' : TBdd V BT σ₁ A P.vγ P.vΘ P.TE (P.G * P.G) := hT.congr (h1.mono H.hBT)
  have hvm2 : P.vm < P.b + 2 := by have := H.hvm; have := H.hBT; omega
  have hK0' : 0 < P.K := hK0
  have hL1 : Lnext P.K P.G lam + 1 ≤ V :=
    le_trans Nat.lt_two_pow_self (two_pow_le_of (Nat.le_mul_of_pos_right _ hK0) R.hLK)
  have hcw : ∀ {N : Net (ZMod m) P.G}, N.Fits (P.G ^ 3 * lam) → ∀ x < P.K ^ P.G, ∀ γ γ' : Fin P.K, γ < γ' →
      (N.coarsen (chiOf P.K P.G x hK0)).c γ γ' ≤ V := fun hf _ _ γ γ' h =>
    le_trans (Net.coarsen_c_le_total _ _ γ γ' h) (le_trans (Net.total_le_fits _ hf) R.htot)
  cases tr with
  | false =>
      exact GroupEx.search_bdd (S := LevelEx.gs P false) hK0 hg hm (GridEx.row_rep Hg hcc)
        (GridEx.grid_bdd GH Hg hT' false) hvm2
        (show P.b + 1 < P.b + 2 by omega) (show P.b + 2 ≤ P.b + 2 by omega) (show P.b + 2 ≤ P.b + 3 by omega)
        (show P.b + 2 ≤ P.b + 4 by omega) (show P.b + 2 ≠ P.b + 3 by omega) (show P.b + 2 ≠ P.b + 4 by omega)
        (show P.b + 3 ≠ P.b + 4 by omega) (show P.b + 2 < P.b + 6 by omega) (show P.b + 3 < P.b + 6 by omega)
        (show P.b + 4 < P.b + 6 by omega) hL R.hKg hGG R.hKG R.hg1 hL1 (hcw (rowNet_fits _ _)) (Ag.refl _ _)
  | true =>
      exact GroupEx.search_bdd (S := LevelEx.gs P true) hK0 hg hm (GridEx.col_rep Hg hcc)
        (GridEx.grid_bdd GH Hg hT' true) hvm2
        (show P.b + 1 < P.b + 2 by omega) (show P.b + 2 ≤ P.b + 2 by omega) (show P.b + 2 ≤ P.b + 3 by omega)
        (show P.b + 2 ≤ P.b + 5 by omega) (show P.b + 2 ≠ P.b + 3 by omega) (show P.b + 2 ≠ P.b + 5 by omega)
        (show P.b + 3 ≠ P.b + 5 by omega) (show P.b + 2 < P.b + 6 by omega) (show P.b + 3 < P.b + 6 by omega)
        (show P.b + 5 < P.b + 6 by omega) hL R.hKg hGG R.hKG R.hg1 hL1 (hcw (colNet_fits _ _)) (Ag.refl _ _)

end UCost

end Factoring.Aux
