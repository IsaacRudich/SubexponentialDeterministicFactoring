/-
The cost of the uniform counting command: the parameters and the sweep.

* `ellE_bdd` (the search for `ℓ` meets `Kb 48 (ℓ + 1)^40`), `multV_bdd` (the multiplier of one level, at most
  `mult`), **`sweepBody_cost`**, **`sweep_cost`**, **`setup_cost`**.

Not an audit surface.
-/
module

public import FactoringAux.UniCostTop

@[expose] public section

namespace Factoring.Aux

open Factoring.Aux.Copied Factoring.Aux.Copied.PLib Ex Uni Finset SB

namespace UCost

/-! ### The number of levels -/

theorem ell_mono (n : ℕ) : Monotone (iterF (ellStep n) 0) :=
  monotone_nat_of_le_succ fun j => by
    show _ ≤ ellStep n j _
    unfold ellStep; split_ifs <;> omega

theorem iter_ell_le {n j : ℕ} (hj : j ≤ n) : iterF (ellStep n) 0 j ≤ ellOf n := ell_mono n hj

/-- The search for `ℓ = ellOf n`. -/
theorem ellE_bdd {V n : ℕ} {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ} (h0 : σ 0 = n) (hn : n ≤ V) (hl : ellOf n + 1 ≤ V)
    (hK : Kb K0u (ellOf n + 1) ^ 40 ≤ V) : Bdd V σ A ellE := by
  have key : (fun j y => eval (Function.update (Function.update σ 903 j) 904 y) A
      (.lett 905 (.add (.var 904) (.lit 1)) (.ifLt (.var 0) (powE 909 (kbE 905) 40) (.var 904) (.var 905)))) =
      ellStep n := by
    funext j y
    rw [eval_lett]
    have e1 : eval (Function.update (Function.update σ 903 j) 904 y) A (.add (.var 904) (.lit 1)) = y + 1 := by
      simp [Ex.eval]
    rw [e1, eval_ifLt']
    rw [eval_powE 909 _ 40 (fun i => by rw [eval_kbE, eval_kbE]; simp)]
    rw [eval_kbE]
    simp [Ex.eval, ellStep, h0]
  have hK1 : Kb K0u (ellOf n + 1) ≤ Kb K0u (ellOf n + 1) ^ 40 :=
    Nat.le_self_pow (by norm_num) _
  have h48 : 48 ≤ V := le_trans (le_trans (Kb_le (Nat.zero_le _)) hK1) hK
  refine ⟨show σ 0 ≤ V by omega, show 0 ≤ V by omega, fun j hj => ?_⟩
  replace hj : j < n := by simpa [Ex.eval, h0] using hj
  show Bdd V (Function.update (Function.update σ 903 j) 904 (iterF (fun j y => eval (Function.update
    (Function.update σ 903 j) 904 y) A (.lett 905 (.add (.var 904) (.lit 1)) (.ifLt (.var 0) (powE 909 (kbE 905) 40)
      (.var 904) (.var 905)))) 0 j)) A _
  rw [key]
  have hy : iterF (ellStep n) 0 j ≤ ellOf n := iter_ell_le hj.le
  set y := iterF (ellStep n) 0 j
  set σ' := Function.update (Function.update σ 903 j) 904 y
  have e904 : σ' 904 = y := by simp [σ']
  have e0 : σ' 0 = n := by simp [σ', h0]
  refine B_lett (B_add (B_var (by rw [e904]; omega)) (B_lit (by omega)) (by simp only [Ex.eval, e904]; omega)) ?_
  rw [show eval σ' A (.add (.var 904) (.lit 1)) = y + 1 by simp [Ex.eval, e904]]
  set σ'' := Function.update σ' 905 (y + 1)
  have f905 : σ'' 905 = y + 1 := by simp [σ'']
  have f904 : σ'' 904 = y := by simp [σ'', e904]
  have f0 : σ'' 0 = n := by simp [σ'', e0]
  have hKy : Kb K0u (y + 1) ≤ Kb K0u (ellOf n + 1) := Kb_le (by omega)
  have hP : ∀ i ≤ 40, Kb K0u (y + 1) ^ i ≤ V := fun i hi =>
    le_trans (Nat.pow_le_pow_left hKy i) (le_trans (Nat.pow_le_pow_right (by have := Kb_pos (ellOf n + 1); omega) hi) hK)
  have h905 : ∀ i, Function.update σ'' 909 i 905 = y + 1 := fun i => by
    rw [Function.update_of_ne (by norm_num), f905]
  refine B_ifLt (B_var (by rw [f0]; omega)) ?_ (fun _ => B_var (by rw [f904]; omega))
    (fun _ => B_var (by rw [f905]; omega))
  exact bdd_nprod_const (x := 909) (n := .lit 40) (b := kbE 905) (c := Kb K0u (y + 1)) (B_lit (by omega))
    (fun i => kbE_bdd (by rw [h905]; omega) (by rw [h905]; exact le_trans hKy (le_trans hK1 hK)))
    (fun i => by rw [eval_kbE, h905]) (fun i hi => hP i (by simpa [Ex.eval] using hi))

/-! ### The multiplier of one level -/

/-- `mult (3 K^8) λ` (`K` in `43`, `λ` in `40`). -/
theorem multV_bdd {V K lam : ℕ} {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ} (hK : σ 43 = K) (hl : σ 40 = lam)
    (hG4 : (3 * K ^ 8) * (3 * K ^ 8) * ((3 * K ^ 8) * (3 * K ^ 8)) ≤ V) (hl2 : lam + 2 ≤ V) (h64 : 64 ≤ V)
    (hM : mult (3 * K ^ 8) lam ≤ V) : Bdd V σ A (multV 43 40) := by
  set G := 3 * K ^ 8
  have hG4' : G ^ 4 ≤ V := by rw [show G ^ 4 = G * G * (G * G) by ring]; exact hG4
  have hGG4 : G ≤ G ^ 4 := by
    rcases Nat.eq_zero_or_pos G with h | h
    · rw [h]; simp
    · exact Nat.le_self_pow (by norm_num) _
  have hGV : G ≤ V := le_trans hGG4 hG4'
  set p := G * (G - 1) / 2
  have hp : p * p = (rects G).card := (card_rects G).symm
  have hpp : p * p ≤ G ^ 4 := hp ▸ rects_le G
  have hnr : G ^ 4 - p * p = nonRects G := by rw [nonRects_eq, card_rects]
  have hmult : mult G lam = (tB lam + 1) ^ nonRects G * 2 ^ (tB lam * (p * p)) := by rw [hp]; rfl
  have h1 : (tB lam + 1) ^ nonRects G ≤ V :=
    le_trans (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)) (hmult ▸ hM)
  have h2 : 2 ^ (tB lam * (p * p)) ≤ V := le_trans (Nat.le_mul_of_pos_left _ (Nat.pow_pos (by omega))) (hmult ▸ hM)
  have ht : tB lam + 1 ≤ V := by unfold tB; have := Nat.div_le_self (lam + 2) 3; omega
  unfold multV
  refine B_lett (gE_bdd (by norm_num) hK hGV (by omega)) ?_
  rw [eval_gE (by norm_num), hK]
  set σ1 := Function.update σ 910 (3 * K ^ 8)
  have e910 : σ1 910 = G := by simp [σ1, G]
  have hG2 : G * G ≤ V := by
    rcases Nat.eq_zero_or_pos G with h | h
    · rw [h]; omega
    · exact le_trans (Nat.le_mul_of_pos_right _ (Nat.mul_pos h h)) hG4
  have hGG : G * (G - 1) ≤ V := le_trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _)) hG2
  refine B_lett (B_div (B_mul (B_var (by rw [e910]; exact hGV)) (B_sub (B_var (by rw [e910]; exact hGV))
    (B_lit (by omega))) (by simp only [Ex.eval, e910]; exact hGG)) (B_lit (by omega))) ?_
  rw [show eval σ1 A (.div (.mul (.var 910) (.sub (.var 910) (.lit 1))) (.lit 2)) = p by simp [Ex.eval, e910, p]]
  set σ2 := Function.update σ1 911 p
  have e911 : σ2 911 = p := by simp [σ2]
  have hpV : p ≤ V := le_trans (Nat.div_le_self _ _) hGG
  refine B_lett (B_mul (B_var (by rw [e911]; exact hpV)) (B_var (by rw [e911]; exact hpV))
    (by simp only [Ex.eval, e911]; exact le_trans hpp hG4')) ?_
  rw [show eval σ2 A (.mul (.var 911) (.var 911)) = p * p by simp [Ex.eval, e911]]
  set σ3 := Function.update σ2 912 (p * p)
  have f912 : σ3 912 = p * p := by simp [σ3]
  have f910 : σ3 910 = G := by simp [σ3, σ2, e910]
  have f40 : σ3 40 = lam := by simp [σ3, σ2, σ1, hl]
  have u40 : ∀ i, Function.update σ3 913 i 40 = lam := fun i => by rw [Function.update_of_ne (by norm_num), f40]
  have u912 : ∀ i, Function.update σ3 913 i 912 = p * p := fun i => by
    rw [Function.update_of_ne (by norm_num), f912]
  have ePow : eval σ3 A (powE 914 (.var 910) 4) = G ^ 4 := by
    rw [eval_powE 914 _ 4 (fun i => by simp [Ex.eval])]; simp [Ex.eval, f910]
  have BPow : Bdd V σ3 A (powE 914 (.var 910) 4) :=
    bdd_nprod_const (x := 914) (n := .lit 4) (b := .var 910) (c := G) (B_lit (by omega))
      (fun i => show _ ≤ V by rw [Function.update_of_ne (by norm_num), f910]; exact hGV)
      (fun i => by simp [Ex.eval, f910])
      (fun i hi => pow_le_of_le hG4' (by omega) i (by simpa [Ex.eval] using hi))
  have eN1 : eval σ3 A (.sub (powE 914 (.var 910) 4) (.var 912)) = nonRects G := by
    simp only [Ex.eval]; rw [ePow, f912, hnr]
  have P1 : Bdd V σ3 A (.prod 913 (.sub (powE 914 (.var 910) 4) (.var 912)) (.lit 0) (.add (tBE 40) (.lit 1))) :=
    bdd_nprod_const (x := 913) (n := .sub (powE 914 (.var 910) 4) (.var 912)) (b := .add (tBE 40) (.lit 1))
      (c := tB lam + 1) (B_sub BPow (B_var (by rw [f912]; exact le_trans hpp hG4')))
      (fun i => B_add (tBE_bdd (u40 i) hl2 (by omega)) (B_lit (by omega))
        (by show eval _ A (tBE 40) + 1 ≤ V; rw [eval_tBE (u40 i)]; exact ht))
      (fun i => by show eval _ A (tBE 40) + 1 = _; rw [eval_tBE (u40 i)])
      (fun i hi => le_trans (Nat.pow_le_pow_right (by omega) (by rw [eN1] at hi; exact hi)) h1)
  have eP1 : eval σ3 A (.prod 913 (.sub (powE 914 (.var 910) 4) (.var 912)) (.lit 0) (.add (tBE 40) (.lit 1))) =
      (tB lam + 1) ^ nonRects G := by
    rw [show Ex.prod 913 (.sub (powE 914 (.var 910) 4) (.var 912)) (.lit 0) (.add (tBE 40) (.lit 1)) =
      nprod 913 (.sub (powE 914 (.var 910) 4) (.var 912)) (.add (tBE 40) (.lit 1)) from rfl,
      eval_nprod_const (c := tB lam + 1) (fun i => by show eval _ A (tBE 40) + 1 = _; rw [eval_tBE (u40 i)]), eN1]
  have hn2 : tB lam * (p * p) ≤ V := le_trans Nat.lt_two_pow_self.le h2
  have eN2 : eval σ3 A (.mul (tBE 40) (.var 912)) = tB lam * (p * p) := by
    simp only [Ex.eval]; rw [eval_tBE f40, f912]
  have P2 : Bdd V σ3 A (.prod 913 (.mul (tBE 40) (.var 912)) (.lit 0) (.lit 2)) :=
    bdd_nprod_const (x := 913) (n := .mul (tBE 40) (.var 912)) (b := .lit 2) (c := 2)
      (B_mul (tBE_bdd f40 hl2 (by omega)) (B_var (by rw [f912]; exact le_trans hpp hG4'))
        (by rw [eval_tBE f40]; show tB lam * σ3 912 ≤ V; rw [f912]; exact hn2))
      (fun i => B_lit (by omega)) (fun i => rfl)
      (fun i hi => le_trans (Nat.pow_le_pow_right (by norm_num) (by rw [eN2] at hi; exact hi)) h2)
  have eP2 : eval σ3 A (.prod 913 (.mul (tBE 40) (.var 912)) (.lit 0) (.lit 2)) = 2 ^ (tB lam * (p * p)) := by
    rw [show Ex.prod 913 (.mul (tBE 40) (.var 912)) (.lit 0) (.lit 2) = nprod 913 (.mul (tBE 40) (.var 912)) (.lit 2)
      from rfl, eval_nprod_const (c := 2) (fun i => rfl), eN2]
  exact B_mul P1 P2 (by rw [eP1, eP2, ← hmult]; exact hM)

/-! ### The sweep -/

theorem dp_multV : Ex.dp (.mul (.var 309) (multV 43 40)) ≤ 100 := by simp [multV, gE, powE, tBE, Ex.dp]
theorem dp_add310 : Ex.dp (.add (.var 310) (.mul (.mul (.lit 2) (g4E 43)) (tBE 40))) ≤ 100 := by
  simp [g4E, gE, powE, tBE, Ex.dp]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
/-- **The cost of one level of the sweep.** -/
theorem sweepBody_cost {V d lam : ℕ} (st : St) (h307 : st.sc 307 = d + 1 + st.sc 306) (h40 : st.sc 40 = lam)
    (h307V : st.sc 307 ≤ V) (hR : LevelReq V 2 (Kb K0u d) (Gs K0u d) lam) (hlv : lvlV (Kb K0u d) ≤ V)
    (hNP : st.sc 303 * Nc K0u d lam ≤ V)
    (hML : st.sc 310 + 2 * Gs K0u d ^ 4 * tB lam ≤ V) :
    (Cmd.run (sweepBody UP) st).2 ≤ 30 * YB V := by
  set W := Wv V
  have hVW : V ≤ W := le_Wv
  have RW := LevelReq.mono hR hVW
  set K := Kb K0u d
  set G := 3 * K ^ 8
  have hK2 : 2 ≤ K := Kb_ge K0u (by norm_num) d
  have h64 : 64 ≤ V := hR.dec.h64
  have hG1 : 1 ≤ G := by show 1 ≤ 3 * K ^ 8; have := Nat.pow_pos (n := 8) (show 0 < K by omega); omega
  have hG4 : G * G * (G * G) ≤ V := hR.hg4
  have hKV : K ≤ V := le_trans (Nat.le_mul_of_pos_right _ (show 0 < Gs K0u d from hG1)) hR.hKG
  have hN1 : 1 ≤ Nc K0u d lam := Nc_pos _ _ _
  have hl2 : lam + 2 ≤ V := (LevelReq.small hR).1
  have hPB := PB_le_YB V
  have hY := YB_ge V
  -- s1: 45 := d
  obtain ⟨v1, a1, k1⟩ := vw_cset vb_dE (show 45 < 1000 by norm_num) st
  set s1 := (Cmd.run (cset dE 45) st).1
  have k1' : (Cmd.run (cset dE 45) st).2 ≤ PB V := by
    refine le_trans k1 (cost_le_PB ?_ dp_dE)
    exact B_sub (B_sub (B_var (by rw [vw_lt (by norm_num)]; omega)) (B_lit (by omega)))
      (B_var (by rw [vw_lt (by norm_num)]; omega))
  rw [show eval (vw st) st.ar dE = d by
    simp only [dE, Ex.eval, vw_lt (show 307 < 1000 by norm_num), vw_lt (show 306 < 1000 by norm_num), h307]
    omega] at v1
  -- s2: 43 := K
  obtain ⟨v2, a2, k2⟩ := vw_cset (vb_kbE 45 (by norm_num)) (show 43 < 1000 by norm_num) s1
  set s2 := (Cmd.run (cset (kbE 45) 43) s1).1
  have k2' : (Cmd.run (cset (kbE 45) 43) s1).2 ≤ PB V :=
    le_trans k2 (cost_le_PB (kbE_bdd (by rw [v1, Function.update_self]; omega)
      (by rw [v1, Function.update_self]; omega)) (dp_kbE 45))
  rw [eval_kbE, v1, Function.update_self] at v2
  have L2 : vw s2 40 = lam := by
    rw [v2, Function.update_of_ne (by norm_num), Function.update_of_ne (by norm_num), vw_lt (by norm_num), h40]
  have K2 : vw s2 43 = K := by rw [v2, Function.update_self]
  -- s3: 47 := Nc
  obtain ⟨v3, a3, k3⟩ := vw_cset vb_NcE (show 47 < 1000 by norm_num) s2
  set s3 := (Cmd.run (cset (NcE 43 40) 47) s2).1
  have k3' : (Cmd.run (cset (NcE 43 40) 47) s2).2 ≤ PB V :=
    le_trans k3 (cost_le_PB (NcE_bdd K2 L2 (le_trans hG4 hVW) (le_trans hR.hC hVW) (le_trans hl2 hVW) (by omega))
      dp_NcE)
  rw [eval_NcE (d := d) (L := lam) (by norm_num) (by norm_num) (by norm_num) K2 L2] at v3
  -- s4: 303 := 303 · Nc
  obtain ⟨v4, a4, k4⟩ := vw_cset (e := .mul (.var 303) (.var 47)) (by simp [VB]) (show 303 < 1000 by norm_num) s3
  set s4 := (Cmd.run (cset (.mul (.var 303) (.var 47)) 303) s3).1
  have P3 : vw s3 303 = st.sc 303 := by
    rw [v3, Function.update_of_ne (by norm_num), v2, Function.update_of_ne (by norm_num),
      Function.update_of_ne (by norm_num), vw_lt (by norm_num)]
  have n3 : vw s3 47 = Nc K0u d lam := by rw [v3, Function.update_self]
  have k4' : (Cmd.run (cset (.mul (.var 303) (.var 47)) 303) s3).2 ≤ PB V := by
    refine le_trans k4 (cost_le_PB (B_mul (B_var ?_) (B_var ?_) ?_) (by simp [Ex.dp]))
    · rw [P3]; exact le_trans (le_trans (Nat.le_mul_of_pos_right _ hN1) hNP) hVW
    · rw [n3]; exact le_trans hR.hC hVW
    · simp only [Ex.eval, P3, n3]; omega
  -- s6: 310 := 310 + 2 G^4 tB(λ)
  set s5 := s4
  obtain ⟨v6, a6, k6⟩ := vw_cset (e := .add (.var 310) (.mul (.mul (.lit 2) (g4E 43)) (tBE 40)))
    (by simp [VB, g4E, gE, powE, tBE]) (show 310 < 1000 by norm_num) s5
  set s6 := (Cmd.run (cset (.add (.var 310) (.mul (.mul (.lit 2) (g4E 43)) (tBE 40))) 310) s5).1
  have K5 : vw s5 43 = K := by rw [v4, Function.update_of_ne (by norm_num), v3, Function.update_of_ne (by norm_num), K2]
  have L5 : vw s5 40 = lam := by
    rw [v4, Function.update_of_ne (by norm_num), v3, Function.update_of_ne (by norm_num), L2]
  have M5 : vw s5 310 = st.sc 310 := by
    rw [v4, Function.update_of_ne (by norm_num), v3,
      Function.update_of_ne (by norm_num), v2, Function.update_of_ne (by norm_num), Function.update_of_ne (by norm_num),
      vw_lt (by norm_num)]
  have h2G4 : 2 * Gs K0u d ^ 4 ≤ V := by
    have := hR.hLn
    have h1 : 2 * Gs K0u d ^ 4 ≤ (12 * Gs K0u d ^ 3 + 11 * Gs K0u d ^ 4 + 24 * Gs K0u d ^ 4 +
        Gs K0u d * Gs K0u d ^ 3 + Kb K0u d ^ 3 + 12) * (lam + 1) :=
      le_trans (by omega) (Nat.le_mul_of_pos_right _ (by omega))
    exact le_trans h1 (le_trans (Nat.le_mul_of_pos_left _ (by omega)) this)
  have eg4 : eval (vw s5) s5.ar (g4E 43) = Gs K0u d ^ 4 := by rw [eval_g4E (by norm_num) (by norm_num), K5]; rfl
  have k6' : (Cmd.run (cset (.add (.var 310) (.mul (.mul (.lit 2) (g4E 43)) (tBE 40))) 310) s5).2 ≤ PB V := by
    refine le_trans k6 (cost_le_PB ?_ dp_add310)
    have Bg : Bdd W (vw s5) s5.ar (.mul (.lit 2) (g4E 43)) :=
      B_mul (B_lit (by omega)) (g4E_bdd (by norm_num) (by norm_num) K5 (le_trans hG4 hVW) (by omega))
        (by rw [eg4]; simp only [Ex.eval]; omega)
    have Bm : Bdd W (vw s5) s5.ar (.mul (.mul (.lit 2) (g4E 43)) (tBE 40)) :=
      B_mul Bg (tBE_bdd L5 (le_trans hl2 hVW) (by omega)) (by
        simp only [Ex.eval]; rw [eg4, eval_tBE L5]; omega)
    refine B_add (B_var (by rw [M5]; omega)) Bm ?_
    simp only [Ex.eval]; rw [eg4, eval_tBE L5, M5]; omega
  -- s7: the level literals; s8: 101 := L'
  have K6 : s6.sc 43 = K := by
    rw [← vw_lt (show 43 < 1000 by norm_num), v6, Function.update_of_ne (by norm_num), K5]
  have k7' : (Cmd.run UP.lset s6).2 ≤ 15 * PB V := by
    rw [show UP.lset = lvlSet 20 43 from rfl]
    obtain ⟨-, -, -, -, h5⟩ := lvlSet_spec (p := 20) (q := 43) s6 K6 (by norm_num) (Or.inr (by norm_num))
      (by norm_num)
    exact le_trans h5 (set_le_PB (by omega))
  obtain ⟨l1, l2, a7⟩ := UP_ok.lset s6
  set s7 := (Cmd.run UP.lset s6).1
  rw [K6] at l1
  have w7 : ∀ y, ¬ (20 ≤ y ∧ y < 40) → vw s7 y = vw s6 y := fun y hy => by
    by_cases hy' : y < 1000
    · rw [vw_lt hy', vw_lt hy', l2 y hy' (by omega)]
    · simp [vw, hy']
  have lit7 : ∀ v k, lokU K v k → vw s7 v = k := fun v k h => by
    have := UP_ok.lvar K v k h; rw [vw_lt (by omega), l1 v k h]
  have L7 : vw s7 40 = lam := by rw [w7 40 (by omega), v6, Function.update_of_ne (by norm_num), L5]
  obtain ⟨-, -, k8⟩ := vw_cset UP_ok.vlnE (show 101 < 1000 by norm_num) s7
  have k8' : (Cmd.run (cset UP.lnE 101) s7).2 ≤ PB V := by
    refine le_trans k8 ?_
    rw [(UP_ok.lnE K (vw s7) s7.ar lit7).2]
    exact cost_le_PB (LnE_bdd (P := lvP K) RW.hLn L7) (le_trans (dpT_LnE _) (by norm_num))
  set s8 := (Cmd.run (cset UP.lnE 101) s7).1
  have hle := seq_le k1' (seq_le k2' (seq_le k3' (seq_le k4' (seq_le k6' (seq_le k7' (seq_le k8'
    (le_refl (Cmd.run (.copy 40 101) s8).2)))))))
  have e : (Cmd.run (sweepBody UP) st).2 = (Cmd.run (.seq (cset dE 45) <| .seq (cset (kbE 45) 43) <|
      .seq (cset (NcE 43 40) 47) <|
      .seq (cset (.mul (.var 303) (.var 47)) 303) <|
      .seq (cset (.add (.var 310) (.mul (.mul (.lit 2) (g4E 43)) (tBE 40))) 310) <|
      .seq UP.lset <| .seq (cset UP.lnE 101) (.copy 40 101)) st).2 := rfl
  rw [e]
  refine le_trans hle ?_
  simp only [Cmd.run_copy]
  omega

theorem NPof_pos (K0 : ℕ) : ∀ d L, 0 < NPof K0 d L
  | 0, _ => by simp [NPof]
  | d + 1, L => Nat.mul_pos (Nc_pos _ _ _) (NPof_pos K0 d _)

/-- The invariant of the sweep (costs). -/
def SC (V : ℕ) (st : St) (ℓ L : ℕ) (j : ℕ) (s : St) : Prop :=
  SwInv st ℓ L j s ∧ ∀ d, d + j = ℓ → DeepReq V 2 K0u d (s.sc 40)

theorem sc_step {V ℓ L : ℕ} (st : St) (h307 : st.sc 307 = ℓ) (hℓ : ℓ ≤ V) (hlv : lvlV (Kb K0u ℓ) ≤ V)
    (hnp : NPof K0u ℓ L ≤ V) (hml : mlogN K0u ℓ L ≤ V) (j : ℕ) (s : St) (hj : j < ℓ)
    (hs : SC V st ℓ L j s) :
    SC V st ℓ L (j + 1) (Cmd.run (sweepBody UP) (s.setSc 306 j)).1 ∧
      (Cmd.run (sweepBody UP) (s.setSc 306 j)).2 ≤ 30 * YB V := by
  obtain ⟨⟨hI, sfr, sar⟩, hD⟩ := hs
  set s' := s.setSc 306 j
  obtain ⟨d, rfl⟩ : ∃ d, ℓ = d + 1 + j := ⟨ℓ - 1 - j, by omega⟩
  obtain ⟨lam, e40, e303, e310⟩ := hI (d + 1) (by omega)
  have hR := hD (d + 1) (by omega)
  rw [e40] at hR
  have g : ∀ y, y ≠ 306 → s'.sc y = s.sc y := fun y hy => by simp [s', Function.update_of_ne hy]
  have h307' : s'.sc 307 = d + 1 + s'.sc 306 := by
    rw [g 307 (by norm_num), sfr 307 (by norm_num) (by simp [WS]) (by norm_num), h307]; simp [s']
  obtain ⟨r40, r303, r310, rfr, rar⟩ := sweepBody_spec s' (d := d) (L := lam) h307'
    (by rw [g 40 (by norm_num), e40])
  have hNP : s'.sc 303 * Nc K0u d lam ≤ V := by
    rw [g 303 (by norm_num)]
    refine le_trans (Nat.mul_le_mul_left _ ?_) (le_trans (le_of_eq e303) hnp)
    exact Nat.le_mul_of_pos_right _ (NPof_pos _ _ _)
  have hML : s'.sc 310 + 2 * Gs K0u d ^ 4 * tB lam ≤ V := by
    rw [g 310 (by norm_num)]
    have : mlogN K0u (d + 1) lam = 2 * Gs K0u d ^ 4 * tB lam + mlogN K0u d (Lnext (Kb K0u d) (Gs K0u d) lam) := rfl
    omega
  have hc := sweepBody_cost s' h307' (by rw [g 40 (by norm_num), e40])
    (by rw [g 307 (by norm_num), sfr 307 (by norm_num) (by simp [WS]) (by norm_num), h307]; exact hℓ)
    hR.1 (le_trans (lvlV_mono (Kb_le (by omega))) hlv) hNP hML
  refine ⟨⟨⟨fun d' hd' => ?_, fun y hy hW h306 => ?_, by rw [rar]; exact sar⟩, fun d' hd' => ?_⟩, hc⟩
  · obtain rfl : d' = d := by omega
    refine ⟨_, r40, ?_, ?_⟩
    · rw [r303, g 303 (by norm_num), ← e303, NPof]; ring
    · rw [r310, g 310 (by norm_num), ← e310, mlogN]; ring
  · rw [rfr y hy hW, g y h306, sfr y hy hW h306]
  · obtain rfl : d' = d := by omega
    rw [r40]; exact hR.2

/-- **The cost of the sweep.** -/
theorem sweep_cost {V ℓ L : ℕ} (st : St) (h307 : st.sc 307 = ℓ) (h40 : st.sc 40 = L) (h303 : st.sc 303 = 1)
    (h310 : st.sc 310 = 0) (hR : DeepReq V 2 K0u ℓ L) (hℓ : ℓ ≤ V)
    (hlv : lvlV (Kb K0u ℓ) ≤ V) (hnp : NPof K0u ℓ L ≤ V) (hml : mlogN K0u ℓ L ≤ V) :
    (Cmd.run (.loop 307 306 (sweepBody UP)) st).2 ≤ 32 * YB V ^ 2 := by
  have h0 : SC V st ℓ L 0 st := by
    refine ⟨⟨fun d hd => ⟨L, h40, ?_, ?_⟩, fun _ _ _ _ => rfl, rfl⟩, fun d hd => ?_⟩ <;>
      obtain rfl : d = ℓ := by omega
    · rw [h303, one_mul]
    · rw [h310, zero_add]
    · rw [h40]; exact hR
  have := Cmd.loop_cost_le (b := 307) (c := 306) (body := sweepBody UP) (st := st) (SC V st ℓ L) (30 * YB V ^ 1) h0
    (fun j s hj hs => (sc_step st h307 hℓ hlv hnp hml j s (by omega) hs).1)
    (fun j s hj hs => by rw [pow_one]; exact (sc_step st h307 hℓ hlv hnp hml j s (by omega) hs).2)
  rw [h307] at this
  exact le_trans this (loop_le (le_trans hℓ le_Wv))

theorem dp_ellE : Ex.dp ellE ≤ 100 := by simp [ellE, kbE, powE, Ex.dp]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
/-- **The cost of the parameters and the sweep.** -/
theorem setup_cost {V : ℕ} (st : St) (hT : TopReq V 2 K0u (ellOf (st.sc 0)) (st.sc 0))
    (hml : mlogN K0u (ellOf (st.sc 0)) (Ltop (Kb K0u (ellOf (st.sc 0))) (Gs K0u (ellOf (st.sc 0)))
      (sOf (st.sc 0))) ≤ V)
    (hnp : NPof K0u (ellOf (st.sc 0)) (Ltop (Kb K0u (ellOf (st.sc 0))) (Gs K0u (ellOf (st.sc 0)))
      (sOf (st.sc 0))) ≤ V)
    (hlv : lvlV (Kb K0u (ellOf (st.sc 0))) ≤ V) (hsm : st.sc 0 + ellOf (st.sc 0) + 64 ≤ V)
    (hkb : Kb K0u (ellOf (st.sc 0) + 1) ^ 40 ≤ V) :
    (Cmd.run (setup UP) st).2 ≤ 60 * YB V ^ 2 := by
  set n := st.sc 0
  set ℓ := ellOf n
  set K := Kb K0u ℓ
  set L := Ltop K (Gs K0u ℓ) (sOf n)
  have hW := @le_Wv V
  have RW := TopReq.mono hT hW
  have hY := YB_ge V
  have hPB := PB_le_YB V
  have hY2 : YB V ≤ YB V ^ 2 := Nat.le_self_pow (by norm_num) _
  have hK2 : 2 ≤ K := Kb_ge K0u (by norm_num) ℓ
  have hg : 0 < Gs K0u ℓ := Nat.mul_pos (by norm_num) (Nat.pow_pos (by omega))
  have hKV : K ≤ V := le_trans (Nat.le_mul_of_pos_right _ hg) hT.hKG
  have hℓV : ellOf n ≤ Wv V := by show ℓ ≤ Wv V; omega
  have hKbV : Kb K0u (ellOf n) ≤ Wv V := by show K ≤ Wv V; omega
  -- e1: 11 := s
  obtain ⟨v1, a1, k1⟩ := vw_cset (e := sE) (by simp [sE, pow2, VB]) (show 11 < 1000 by norm_num) st
  set e1 := (Cmd.run (cset sE 11) st).1
  have k1' : (Cmd.run (cset sE 11) st).2 ≤ PB V :=
    le_trans k1 (cost_le_PB (sE_bdd (by rw [vw_lt (by norm_num)]; exact RW.hn)) (le_trans dpT_sE (by norm_num)))
  rw [eval_sE, vw_lt (show 0 < 1000 by norm_num)] at v1
  -- e2: 307 := ℓ
  obtain ⟨v2, a2, k2⟩ := vw_cset (e := ellE) (by simp [ellE, kbE, powE, VB]) (show 307 < 1000 by norm_num) e1
  set e2 := (Cmd.run (cset ellE 307) e1).1
  have z1 : vw e1 0 = n := by rw [v1, Function.update_of_ne (by norm_num), vw_lt (show 0 < 1000 by norm_num)]
  have k2' : (Cmd.run (cset ellE 307) e1).2 ≤ PB V :=
    le_trans k2 (cost_le_PB (ellE_bdd z1 (by omega) (by omega) (le_trans hkb hW)) dp_ellE)
  rw [eval_ellE, z1] at v2
  -- e3: 43 := K
  obtain ⟨v3, a3, k3⟩ := vw_cset (vb_kbE 307 (by norm_num)) (show 43 < 1000 by norm_num) e2
  set e3 := (Cmd.run (cset (kbE 307) 43) e2).1
  have k3' : (Cmd.run (cset (kbE 307) 43) e2).2 ≤ PB V :=
    le_trans k3 (cost_le_PB (kbE_bdd (by rw [v2, Function.update_self]; exact hℓV)
      (by rw [v2, Function.update_self]; exact hKbV)) (dp_kbE 307))
  rw [eval_kbE, v2, Function.update_self] at v3
  obtain ⟨v4, a4, -⟩ := vw_copy (show 316 < 1000 by norm_num) (show 43 < 1000 by norm_num) e3
  set e4 := (Cmd.run (.copy 316 43) e3).1
  rw [v3, Function.update_self] at v4
  have K4 : e4.sc 43 = K := by
    rw [← vw_lt (show 43 < 1000 by norm_num), v4, Function.update_of_ne (by norm_num), Function.update_self]
  have k5' : (Cmd.run UP.tset e4).2 ≤ 15 * PB V := by
    rw [show UP.tset = topSet 43 from rfl]
    obtain ⟨-, -, -, -, h5⟩ := topSet_spec (q := 43) e4 K4 (Or.inr (by norm_num)) (by norm_num)
    have := set_le_PB (V := V) (K := K) (by omega)
    omega
  obtain ⟨t1, t2, a5⟩ := UP_ok.tset e4
  set e5 := (Cmd.run UP.tset e4).1
  rw [K4] at t1
  have w5 : ∀ y < 1000, y ≠ 1 → y ≠ 3 → (y < 5 ∨ 9 < y) → vw e5 y = vw e4 y := fun y hy h1 h3 h59 => by
    rw [vw_lt hy, vw_lt hy, t2 y hy h1 h3 h59]
  obtain ⟨v6, a6, k6⟩ := vw_cset UP_ok.vl0E (show 12 < 1000 by norm_num) e5
  set e6 := (Cmd.run (cset UP.l0E 12) e5).1
  have tk5 : ∀ v k, tokU K v k → vw e5 v = k := fun v k h => by
    have := topOk_lt h; rw [vw_lt (by omega), t1 v k h]
  have s5 : vw e5 11 = sOf n := by
    rw [w5 11 (by norm_num) (by norm_num) (by norm_num) (by norm_num), v4, Function.update_of_ne (by norm_num),
      Function.update_of_ne (by norm_num), Function.update_of_ne (by norm_num), v1, Function.update_self]
  have k6' : (Cmd.run (cset UP.l0E 12) e5).2 ≤ PB V := by
    refine le_trans k6 ?_
    rw [(UP_ok.l0E K (vw e5) e5.ar tk5).2]
    exact cost_le_PB (L0E_bdd RW.mul s5 RW.hL0) (le_trans (dpT_L0E _ _) (by norm_num))
  rw [(UP_ok.l0E K (vw e5) e5.ar tk5).1, eval_L0E s5] at v6
  obtain ⟨v7, a7, -⟩ := vw_copy (show 40 < 1000 by norm_num) (show 12 < 1000 by norm_num) e6
  set e7 := (Cmd.run (.copy 40 12) e6).1
  obtain ⟨v8, a8, -⟩ := vw_setK (k := 1) (show 303 < 1000 by norm_num) e7
  set e8 := (Cmd.run (.setK 303 1) e7).1
  obtain ⟨v10, a10, -⟩ := vw_setK (k := 0) (show 310 < 1000 by norm_num) e8
  set e10 := (Cmd.run (.setK 310 0) e8).1
  have L6 : vw e6 12 = L := by rw [v6, Function.update_self]; rfl
  have g10 : ∀ y, y ≠ 310 → y ≠ 309 → y ≠ 303 → y ≠ 40 → vw e10 y = vw e6 y := fun y a _ c d => by
    rw [v10, Function.update_of_ne a, v8, Function.update_of_ne c, v7,
      Function.update_of_ne d]
  have k11 := sweep_cost e10 (ℓ := ℓ) (L := L)
    (by rw [← vw_lt (show 307 < 1000 by norm_num), g10 307 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
      v6, Function.update_of_ne (by norm_num), w5 307 (by norm_num) (by norm_num) (by norm_num) (by norm_num), v4]
        simp [ℓ, n])
    (by rw [← vw_lt (show 40 < 1000 by norm_num), v10, Function.update_of_ne (by norm_num),
      v8, Function.update_of_ne (by norm_num), v7, Function.update_self, L6])
    (by rw [← vw_lt (show 303 < 1000 by norm_num), v10, Function.update_of_ne (by norm_num),
      v8, Function.update_self])
    (by rw [← vw_lt (show 310 < 1000 by norm_num), v10, Function.update_self])
    hT.deep (by omega) hlv hnp hml
  have hle := seq_le k1' (seq_le k2' (seq_le k3' (seq_le (le_refl (Cmd.run (.copy 316 43) e3).2) (seq_le k5'
    (seq_le k6' (seq_le (le_refl (Cmd.run (.copy 40 12) e6).2) (seq_le (le_refl (Cmd.run (.setK 303 1) e7).2)
      (seq_le (le_refl (Cmd.run (.setK 310 0) e8).2) k11))))))))
  have e : (Cmd.run (setup UP) st).2 = (Cmd.run (.seq (cset sE 11) <| .seq (cset ellE 307) <|
      .seq (cset (kbE 307) 43) <| .seq (.copy 316 43) <|
      .seq UP.tset <| .seq (cset UP.l0E 12) <|
      .seq (.copy 40 12) <| .seq (.setK 303 1) <| .seq (.setK 310 0) <|
      .loop 307 306 (sweepBody UP)) st).2 := rfl
  rw [e]
  refine le_trans hle ?_
  simp only [Cmd.run_copy, Cmd.run_setK]
  omega

end UCost

end Factoring.Aux
