/-
The cost of the uniform counting command: one level of one path (**`lvlBody_cost`**).

The chain of states is `lvlBody_spec`'s; at each step the cost is bounded by the expression's value bound
(`Bdd (Wv V)`) and its depth (`cost_le_PB`), the copies' costs being the originals' (`UOK`).

Not an audit surface.
-/
module

public import FactoringAux.UniCostExp

@[expose] public section

namespace Factoring.Aux

open Factoring.Aux.Copied Factoring.Aux.Copied.PLib Ex Uni Finset SB

namespace UCost

theorem dp_rdT : Ex.dp rdT = 9 := by simp [rdT, rdTE, pow2, Ex.dp]
theorem dp_dE : Ex.dp dE ≤ 100 := by simp [dE, Ex.dp]
theorem dp_kbE (v : ℕ) : Ex.dp (kbE v) ≤ 100 := by simp [kbE, powE, Ex.dp]
theorem dp_NcE : Ex.dp (NcE 43 40) ≤ 100 := by simp [NcE, g4E, gE, powE, tBE, Ex.dp]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
/-- **The cost of one level of one path.** -/
theorem lvlBody_cost {V m d L par : ℕ} (st : St) (T : Clique (ZMod m) (Kb K0u (d + 1)) L)
    (hm : 1 < m) (h10 : st.sc 10 = m) (h307 : st.sc 307 = d + 1 + st.sc 306) (h40 : st.sc 40 = L)
    (h41 : st.sc 41 = par) (hpar : par < 3) (hpj : par ≠ st.sc 306 % 2) (h42 : st.sc 42 = Kb K0u (d + 1))
    (hT : Holds st.ar par T) (h305 : st.sc 305 ≤ V) (h307V : st.sc 307 ≤ V)
    (hR : LevelReq V m (Kb K0u d) (Gs K0u d) L) (hLK : 2 ^ (L * Kb K0u (d + 1)) ≤ V)
    (hlv : lvlV (Kb K0u d) ≤ V) :
    (Cmd.run (lvlBody UP) st).2 ≤ 40 * YB V := by
  have H := UP_ok
  set W := Wv V
  have hVW : V ≤ W := le_Wv
  have hVV : V * V ≤ W := sq_le_Wv
  have RW : LevelReq W m (Kb K0u d) (Gs K0u d) L := LevelReq.mono hR hVW
  set j := st.sc 306
  set K := Kb K0u d
  set G := 3 * K ^ 8
  set N := Nc K0u d L
  set R := st.sc 305
  set c := R % N
  set L' := Lnext K G L
  have hN : 0 < N := Nc_pos _ _ _
  have hc : c < N := Nat.mod_lt _ hN
  have hK2 : 2 ≤ K := Kb_ge K0u (by norm_num) d
  have h64 : 64 ≤ V := hR.dec.h64
  have hmV : m ≤ V := hR.dec.mV
  have hG1 : 1 ≤ G := by show 1 ≤ 3 * K ^ 8; have := Nat.pow_pos (n := 8) (show 0 < K by omega); omega
  have hG4 : G * G * (G * G) ≤ V := hR.hg4
  have hGG : G * G ≤ V := le_trans (Nat.le_mul_of_pos_right _ (Nat.mul_pos (by omega) (by omega))) hG4
  have hKV : K ≤ V := le_trans (Nat.le_mul_of_pos_right _ (show 0 < Gs K0u d from hG1)) hR.hKG
  have hNV : N ≤ V := hR.hC
  have hPB := PB_le_YB V
  have hY64 := YB_ge V
  -- s1: 45 := d
  obtain ⟨v1, a1, k1⟩ := vw_cset vb_dE (show 45 < 1000 by norm_num) st
  set s1 := (Cmd.run (cset dE 45) st).1
  have k1' : (Cmd.run (cset dE 45) st).2 ≤ PB V := by
    refine le_trans k1 (cost_le_PB ?_ dp_dE)
    exact B_sub (B_sub (B_var (by rw [vw_lt (by norm_num)]; omega)) (B_lit (by omega)))
      (B_var (by rw [vw_lt (by norm_num)]; omega))
  have e1 : eval (vw st) st.ar dE = d := by
    simp only [dE, Ex.eval, vw_lt (show 307 < 1000 by norm_num), vw_lt (show 306 < 1000 by norm_num), h307]
    omega
  rw [e1] at v1
  -- s2: 43 := K
  obtain ⟨v2, a2, k2⟩ := vw_cset (vb_kbE 45 (by norm_num)) (show 43 < 1000 by norm_num) s1
  set s2 := (Cmd.run (cset (kbE 45) 43) s1).1
  have k2' : (Cmd.run (cset (kbE 45) 43) s1).2 ≤ PB V := by
    refine le_trans k2 (cost_le_PB (kbE_bdd (by rw [v1, Function.update_self]; omega)
      (by rw [v1, Function.update_self]; omega)) (dp_kbE 45))
  rw [eval_kbE, v1, Function.update_self] at v2
  -- s3: the level literals
  have s2_43 : s2.sc 43 = K := by rw [← vw_lt (show 43 < 1000 by norm_num), v2, Function.update_self]
  have k3' : (Cmd.run UP.lset s2).2 ≤ 15 * PB V := by
    rw [show UP.lset = lvlSet 20 43 from rfl]
    obtain ⟨-, -, -, -, h5⟩ := lvlSet_spec (p := 20) (q := 43) s2 s2_43 (by norm_num) (Or.inr (by norm_num))
      (by norm_num)
    exact le_trans h5 (set_le_PB (by omega))
  obtain ⟨l1, l2, a3⟩ := H.lset s2
  set s3 := (Cmd.run UP.lset s2).1
  rw [s2_43] at l1
  have v3 : ∀ y, ¬ (20 ≤ y ∧ y < 40) → vw s3 y = vw s2 y := fun y hy => by
    by_cases hy' : y < 1000
    · rw [vw_lt hy', vw_lt hy', l2 y hy' (by omega)]
    · simp [vw, hy']
  have lit3 : ∀ v k, lokU K v k → vw s3 v = k := fun v k h => by
    have := H.lvar K v k h; rw [vw_lt (by omega), l1 v k h]
  have c3 : ∀ y, ¬ (20 ≤ y ∧ y < 40) → y ≠ 45 → y ≠ 43 → vw s3 y = vw st y := fun y h1 h2 h3 => by
    rw [v3 y h1, v2, Function.update_of_ne h3, Function.update_of_ne h2]
  -- s4: 47 := N
  obtain ⟨v4, a4, k4⟩ := vw_cset vb_NcE (show 47 < 1000 by norm_num) s3
  set s4 := (Cmd.run (cset (NcE 43 40) 47) s3).1
  have K3 : vw s3 43 = K := by rw [v3 43 (by omega), v2, Function.update_self]
  have L3 : vw s3 40 = L := by rw [c3 40 (by omega) (by omega) (by omega), vw_lt (by norm_num), h40]
  have k4' : (Cmd.run (cset (NcE 43 40) 47) s3).2 ≤ PB V :=
    le_trans k4 (cost_le_PB (NcE_bdd K3 L3 (le_trans hG4 hVW) (le_trans hR.hC hVW)
      (le_trans (LevelReq.small hR).1 hVW) (by omega)) dp_NcE)
  rw [eval_NcE (d := d) (L := L) (by norm_num) (by norm_num) (by norm_num) K3 L3] at v4
  have c4 : ∀ y, ¬ (20 ≤ y ∧ y < 40) → y ≠ 45 → y ≠ 43 → y ≠ 47 → vw s4 y = vw st y := fun y h1 h2 h3 h4 => by
    rw [v4, Function.update_of_ne h4, c3 y h1 h2 h3]
  -- s5: 100 := c, s6: 305 := R / N
  obtain ⟨v5, a5, k5⟩ := vw_cset (e := .mod (.var 305) (.var 47)) (by simp [VB]) (show 100 < 1000 by norm_num) s4
  set s5 := (Cmd.run (cset (.mod (.var 305) (.var 47)) 100) s4).1
  have r4 : vw s4 305 = R := by rw [c4 305 (by omega) (by omega) (by omega) (by omega), vw_lt (by norm_num)]
  have n4 : vw s4 47 = N := by rw [v4, Function.update_self]
  have k5' : (Cmd.run (cset (.mod (.var 305) (.var 47)) 100) s4).2 ≤ PB V :=
    le_trans k5 (cost_le_PB (B_mod (B_var (by rw [r4]; omega)) (B_var (by rw [n4]; omega))) (by simp [Ex.dp]))
  rw [show eval (vw s4) s4.ar (.mod (.var 305) (.var 47)) = c by simp only [Ex.eval, r4, n4]; rfl] at v5
  obtain ⟨v6, a6, k6⟩ := vw_cset (e := .div (.var 305) (.var 47)) (by simp [VB]) (show 305 < 1000 by norm_num) s5
  set s6 := (Cmd.run (cset (.div (.var 305) (.var 47)) 305) s5).1
  have r5 : vw s5 305 = R := by rw [v5, Function.update_of_ne (by norm_num), r4]
  have n5 : vw s5 47 = N := by rw [v5, Function.update_of_ne (by norm_num), n4]
  have k6' : (Cmd.run (cset (.div (.var 305) (.var 47)) 305) s5).2 ≤ PB V :=
    le_trans k6 (cost_le_PB (B_div (B_var (by rw [r5]; omega)) (B_var (by rw [n5]; omega))) (by simp [Ex.dp]))
  rw [show eval (vw s5) s5.ar (.div (.var 305) (.var 47)) = R / N by
    simp only [Ex.eval, v5, Function.update_of_ne (show (305 : ℕ) ≠ 100 by norm_num),
      Function.update_of_ne (show (47 : ℕ) ≠ 100 by norm_num), r4, n4]] at v6
  -- the level's context
  have c6 : ∀ y, y < 100 → ¬ (20 ≤ y ∧ y < 40) → y ≠ 45 → y ≠ 43 → y ≠ 47 → (vw s6) y = vw st y :=
    fun y hy h1 h2 h3 h4 => by
      rw [v6, Function.update_of_ne (by omega), v5, Function.update_of_ne (by omega), c4 y h1 h2 h3 h4]
  have lit6 : ∀ v k, lokU K v k → (vw s6) v = k := fun v k h => by
    have := H.lvar K v k h
    rw [v6, Function.update_of_ne (by omega), v5, Function.update_of_ne (by omega), v4,
      Function.update_of_ne (by omega), lit3 v k h]
  have ar6 : s6.ar = st.ar := by rw [a6, a5, a4, a3, a2, a1]
  have q42 : vw s6 42 = Kb K0u (d + 1) := by
    rw [c6 42 (by norm_num) (by omega) (by omega) (by omega) (by omega), vw_lt (by norm_num), h42]
  have q40 : vw s6 40 = L := by
    rw [c6 40 (by norm_num) (by omega) (by omega) (by omega) (by omega), vw_lt (by norm_num), h40]
  have q41 : vw s6 41 = par := by
    rw [c6 41 (by norm_num) (by omega) (by omega) (by omega) (by omega), vw_lt (by norm_num), h41]
  have hKb : Kb K0u (d + 1) ≤ V := hGG
  have mkT : ∀ A', Holds A' par T → TBdd W 60 (vw s6) A' 60 61 rdT (Kb K0u (d + 1)) := fun A' hA' =>
    rdT_tbdd hA' q42 q40 q41 hpar hm hmV hKb hLK
  have hT6 : TRep m 60 (vw s6) s6.ar 60 61 rdT T := by
    rw [ar6]
    exact rdTE_rep (K := Kb K0u (d + 1)) hm hT q42 q40 q41 (by norm_num) (by norm_num) (by norm_num)
  have mkH : ∀ A', TRep m 60 (vw s6) A' 60 61 rdT T → LevelHyp m 60 (vw s6) A' (lvP K) L T := fun A' hr =>
    { hm := hm, hK := hK2, hG := rfl, rep := hr,
      vm := by show (vw s6) 10 = m; rw [c6 10 (by norm_num) (by omega) (by omega) (by omega) (by omega), vw_lt (by norm_num), h10]
      vl := q40
      hvm := by simp [lvP], hγ := by simp [lvP], hΘ := by simp [lvP], hγΘ := by simp [lvP],
      hlγ := by simp [lvP], hBT := by simp [lvP], hl := by simp [lvP], hγb := by simp [lvP],
      hΘb := by simp [lvP] }
  have H6 := mkH s6.ar hT6
  have T6 : TBdd W 60 (vw s6) s6.ar 60 61 rdT (Kb K0u (d + 1)) := mkT s6.ar (by rw [ar6]; exact hT)
  -- s7: 101 := L'
  obtain ⟨v7, a7, k7⟩ := vw_cset H.vlnE (show 101 < 1000 by norm_num) s6
  set s7 := (Cmd.run (cset UP.lnE 101) s6).1
  have k7' : (Cmd.run (cset UP.lnE 101) s6).2 ≤ PB V := by
    refine le_trans k7 ?_
    rw [(H.lnE K (vw s6) s6.ar lit6).2]
    exact cost_le_PB (LnE_bdd (P := lvP K) RW.hLn q40) (le_trans (dpT_LnE _) (by norm_num))
  rw [(H.lnE K (vw s6) s6.ar lit6).1, LevelEx.eval_LnE (lam := L) H6.vl] at v7
  -- s8, s9: the searches
  have ag7 : Ag 100 (vw s6) (vw s7) := fun y hy => by rw [v7, Function.update_of_ne (by omega)]
  have c7 : vw s7 100 = c := by
    rw [v7, Function.update_of_ne (by norm_num), v6, Function.update_of_ne (by norm_num), v5, Function.update_self]
  have L7 : vw s7 101 = L' := by rw [v7, Function.update_self]; rfl
  have lit7 : ∀ v k, lokU K v k → vw s7 v = k := fun v k h => by
    have := H.lvar K v k h; rw [ag7 v (by omega), lit6 v k h]
  obtain ⟨v8, a8, k8⟩ := vw_cset (H.vsrE false) (show 104 < 1000 by norm_num) s7
  set s8 := (Cmd.run (cset (UP.srE false) 104) s7).1
  have k8' : (Cmd.run (cset (UP.srE false) 104) s7).2 ≤ PB V := by
    refine le_trans k8 ?_
    rw [(H.srE K false (vw s7) s7.ar lit7).2, show s7.ar = s6.ar from a7]
    exact cost_le_PB (lvl_search_bdd H6 T6 RW false hc ag7 c7 L7)
      (le_trans (dpT_level_search _ false _ _) (by norm_num))
  have hs8 : eval (vw s7) s6.ar (GroupEx.searchE (LevelEx.gs (lvP K) false) 102 103) = _ :=
    lvl_search_row H6 hc ag7 c7 L7
  rw [(H.srE K false (vw s7) s7.ar lit7).1, show s7.ar = s6.ar from a7, hs8] at v8
  have ag8 : Ag 100 (vw s6) (vw s8) := fun y hy => by rw [v8, Function.update_of_ne (by omega), ag7 y hy]
  have c8 : vw s8 100 = c := by rw [v8, Function.update_of_ne (by norm_num), c7]
  have L8 : vw s8 101 = L' := by rw [v8, Function.update_of_ne (by norm_num), L7]
  have lit8 : ∀ v k, lokU K v k → vw s8 v = k := fun v k h => by
    have := H.lvar K v k h; rw [ag8 v (by omega), lit6 v k h]
  obtain ⟨v9, a9, k9⟩ := vw_cset (H.vsrE true) (show 105 < 1000 by norm_num) s8
  set s9 := (Cmd.run (cset (UP.srE true) 105) s8).1
  have k9' : (Cmd.run (cset (UP.srE true) 105) s8).2 ≤ PB V := by
    refine le_trans k9 ?_
    rw [(H.srE K true (vw s8) s8.ar lit8).2, show s8.ar = s6.ar by rw [a8, a7]]
    exact cost_le_PB (lvl_search_bdd H6 T6 RW true hc ag8 c8 L8)
      (le_trans (dpT_level_search _ true _ _) (by norm_num))
  have hs9 : eval (vw s8) s6.ar (GroupEx.searchE (LevelEx.gs (lvP K) true) 102 103) = _ :=
    lvl_search_col H6 hc ag8 c8 L8
  rw [(H.srE K true (vw s8) s8.ar lit8).1, show s8.ar = s6.ar by rw [a8, a7], hs9] at v9
  have ag9 : Ag 100 (vw s6) (vw s9) := fun y hy => by rw [v9, Function.update_of_ne (by omega), ag8 y hy]
  have c9 : vw s9 100 = c := by rw [v9, Function.update_of_ne (by norm_num), c8]
  have L9 : vw s9 101 = L' := by rw [v9, Function.update_of_ne (by norm_num), L8]
  -- s10: 320 := j % 2, s11: 321 := K · 2^(L' K)
  obtain ⟨v10, a10, k10⟩ := vw_cset (e := .mod (.var 306) (.lit 2)) (by simp [VB]) (show 320 < 1000 by norm_num) s9
  set s10 := (Cmd.run (cset (.mod (.var 306) (.lit 2)) 320) s9).1
  have j9 : vw s9 306 = j := by
    rw [v9, Function.update_of_ne (by norm_num), v8, Function.update_of_ne (by norm_num), v7,
      Function.update_of_ne (by norm_num), v6, Function.update_of_ne (by norm_num), v5,
      Function.update_of_ne (by norm_num), c4 306 (by omega) (by omega) (by omega) (by omega), vw_lt (by norm_num)]
  have k10' : (Cmd.run (cset (.mod (.var 306) (.lit 2)) 320) s9).2 ≤ PB V :=
    le_trans k10 (cost_le_PB (B_mod (B_var (by rw [j9]; omega)) (B_lit (by omega))) (by simp [Ex.dp]))
  rw [show eval (vw s9) s9.ar (.mod (.var 306) (.lit 2)) = j % 2 by simp only [Ex.eval, j9]] at v10
  obtain ⟨v11, a11, k11⟩ := vw_cset (e := .mul (.var 43) (pow2 915 (.mul (.var 101) (.var 43))))
    (by simp [VB, pow2]) (show 321 < 1000 by norm_num) s10
  set s11 := (Cmd.run (cset (.mul (.var 43) (pow2 915 (.mul (.var 101) (.var 43)))) 321) s10).1
  have k10K : vw s10 43 = K := by
    rw [v10, Function.update_of_ne (by norm_num), ag9 43 (by norm_num), v6, Function.update_of_ne (by norm_num),
      v5, Function.update_of_ne (by norm_num), v4, Function.update_of_ne (by norm_num),
      v3 43 (by omega), v2, Function.update_self]
  have L10 : vw s10 101 = L' := by rw [v10, Function.update_of_ne (by norm_num), L9]
  have hLK' : 2 ^ (L' * K) ≤ V := hR.hLK
  have hL'K : L' * K ≤ V := le_trans Nat.lt_two_pow_self.le hLK'
  have hn : K * 2 ^ (L' * K) ≤ W := le_trans (Nat.mul_le_mul hKV hLK') hVV
  have k11' : (Cmd.run (cset (.mul (.var 43) (pow2 915 (.mul (.var 101) (.var 43)))) 321) s10).2 ≤ PB V := by
    refine le_trans k11 (cost_le_PB ?_ (by simp [Ex.dp, pow2]))
    have Bm : Bdd W (vw s10) s10.ar (.mul (.var 101) (.var 43)) :=
      B_mul (B_var (by rw [L10]; exact le_trans (le_trans (Nat.le_mul_of_pos_right _ (by omega)) hL'K) hVW))
        (B_var (by rw [k10K]; omega)) (by simp only [Ex.eval, L10, k10K]; omega)
    refine B_mul (B_var (by rw [k10K]; omega)) (B_pow2 Bm (by omega) (by simp only [Ex.eval, L10, k10K]; omega)) ?_
    simp only [Ex.eval, eval_pow2, L10, k10K]; exact hn
  rw [show eval (vw s10) s10.ar (.mul (.var 43) (pow2 915 (.mul (.var 101) (.var 43)))) = K * 2 ^ (L' * K) by
    simp only [Ex.eval, eval_pow2, k10K, L10]] at v11
  -- s12: the next table
  set T' := nextT K (Kb_pos d) T ⟨c, hc⟩
  have ar11 : s11.ar = st.ar := by rw [a11, a10, a9, a8, a7, ar6]
  have p11 : s11.sc 320 = j % 2 := by
    rw [← vw_lt (show 320 < 1000 by norm_num), v11, Function.update_of_ne (by norm_num), v10, Function.update_self]
  have n11 : s11.sc 321 = K * 2 ^ (L' * K) := by
    rw [← vw_lt (show 321 < 1000 by norm_num), v11, Function.update_self]
  have k11K : s11.sc 43 = K := by
    rw [← vw_lt (show 43 < 1000 by norm_num), v11, Function.update_of_ne (by norm_num), k10K]
  have henv : ∀ i (A' : ℕ → ℕ → ℕ), AgP s11.ar A' (s11.sc 320) →
      Ag 106 (vw s9) (fillEnv s11.sc 311 43 162 163 i) ∧ (∀ v k, lokU K v k → fillEnv s11.sc 311 43 162 163 i v = k) ∧
      LevelHyp m 60 (vw s6) A' (lvP K) L T ∧ TBdd W 60 (vw s6) A' 60 61 rdT (Kb K0u (d + 1)) := by
    intro i A' hA'
    set σ := fillEnv s11.sc 311 43 162 163 i
    have hσ : ∀ y < 1000, y ≠ 311 → y ≠ 162 → y ≠ 163 → σ y = vw s11 y := fun y hy h1 h2 h3 => by
      simp only [σ, fillEnv]
      rw [Function.update_of_ne h3, Function.update_of_ne h2, Function.update_of_ne h1, vw_lt hy]
    have ag : Ag 106 (vw s9) σ := fun y hy => by
      rw [hσ y (by omega) (by omega) (by omega) (by omega), v11, Function.update_of_ne (by omega), v10,
        Function.update_of_ne (by omega)]
    have hTA : Holds A' par T := hT.congr (fun x hx => by rw [hA'.2 x (by rw [p11]; omega), ar11]) hpar
    have hrep : TRep m 60 (vw s6) A' 60 61 rdT T :=
      rdTE_rep (K := Kb K0u (d + 1)) hm hTA q42 q40 q41 (by norm_num) (by norm_num) (by norm_num)
    exact ⟨ag, fun v k h => by have := H.lvar K v k h; rw [ag v (by omega), ag9 v (by omega), lit6 v k h],
      mkH A' hrep, mkT A' hTA⟩
  have hval : ∀ i < s11.sc 321, ∀ A', AgP s11.ar A' (s11.sc 320) →
      eval (fillEnv s11.sc 311 43 162 163 i) A' UP.nxE = (tabK T' (i % K) (i / K)).val := by
    intro i _ A' hA'
    obtain ⟨ag, litσ, H', -⟩ := henv i A' hA'
    have hR' := LevelEx.level_rep H' hc ag9 c9 L9
      (by show vw s9 104 = _; rw [v9, Function.update_of_ne (by norm_num), v8, Function.update_self])
      (by show vw s9 105 = _; rw [v9, Function.update_self])
    have hγ : i % K < K := Nat.mod_lt _ (by omega)
    have z := hR' _ ag ⟨i % K, hγ⟩ (i / K) (by simp [fillEnv, k11K, lvP]) (by simp [fillEnv, k11K, lvP])
    rw [(H.nxE K _ A' litσ).1, z.eq_val, tabK, dif_pos hγ]
    rfl
  have hcost : ∀ i < s11.sc 321, ∀ A', AgP s11.ar A' (s11.sc 320) →
      cost (fillEnv s11.sc 311 43 162 163 i) A' UP.nxE ≤ PB V := by
    intro i hi A' hA'
    obtain ⟨ag, litσ, H', T'⟩ := henv i A' hA'
    have hB := nextTE_bdd H' T' RW hc ag9 c9 L9
      (by show vw s9 104 = _; rw [v9, Function.update_of_ne (by norm_num), v8, Function.update_self])
      (by show vw s9 105 = _; rw [v9, Function.update_self])
    have hγ : i % K < K := Nat.mod_lt _ (by omega)
    rw [(H.nxE K _ A' litσ).2]
    refine cost_le_PB (hB _ ag (by simp [fillEnv, k11K, lvP]; exact hγ) ?_) ?_
    · show fillEnv s11.sc 311 43 162 163 i 163 ≤ W
      simp only [fillEnv, Function.update_self, k11K]
      rw [n11] at hi
      exact le_trans (Nat.div_le_self _ _) (by omega)
    · exact le_trans (dpT_nextTE _) (by simp only [lvP, dp_rdT]; norm_num)
  have k12 := fill_spec UP.nxE (vn := 321) (vi := 311) (vK := 43) (vγ := 162) (vΘ := 163) (vpar := 320)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) H.vnxE s11 (by rw [p11]; omega) _ (PB V) hval hcost
  rw [n11] at k12
  have k12' : (Cmd.run (fillC UP.nxE 321 311 43 162 163 320) s11).2 ≤ 3 * YB V := le_trans k12 (fill_le hn le_rfl)
  set s12 := (Cmd.run (fillC UP.nxE 321 311 43 162 163 320) s11).1
  set s13 := (Cmd.run (.copy 40 101) s12).1
  set s14 := (Cmd.run (.copy 41 320) s13).1
  have hle := seq_le k1' (seq_le k2' (seq_le k3' (seq_le k4' (seq_le k5' (seq_le k6' (seq_le k7' (seq_le k8'
    (seq_le k9' (seq_le k10' (seq_le k11' (seq_le k12' (seq_le (le_refl (Cmd.run (.copy 40 101) s12).2)
      (seq_le (le_refl (Cmd.run (.copy 41 320) s13).2) (le_refl (Cmd.run (.copy 42 43) s14).2))))))))))))))
  have e : (Cmd.run (lvlBody UP) st).2 = (Cmd.run (.seq (cset dE 45) <| .seq (cset (kbE 45) 43) <| .seq UP.lset <|
      .seq (cset (NcE 43 40) 47) <|
      .seq (cset (.mod (.var 305) (.var 47)) 100) <| .seq (cset (.div (.var 305) (.var 47)) 305) <|
      .seq (cset UP.lnE 101) <| .seq (cset (UP.srE false) 104) <| .seq (cset (UP.srE true) 105) <|
      .seq (cset (.mod (.var 306) (.lit 2)) 320) <|
      .seq (cset (.mul (.var 43) (pow2 915 (.mul (.var 101) (.var 43)))) 321) <|
      .seq (fillC UP.nxE 321 311 43 162 163 320) <| .seq (.copy 40 101) <| .seq (.copy 41 320) (.copy 42 43)) st).2 :=
    rfl
  rw [e]
  refine le_trans hle ?_
  simp only [Cmd.run_copy]
  omega

end UCost

end Factoring.Aux
