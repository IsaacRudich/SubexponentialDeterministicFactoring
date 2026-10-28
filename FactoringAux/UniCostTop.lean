/-
The cost of the uniform counting command: the top (search, table) and the count modulo `m`.

The top reads arrays `0`, `1` only through bit tests (`RdN`), so its cost is the cost with every cell replaced by
`[cell ≠ 0]` (`eval_cost_normA`), where the value bounds of `topE_bdd` apply (they need cells `≤ 1`).

* `top_search_bdd`, `top_tab_bdd` (from `topE_bdd`'s steps); **`countM_cost`**.

Not an audit surface.
-/
module

public import FactoringAux.UniCostPath

@[expose] public section

namespace Factoring.Aux

open Factoring.Aux.Copied Factoring.Aux.Copied.PLib Ex Uni Finset SB MulEx

namespace UCost

theorem top_rd (g : ℕ) : (CoarsenEx.nex (clPc g)).Rd :=
  coarsen_rdn (P := clPc g) (mulNEx_rdn 16 10 11) (by simp [clPc, nodesE, AE, pow2, RdN])
    (by simp [clPc, clχE, sel, kA, AE, pow2, RdN])

section Top

variable {V m ℓ n k : ℕ} {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ}

/-- The top search's values. -/
theorem top_search_bdd (R : TopReq V m K0u ℓ n) (hA : ∀ a j, A a j ≤ 1) (h10 : σ 10 = m) (h11 : σ 11 = sOf n)
    (h0 : σ 0 = n) (h2 : σ 2 = k) (hkn : k ≤ n) (h12 : σ 12 = Ltop (Kb K0u ℓ) (Gs K0u ℓ) (sOf n)) :
    Bdd V σ A (GroupEx.searchE (gsTop (Kb K0u ℓ) (Gs K0u ℓ)) 13 14) := by
  set K := Kb K0u ℓ
  set g := Gs K0u ℓ
  set s := sOf n
  set L := Ltop K g s
  have hm := R.hm
  have hK2 : 2 ≤ K := Kb_ge K0u (by norm_num) ℓ
  have hK0 : 0 < K := by omega
  have hg : 0 < g := by show 0 < 3 * K ^ 8; positivity
  have hV := R.mul
  have hL1 : L + 1 ≤ V := le_trans Nat.lt_two_pow_self (two_pow_le_of (Nat.le_mul_of_pos_right _ hK0) R.hLK)
  have htot : 10 * (pA s * pA s) * fw s ≤ V := by
    refine PV hV (a := 9) ?_ (by norm_num)
    have h10 : 10 ≤ (2 ^ pL s) ^ 2 := by have := four_le_P s; nlinarith
    calc 10 * (pA s * pA s) * fw s ≤ (2 ^ pL s) ^ 2 * ((2 ^ pL s) ^ 1 * (2 ^ pL s) ^ 1) * (2 ^ pL s) ^ 5 :=
          Nat.mul_le_mul (Nat.mul_le_mul h10 (Nat.mul_le_mul (pA_P s) (pA_P s))) (fw_P s)
      _ = (2 ^ pL s) ^ 9 := by ring
  have H2 := clusterHyp (A := A) (σ₀ := σ) hm hg h10 h11 h0 h2 hkn (sOf_spec n)
  have Hb2 := cluster_bdd R hA (σ₀ := σ) h10 h11 h0 h2 hkn hg
  have hr2 := coarsen_rep H2 (show 10 < 13 by norm_num)
  have hE2 := coarsen_bdd H2 Hb2 (show 10 < 13 by norm_num)
  set CN := clusterNet s (ZMod m) (numCells (A 0) 1 n) k (numCells (A 1) k (n - k)) g hg
  have hcw : ∀ x < K ^ g, ∀ γ γ' : Fin K, γ < γ' → (CN.coarsen (chiOf K g x hK0)).c γ γ' ≤ V :=
    fun _ _ γ γ' h => le_trans (Net.coarsen_c_le_total _ _ γ γ' h)
      (le_trans (clusterNet_total_le s _ _ k _ g hg) htot)
  exact GroupEx.search_bdd (S := gsTop K g) hK0 hg hm hr2 hE2 (show 10 < 13 by norm_num)
    (show 12 < 13 by norm_num) (show 13 ≤ 13 by norm_num) (show 13 ≤ 14 by norm_num) (show 13 ≤ 15 by norm_num)
    (show (13 : ℕ) ≠ 14 by norm_num) (show (13 : ℕ) ≠ 15 by norm_num) (show (14 : ℕ) ≠ 15 by norm_num)
    (show 13 < 26 by norm_num) (show 14 < 26 by norm_num) (show 15 < 26 by norm_num) h12
    R.hKg R.hgg R.hKG R.hg1 hL1 hcw (Ag.refl _ _)

/-- The top table's values (at the search's choice). -/
theorem top_tab_bdd (R : TopReq V m K0u ℓ n) (hA : ∀ a j, A a j ≤ 1) (h10 : σ 10 = m) (h11 : σ 11 = sOf n)
    (h0 : σ 0 = n) (h2 : σ 2 = k) (hkn : k ≤ n) (h12 : σ 12 = Ltop (Kb K0u ℓ) (Gs K0u ℓ) (sOf n))
    (hg : 0 < Gs K0u ℓ) (hK0 : 0 < Kb K0u ℓ)
    (h15 : σ 15 = firstGood (okG (clusterNet (sOf n) (ZMod m) (numCells (A 0) 1 n) k (numCells (A 1) k (n - k))
      (Gs K0u ℓ) hg) (Kb K0u ℓ) (Ltop (Kb K0u ℓ) (Gs K0u ℓ) (sOf n)) hK0) (Kb K0u ℓ ^ Gs K0u ℓ)
      (Kb K0u ℓ ^ Gs K0u ℓ)) :
    TBdd V 16 σ A 82 83 (GroupEx.tab (gsTop (Kb K0u ℓ) (Gs K0u ℓ))) (Kb K0u ℓ) := by
  set K := Kb K0u ℓ
  set g := Gs K0u ℓ
  set s := sOf n
  set L := Ltop K g s
  have hm := R.hm
  have hK2 : 2 ≤ K := Kb_ge K0u (by norm_num) ℓ
  have hLK1 : 2 ^ L ≤ V := two_pow_le_of (Nat.le_mul_of_pos_right _ hK0) R.hLK
  have H3 := clusterHyp (A := A) (σ₀ := σ) hm hg h10 h11 h0 h2 hkn (sOf_spec n)
  have Hb3 := cluster_bdd R hA (σ₀ := σ) h10 h11 h0 h2 hkn hg
  have hr3 := (coarsen_rep H3 (show 10 < 13 by norm_num)).mono (show 13 ≤ 16 by norm_num)
  have hE3 := (coarsen_bdd H3 Hb3 (show 10 < 13 by norm_num)).mono (show 13 ≤ 16 by norm_num)
  set CN := clusterNet s (ZMod m) (numCells (A 0) 1 n) k (numCells (A 1) k (n - k)) g hg
  set xf := firstGood (okG CN K L hK0) (K ^ g) (K ^ g)
  obtain ⟨x0, hx0, hok⟩ := good_exists CN (clP s g) (10 * (pA s * pA s) * fw s)
    (clusterNet_fits s _ _ k _ g hg) (clusterNet_total_le s _ _ k _ g hg) hK2 rfl
  have hsp := firstGood_spec (okG CN K L hK0) (le_refl (K ^ g)) ⟨x0, hx0, hok⟩
  refine GroupEx.tab_bdd (S := gsTop K g) (x := xf) (L := L) hK0 hg hm hr3 hE3 (show 10 < 16 by norm_num)
    (show 15 < 16 by norm_num) (show 12 < 16 by norm_num) (show 16 ≤ 26 by norm_num) h15 h12
    (le_trans hsp.1.le R.hKg) R.hKg R.hgg R.mm (fun γ => ?_)
    (fun γ γ' h => two_pow_le_of (hsp.2.2 γ γ' h) hLK1)
    (fun a b h _ => two_pow_le_of (Net.c_le_fits _ (clusterNet_fits s (ZMod m) _ k _ g hg) a b h) R.hclP) R.hLK
  refine le_trans (coarsen_s_le_unif _ _ γ (Wc s g) (2 * g / K) (fun a => cluster_s_le s m _ k _ g hg a) ?_) R.hgrp
  rw [Nat.le_div_iff_mul_le hK0, mul_comm]
  exact hsp.2.1 γ

end Top

theorem normA_congr {A A' : ℕ → ℕ → ℕ} {a : ℕ} (h : A' a = A a) : normA A' a = normA A a := by
  funext j; simp only [normA, h]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
/-- **The cost of the whole count modulo `m`.** -/
theorem countM_cost {V m n k ℓ : ℕ} (st : St) (hm : 1 < m) (h10 : st.sc 10 = m) (h11 : st.sc 11 = sOf n)
    (h0 : st.sc 0 = n) (h2 : st.sc 2 = k) (hkn : k < n) (h307 : st.sc 307 = ℓ) (h316 : st.sc 316 = Kb K0u ℓ)
    (h12 : st.sc 12 = Ltop (Kb K0u ℓ) (Gs K0u ℓ) (sOf n)) (h303 : st.sc 303 ≤ V)
    (htok : ∀ v k', tokU (Kb K0u ℓ) v k' → st.sc v = k') (R : TopReq V m K0u ℓ n) (hℓ : ℓ ≤ V)
    (hlv : lvlV (Kb K0u ℓ) ≤ V) :
    (Cmd.run (countM UP) st).2 ≤ 60 * YB V ^ 3 := by
  have : NeZero m := ⟨by omega⟩
  have hW := @le_Wv V
  have hVV := @sq_le_Wv V
  have RW := TopReq.mono R hW
  have hY := YB_ge V
  have hPB := PB_le_YB V
  have hY3 : YB V ≤ YB V ^ 3 := Nat.le_self_pow (by norm_num) _
  set K := Kb K0u ℓ
  set L := Ltop K (3 * K ^ 8) (sOf n)
  have hK : 2 ≤ K := Kb_ge K0u (by norm_num) ℓ
  have hK0 : 0 < K := by omega
  have hg : 0 < 3 * K ^ 8 := Nat.mul_pos (by norm_num) (Nat.pow_pos hK0)
  have hKV : K ≤ V := le_trans (Nat.le_mul_of_pos_right _ (show 0 < Gs K0u ℓ from hg)) R.hKG
  have hLK : 2 ^ (L * K) ≤ V := R.hLK
  have hLKV : L * K ≤ V := le_trans Nat.lt_two_pow_self.le hLK
  set N := numCells (st.ar 0) 1 n
  set x := numCells (st.ar 1) k (n - k)
  set CN := clusterNet (sOf n) (ZMod m) N k x (3 * K ^ 8) hg
  set xf := firstGood (okG CN K L (by omega)) (K ^ (3 * K ^ 8)) (K ^ (3 * K ^ 8))
  set Tt := (CN.coarsen (chiOf K (3 * K ^ 8) xf (by omega))).toClique L
  set CNn := clusterNet (sOf n) (ZMod m) (numCells (normA st.ar 0) 1 n) k (numCells (normA st.ar 1) k (n - k))
    (3 * K ^ 8) hg
  set xfn := firstGood (okG CNn K L (by omega)) (K ^ (3 * K ^ 8)) (K ^ (3 * K ^ 8))
  have hS := group_search_rdn (S := gsTop K (3 * K ^ 8)) (top_rd _) 13 14
  have hTb := group_tab_rdn (S := gsTop K (3 * K ^ 8)) (top_rd (3 * K ^ 8))
  -- c1: 15 := xf
  obtain ⟨v1, a1, k1⟩ := vw_cset UP_ok.vtsE (show 15 < 1000 by norm_num) st
  set c1 := (Cmd.run (cset UP.tsE 15) st).1
  have tk : ∀ v k', tokU K v k' → vw st v = k' := fun v k' h => by
    have := topOk_lt h; rw [vw_lt (by omega), htok v k' h]
  have q10 : vw st 10 = m := by rw [vw_lt (by norm_num), h10]
  have q11 : vw st 11 = sOf n := by rw [vw_lt (by norm_num), h11]
  have q0 : vw st 0 = n := by rw [vw_lt (by norm_num), h0]
  have q2 : vw st 2 = k := by rw [vw_lt (by norm_num), h2]
  have q12 : vw st 12 = L := by rw [vw_lt (by norm_num), h12]; rfl
  have k1' : (Cmd.run (cset UP.tsE 15) st).2 ≤ PB V := by
    refine le_trans k1 ?_
    rw [(UP_ok.tsE K (vw st) st.ar tk).2, (eval_cost_normA hS (vw st) st.ar).2]
    exact cost_le_PB (top_search_bdd RW (normA_le _) q10 q11 q0 q2 hkn.le q12)
      (le_trans (dpT_top_search _ _ _ _) (by norm_num))
  have ev1 := (UP_ok.tsE K (vw st) st.ar tk).1
  have xR : eval (vw st) st.ar UP.tsE = xf := by
    rw [ev1, top_search hK hm q10 q11 q0 q2 hkn.le q12]
  have xN : eval (vw st) st.ar UP.tsE = xfn := by
    rw [ev1, (eval_cost_normA hS (vw st) st.ar).1, top_search hK hm q10 q11 q0 q2 hkn.le q12]
  rw [xR] at v1
  -- c2: 321 := K · 2^(L K); c3: 320 := 2
  obtain ⟨v2, a2, k2⟩ := vw_cset (e := .mul (.var 316) (pow2 915 (.mul (.var 12) (.var 316)))) (by simp [VB, pow2])
    (show 321 < 1000 by norm_num) c1
  set c2 := (Cmd.run (cset (.mul (.var 316) (pow2 915 (.mul (.var 12) (.var 316)))) 321) c1).1
  have k1K : vw c1 316 = K := by rw [v1, Function.update_of_ne (by norm_num), vw_lt (by norm_num), h316]
  have l1 : vw c1 12 = L := by rw [v1, Function.update_of_ne (by norm_num), q12]
  have hn : K * 2 ^ (L * K) ≤ Wv V := le_trans (Nat.mul_le_mul hKV hLK) hVV
  have k2' : (Cmd.run (cset (.mul (.var 316) (pow2 915 (.mul (.var 12) (.var 316)))) 321) c1).2 ≤ PB V := by
    refine le_trans k2 (cost_le_PB ?_ (by simp [Ex.dp, pow2]))
    have Bm : Bdd (Wv V) (vw c1) c1.ar (.mul (.var 12) (.var 316)) :=
      B_mul (B_var (by rw [l1]; exact le_trans (le_trans (Nat.le_mul_of_pos_right _ hK0) hLKV) hW))
        (B_var (by rw [k1K]; omega)) (by simp only [Ex.eval, l1, k1K]; omega)
    refine B_mul (B_var (by rw [k1K]; omega)) (B_pow2 Bm (by omega) (by simp only [Ex.eval, l1, k1K]; omega)) ?_
    simp only [Ex.eval, eval_pow2, l1, k1K]; exact hn
  rw [show eval (vw c1) c1.ar (.mul (.var 316) (pow2 915 (.mul (.var 12) (.var 316)))) = K * 2 ^ (L * K) by
    simp only [Ex.eval, eval_pow2, k1K, l1]] at v2
  obtain ⟨v3, a3, -⟩ := vw_setK (k := 2) (show 320 < 1000 by norm_num) c2
  set c3 := (Cmd.run (.setK 320 2) c2).1
  have w3 : ∀ y, y ≠ 320 → y ≠ 321 → y ≠ 15 → vw c3 y = vw st y := fun y h1 h2 h3 => by
    rw [v3, Function.update_of_ne h1, v2, Function.update_of_ne h2, v1, Function.update_of_ne h3]
  have ar3 : c3.ar = st.ar := by rw [a3, a2, a1]
  have sc3 : ∀ y < 1000, y ≠ 320 → y ≠ 321 → y ≠ 15 → c3.sc y = st.sc y := fun y hy h1 h2 h3 => by
    rw [← vw_lt hy, w3 y h1 h2 h3, vw_lt hy]
  have p3 : c3.sc 320 = 2 := by rw [← vw_lt (show 320 < 1000 by norm_num), v3, Function.update_self]
  have n3 : c3.sc 321 = K * 2 ^ (L * K) := by
    rw [← vw_lt (show 321 < 1000 by norm_num), v3, Function.update_of_ne (by norm_num), v2, Function.update_self]
  have x3 : c3.sc 15 = xf := by
    rw [← vw_lt (show 15 < 1000 by norm_num), v3, Function.update_of_ne (by norm_num), v2,
      Function.update_of_ne (by norm_num), v1, Function.update_self]
  have x3n : c3.sc 15 = xfn := by rw [x3, ← xR, xN]
  have K3 : c3.sc 316 = K := by rw [sc3 316 (by norm_num) (by norm_num) (by norm_num) (by norm_num), h316]
  -- c4: the top table
  have henv : ∀ i (A' : ℕ → ℕ → ℕ), AgP c3.ar A' (c3.sc 320) →
      (∀ y < 82, y ≠ 15 → fillEnv c3.sc 311 316 82 83 i y = st.sc y) ∧
        (∀ v k', tokU K v k' → fillEnv c3.sc 311 316 82 83 i v = k') ∧ A' 0 = st.ar 0 ∧ A' 1 = st.ar 1 ∧
        fillEnv c3.sc 311 316 82 83 i 15 = xf := by
    intro i A' hA'
    have hσ : ∀ y < 1000, y ≠ 311 → y ≠ 82 → y ≠ 83 → fillEnv c3.sc 311 316 82 83 i y = c3.sc y :=
      fun y hy h1 h2 h3 => by
        simp only [fillEnv]
        rw [Function.update_of_ne h3, Function.update_of_ne h2, Function.update_of_ne h1]
    have g : ∀ y < 82, y ≠ 15 → fillEnv c3.sc 311 316 82 83 i y = st.sc y := fun y hy h => by
      rw [hσ y (by omega) (by omega) (by omega) (by omega), sc3 y (by omega) (by omega) (by omega) h]
    exact ⟨g, fun v k' h => by have := topOk_lt h; have := h.1; rw [g v (by omega) (by omega), htok v k' h],
      by rw [hA'.1 0 (by norm_num), ar3], by rw [hA'.1 1 (by norm_num), ar3],
      by rw [hσ 15 (by norm_num) (by norm_num) (by norm_num) (by norm_num), x3]⟩
  have hval : ∀ i < c3.sc 321, ∀ A', AgP c3.ar A' (c3.sc 320) →
      eval (fillEnv c3.sc 311 316 82 83 i) A' UP.ttE = (tabK Tt (i % K) (i / K)).val := by
    intro i _ A' hA'
    obtain ⟨g, tkσ, e0, e1, x15⟩ := henv i A' hA'
    have hR := top_tab_rep (σ := fillEnv c3.sc 311 316 82 83 i) (A := A') (m := m) (n := n) (k := k) hK hm
      (by rw [g 10 (by norm_num) (by norm_num), h10])
      (by rw [g 11 (by norm_num) (by norm_num), h11]) (by rw [g 0 (by norm_num) (by norm_num), h0])
      (by rw [g 2 (by norm_num) (by norm_num), h2]) hkn.le (by rw [g 12 (by norm_num) (by norm_num), h12]; rfl)
      (xf := xf) x15
    rw [e0, e1] at hR
    have hγ : i % K < K := Nat.mod_lt _ (by omega)
    have z := hR _ (Ag.refl _ _) ⟨i % K, hγ⟩ (i / K) (by simp [fillEnv, K3]) (by simp [fillEnv, K3])
    rw [(UP_ok.ttE K _ A' tkσ).1, z.eq_val, tabK, dif_pos hγ]
  have hcost : ∀ i < c3.sc 321, ∀ A', AgP c3.ar A' (c3.sc 320) →
      cost (fillEnv c3.sc 311 316 82 83 i) A' UP.ttE ≤ PB V := by
    intro i hi A' hA'
    obtain ⟨g, tkσ, e0, e1, x15⟩ := henv i A' hA'
    rw [(UP_ok.ttE K _ A' tkσ).2, (eval_cost_normA hTb _ A').2]
    have n0 : normA A' 0 = normA st.ar 0 := normA_congr e0
    have n1 : normA A' 1 = normA st.ar 1 := normA_congr e1
    have hB := top_tab_bdd (A := normA A') (σ := fillEnv c3.sc 311 316 82 83 i) RW (normA_le _)
      (by rw [g 10 (by norm_num) (by norm_num), h10]) (by rw [g 11 (by norm_num) (by norm_num), h11])
      (by rw [g 0 (by norm_num) (by norm_num), h0]) (by rw [g 2 (by norm_num) (by norm_num), h2]) hkn.le
      (by rw [g 12 (by norm_num) (by norm_num), h12]) hg hK0 (by
        rw [n0, n1, x15, ← x3, x3n]; rfl)
    have hγ : i % K < K := Nat.mod_lt _ (by omega)
    refine cost_le_PB (hB _ (Ag.refl _ _) (by simp [fillEnv, K3]; exact hγ) ?_)
      (le_trans (dpT_top_tab _ _) (by norm_num))
    show fillEnv c3.sc 311 316 82 83 i 83 ≤ Wv V
    simp only [fillEnv, Function.update_self, K3]
    rw [n3] at hi
    exact le_trans (Nat.div_le_self _ _) (by omega)
  have k4 := fill_spec UP.ttE (vn := 321) (vi := 311) (vK := 316) (vγ := 82) (vΘ := 83) (vpar := 320)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) UP_ok.vttE c3 (by rw [p3]; omega) _ (PB V) hval hcost
  rw [n3] at k4
  have k4' : (Cmd.run (fillC UP.ttE 321 311 316 82 83 320) c3).2 ≤ 3 * YB V := le_trans k4 (fill_le hn le_rfl)
  obtain ⟨f1, f2⟩ := fill_val UP.ttE (vn := 321) (vi := 311) (vK := 316) (vγ := 82) (vΘ := 83) (vpar := 320)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) UP_ok.vttE c3 (by rw [p3]; omega) _ hval
  set c4 := (Cmd.run (fillC UP.ttE 321 311 316 82 83 320) c3).1
  have ar4 : c4.ar = filled st.ar (fun i => (tabK Tt (i % K) (i / K)).val) 2 (K * 2 ^ (L * K)) := by
    rw [f1, ar3, p3, n3]
  have hT4 : Holds c4.ar 2 Tt := by rw [ar4]; exact holds_filled Tt _ (by norm_num) (by omega)
  obtain ⟨v5, a5, -⟩ := vw_setK (k := 0) (show 308 < 1000 by norm_num) c4
  set c5 := (Cmd.run (.setK 308 0) c4).1
  have sc5 : ∀ y < 990, y ≠ 308 → y ≠ 311 → y ≠ 320 → y ≠ 321 → y ≠ 15 → c5.sc y = st.sc y :=
    fun y hy h0 h1 h2 h3 h4 => by
      rw [← vw_lt (show y < 1000 by omega), v5, Function.update_of_ne h0, vw_lt (by omega), f2 y hy h1,
        sc3 y (by omega) h2 h3 h4]
  have k6 := pathLoop_cost Tt c5 hm (by rw [sc5 10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num), h10])
    (by rw [sc5 307 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), h307])
    (by rw [sc5 12 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), h12]; rfl)
    (by rw [sc5 316 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), h316])
    (by rw [← vw_lt (show 308 < 1000 by norm_num), v5, Function.update_self])
    (by rw [sc5 303 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; exact h303)
    (by rw [a5]; exact hT4) R.deep hLK hℓ hlv
  have hle := seq_le k1' (seq_le k2' (seq_le (le_refl (Cmd.run (.setK 320 2) c2).2) (seq_le k4'
    (seq_le (le_refl (Cmd.run (.setK 308 0) c4).2) k6))))
  have e : (Cmd.run (countM UP) st).2 = (Cmd.run (.seq (cset UP.tsE 15) <|
      .seq (cset (.mul (.var 316) (pow2 915 (.mul (.var 12) (.var 316)))) 321) <|
      .seq (.setK 320 2) <| .seq (fillC UP.ttE 321 311 316 82 83 320) <| .seq (.setK 308 0)
      (.loop 303 304 (pathBody UP))) st).2 := rfl
  rw [e]
  refine le_trans hle ?_
  simp only [Cmd.run_setK]
  omega

end UCost

end Factoring.Aux
