/-
The cost of the uniform counting command: the multiplier `deepMult` modulo `m` (`dmLoop`).

Every product of `multVm` is reduced modulo `m`, so its values are below `m²` or the level's own sizes.

* `multVm_bdd`, **`dmBody_cost`**, **`dmLoop_cost`** (with the bound `309 ≤ m` at the end).

Not an audit surface.
-/
module

public import FactoringAux.UniCostSetup

@[expose] public section

namespace Factoring.Aux

open Factoring.Aux.Copied Factoring.Aux.Copied.PLib Ex Uni Finset SB

namespace UCost

/-- `mult (3 K^8) λ` modulo `m` (`K` in `43`, `λ` in `40`, `m` in `10`). -/
theorem multVm_bdd {V K lam m : ℕ} {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ} (hK : σ 43 = K) (hl : σ 40 = lam)
    (hm10 : σ 10 = m) (hm : 1 < m) (hmm : m * m ≤ V)
    (hG4 : (3 * K ^ 8) * (3 * K ^ 8) * ((3 * K ^ 8) * (3 * K ^ 8)) ≤ V)
    (hT : (3 * K ^ 8) * (3 * K ^ 8) * ((3 * K ^ 8) * (3 * K ^ 8)) * (lam + 1) ≤ V) (hl2 : lam + 2 ≤ V)
    (h64 : 64 ≤ V) : Bdd V σ A (multVm 43 40 10) := by
  set G := 3 * K ^ 8
  have hG4' : G ^ 4 ≤ V := by rw [show G ^ 4 = G * G * (G * G) by ring]; exact hG4
  have hGG4 : G ≤ G ^ 4 := by
    rcases Nat.eq_zero_or_pos G with h | h
    · rw [h]; simp
    · exact Nat.le_self_pow (by norm_num) _
  have hGV : G ≤ V := le_trans hGG4 hG4'
  have hmV : m ≤ V := le_trans (Nat.le_mul_of_pos_left _ (by omega)) hmm
  set p := G * (G - 1) / 2
  have hp : p * p = (rects G).card := (card_rects G).symm
  have hpp : p * p ≤ G ^ 4 := hp ▸ rects_le G
  have hnr : G ^ 4 - p * p = nonRects G := by rw [nonRects_eq, card_rects]
  have ht : tB lam + 1 ≤ V := by unfold tB; have := Nat.div_le_self (lam + 2) 3; omega
  have htpp : tB lam * (p * p) ≤ V := by
    refine le_trans ?_ hT
    rw [mul_comm]
    exact Nat.mul_le_mul (by rw [show G * G * (G * G) = G ^ 4 by ring]; exact hpp) (tB_le lam)
  unfold multVm
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
  have f10 : σ3 10 = m := by simp [σ3, σ2, σ1, hm10]
  have u40 : ∀ i, Function.update σ3 913 i 40 = lam := fun i => by rw [Function.update_of_ne (by norm_num), f40]
  have u10 : ∀ i, Function.update σ3 913 i 10 = m := fun i => by rw [Function.update_of_ne (by norm_num), f10]
  have BPow : Bdd V σ3 A (powE 914 (.var 910) 4) :=
    bdd_nprod_const (x := 914) (n := .lit 4) (b := .var 910) (c := G) (B_lit (by omega))
      (fun i => show _ ≤ V by rw [Function.update_of_ne (by norm_num), f910]; exact hGV)
      (fun i => by simp [Ex.eval, f910])
      (fun i hi => pow_le_of_le hG4' (by omega) i (by simpa [Ex.eval] using hi))
  have B10 : Bdd V σ3 A (.var 10) := show σ3 10 ≤ V by rw [f10]; exact hmV
  have P1 : Bdd V σ3 A (.prod 913 (.sub (powE 914 (.var 910) 4) (.var 912)) (.var 10)
      (.mod (.add (tBE 40) (.lit 1)) (.var 10))) :=
    B_prod_mod (B_sub BPow (B_var (by rw [f912]; exact le_trans hpp hG4'))) B10
      (by show 0 < σ3 10; rw [f10]; omega) (by show σ3 10 ≤ V; rw [f10]; exact hmV) (by omega)
      (fun i _ => B_mod (B_add (tBE_bdd (u40 i) hl2 (by omega)) (B_lit (by omega))
        (by show eval _ A (tBE 40) + 1 ≤ V; rw [eval_tBE (u40 i)]; exact ht))
        (show _ ≤ V by rw [u10]; exact hmV))
  have P2 : Bdd V σ3 A (.prod 913 (.mul (tBE 40) (.var 912)) (.var 10) (.mod (.lit 2) (.var 10))) :=
    B_prod_mod (B_mul (tBE_bdd f40 hl2 (by omega)) (B_var (by rw [f912]; exact le_trans hpp hG4'))
        (by rw [eval_tBE f40]; show tB lam * σ3 912 ≤ V; rw [f912]; exact htpp)) B10
      (by show 0 < σ3 10; rw [f10]; omega) (by show σ3 10 ≤ V; rw [f10]; exact hmV) (by omega)
      (fun i _ => B_mod (B_lit (by omega)) (show _ ≤ V by rw [u10]; exact hmV))
  have v1 : eval σ3 A (.prod 913 (.sub (powE 914 (.var 910) 4) (.var 912)) (.var 10)
      (.mod (.add (tBE 40) (.lit 1)) (.var 10))) ≤ m := by
    simp only [Ex.eval]; rw [f10]; exact foldProd_le _ (by omega) _
  have v2 : eval σ3 A (.prod 913 (.mul (tBE 40) (.var 912)) (.var 10) (.mod (.lit 2) (.var 10))) ≤ m := by
    simp only [Ex.eval]; rw [f10]; exact foldProd_le _ (by omega) _
  exact B_mod (B_mul P1 P2 (le_trans (Nat.mul_le_mul v1 v2) hmm)) B10

theorem dp_dmE : Ex.dp (.mod (.mul (.var 309) (multVm 43 40 10)) (.var 10)) ≤ 100 := by
  simp [multVm, gE, powE, tBE, Ex.dp]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
/-- **The cost of one level of the multiplier loop.** -/
theorem dmBody_cost {V m d lam : ℕ} (st : St) (h307 : st.sc 307 = d + 1 + st.sc 306) (h40 : st.sc 40 = lam)
    (h10 : st.sc 10 = m) (hm : 1 < m) (h307V : st.sc 307 ≤ V) (h309 : st.sc 309 ≤ m)
    (hR : LevelReq V m (Kb K0u d) (Gs K0u d) lam) (hlv : lvlV (Kb K0u d) ≤ V) :
    (Cmd.run (dmBody UP) st).2 ≤ 25 * YB V := by
  set W := Wv V
  have hVW : V ≤ W := le_Wv
  have RW := LevelReq.mono hR hVW
  set K := Kb K0u d
  have hK2 : 2 ≤ K := Kb_ge K0u (by norm_num) d
  have h64 : 64 ≤ V := hR.dec.h64
  have hmm : m * m ≤ V := hR.dec.hmm
  have hmV : m ≤ V := hR.dec.mV
  have hG1 : 0 < Gs K0u d := Nat.mul_pos (by norm_num) (Nat.pow_pos (by omega))
  have hKV : K ≤ V := le_trans (Nat.le_mul_of_pos_right _ hG1) hR.hKG
  have hl2 : lam + 2 ≤ V := (LevelReq.small hR).1
  have hT : Gs K0u d * Gs K0u d * (Gs K0u d * Gs K0u d) * (lam + 1) ≤ V := by
    have := hR.hLn
    have h1 : Gs K0u d * Gs K0u d * (Gs K0u d * Gs K0u d) * (lam + 1) ≤ (12 * Gs K0u d ^ 3 + 11 * Gs K0u d ^ 4 +
        24 * Gs K0u d ^ 4 + Gs K0u d * Gs K0u d ^ 3 + Kb K0u d ^ 3 + 12) * (lam + 1) :=
      Nat.mul_le_mul_right _ (by rw [show Gs K0u d * Gs K0u d * (Gs K0u d * Gs K0u d) = Gs K0u d ^ 4 by ring]; omega)
    exact le_trans h1 (le_trans (Nat.le_mul_of_pos_left _ (by omega)) this)
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
  have M2 : vw s2 10 = m := by
    rw [v2, Function.update_of_ne (by norm_num), Function.update_of_ne (by norm_num), vw_lt (by norm_num), h10]
  have D2 : vw s2 309 = st.sc 309 := by
    rw [v2, Function.update_of_ne (by norm_num), Function.update_of_ne (by norm_num), vw_lt (by norm_num)]
  -- s3: 309 := 309 · mult mod m
  obtain ⟨v3, a3, k3⟩ := vw_cset (e := .mod (.mul (.var 309) (multVm 43 40 10)) (.var 10))
    (by simp [VB, multVm, gE, powE, tBE]) (show 309 < 1000 by norm_num) s2
  set s3 := (Cmd.run (cset (.mod (.mul (.var 309) (multVm 43 40 10)) (.var 10)) 309) s2).1
  have hmv : eval (vw s2) s2.ar (multVm 43 40 10) < m := by
    rw [eval_multVm (by omega) (by norm_num) (by norm_num) (by norm_num) K2 L2 M2]; exact Nat.mod_lt _ (by omega)
  have k3' : (Cmd.run (cset (.mod (.mul (.var 309) (multVm 43 40 10)) (.var 10)) 309) s2).2 ≤ PB V := by
    refine le_trans k3 (cost_le_PB ?_ dp_dmE)
    refine B_mod (B_mul (B_var (by rw [D2]; omega)) (multVm_bdd K2 L2 M2 hm (le_trans hmm hVW)
      (le_trans hR.hg4 hVW) (le_trans hT hVW) (le_trans hl2 hVW) (by omega)) ?_) (B_var (by rw [M2]; omega))
    show vw s2 309 * _ ≤ W
    rw [D2]; exact le_trans (Nat.mul_le_mul h309 hmv.le) (le_trans hmm hVW)
  -- s4: the level literals; s5: 101 := L'
  have K3 : s3.sc 43 = K := by
    rw [← vw_lt (show 43 < 1000 by norm_num), v3, Function.update_of_ne (by norm_num), K2]
  have k4' : (Cmd.run UP.lset s3).2 ≤ 15 * PB V := by
    rw [show UP.lset = lvlSet 20 43 from rfl]
    obtain ⟨-, -, -, -, h5⟩ := lvlSet_spec (p := 20) (q := 43) s3 K3 (by norm_num) (Or.inr (by norm_num))
      (by norm_num)
    exact le_trans h5 (set_le_PB (by omega))
  obtain ⟨l1, l2, a4⟩ := UP_ok.lset s3
  set s4 := (Cmd.run UP.lset s3).1
  rw [K3] at l1
  have w4 : ∀ y, ¬ (20 ≤ y ∧ y < 40) → vw s4 y = vw s3 y := fun y hy => by
    by_cases hy' : y < 1000
    · rw [vw_lt hy', vw_lt hy', l2 y hy' (by omega)]
    · simp [vw, hy']
  have lit4 : ∀ v k, lokU K v k → vw s4 v = k := fun v k h => by
    have := UP_ok.lvar K v k h; rw [vw_lt (by omega), l1 v k h]
  have L4 : vw s4 40 = lam := by rw [w4 40 (by omega), v3, Function.update_of_ne (by norm_num), L2]
  obtain ⟨-, -, k5⟩ := vw_cset UP_ok.vlnE (show 101 < 1000 by norm_num) s4
  have k5' : (Cmd.run (cset UP.lnE 101) s4).2 ≤ PB V := by
    refine le_trans k5 ?_
    rw [(UP_ok.lnE K (vw s4) s4.ar lit4).2]
    exact cost_le_PB (LnE_bdd (P := lvP K) RW.hLn L4) (le_trans (dpT_LnE _) (by norm_num))
  set s5 := (Cmd.run (cset UP.lnE 101) s4).1
  have hle := seq_le k1' (seq_le k2' (seq_le k3' (seq_le k4' (seq_le k5'
    (le_refl (Cmd.run (.copy 40 101) s5).2)))))
  have e : (Cmd.run (dmBody UP) st).2 = (Cmd.run (.seq (cset dE 45) <| .seq (cset (kbE 45) 43) <|
      .seq (cset (.mod (.mul (.var 309) (multVm 43 40 10)) (.var 10)) 309) <|
      .seq UP.lset <| .seq (cset UP.lnE 101) (.copy 40 101)) st).2 := rfl
  rw [e]
  refine le_trans hle ?_
  simp only [Cmd.run_copy]
  omega

/-- The invariant of the multiplier loop (costs). -/
def DC (V m ℓ : ℕ) (j : ℕ) (s : St) : Prop :=
  (∀ d, d + j = ℓ → DeepReq V m K0u d (s.sc 40)) ∧ s.sc 309 ≤ m ∧ s.sc 10 = m ∧ s.sc 307 = ℓ

theorem dc_step {V m ℓ : ℕ} (hm : 1 < m) (hℓ : ℓ ≤ V) (hlv : lvlV (Kb K0u ℓ) ≤ V) (j : ℕ) (s : St) (hj : j < ℓ)
    (hs : DC V m ℓ j s) :
    DC V m ℓ (j + 1) (Cmd.run (dmBody UP) (s.setSc 306 j)).1 ∧ (Cmd.run (dmBody UP) (s.setSc 306 j)).2 ≤ 25 * YB V := by
  obtain ⟨hD, s309, s10, s307⟩ := hs
  set s' := s.setSc 306 j
  obtain ⟨d, rfl⟩ : ∃ d, ℓ = d + 1 + j := ⟨ℓ - 1 - j, by omega⟩
  have hR := hD (d + 1) (by omega)
  have g : ∀ y, y ≠ 306 → s'.sc y = s.sc y := fun y hy => by simp [s', Function.update_of_ne hy]
  have h307 : s'.sc 307 = d + 1 + s'.sc 306 := by rw [g 307 (by norm_num), s307]; simp [s']
  have h40 : s'.sc 40 = s.sc 40 := g 40 (by norm_num)
  have h10 : s'.sc 10 = m := by rw [g 10 (by norm_num), s10]
  obtain ⟨r40, r309, rfr, -⟩ := dmBody_spec s' (d := d) (L := s.sc 40) (m := m) (by omega) h307 h40 h10
  have hc := dmBody_cost s' h307 h40 h10 hm (by rw [g 307 (by norm_num), s307]; exact hℓ)
    (by rw [g 309 (by norm_num)]; exact s309) hR.1 (le_trans (lvlV_mono (Kb_le (by omega))) hlv)
  refine ⟨⟨fun d' hd' => ?_, ?_, ?_, ?_⟩, hc⟩
  · obtain rfl : d' = d := by omega
    rw [r40]; exact hR.2
  · rw [r309]; exact (Nat.mod_lt _ (by omega)).le
  · rw [rfr 10 (by norm_num) (by simp [WD]), h10]
  · rw [rfr 307 (by norm_num) (by simp [WD]), g 307 (by norm_num), s307]

/-- **The cost of the multiplier loop**, and the multiplier is at most `m` at the end. -/
theorem dmLoop_cost {V m ℓ L : ℕ} (st : St) (hm : 1 < m) (h307 : st.sc 307 = ℓ) (h12 : st.sc 12 = L)
    (h10 : st.sc 10 = m) (hR : DeepReq V m K0u ℓ L) (hℓ : ℓ ≤ V) (hlv : lvlV (Kb K0u ℓ) ≤ V) :
    (Cmd.run (dmLoop UP) st).2 ≤ 30 * YB V ^ 2 ∧ (Cmd.run (dmLoop UP) st).1.sc 309 ≤ m := by
  set s1 := (Cmd.run (.copy 40 12) st).1
  set s2 := (Cmd.run (.setK 309 1) s1).1
  have h0 : DC V m ℓ 0 s2 := by
    refine ⟨fun d hd => ?_, ?_, ?_, ?_⟩
    · obtain rfl : d = ℓ := by omega
      simp only [s2, s1, Cmd.run_setK, Cmd.run_copy, St.setSc_sc]
      rw [Function.update_of_ne (by norm_num), Function.update_self, h12]; exact hR
    · simp [s2, Cmd.run_setK]; omega
    · simp [s2, s1, Cmd.run_setK, Cmd.run_copy, h10]
    · simp [s2, s1, Cmd.run_setK, Cmd.run_copy, h307]
  have e307 : s2.sc 307 = ℓ := h0.2.2.2
  have hI := Cmd.loop_inv (b := 307) (c := 306) (body := dmBody UP) (st := s2) (DC V m ℓ) h0
    (fun j s hj hs => (dc_step hm hℓ hlv j s (by omega) hs).1)
  have hC := Cmd.loop_cost_le (b := 307) (c := 306) (body := dmBody UP) (st := s2) (DC V m ℓ) (25 * YB V ^ 1) h0
    (fun j s hj hs => (dc_step hm hℓ hlv j s (by omega) hs).1)
    (fun j s hj hs => by rw [pow_one]; exact (dc_step hm hℓ hlv j s (by omega) hs).2)
  rw [e307] at hI hC
  have hL : (Cmd.run (.loop 307 306 (dmBody UP)) s2).2 ≤ 27 * YB V ^ 2 := le_trans hC (loop_le (le_trans hℓ le_Wv))
  have hY := YB_ge V
  have hY2 : YB V ≤ YB V ^ 2 := Nat.le_self_pow (by norm_num) _
  refine ⟨?_, hI.2.1⟩
  have hle := seq_le (le_refl (Cmd.run (.copy 40 12) st).2) (seq_le (le_refl (Cmd.run (.setK 309 1) s1).2) hL)
  rw [show dmLoop UP = .seq (.copy 40 12) (.seq (.setK 309 1) (.loop 307 306 (dmBody UP))) from rfl]
  refine le_trans hle ?_
  simp only [Cmd.run_copy, Cmd.run_setK]
  omega

end UCost

end Factoring.Aux
