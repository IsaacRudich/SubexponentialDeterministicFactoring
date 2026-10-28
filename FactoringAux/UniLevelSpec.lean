/-
The uniform engine: what the literal-free copies must satisfy (`UOK`), and one level of one path
(**`lvlBody_spec`**: from the table `T` in slot `par`, the next table `nextT T c` in slot `j % 2`, with
`c = R % Nc`, `R := R / Nc`).

Not an audit surface.
-/
module

public import FactoringAux.UniEngine
public import FactoringAux.UniRun

@[expose] public section

namespace Factoring.Aux

open Factoring.Aux.Copied Factoring.Aux.Copied.PLib Ex Uni

/-- **The specification of the copies.** `lok K v k`: level literal variable `v` holds `k` (group count `K`);
`tok K v k` the same for the top. -/
structure UOK (U : UParts) (lok tok : ℕ → ℕ → ℕ → Prop) : Prop where
  lvar : ∀ K v k, lok K v k → 20 ≤ v ∧ v < 40
  tvar : ∀ K v k, tok K v k → v = 1 ∨ v = 3 ∨ (5 ≤ v ∧ v ≤ 9)
  lset : ∀ st : St, (∀ v k, lok (st.sc 43) v k → (Cmd.run U.lset st).1.sc v = k) ∧
    (∀ y < 1000, (y < 20 ∨ 40 ≤ y) → (Cmd.run U.lset st).1.sc y = st.sc y) ∧ (Cmd.run U.lset st).1.ar = st.ar
  tset : ∀ st : St, (∀ v k, tok (st.sc 43) v k → (Cmd.run U.tset st).1.sc v = k) ∧
    (∀ y < 1000, y ≠ 1 → y ≠ 3 → (y < 5 ∨ 9 < y) → (Cmd.run U.tset st).1.sc y = st.sc y) ∧
    (Cmd.run U.tset st).1.ar = st.ar
  lnE : ∀ K σ A, (∀ v k, lok K v k → σ v = k) →
    eval σ A U.lnE = eval σ A (LevelEx.LnE (lvP K)) ∧ cost σ A U.lnE = cost σ A (LevelEx.LnE (lvP K))
  srE : ∀ K tr σ A, (∀ v k, lok K v k → σ v = k) →
    eval σ A (U.srE tr) = eval σ A (GroupEx.searchE (LevelEx.gs (lvP K) tr) 102 103) ∧
      cost σ A (U.srE tr) = cost σ A (GroupEx.searchE (LevelEx.gs (lvP K) tr) 102 103)
  nxE : ∀ K σ A, (∀ v k, lok K v k → σ v = k) →
    eval σ A U.nxE = eval σ A (LevelEx.nextTE (lvP K)) ∧ cost σ A U.nxE = cost σ A (LevelEx.nextTE (lvP K))
  l0E : ∀ K σ A, (∀ v k, tok K v k → σ v = k) →
    eval σ A U.l0E = eval σ A (L0E K (3 * K ^ 8)) ∧ cost σ A U.l0E = cost σ A (L0E K (3 * K ^ 8))
  tsE : ∀ K σ A, (∀ v k, tok K v k → σ v = k) →
    eval σ A U.tsE = eval σ A (GroupEx.searchE (gsTop K (3 * K ^ 8)) 13 14) ∧
      cost σ A U.tsE = cost σ A (GroupEx.searchE (gsTop K (3 * K ^ 8)) 13 14)
  ttE : ∀ K σ A, (∀ v k, tok K v k → σ v = k) →
    eval σ A U.ttE = eval σ A (GroupEx.tab (gsTop K (3 * K ^ 8))) ∧
      cost σ A U.ttE = cost σ A (GroupEx.tab (gsTop K (3 * K ^ 8)))
  vlnE : VB 1000 U.lnE
  vsrE : ∀ tr, VB 1000 (U.srE tr)
  vnxE : VB 990 U.nxE
  vl0E : VB 1000 U.l0E
  vtsE : VB 1000 U.tsE
  vttE : VB 990 U.ttE

section Search

variable {m BT lam : ℕ} {σ₀ : ℕ → ℕ} {A : ℕ → ℕ → ℕ} {P : LP} {Tab : Clique (ZMod m) (P.G * P.G) lam}

/-- The row search of a level. -/
theorem lvl_search_row (H : LevelHyp m BT σ₀ A P lam Tab) {cc : ℕ}
    (hcc : cc < (tB lam + 1) ^ (P.G * P.G * (P.G * P.G))) {σ₁ : ℕ → ℕ} (h1 : Ag P.b σ₀ σ₁) (hc : σ₁ P.b = cc)
    (hL : σ₁ (P.b + 1) = Lnext P.K P.G lam) :
    eval σ₁ A (GroupEx.searchE (LevelEx.gs P false) (P.b + 2) (P.b + 3)) =
      firstGood (okG (rowNet (toGrid Tab) (restrictC ((phiEquiv P.G (tB lam)).symm ⟨cc, hcc⟩)))
        P.K (Lnext P.K P.G lam) (by have := H.hK; omega)) (P.K ^ P.G) (P.K ^ P.G) := by
  have hK0 : 0 < P.K := by have := H.hK; omega
  have hvm : P.vm < P.b + 2 := by have := H.hvm; have := H.hBT; omega
  have Hg := LevelEx.gridHyp H h1 hc
  exact GroupEx.eval_searchE (S := LevelEx.gs P false) hK0 Hg.hg H.hm (GridEx.row_rep Hg hcc) hvm
    (show P.b + 1 < P.b + 2 by omega) (show P.b + 2 ≤ P.b + 2 by omega) (show P.b + 2 ≤ P.b + 3 by omega)
    (show P.b + 2 ≤ P.b + 4 by omega) (show P.b + 2 ≠ P.b + 3 by omega) (show P.b + 2 ≠ P.b + 4 by omega)
    (show P.b + 3 ≠ P.b + 4 by omega) (show P.b + 2 < P.b + 6 by omega) (show P.b + 3 < P.b + 6 by omega)
    (show P.b + 4 < P.b + 6 by omega) hL (Ag.refl _ _)

/-- The column search of a level. -/
theorem lvl_search_col (H : LevelHyp m BT σ₀ A P lam Tab) {cc : ℕ}
    (hcc : cc < (tB lam + 1) ^ (P.G * P.G * (P.G * P.G))) {σ₁ : ℕ → ℕ} (h1 : Ag P.b σ₀ σ₁) (hc : σ₁ P.b = cc)
    (hL : σ₁ (P.b + 1) = Lnext P.K P.G lam) :
    eval σ₁ A (GroupEx.searchE (LevelEx.gs P true) (P.b + 2) (P.b + 3)) =
      firstGood (okG (colNet (toGrid Tab) (restrictC ((phiEquiv P.G (tB lam)).symm ⟨cc, hcc⟩)))
        P.K (Lnext P.K P.G lam) (by have := H.hK; omega)) (P.K ^ P.G) (P.K ^ P.G) := by
  have hK0 : 0 < P.K := by have := H.hK; omega
  have hvm : P.vm < P.b + 2 := by have := H.hvm; have := H.hBT; omega
  have Hg := LevelEx.gridHyp H h1 hc
  exact GroupEx.eval_searchE (S := LevelEx.gs P true) hK0 Hg.hg H.hm (GridEx.col_rep Hg hcc) hvm
    (show P.b + 1 < P.b + 2 by omega) (show P.b + 2 ≤ P.b + 2 by omega) (show P.b + 2 ≤ P.b + 3 by omega)
    (show P.b + 2 ≤ P.b + 5 by omega) (show P.b + 2 ≠ P.b + 3 by omega) (show P.b + 2 ≠ P.b + 5 by omega)
    (show P.b + 3 ≠ P.b + 5 by omega) (show P.b + 2 < P.b + 6 by omega) (show P.b + 3 < P.b + 6 by omega)
    (show P.b + 5 < P.b + 6 by omega) hL (Ag.refl _ _)

end Search

namespace Uni

/-- The scalars a level writes (below `990`). -/
def WL (y : ℕ) : Prop :=
  (20 ≤ y ∧ y < 48) ∨ y = 100 ∨ y = 101 ∨ y = 104 ∨ y = 105 ∨ y = 305 ∨ y = 311 ∨ y = 320 ∨ y = 321

theorem vb_dE : VB 1000 dE := by simp [dE, VB]
theorem vb_kbE (v : ℕ) (h : v < 1000) : VB 1000 (kbE v) := by simp [kbE, powE, VB]; omega
theorem vb_NcE : VB 1000 (NcE 43 40) := by simp [NcE, g4E, gE, powE, tBE, VB]

end Uni

theorem ZR.eq_val {m v : ℕ} {x : ZMod m} (h : ZR m v x) : v = x.val := by
  rw [← h.2, ZMod.val_cast_of_lt h.1]

/-- A table written by `fillC` (entry `i` = `(γ, Q) = (i % K, i / K)`) is held. -/
theorem holds_filled {m K L : ℕ} (T : Clique (ZMod m) K L) (A : ℕ → ℕ → ℕ) {p : ℕ} (hp : p < 3) (hK : 0 < K) :
    Holds (filled A (fun i => (tabK T (i % K) (i / K)).val) p (K * 2 ^ (L * K))) p T := by
  intro γ hγ Q hQ
  have e1 : (3 * (γ + K * Q) + p) % 3 = p := by omega
  have e2 : (3 * (γ + K * Q) + p) / 3 = γ + K * Q := by omega
  have e3 : γ + K * Q < K * 2 ^ (L * K) := by
    calc γ + K * Q < K + K * Q := by omega
      _ = K * (Q + 1) := by ring
      _ ≤ K * 2 ^ (L * K) := Nat.mul_le_mul_left _ hQ
  have e4 : (γ + K * Q) % K = γ := by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hγ]
  have e5 : (γ + K * Q) / K = Q := by
    rw [Nat.add_mul_div_left _ _ hK, Nat.div_eq_of_lt hγ, zero_add]
  simp only [filled, Function.update_self, e1, e2, true_and, if_pos e3, e4, e5]

theorem Kb_pos (d : ℕ) : 0 < Kb K0u d := by have := Kb_ge K0u (by norm_num) d; omega

/-- **One level of one path.** -/
theorem lvlBody_spec (U : UParts) {lok tok : ℕ → ℕ → ℕ → Prop} (H : UOK U lok tok) {m d L par R : ℕ} (st : St)
    (T : Clique (ZMod m) (Kb K0u (d + 1)) L)
    (hm : 1 < m) (h10 : st.sc 10 = m) (h307 : st.sc 307 = d + 1 + st.sc 306) (h40 : st.sc 40 = L)
    (h41 : st.sc 41 = par) (hpar : par < 3) (hpj : par ≠ st.sc 306 % 2) (h42 : st.sc 42 = Kb K0u (d + 1))
    (h305 : st.sc 305 = R) (hT : Holds st.ar par T) :
    (Cmd.run (lvlBody U) st).1.sc 40 = Lnext (Kb K0u d) (Gs K0u d) L ∧
      (Cmd.run (lvlBody U) st).1.sc 41 = st.sc 306 % 2 ∧ (Cmd.run (lvlBody U) st).1.sc 42 = Kb K0u d ∧
      (Cmd.run (lvlBody U) st).1.sc 305 = R / Nc K0u d L ∧
      Holds (Cmd.run (lvlBody U) st).1.ar (st.sc 306 % 2) (nextT (Kb K0u d) (Kb_pos d) T
        ⟨R % Nc K0u d L, Nat.mod_lt _ (Nc_pos _ _ _)⟩) ∧
      AgP st.ar (Cmd.run (lvlBody U) st).1.ar (st.sc 306 % 2) ∧
      ∀ y < 990, ¬ WL y → (Cmd.run (lvlBody U) st).1.sc y = st.sc y := by
  set j := st.sc 306
  set K := Kb K0u d
  set G := 3 * K ^ 8
  set N := Nc K0u d L
  set c := R % N
  set L' := Lnext K G L
  have hN : 0 < N := Nc_pos _ _ _
  have hc : c < N := Nat.mod_lt _ hN
  have hK2 : 2 ≤ K := Kb_ge K0u (by norm_num) d
  -- s1: 45 := d
  obtain ⟨v1, a1, -⟩ := vw_cset vb_dE (show 45 < 1000 by norm_num) st
  set s1 := (Cmd.run (cset dE 45) st).1
  have e1 : eval (vw st) st.ar dE = d := by
    simp only [dE, Ex.eval, vw_lt (show 307 < 1000 by norm_num), vw_lt (show 306 < 1000 by norm_num), h307]
    omega
  rw [e1] at v1
  -- s2: 43 := K
  obtain ⟨v2, a2, -⟩ := vw_cset (vb_kbE 45 (by norm_num)) (show 43 < 1000 by norm_num) s1
  set s2 := (Cmd.run (cset (kbE 45) 43) s1).1
  rw [eval_kbE, v1, Function.update_self] at v2
  -- s3: the level literals
  obtain ⟨l1, l2, a3⟩ := H.lset s2
  set s3 := (Cmd.run U.lset s2).1
  have s2_43 : s2.sc 43 = K := by rw [← vw_lt (show 43 < 1000 by norm_num), v2, Function.update_self]
  rw [s2_43] at l1
  have v3 : ∀ y, ¬ (20 ≤ y ∧ y < 40) → vw s3 y = vw s2 y := fun y hy => by
    by_cases hy' : y < 1000
    · rw [vw_lt hy', vw_lt hy', l2 y hy' (by omega)]
    · simp [vw, hy']
  have lit3 : ∀ v k, lok K v k → vw s3 v = k := fun v k h => by
    have := H.lvar K v k h; rw [vw_lt (by omega), l1 v k h]
  -- the context before the level's own variables
  have c3 : ∀ y, ¬ (20 ≤ y ∧ y < 40) → y ≠ 45 → y ≠ 43 → vw s3 y = vw st y := fun y h1 h2 h3 => by
    rw [v3 y h1, v2, Function.update_of_ne h3, Function.update_of_ne h2]
  -- s4: 47 := N
  obtain ⟨v4, a4, -⟩ := vw_cset vb_NcE (show 47 < 1000 by norm_num) s3
  set s4 := (Cmd.run (cset (NcE 43 40) 47) s3).1
  rw [eval_NcE (d := d) (L := L) (by norm_num) (by norm_num) (by norm_num)
    (by rw [v3 43 (by omega), v2, Function.update_self])
    (by rw [c3 40 (by omega) (by omega) (by omega), vw_lt (by norm_num), h40])] at v4
  have c4 : ∀ y, ¬ (20 ≤ y ∧ y < 40) → y ≠ 45 → y ≠ 43 → y ≠ 47 → vw s4 y = vw st y := fun y h1 h2 h3 h4 => by
    rw [v4, Function.update_of_ne h4, c3 y h1 h2 h3]
  -- s5: 100 := c, s6: 305 := R / N
  obtain ⟨v5, a5, -⟩ := vw_cset (e := .mod (.var 305) (.var 47)) (by simp [VB]) (show 100 < 1000 by norm_num) s4
  set s5 := (Cmd.run (cset (.mod (.var 305) (.var 47)) 100) s4).1
  have r4 : vw s4 305 = R := by rw [c4 305 (by omega) (by omega) (by omega) (by omega), vw_lt (by norm_num), h305]
  have n4 : vw s4 47 = N := by rw [v4, Function.update_self]
  rw [show eval (vw s4) s4.ar (.mod (.var 305) (.var 47)) = c by simp only [Ex.eval, r4, n4]; rfl] at v5
  obtain ⟨v6, a6, -⟩ := vw_cset (e := .div (.var 305) (.var 47)) (by simp [VB]) (show 305 < 1000 by norm_num) s5
  set s6 := (Cmd.run (cset (.div (.var 305) (.var 47)) 305) s5).1
  rw [show eval (vw s5) s5.ar (.div (.var 305) (.var 47)) = R / N by
    simp only [Ex.eval, v5, Function.update_of_ne (show (305 : ℕ) ≠ 100 by norm_num),
      Function.update_of_ne (show (47 : ℕ) ≠ 100 by norm_num), r4, n4]] at v6
  -- the level's context
  have c6 : ∀ y, y < 100 → ¬ (20 ≤ y ∧ y < 40) → y ≠ 45 → y ≠ 43 → y ≠ 47 → (vw s6) y = vw st y :=
    fun y hy h1 h2 h3 h4 => by
      rw [v6, Function.update_of_ne (by omega), v5, Function.update_of_ne (by omega), c4 y h1 h2 h3 h4]
  have lit6 : ∀ v k, lok K v k → (vw s6) v = k := fun v k h => by
    have := H.lvar K v k h
    rw [v6, Function.update_of_ne (by omega), v5, Function.update_of_ne (by omega), v4,
      Function.update_of_ne (by omega), lit3 v k h]
  have ar6 : s6.ar = st.ar := by rw [a6, a5, a4, a3, a2, a1]
  have hT6 : TRep m 60 (vw s6) s6.ar 60 61 rdT T := by
    rw [ar6]
    exact rdTE_rep (K := Kb K0u (d + 1)) hm hT
      (by rw [c6 42 (by norm_num) (by omega) (by omega) (by omega) (by omega), vw_lt (by norm_num), h42])
      (by rw [c6 40 (by norm_num) (by omega) (by omega) (by omega) (by omega), vw_lt (by norm_num), h40])
      (by rw [c6 41 (by norm_num) (by omega) (by omega) (by omega) (by omega), vw_lt (by norm_num), h41])
      (by norm_num) (by norm_num) (by norm_num)
  have mkH : ∀ A', TRep m 60 (vw s6) A' 60 61 rdT T → LevelHyp m 60 (vw s6) A' (lvP K) L T := fun A' hr =>
    { hm := hm, hK := hK2, hG := rfl, rep := hr,
      vm := by show (vw s6) 10 = m; rw [c6 10 (by norm_num) (by omega) (by omega) (by omega) (by omega), vw_lt (by norm_num), h10]
      vl := by show (vw s6) 40 = L; rw [c6 40 (by norm_num) (by omega) (by omega) (by omega) (by omega), vw_lt (by norm_num), h40]
      hvm := by simp [lvP], hγ := by simp [lvP], hΘ := by simp [lvP], hγΘ := by simp [lvP],
      hlγ := by simp [lvP], hBT := by simp [lvP], hl := by simp [lvP], hγb := by simp [lvP],
      hΘb := by simp [lvP] }
  have H6 := mkH s6.ar hT6
  -- s7: 101 := L'
  obtain ⟨v7, a7, -⟩ := vw_cset H.vlnE (show 101 < 1000 by norm_num) s6
  set s7 := (Cmd.run (cset U.lnE 101) s6).1
  rw [(H.lnE K (vw s6) s6.ar lit6).1, LevelEx.eval_LnE (lam := L) H6.vl] at v7
  -- s8, s9: the searches
  have ag7 : Ag 100 (vw s6) (vw s7) := fun y hy => by rw [v7, Function.update_of_ne (by omega)]
  have c7 : vw s7 100 = c := by
    rw [v7, Function.update_of_ne (by norm_num), v6, Function.update_of_ne (by norm_num), v5, Function.update_self]
  have L7 : vw s7 101 = L' := by rw [v7, Function.update_self]; rfl
  have lit7 : ∀ v k, lok K v k → vw s7 v = k := fun v k h => by
    have := H.lvar K v k h; rw [ag7 v (by omega), lit6 v k h]
  obtain ⟨v8, a8, -⟩ := vw_cset (H.vsrE false) (show 104 < 1000 by norm_num) s7
  set s8 := (Cmd.run (cset (U.srE false) 104) s7).1
  have hs8 : eval (vw s7) s6.ar (GroupEx.searchE (LevelEx.gs (lvP K) false) 102 103) = _ :=
    lvl_search_row H6 hc ag7 c7 L7
  rw [(H.srE K false (vw s7) s7.ar lit7).1, show s7.ar = s6.ar from a7, hs8] at v8
  have ag8 : Ag 100 (vw s6) (vw s8) := fun y hy => by rw [v8, Function.update_of_ne (by omega), ag7 y hy]
  have c8 : vw s8 100 = c := by rw [v8, Function.update_of_ne (by norm_num), c7]
  have L8 : vw s8 101 = L' := by rw [v8, Function.update_of_ne (by norm_num), L7]
  have lit8 : ∀ v k, lok K v k → vw s8 v = k := fun v k h => by
    have := H.lvar K v k h; rw [ag8 v (by omega), lit6 v k h]
  obtain ⟨v9, a9, -⟩ := vw_cset (H.vsrE true) (show 105 < 1000 by norm_num) s8
  set s9 := (Cmd.run (cset (U.srE true) 105) s8).1
  have hs9 : eval (vw s8) s6.ar (GroupEx.searchE (LevelEx.gs (lvP K) true) 102 103) = _ :=
    lvl_search_col H6 hc ag8 c8 L8
  rw [(H.srE K true (vw s8) s8.ar lit8).1, show s8.ar = s6.ar by rw [a8, a7], hs9] at v9
  have ag9 : Ag 100 (vw s6) (vw s9) := fun y hy => by rw [v9, Function.update_of_ne (by omega), ag8 y hy]
  have c9 : vw s9 100 = c := by rw [v9, Function.update_of_ne (by norm_num), c8]
  have L9 : vw s9 101 = L' := by rw [v9, Function.update_of_ne (by norm_num), L8]
  -- s10: 320 := j % 2, s11: 321 := K · 2^(L' K)
  obtain ⟨v10, a10, -⟩ := vw_cset (e := .mod (.var 306) (.lit 2)) (by simp [VB]) (show 320 < 1000 by norm_num) s9
  set s10 := (Cmd.run (cset (.mod (.var 306) (.lit 2)) 320) s9).1
  have j9 : vw s9 306 = j := by
    rw [v9, Function.update_of_ne (by norm_num), v8, Function.update_of_ne (by norm_num), v7,
      Function.update_of_ne (by norm_num), v6, Function.update_of_ne (by norm_num), v5,
      Function.update_of_ne (by norm_num), c4 306 (by omega) (by omega) (by omega) (by omega), vw_lt (by norm_num)]
  rw [show eval (vw s9) s9.ar (.mod (.var 306) (.lit 2)) = j % 2 by simp only [Ex.eval, j9]] at v10
  obtain ⟨v11, a11, -⟩ := vw_cset (e := .mul (.var 43) (pow2 915 (.mul (.var 101) (.var 43))))
    (by simp [VB, pow2]) (show 321 < 1000 by norm_num) s10
  set s11 := (Cmd.run (cset (.mul (.var 43) (pow2 915 (.mul (.var 101) (.var 43)))) 321) s10).1
  have k10 : vw s10 43 = K := by
    rw [v10, Function.update_of_ne (by norm_num), ag9 43 (by norm_num), v6, Function.update_of_ne (by norm_num),
      v5, Function.update_of_ne (by norm_num), v4, Function.update_of_ne (by norm_num),
      v3 43 (by omega), v2, Function.update_self]
  have L10 : vw s10 101 = L' := by rw [v10, Function.update_of_ne (by norm_num), L9]
  rw [show eval (vw s10) s10.ar (.mul (.var 43) (pow2 915 (.mul (.var 101) (.var 43)))) = K * 2 ^ (L' * K) by
    simp only [Ex.eval, eval_pow2, k10, L10]] at v11
  -- s12: the next table
  set T' := nextT K (Kb_pos d) T ⟨c, hc⟩
  have ar11 : s11.ar = st.ar := by rw [a11, a10, a9, a8, a7, ar6]
  have p11 : s11.sc 320 = j % 2 := by
    rw [← vw_lt (show 320 < 1000 by norm_num), v11, Function.update_of_ne (by norm_num), v10, Function.update_self]
  have n11 : s11.sc 321 = K * 2 ^ (L' * K) := by
    rw [← vw_lt (show 321 < 1000 by norm_num), v11, Function.update_self]
  have k11 : s11.sc 43 = K := by
    rw [← vw_lt (show 43 < 1000 by norm_num), v11, Function.update_of_ne (by norm_num), k10]
  have hval : ∀ i < s11.sc 321, ∀ A', AgP s11.ar A' (s11.sc 320) →
      eval (fillEnv s11.sc 311 43 162 163 i) A' U.nxE = (tabK T' (i % K) (i / K)).val := by
    intro i _ A' hA'
    set σ := fillEnv s11.sc 311 43 162 163 i
    have hσ : ∀ y < 1000, y ≠ 311 → y ≠ 162 → y ≠ 163 → σ y = vw s11 y := fun y hy h1 h2 h3 => by
      simp only [σ, fillEnv]
      rw [Function.update_of_ne h3, Function.update_of_ne h2, Function.update_of_ne h1, vw_lt hy]
    have ag : Ag 106 (vw s9) σ := fun y hy => by
      rw [hσ y (by omega) (by omega) (by omega) (by omega), v11, Function.update_of_ne (by omega), v10,
        Function.update_of_ne (by omega)]
    have litσ : ∀ v k, lok K v k → σ v = k := fun v k h => by
      have := H.lvar K v k h; rw [ag v (by omega), ag9 v (by omega), lit6 v k h]
    have hTA : Holds A' par T := hT.congr (fun x hx => by rw [hA'.2 x (by rw [p11]; omega), ar11]) hpar
    have hrep : TRep m 60 (vw s6) A' 60 61 rdT T :=
      rdTE_rep (K := Kb K0u (d + 1)) hm hTA
        (by rw [c6 42 (by norm_num) (by omega) (by omega) (by omega) (by omega), vw_lt (by norm_num), h42])
        (by rw [c6 40 (by norm_num) (by omega) (by omega) (by omega) (by omega), vw_lt (by norm_num), h40])
        (by rw [c6 41 (by norm_num) (by omega) (by omega) (by omega) (by omega), vw_lt (by norm_num), h41])
        (by norm_num) (by norm_num) (by norm_num)
    have H' := mkH A' hrep
    have hR := LevelEx.level_rep H' hc ag9 c9 L9
      (by show vw s9 104 = _; rw [v9, Function.update_of_ne (by norm_num), v8, Function.update_self])
      (by show vw s9 105 = _; rw [v9, Function.update_self])
    have hγ : i % K < K := Nat.mod_lt _ (by omega)
    have z := hR σ ag ⟨i % K, hγ⟩ (i / K) (by show σ 162 = i % K; simp [σ, fillEnv, k11])
      (by show σ 163 = i / K; simp [σ, fillEnv, k11])
    rw [(H.nxE K σ A' litσ).1, z.eq_val, tabK, dif_pos hγ]
    rfl
  obtain ⟨f1, f2⟩ := fill_val U.nxE (vn := 321) (vi := 311) (vK := 43) (vγ := 162) (vΘ := 163) (vpar := 320)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) H.vnxE s11 (by rw [p11]; omega) _ hval
  set s12 := (Cmd.run (fillC U.nxE 321 311 43 162 163 320) s11).1
  have w12 : ∀ y < 990, y ≠ 311 → vw s12 y = vw s11 y := fun y hy h => by
    rw [vw_lt (by omega), vw_lt (by omega), f2 y hy h]
  obtain ⟨v13, a13, -⟩ := vw_copy (show 40 < 1000 by norm_num) (show 101 < 1000 by norm_num) s12
  set s13 := (Cmd.run (.copy 40 101) s12).1
  obtain ⟨v14, a14, -⟩ := vw_copy (show 41 < 1000 by norm_num) (show 320 < 1000 by norm_num) s13
  set s14 := (Cmd.run (.copy 41 320) s13).1
  obtain ⟨v15, a15, -⟩ := vw_copy (show 42 < 1000 by norm_num) (show 43 < 1000 by norm_num) s14
  set s15 := (Cmd.run (.copy 42 43) s14).1
  have hrun : (Cmd.run (lvlBody U) st).1 = s15 := by simp only [lvlBody, Cmd.run_seq]; rfl
  rw [hrun]
  have l12 : vw s12 101 = L' := by rw [w12 101 (by norm_num) (by norm_num), v11, Function.update_of_ne (by norm_num), L10]
  have p12 : vw s12 320 = j % 2 := by rw [w12 320 (by norm_num) (by norm_num), vw_lt (by norm_num), p11]
  have k12 : vw s12 43 = K := by rw [w12 43 (by norm_num) (by norm_num), vw_lt (by norm_num), k11]
  have frame : ∀ y < 990, ¬ WL y → vw s15 y = vw st y := fun y hy hW => by
    simp only [WL] at hW
    rw [v15, Function.update_of_ne (by omega), v14, Function.update_of_ne (by omega), v13,
      Function.update_of_ne (by omega), w12 y hy (by omega), v11, Function.update_of_ne (by omega), v10,
      Function.update_of_ne (by omega), v9, Function.update_of_ne (by omega), v8, Function.update_of_ne (by omega),
      v7, Function.update_of_ne (by omega), v6, Function.update_of_ne (by omega), v5,
      Function.update_of_ne (by omega), c4 y (by omega) (by omega) (by omega) (by omega)]
  have ar15 : s15.ar = filled st.ar (fun i => (tabK T' (i % K) (i / K)).val) (j % 2) (K * 2 ^ (L' * K)) := by
    rw [a15, a14, a13, f1, ar11, p11, n11]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← vw_lt (show 40 < 1000 by norm_num), v15, Function.update_of_ne (by norm_num), v14,
      Function.update_of_ne (by norm_num), v13, Function.update_self, l12]
    rfl
  · rw [← vw_lt (show 41 < 1000 by norm_num), v15, Function.update_of_ne (by norm_num), v14,
      Function.update_self, v13, Function.update_of_ne (by norm_num), p12]
  · rw [← vw_lt (show 42 < 1000 by norm_num), v15, Function.update_self, v14, Function.update_of_ne (by norm_num),
      v13, Function.update_of_ne (by norm_num), k12]
  · rw [← vw_lt (show 305 < 1000 by norm_num), v15, Function.update_of_ne (by norm_num), v14,
      Function.update_of_ne (by norm_num), v13, Function.update_of_ne (by norm_num),
      w12 305 (by norm_num) (by norm_num), v11, Function.update_of_ne (by norm_num), v10,
      Function.update_of_ne (by norm_num), v9, Function.update_of_ne (by norm_num), v8,
      Function.update_of_ne (by norm_num), v7, Function.update_of_ne (by norm_num), v6, Function.update_self]
  · rw [ar15]; exact holds_filled T' _ (by omega) (by omega)
  · rw [ar15]; exact filled_agP _ _ _ _
  · intro y hy hW
    rw [← vw_lt (show y < 1000 by omega), frame y hy hW, vw_lt (by omega)]


end Factoring.Aux
