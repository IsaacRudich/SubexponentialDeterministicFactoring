/-
The uniform engine: the top (the multiplication network, its clusters, the top grouping).

The top facts are `top_rep`'s steps (`EngineTop.lean`) for an arbitrary context: the search (`top_search`), the top
table (`top_tab_rep`), its value (`top_value`).

Not an audit surface.
-/
module

public import FactoringAux.UniPathSpec
public import FactoringAux.UniInst

@[expose] public section

namespace Factoring.Aux

open Factoring.Aux.Copied Factoring.Aux.Copied.PLib Ex Uni Finset

section Top

variable {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ} {m n k K : ℕ}

theorem top_search (hK : 2 ≤ K) (hm : 1 < m) (h10 : σ 10 = m) (h11 : σ 11 = sOf n) (h0 : σ 0 = n) (h2 : σ 2 = k)
    (hkn : k ≤ n) (h12 : σ 12 = Ltop K (3 * K ^ 8) (sOf n)) :
    eval σ A (GroupEx.searchE (gsTop K (3 * K ^ 8)) 13 14) =
      firstGood (okG (clusterNet (sOf n) (ZMod m) (numCells (A 0) 1 n) k (numCells (A 1) k (n - k)) (3 * K ^ 8)
        (by positivity)) K (Ltop K (3 * K ^ 8) (sOf n)) (by omega)) (K ^ (3 * K ^ 8)) (K ^ (3 * K ^ 8)) := by
  have hg : 0 < 3 * K ^ 8 := by positivity
  have H2 := clusterHyp (A := A) (σ₀ := σ) hm hg h10 h11 h0 h2 hkn (sOf_spec n)
  have hr2 := coarsen_rep H2 (show 10 < 13 by norm_num)
  exact GroupEx.eval_searchE (S := gsTop K (3 * K ^ 8)) (L := Ltop K (3 * K ^ 8) (sOf n)) (show 0 < K by omega) hg hm hr2
    (show 10 < 13 by norm_num) (show 12 < 13 by norm_num) (show 13 ≤ 13 by norm_num) (show 13 ≤ 14 by norm_num)
    (show 13 ≤ 15 by norm_num) (show (13 : ℕ) ≠ 14 by norm_num) (show (13 : ℕ) ≠ 15 by norm_num)
    (show (14 : ℕ) ≠ 15 by norm_num) (show 13 < 26 by norm_num) (show 14 < 26 by norm_num)
    (show 15 < 26 by norm_num) h12 (Ag.refl _ _)

theorem top_tab_rep (hK : 2 ≤ K) (hm : 1 < m) (h10 : σ 10 = m) (h11 : σ 11 = sOf n) (h0 : σ 0 = n) (h2 : σ 2 = k)
    (hkn : k ≤ n) (h12 : σ 12 = Ltop K (3 * K ^ 8) (sOf n)) {xf : ℕ} (h15 : σ 15 = xf) :
    TRep m 16 σ A 82 83 (GroupEx.tab (gsTop K (3 * K ^ 8)))
      (((clusterNet (sOf n) (ZMod m) (numCells (A 0) 1 n) k (numCells (A 1) k (n - k)) (3 * K ^ 8)
        (by positivity)).coarsen (chiOf K (3 * K ^ 8) xf (by omega))).toClique (Ltop K (3 * K ^ 8) (sOf n))) := by
  have hg : 0 < 3 * K ^ 8 := by positivity
  have H3 := clusterHyp (A := A) (σ₀ := σ) hm hg h10 h11 h0 h2 hkn (sOf_spec n)
  have hr3 := (coarsen_rep H3 (show 10 < 13 by norm_num)).mono (show 13 ≤ 16 by norm_num)
  exact GroupEx.group_rep (S := gsTop K (3 * K ^ 8)) (x := xf) (L := Ltop K (3 * K ^ 8) (sOf n)) (show 0 < K by omega) hg hm
    hr3 (show 10 < 16 by norm_num) (show 15 < 16 by norm_num) (show 12 < 16 by norm_num)
    (show 16 ≤ 26 by norm_num) h15 h12

theorem top_value (hK : 2 ≤ K) (m : ℕ) (N : ℕ) (hN1 : 1 ≤ N) (hNn : N < 2 ^ n) (x : ℕ) :
    (((clusterNet (sOf n) (ZMod m) N k x (3 * K ^ 8) (by positivity)).coarsen
      (chiOf K (3 * K ^ 8) (firstGood (okG (clusterNet (sOf n) (ZMod m) N k x (3 * K ^ 8) (by positivity)) K
        (Ltop K (3 * K ^ 8) (sOf n)) (by omega)) (K ^ (3 * K ^ 8)) (K ^ (3 * K ^ 8))) (by omega))).toClique
          (Ltop K (3 * K ^ 8) (sOf n))).value =
      ((N.divisors.filter (fun d => d / 2 ^ k = x)).card : ZMod m) := by
  set s := sOf n
  set g := 3 * K ^ 8
  have hg : 0 < g := by positivity
  set CN := clusterNet s (ZMod m) N k x g hg
  obtain ⟨x0, hx0, hok⟩ := good_exists CN (clP s g) (10 * (pA s * pA s) * fw s) (clusterNet_fits s _ N k x g hg)
    (clusterNet_total_le s _ N k x g hg) hK rfl
  have hspec := firstGood_spec (okG CN K (Ltop K g s) (by omega)) (le_refl (K ^ g)) ⟨x0, hx0, hok⟩
  have hNlt : N < 2 ^ (pL s * pL s) :=
    lt_of_lt_of_le hNn (Nat.pow_le_pow_right (by norm_num) (sOf_spec n))
  rw [okG_value CN (by omega) hspec.2, clusterNet_value s _ N k x g hg hN1 hNlt]

end Top

namespace Uni

/-- The scalars the count modulo `m` writes (below `990`). -/
def WC (y : ℕ) : Prop := WP y ∨ y = 304 ∨ y = 15 ∨ y = 320 ∨ y = 321 ∨ y = 311

end Uni

/-- The number of divisors of `N` with high bits `x` (from position `k`). -/
def cntAll (N k x : ℕ) : ℕ := (N.divisors.filter (fun d => d / 2 ^ k = x)).card

set_option maxRecDepth 20000 in
/-- **The whole count modulo `m`.** -/
theorem countM_spec {m n k ℓ : ℕ} (st : St) (hm : 1 < m) (h10 : st.sc 10 = m) (h11 : st.sc 11 = sOf n)
    (h0 : st.sc 0 = n) (h2 : st.sc 2 = k) (hkn : k < n) (h307 : st.sc 307 = ℓ) (h316 : st.sc 316 = Kb K0u ℓ)
    (h12 : st.sc 12 = Ltop (Kb K0u ℓ) (Gs K0u ℓ) (sOf n))
    (h303 : st.sc 303 = NPof K0u ℓ (Ltop (Kb K0u ℓ) (Gs K0u ℓ) (sOf n)))
    (htok : ∀ v k', tokU (Kb K0u ℓ) v k' → st.sc v = k') (hN1 : 1 ≤ numCells (st.ar 0) 1 n) :
    (Cmd.run (countM UP) st).1.sc 308 =
        (((deepMult K0u ℓ (Ltop (Kb K0u ℓ) (Gs K0u ℓ) (sOf n)) : ℕ) : ZMod m) *
          (cntAll (numCells (st.ar 0) 1 n) k (numCells (st.ar 1) k (n - k)) : ZMod m)).val ∧
      (∀ y < 990, ¬ WC y → (Cmd.run (countM UP) st).1.sc y = st.sc y) ∧
      (∀ a, a ≠ 3 → (Cmd.run (countM UP) st).1.ar a = st.ar a) := by
  have : NeZero m := ⟨by omega⟩
  set K := Kb K0u ℓ
  set L := Ltop K (3 * K ^ 8) (sOf n)
  have hK : 2 ≤ K := Kb_ge K0u (by norm_num) ℓ
  set N := numCells (st.ar 0) 1 n
  set x := numCells (st.ar 1) k (n - k)
  have hg : 0 < 3 * K ^ 8 := by positivity
  set CN := clusterNet (sOf n) (ZMod m) N k x (3 * K ^ 8) hg
  set xf := firstGood (okG CN K L (by omega)) (K ^ (3 * K ^ 8)) (K ^ (3 * K ^ 8))
  set Tt := (CN.coarsen (chiOf K (3 * K ^ 8) xf (by omega))).toClique L
  rw [countM]
  repeat rw [Cmd.run_seq]
  -- c1: 15 := xf
  obtain ⟨v1, a1, -⟩ := vw_cset UP_ok.vtsE (show 15 < 1000 by norm_num) st
  set c1 := (Cmd.run (cset UP.tsE 15) st).1
  have tk : ∀ v k', tokU K v k' → vw st v = k' := fun v k' h => by
    have := topOk_lt h; rw [vw_lt (by omega), htok v k' h]
  rw [(UP_ok.tsE K (vw st) st.ar tk).1, top_search hK hm (by rw [vw_lt (by norm_num), h10])
    (by rw [vw_lt (by norm_num), h11]) (by rw [vw_lt (by norm_num), h0]) (by rw [vw_lt (by norm_num), h2]) hkn.le
    (by rw [vw_lt (by norm_num), h12]; rfl)] at v1
  -- c2: 321 := K · 2^(L K); c3: 320 := 2
  obtain ⟨v2, a2, -⟩ := vw_cset (e := .mul (.var 316) (pow2 915 (.mul (.var 12) (.var 316)))) (by simp [VB, pow2])
    (show 321 < 1000 by norm_num) c1
  set c2 := (Cmd.run (cset (.mul (.var 316) (pow2 915 (.mul (.var 12) (.var 316)))) 321) c1).1
  have k1 : vw c1 316 = K := by rw [v1, Function.update_of_ne (by norm_num), vw_lt (by norm_num), h316]
  have l1 : vw c1 12 = L := by rw [v1, Function.update_of_ne (by norm_num), vw_lt (by norm_num), h12]; rfl
  rw [show eval (vw c1) c1.ar (.mul (.var 316) (pow2 915 (.mul (.var 12) (.var 316)))) = K * 2 ^ (L * K) by
    simp only [Ex.eval, eval_pow2, k1, l1]] at v2
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
  have K3 : c3.sc 316 = K := by rw [sc3 316 (by norm_num) (by norm_num) (by norm_num) (by norm_num), h316]
  -- c4: the top table
  have hval : ∀ i < c3.sc 321, ∀ A', AgP c3.ar A' (c3.sc 320) →
      eval (fillEnv c3.sc 311 316 82 83 i) A' UP.ttE = (tabK Tt (i % K) (i / K)).val := by
    intro i _ A' hA'
    set σ := fillEnv c3.sc 311 316 82 83 i
    have hσ : ∀ y < 1000, y ≠ 311 → y ≠ 82 → y ≠ 83 → σ y = c3.sc y := fun y hy h1 h2 h3 => by
      simp only [σ, fillEnv]
      rw [Function.update_of_ne h3, Function.update_of_ne h2, Function.update_of_ne h1]
    have g : ∀ y < 82, y ≠ 15 → σ y = st.sc y := fun y hy h => by
      rw [hσ y (by omega) (by omega) (by omega) (by omega), sc3 y (by omega) (by omega) (by omega) h]
    have tkσ : ∀ v k', tokU K v k' → σ v = k' := fun v k' h => by
      have := topOk_lt h; have := h.1; rw [g v (by omega) (by omega), htok v k' h]
    have e0 : A' 0 = st.ar 0 := by rw [hA'.1 0 (by norm_num), ar3]
    have e1 : A' 1 = st.ar 1 := by rw [hA'.1 1 (by norm_num), ar3]
    have hR := top_tab_rep (σ := σ) (A := A') (m := m) (n := n) (k := k) hK hm (by rw [g 10 (by norm_num) (by norm_num), h10])
      (by rw [g 11 (by norm_num) (by norm_num), h11]) (by rw [g 0 (by norm_num) (by norm_num), h0])
      (by rw [g 2 (by norm_num) (by norm_num), h2]) hkn.le (by rw [g 12 (by norm_num) (by norm_num), h12]; rfl)
      (xf := xf) (by rw [hσ 15 (by norm_num) (by norm_num) (by norm_num) (by norm_num), x3])
    rw [e0, e1] at hR
    have hγ : i % K < K := Nat.mod_lt _ (by omega)
    have z := hR σ (Ag.refl _ _) ⟨i % K, hγ⟩ (i / K) (by simp [σ, fillEnv, K3]) (by simp [σ, fillEnv, K3])
    rw [(UP_ok.ttE K σ A' tkσ).1, z.eq_val, tabK, dif_pos hγ]
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
  have hP := pathLoop_spec UP UP_ok Tt c5 hm (by rw [sc5 10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num), h10])
    (by rw [sc5 307 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
      h307])
    (by rw [sc5 12 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
      h12]; rfl)
    (by rw [sc5 316 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
      h316])
    (by rw [← vw_lt (show 308 < 1000 by norm_num), v5, Function.update_self]) (by rw [a5]; exact hT4)
  obtain ⟨r308, rfr, -, rar⟩ := hP
  refine ⟨?_, fun y hy hW => ?_, fun a ha => ?_⟩
  · rw [r308, sc5 303 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
      h303, show Ltop (Kb K0u ℓ) (Gs K0u ℓ) (sOf n) = L from rfl, sum_chainVal, deepVal_eq,
      top_value hK m N hN1 (numCells_lt _ _ _) x]
    rfl
  · simp only [WC, WP, WL] at hW
    rw [rfr y hy (by simp only [WP, WL]; omega) (by omega), sc5 y hy (by omega) (by omega) (by omega) (by omega)
      (by omega)]
  · rw [rar a ha, a5, ar4]
    simp [filled, Function.update_of_ne ha]

end Factoring.Aux
