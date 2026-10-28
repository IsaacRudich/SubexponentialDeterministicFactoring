/-
The cost of the counting expression: value bounds of the chain (`deepEx`).

* `BruteReq`, **`brute_bdd`**: the brute force at the bottom.
* `LevelReq` (the requirements on `V` at one level), `DeepReq` (along the chain), **`deep_bdd`**.

Not an audit surface.
-/
module

public import FactoringAux.EngineCostGroup
public import FactoringAux.EngineDeepEx

@[expose] public section

namespace Factoring.Aux

open Finset Ex SB

/-! ### The brute force -/

/-- What the brute force over a `(K, L)`-clique needs of `V`. -/
structure BruteReq (V m K L : ℕ) : Prop where
  hm : 1 < m
  mm : m * m ≤ V
  hK : 1 ≤ K
  KK : K * K ≤ V
  hLK : 2 ^ (L * (K * K)) ≤ V
  two : 2 ≤ V

theorem BruteReq.LV {V m K L : ℕ} (R : BruteReq V m K L) : L ≤ V := by
  have h1 : L ≤ L * (K * K) := Nat.le_mul_of_pos_right _ (Nat.mul_pos R.hK R.hK)
  exact le_trans (le_trans h1 Nat.lt_two_pow_self.le) R.hLK

theorem BruteReq.mV {V m K L : ℕ} (R : BruteReq V m K L) : m ≤ V :=
  le_trans (Nat.le_mul_of_pos_left _ (by have := R.hm; omega)) R.mm

theorem BruteReq.KV {V m K L : ℕ} (R : BruteReq V m K L) : K ≤ V :=
  le_trans (Nat.le_mul_of_pos_left _ R.hK) R.KK

section Brute

variable {V m K L : ℕ} {A : ℕ → ℕ → ℕ}

theorem blkKE_bdd (R : BruteReq V m K L) {σ : ℕ → ℕ} {b vL : ℕ} {i j : Ex} (hL : σ vL = L) (hxV : σ b ≤ V)
    (hi : Bdd V σ A i) (hj : Bdd V σ A j) (hi' : eval σ A i < K) (hj' : eval σ A j < K) :
    Bdd V σ A (blkKE b vL K i j) := by
  have hKi : K * eval σ A i + K ≤ K * K := by
    have := Nat.mul_le_mul_left K (show eval σ A i + 1 ≤ K by omega); rw [mul_add, mul_one] at this; exact this
  have hjK : eval σ A j + K * eval σ A i ≤ K * K := by omega
  have hL1 : L * (eval σ A j + K * eval σ A i) ≤ L * (K * K) := Nat.mul_le_mul_left _ hjK
  have h2L : 2 ^ (L * (eval σ A j + K * eval σ A i)) ≤ V :=
    le_trans (Nat.pow_le_pow_right (by norm_num) hL1) R.hLK
  have hLV : σ vL ≤ V := by rw [hL]; exact R.LV
  have Bm : Bdd V σ A (.mul (.lit K) i) := B_mul (B_lit R.KV) hi (show K * eval σ A i ≤ V from le_trans (by omega) R.KK)
  have Ba : Bdd V σ A (.add j (.mul (.lit K) i)) := B_add hj Bm (le_trans hjK R.KK)
  have Bp : Bdd V σ A (.mul (.var vL) (.add j (.mul (.lit K) i))) := by
    refine B_mul (B_var hLV) Ba ?_
    show σ vL * (eval σ A j + K * eval σ A i) ≤ V
    rw [hL]; exact le_trans (le_trans hL1 Nat.lt_two_pow_self.le) R.hLK
  have B2 : Bdd V σ A (pow2 (b + 3) (.mul (.var vL) (.add j (.mul (.lit K) i)))) := by
    refine B_pow2 Bp R.two ?_
    show 2 ^ (σ vL * (eval σ A j + K * eval σ A i)) ≤ V
    rw [hL]; exact h2L
  have B3 : Bdd V σ A (pow2 (b + 3) (.var vL)) := by
    refine B_pow2 (B_var hLV) R.two ?_
    show 2 ^ σ vL ≤ V
    rw [hL]
    exact le_trans (Nat.pow_le_pow_right (by norm_num) (Nat.le_mul_of_pos_right _ (Nat.mul_pos R.hK R.hK))) R.hLK
  exact B_mod (B_div (B_var hxV) B2) B3

/-- **The brute force's values.** -/
theorem brute_bdd (R : BruteReq V m K L) {BT b vm vL vγ vΘ : ℕ} {σ₀ : ℕ → ℕ} {TE : Ex}
    (hT : TBdd V BT σ₀ A vγ vΘ TE K) (hσm : σ₀ vm = m) (hσL : σ₀ vL = L) (hvm : vm < BT)
    (hγ : BT ≤ vγ) (hΘ : BT ≤ vΘ) (hγΘ : vγ ≠ vΘ) (hLγ : vL ≠ vγ) (hBT : BT ≤ b) (hL : vL < b) (hγb : vγ < b)
    (_hΘb : vΘ < b) {σ : ℕ → ℕ} (hσ : Ag b σ₀ σ) : Bdd V σ A (bruteE b vm vL vγ vΘ K TE) := by
  have hmσ : σ vm = m := by rw [hσ _ (by omega), hσm]
  have hLσ : σ vL = L := by rw [hσ _ hL, hσL]
  have hm0 : 0 < m := by have := R.hm; omega
  have hV1 : 1 ≤ V := by have := R.two; omega
  have hKV := R.KV
  unfold bruteE
  refine B_zsum (by rw [hmσ]; exact hm0) (by rw [hmσ]; exact R.mV) (B_pow2 (B_mul (B_var (by rw [hLσ]; exact R.LV))
    (B_lit R.KK) ?_) R.two ?_) fun x hx => ?_
  · show σ vL * (K * K) ≤ V
    rw [hLσ]; exact le_trans Nat.lt_two_pow_self.le R.hLK
  · show 2 ^ (σ vL * (K * K)) ≤ V
    rw [hLσ]; exact R.hLK
  replace hx : x < 2 ^ (L * (K * K)) := by
    rw [eval_pow2] at hx; simpa only [Ex.eval, hLσ] using hx
  have hxV : x ≤ V := le_trans hx.le R.hLK
  set σ1 := Function.update σ b x
  have m1 : σ1 vm = m := by simp only [σ1]; upd; exact hmσ
  have l1 : σ1 vL = L := by simp only [σ1]; upd; exact hLσ
  have x1 : σ1 b = x := by simp [σ1]
  have hm1 : 1 < σ1 vm := by rw [m1]; exact R.hm
  refine B_zmul ?_ ?_ (by rw [m1]; exact R.mV) ?_
  · refine B_zprod (by omega) (by rw [m1]; exact R.mV) hV1 (B_lit hKV) fun γ hγK => ?_
    replace hγK : γ < K := hγK
    set σ2 := Function.update σ1 (b + 1) γ
    have l2 : σ2 vL = L := by simp only [σ2]; upd; exact l1
    have x2 : σ2 b = x := by simp only [σ2]; upd; exact x1
    have g2 : σ2 (b + 1) = γ := by simp [σ2]
    refine B_ifEq (blkKE_bdd R l2 (by rw [x2]; exact hxV) (B_var (by rw [g2]; omega))
      (B_var (by rw [g2]; omega)) (by show σ2 (b + 1) < K; rw [g2]; exact hγK)
      (by show σ2 (b + 1) < K; rw [g2]; exact hγK)) (B_lit (Nat.zero_le _)) ?_ (B_lit (Nat.zero_le _))
    refine B_lett (B_var (by rw [g2]; omega)) ?_
    set σ3 := Function.update σ2 vγ (eval σ2 A (.var (b + 1)))
    have e3 : eval σ2 A (.var (b + 1)) = γ := g2
    have l3 : σ3 vL = L := by simp only [σ3]; rw [Function.update_of_ne hLγ]; exact l2
    have x3 : σ3 b = x := by simp only [σ3]; rw [Function.update_of_ne (by omega)]; exact x2
    have g3 : σ3 (b + 1) = γ := by simp only [σ3]; rw [Function.update_of_ne (by omega)]; exact g2
    have hKγ : K * γ ≤ K * K := Nat.mul_le_mul_left _ hγK.le
    have hp : L * (K * γ) ≤ L * (K * K) := Nat.mul_le_mul_left _ hKγ
    refine B_lett (B_div (B_var (by rw [x3]; exact hxV)) (B_pow2 (B_mul (B_var (by rw [l3]; exact R.LV))
      (B_mul (B_lit hKV) (B_var (by rw [g3]; omega)) ?_) ?_) R.two ?_)) ?_
    · show K * σ3 (b + 1) ≤ V
      rw [g3]; exact le_trans hKγ R.KK
    · show σ3 vL * (K * σ3 (b + 1)) ≤ V
      rw [l3, g3]; exact le_trans (le_trans hp Nat.lt_two_pow_self.le) R.hLK
    · show 2 ^ (σ3 vL * (K * σ3 (b + 1))) ≤ V
      rw [l3, g3]; exact le_trans (Nat.pow_le_pow_right (by norm_num) hp) R.hLK
    · have a4 : Ag BT σ₀ (Function.update σ3 vΘ (eval σ3 A (.div (.var b) (pow2 (b + 3) (.mul (.var vL)
          (.mul (.lit K) (.var (b + 1)))))))) :=
        ((((hσ.mono hBT).upd (by omega) x).upd (by omega) γ).upd hγ _).upd hΘ _
      refine hT _ a4 ?_ ?_
      · rw [Function.update_of_ne hγΘ]; simp only [σ3, Function.update_self, e3]; exact hγK
      · rw [Function.update_self]
        show σ3 b / _ ≤ V
        rw [x3]; exact le_trans (Nat.div_le_self _ _) hxV
  · refine B_zprod (by omega) (by rw [m1]; exact R.mV) hV1 (B_lit hKV) fun γ hγK => ?_
    replace hγK : γ < K := hγK
    have m2 : Function.update σ1 (b + 1) γ vm = m := by upd; exact m1
    refine B_zprod (by rw [m2]; exact hm0) (by rw [m2]; exact R.mV) hV1 (B_lit hKV) fun γ' hγ' => ?_
    replace hγ' : γ' < K := hγ'
    set σ2 := Function.update (Function.update σ1 (b + 1) γ) (b + 2) γ'
    have l2 : σ2 vL = L := by simp only [σ2]; upd; exact l1
    have x2 : σ2 b = x := by simp only [σ2]; upd; exact x1
    have g1 : σ2 (b + 1) = γ := by simp only [σ2]; upd
    have g2 : σ2 (b + 2) = γ' := by simp only [σ2]; upd
    have Bi : Bdd V σ2 A (.var (b + 1)) := B_var (by rw [g1]; omega)
    have Bj : Bdd V σ2 A (.var (b + 2)) := B_var (by rw [g2]; omega)
    have ei : eval σ2 A (.var (b + 1)) < K := by show σ2 (b + 1) < K; rw [g1]; exact hγK
    have ej : eval σ2 A (.var (b + 2)) < K := by show σ2 (b + 2) < K; rw [g2]; exact hγ'
    have xV : σ2 b ≤ V := by rw [x2]; exact hxV
    exact B_ifLt Bi Bj (fun _ => B_ifEq (blkKE_bdd R l2 xV Bi Bj ei ej) (blkKE_bdd R l2 xV Bj Bi ej ei)
      (B_lit hV1) (B_lit (Nat.zero_le _))) fun _ => B_lit hV1
  · exact le_trans (Nat.mul_le_mul (lt_zprod hm1).le (lt_zprod hm1).le) (by rw [m1]; exact R.mm)

end Brute

/-! ### One level -/

/-- What one level (grid side `G`, `K` groups, width `λ`) needs of `V`. -/
structure LevelReq (V m K G lam : ℕ) : Prop where
  dec : DecV V m lam
  hS : 2 ^ (lam * (G * (G * G))) ≤ V
  hW : 2 ^ (3 * (lam * (G * G))) ≤ V
  hC : (tB lam + 1) ^ (G * G * (G * G)) ≤ V
  hg4 : G * G * (G * G) ≤ V
  hKg : K ^ G ≤ V
  hKG : K * G ≤ V
  hg1 : 2 * G + 1 ≤ V
  hgrp : 2 ^ (lam * (G * (G * G)) * (2 * G / K)) ≤ V
  hLK : 2 ^ (Lnext K G lam * K) ≤ V
  htot : G * (G ^ 3 * lam) ≤ V
  hUE : G * (G * (G ^ 2 * lam)) + 1 ≤ V
  hLn : (K + 1) * ((12 * G ^ 3 + 11 * G ^ 4 + 24 * G ^ 4 + G * G ^ 3 + K ^ 3 + 12) * (lam + 1)) ≤ V
  hmult : (tB lam + 1) * (G * G * (G * G)) + 2 ≤ V

theorem Net.total_le_fits {R : Type*} [CommRing R] {g : ℕ} (N : Net R g) {P : ℕ} (h : N.Fits P) :
    N.total ≤ g * P := by
  unfold Net.total
  calc ∑ a, ∑ b, N.cc a b ≤ ∑ _a : Fin g, P := sum_le_sum fun a _ => h a
    _ = g * P := by simp

theorem nsum_bdd_le {V : ℕ} {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ} {x : ℕ} {n b : Ex} {c : ℕ} (hn : Bdd V σ A n)
    (hb : ∀ j < eval σ A n, Bdd V (Function.update σ x j) A b ∧ eval (Function.update σ x j) A b ≤ c)
    (hV : eval σ A n * c ≤ V) : Bdd V σ A (nsum x n b) ∧ eval σ A (nsum x n b) ≤ eval σ A n * c :=
  ⟨B_nsum' hn hb hV, by rw [eval_nsum]; exact Ex.sum_le_card_mul fun j hj => (hb j (mem_range.mp (by simpa using hj))).2⟩

section Level

variable {V m BT lam : ℕ} {P : LP} {σ₀ : ℕ → ℕ} {A : ℕ → ℕ → ℕ}

theorem UE_bdd {B : ℕ} {N : Net (ZMod m) P.G} {κ : Coding N} (tr : Bool)
    (h : NRep m P.vm B σ₀ A (NVars.std (P.b + 6)) (GridEx.nex (LevelEx.gp P) tr) N κ)
    (hE : NBdd V B σ₀ A (NVars.std (P.b + 6)) (GridEx.nex (LevelEx.gp P) tr) P.G)
    (hc : ∀ a b, N.c a b ≤ P.G ^ 2 * lam) (hB : B ≤ P.b + 6) (hg : 0 < P.G) (hGV : P.G ≤ V)
    (hU : P.G * (P.G * (P.G ^ 2 * lam)) ≤ V) {σ : ℕ → ℕ} (hσ : Ag B σ₀ σ) :
    Bdd V σ A (LevelEx.UE P tr) ∧ eval σ A (LevelEx.UE P tr) ≤ P.G * (P.G * (P.G ^ 2 * lam)) := by
  have hU1 : P.G * (P.G ^ 2 * lam) ≤ V := le_trans (Nat.le_mul_of_pos_left _ hg) hU
  unfold LevelEx.UE
  refine nsum_bdd_le (B_lit hGV) (fun a ha => ?_) hU
  replace ha : a < P.G := ha
  refine nsum_bdd_le (B_lit hGV) (fun a' ha' => ?_) hU1
  replace ha' : a' < P.G := ha'
  set σ2 := Function.update (Function.update σ (P.b + 6) a) (P.b + 7) a'
  have e6 : σ2 (P.b + 6) = a := by simp only [σ2]; upd
  have e7 : σ2 (P.b + 7) = a' := by simp only [σ2]; upd
  have a2 : Ag B σ₀ σ2 := (hσ.upd (by omega) a).upd (by omega) a'
  refine ⟨B_ifLt (B_var (by rw [e6]; omega)) (B_var (by rw [e7]; omega)) (fun hlt => hE.c σ2 a2 hlt
    (by show σ2 (P.b + 6 + 1) < P.G; rw [show P.b + 6 + 1 = P.b + 7 by omega, e7]; exact ha'))
    (fun _ => B_lit (Nat.zero_le _)), ?_⟩
  rw [eval_ifLt']
  split_ifs with hlt
  · exact le_trans (le_of_eq (h.c σ2 a2 ⟨a, ha⟩ ⟨a', ha'⟩ (by show a < a'; simpa [Ex.eval, e6, e7] using hlt) e6
      (by show σ2 (P.b + 6 + 1) = a'; rw [show P.b + 6 + 1 = P.b + 7 by omega, e7]))) (hc _ _)
  · exact Nat.zero_le _

/-- The grid requirements of a level. -/
theorem LevelReq.grid {K G cc : ℕ} (R : LevelReq V m K G lam) (hcc : cc ≤ V) (P : GP) (hG : P.g = G) :
    GridBddHyp V m lam cc P where
  dec := R.dec
  hS := by rw [hG]; exact R.hS
  hW := by rw [hG]; exact R.hW
  hC := by rw [hG]; exact R.hC
  hg4 := by rw [hG]; exact R.hg4
  hcc := hcc

theorem two_pow_le_of {a b V : ℕ} (hab : a ≤ b) (h : 2 ^ b ≤ V) : 2 ^ a ≤ V :=
  le_trans (Nat.pow_le_pow_right (by norm_num) hab) h

/-- **Value bounds of the next table.** -/
theorem nextTE_bdd {Tab : Clique (ZMod m) (P.G * P.G) lam} (H : LevelHyp m BT σ₀ A P lam Tab)
    (hT : TBdd V BT σ₀ A P.vγ P.vΘ P.TE (P.G * P.G)) (R : LevelReq V m P.K P.G lam) {cc : ℕ}
    (hcc : cc < (tB lam + 1) ^ (P.G * P.G * (P.G * P.G)))
    {σ₁ : ℕ → ℕ} (h1 : Ag P.b σ₀ σ₁) (hc : σ₁ P.b = cc) (hL : σ₁ (P.b + 1) = Lnext P.K P.G lam)
    (hr : σ₁ (P.b + 4) = firstGood (okG (rowNet (toGrid Tab) (restrictC ((phiEquiv P.G (tB lam)).symm ⟨cc, hcc⟩)))
      P.K (Lnext P.K P.G lam) (by have := H.hK; omega)) (P.K ^ P.G) (P.K ^ P.G))
    (hcl : σ₁ (P.b + 5) = firstGood (okG (colNet (toGrid Tab) (restrictC ((phiEquiv P.G (tB lam)).symm ⟨cc, hcc⟩)))
      P.K (Lnext P.K P.G lam) (by have := H.hK; omega)) (P.K ^ P.G) (P.K ^ P.G)) :
    TBdd V (P.b + 6) σ₁ A (P.b + 62) (P.b + 63) (LevelEx.nextTE P) P.K := by
  have Hg := LevelEx.gridHyp H h1 hc
  have hK0 : 0 < P.K := by have := H.hK; omega
  have hg : 0 < P.G := Hg.hg
  have hvm : P.vm < P.b + 6 := by have := H.hvm; have := H.hBT; omega
  have GH := R.grid (le_trans hcc.le R.hC) (LevelEx.gp P) rfl
  obtain ⟨hGG, -, -, -, -, -, hGV⟩ := GH.facts hg
  have hT' : TBdd V BT σ₁ A P.vγ P.vΘ P.TE (P.G * P.G) := hT.congr (h1.mono H.hBT)
  have nb : ∀ tr, NBdd V (P.b + 6) σ₁ A (NVars.std (P.b + 6)) (GridEx.nex (LevelEx.gp P) tr) P.G := fun tr =>
    (GridEx.grid_bdd GH Hg hT' tr).mono (show P.b + 2 ≤ P.b + 6 by omega)
  set ι := restrictC ((phiEquiv P.G (tB lam)).symm ⟨cc, hcc⟩)
  have hr' : NRep m P.vm (P.b + 6) σ₁ A (NVars.std (P.b + 6)) (GridEx.nex (LevelEx.gp P) false)
      (rowNet (toGrid Tab) ι) (rowCoding _ _) :=
    (GridEx.row_rep Hg hcc).mono (show P.b + 2 ≤ P.b + 6 by omega)
  have hc' : NRep m P.vm (P.b + 6) σ₁ A (NVars.std (P.b + 6)) (GridEx.nex (LevelEx.gp P) true)
      (colNet (toGrid Tab) ι) (colCoding _ _) :=
    (GridEx.col_rep Hg hcc).mono (show P.b + 2 ≤ P.b + 6 by omega)
  have hUE' : P.G * (P.G * (P.G ^ 2 * lam)) ≤ V := by have := R.hUE; omega
  have hxV : ∀ x, x < P.K ^ P.G → x ≤ V := fun x hx => le_trans hx.le R.hKg
  have hLK1 : 2 ^ Lnext P.K P.G lam ≤ V := two_pow_le_of (Nat.le_mul_of_pos_right _ hK0) R.hLK
  have hGl : P.G ^ 2 * lam ≤ lam * (P.G * (P.G * P.G)) := by
    have : P.G * P.G ≤ P.G * (P.G * P.G) := Nat.le_mul_of_pos_left _ hg
    calc P.G ^ 2 * lam = lam * (P.G * P.G) := by ring
      _ ≤ lam * (P.G * (P.G * P.G)) := Nat.mul_le_mul_left _ this
  intro σ hσ hγ hQ
  obtain ⟨Br, -⟩ := UE_bdd false hr' (nb false) (rowNet_c_le (toGrid Tab) ι) le_rfl hg hGV hUE' hσ
  obtain ⟨Bc, vc⟩ := UE_bdd true hc' (nb true) (colNet_c_le (toGrid Tab) ι) le_rfl hg hGV hUE' hσ
  have er := LevelEx.eval_UE false hr' le_rfl hσ
  have ec := LevelEx.eval_UE true hc' le_rfl hσ
  unfold LevelEx.nextTE
  have B1 : Bdd V σ A (.lit 1) := B_lit (by have := R.hUE; omega)
  have hadd : eval σ A (LevelEx.UE P true) + eval σ A (.lit 1) ≤ V := by
    show eval σ A (LevelEx.UE P true) + 1 ≤ V
    have := R.hUE; omega
  refine B_ifLt Br (B_add Bc B1 hadd) (fun hlt => ?_) (fun hge => ?_)
  · replace hlt : eval σ A (LevelEx.UE P false) < eval σ A (LevelEx.UE P true) + 1 := hlt
    rw [er, ec] at hlt
    have htot : (rowNet (toGrid Tab) ι).total ≤ (colNet (toGrid Tab) ι).total := by
      rw [Net.total_eq, Net.total_eq]; omega
    have hU : (rowNet (toGrid Tab) ι).total ≤ Umax P.G lam := total_le_Umax (toGrid Tab) ι (min_eq_left htot).symm
    obtain ⟨x, hx, hok⟩ := good_exists (rowNet (toGrid Tab) ι) _ _ (rowNet_fits (toGrid Tab) ι) hU H.hK H.hG
    have hsp := firstGood_spec (okG (rowNet (toGrid Tab) ι) P.K (Lnext P.K P.G lam) hK0) (le_refl (P.K ^ P.G))
      ⟨x, hx, hok⟩
    refine GroupEx.tab_bdd (S := LevelEx.gs P false) hK0 hg H.hm hr' (nb false) hvm
      (show P.b + 4 < P.b + 6 by omega) (show P.b + 1 < P.b + 6 by omega) le_rfl hr hL (hxV _ hsp.1) R.hKg hGG
      R.dec.hmm (fun γ => ?_) (fun γ γ' hlt => two_pow_le_of (hsp.2.2 γ γ' hlt) hLK1)
      (fun a b hab _ => two_pow_le_of ((rowNet_c_le (toGrid Tab) ι a b).trans hGl) R.hS) R.hLK σ hσ hγ hQ
    refine le_trans (coarsen_s_le_unif _ _ γ (lam * (P.G * (P.G * P.G))) (2 * P.G / P.K) (fun _ => le_rfl) ?_) R.hgrp
    rw [Nat.le_div_iff_mul_le hK0, mul_comm]
    exact hsp.2.1 γ
  · replace hge : ¬ eval σ A (LevelEx.UE P false) < eval σ A (LevelEx.UE P true) + 1 := hge
    rw [er, ec] at hge
    have htot : (colNet (toGrid Tab) ι).total ≤ (rowNet (toGrid Tab) ι).total := by
      rw [Net.total_eq, Net.total_eq]; omega
    have hU : (colNet (toGrid Tab) ι).total ≤ Umax P.G lam := total_le_Umax (toGrid Tab) ι (min_eq_right htot).symm
    obtain ⟨x, hx, hok⟩ := good_exists (colNet (toGrid Tab) ι) _ _ (colNet_fits (toGrid Tab) ι) hU H.hK H.hG
    have hsp := firstGood_spec (okG (colNet (toGrid Tab) ι) P.K (Lnext P.K P.G lam) hK0) (le_refl (P.K ^ P.G))
      ⟨x, hx, hok⟩
    refine GroupEx.tab_bdd (S := LevelEx.gs P true) hK0 hg H.hm hc' (nb true) hvm
      (show P.b + 5 < P.b + 6 by omega) (show P.b + 1 < P.b + 6 by omega) le_rfl hcl hL (hxV _ hsp.1) R.hKg hGG
      R.dec.hmm (fun γ => ?_) (fun γ γ' hlt => two_pow_le_of (hsp.2.2 γ γ' hlt) hLK1)
      (fun a b hab _ => two_pow_le_of ((colNet_c_le (toGrid Tab) ι a b).trans hGl) R.hS) R.hLK σ hσ hγ hQ
    refine le_trans (coarsen_s_le_unif _ _ γ (lam * (P.G * (P.G * P.G))) (2 * P.G / P.K) (fun _ => le_rfl) ?_) R.hgrp
    rw [Nat.le_div_iff_mul_le hK0, mul_comm]
    exact hsp.2.1 γ

theorem LnE_bdd
    (hLn : (P.K + 1) * ((12 * P.G ^ 3 + 11 * P.G ^ 4 + 24 * P.G ^ 4 + P.G * P.G ^ 3 + P.K ^ 3 + 12) * (lam + 1)) ≤ V)
    {σ : ℕ → ℕ} (hl : σ P.vl = lam) : Bdd V σ A (LevelEx.LnE P) := by
  have hX := hLn
  set Q := 12 * P.G ^ 3 + 11 * P.G ^ 4 + 24 * P.G ^ 4 + P.G * P.G ^ 3 + P.K ^ 3 + 12 with hQdef
  have hQ : Q * (lam + 1) ≤ (P.K + 1) * (Q * (lam + 1)) := Nat.le_mul_of_pos_left _ (by omega)
  have hQ1 : Q ≤ Q * (lam + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have hl1 : ∀ c, c ≤ Q → c * lam ≤ Q * (lam + 1) := fun c hc => Nat.mul_le_mul hc (by omega)
  have hs2 : 12 * P.G ^ 3 * lam + 11 * P.G ^ 4 * lam + 24 * P.G ^ 4 ≤ Q * (lam + 1) := by
    have : 12 * P.G ^ 3 * lam + 11 * P.G ^ 4 * lam + 24 * P.G ^ 4 ≤
        (12 * P.G ^ 3 + 11 * P.G ^ 4 + 24 * P.G ^ 4) * (lam + 1) := by
      rw [show (12 * P.G ^ 3 + 11 * P.G ^ 4 + 24 * P.G ^ 4) * (lam + 1) = 12 * P.G ^ 3 * lam + 11 * P.G ^ 4 * lam +
        24 * P.G ^ 4 + (24 * P.G ^ 4 * lam + 12 * P.G ^ 3 + 11 * P.G ^ 4) by ring]
      exact Nat.le_add_right _ _
    exact le_trans this (Nat.mul_le_mul (by omega) le_rfl)
  have hK1 : P.K * ((12 * P.G ^ 3 * lam + 11 * P.G ^ 4 * lam + 24 * P.G ^ 4) / 12) ≤ P.K * (Q * (lam + 1)) :=
    Nat.mul_le_mul_left _ (le_trans (Nat.div_le_self _ _) hs2)
  have hlast : P.K * ((12 * P.G ^ 3 * lam + 11 * P.G ^ 4 * lam + 24 * P.G ^ 4) / 12) + P.G * P.G ^ 3 * lam ≤ V := by
    have := hl1 (P.G * P.G ^ 3) (by omega)
    refine le_trans ?_ hX
    rw [add_mul, one_mul]; omega
  have hKQ : P.K ≤ Q := by
    have : P.K ≤ P.K ^ 3 := Nat.le_self_pow (by norm_num) _
    omega
  have hV : ∀ c, c ≤ Q * (lam + 1) → c ≤ V := fun c hc => le_trans (le_trans hc hQ) hX
  unfold LevelEx.LnE
  refine B_div (B_add (B_mul (B_lit ?_) (B_div (B_add (B_add (B_mul (B_lit ?_) (B_var ?_) ?_)
    (B_mul (B_lit ?_) (B_var ?_) ?_) ?_) (B_lit ?_) ?_) (B_lit ?_)) ?_) (B_mul (B_lit ?_) (B_var ?_) ?_) ?_) (B_lit ?_)
  all_goals try simp only [Ex.eval, hl]
  all_goals first
    | exact hlast
    | exact le_trans hK1 (le_trans (Nat.mul_le_mul_right _ (Nat.le_succ _)) hX)
    | exact hV _ (le_trans hKQ hQ1)
    | exact hV _ (by omega)
    | exact hV _ (hl1 _ (by omega))
    | exact hV _ (le_trans (by omega) hs2)
    | exact hV _ (le_trans (Nat.le_mul_of_pos_left _ (by omega)) (Nat.mul_le_mul_left _ (Nat.le_succ _)))

end Level

/-! ### The chain -/

/-- What the chain from depth `d` (width `L`) needs of `V`. -/
def DeepReq (V m K0 : ℕ) : ℕ → ℕ → Prop
  | 0, L => BruteReq V m (Kb K0 0) L
  | d + 1, L => LevelReq V m (Kb K0 d) (Gs K0 d) L ∧ DeepReq V m K0 d (Lnext (Kb K0 d) (Gs K0 d) L)

/-- **Value bounds of the chain.** -/
theorem deep_bdd {V m : ℕ} {A : ℕ → ℕ → ℕ} (K0 : ℕ) (hK : 2 ≤ K0) (hm : 1 < m) :
    ∀ (d b BT vm vl vγ vΘ : ℕ) (TE : Ex) (L : ℕ) (T : Clique (ZMod m) (Kb K0 d) L) (σ₀ : ℕ → ℕ),
      TRep m BT σ₀ A vγ vΘ TE T → TBdd V BT σ₀ A vγ vΘ TE (Kb K0 d) → DeepReq V m K0 d L →
      σ₀ vm = m → σ₀ vl = L → vm < BT → BT ≤ vγ → BT ≤ vΘ → vγ ≠ vΘ → vl ≠ vγ →
      BT ≤ b → vl < b → vγ < b → vΘ < b → ∀ σ, Ag b σ₀ σ → Bdd V σ A (deepEx K0 d b vm vl vγ vΘ TE)
  | 0, b, BT, vm, vl, vγ, vΘ, TE, L, T, σ₀, _, hTB, hR, hσm, hσl, hvm, hγ, hΘ, hγΘ, hlγ, hBT, hl, hγb, hΘb, σ, hσ =>
      brute_bdd hR hTB hσm hσl hvm hγ hΘ hγΘ hlγ hBT hl hγb hΘb hσ
  | d + 1, b, BT, vm, vl, vγ, vΘ, TE, L, T, σ₀, hT, hTB, hR, hσm, hσl, hvm, hγ, hΘ, hγΘ, hlγ, hBT, hl, hγb, hΘb,
      σ, hσ => by
      have hmσ : σ vm = m := by rw [hσ _ (by omega), hσm]
      have hlσ : σ vl = L := by rw [hσ _ hl, hσl]
      set P : LP := ⟨b, vm, vl, vγ, vΘ, Kb K0 d, Gs K0 d, TE⟩
      have hPb : P.b = b := rfl
      have R : LevelReq V m P.K P.G L := hR.1
      have H : LevelHyp m BT σ A P L T :=
        { hm := hm, hK := Kb_ge K0 hK d, hG := rfl, rep := hT.congr (hσ.mono hBT), vm := hmσ, vl := hlσ,
          hvm := hvm, hγ := hγ, hΘ := hΘ, hγΘ := hγΘ, hlγ := hlγ, hBT := hBT, hl := hl, hγb := hγb, hΘb := hΘb }
      have hTB' : TBdd V BT σ A vγ vΘ TE (P.G * P.G) := hTB.congr (hσ.mono hBT)
      have hK0 : 0 < P.K := by have := H.hK; omega
      have hg : 0 < P.G := by show 0 < 3 * Kb K0 d ^ 8; have := H.hK; positivity
      have hmV : m ≤ V := R.dec.mV
      have GH0 := R.grid (cc := 0) (Nat.zero_le _) (LevelEx.gp P) rfl
      obtain ⟨hGG, -, -, h64, -, hl2, hGV⟩ := GH0.facts hg
      set N := (tB L + 1) ^ (Gs K0 d * Gs K0 d * (Gs K0 d * Gs K0 d))
      have hn : eval σ A (.prod (b + 1) (.lit (Gs K0 d * Gs K0 d * (Gs K0 d * Gs K0 d))) (.lit 0)
          (.add (tBE vl) (.lit 1))) = N := by
        simp only [Ex.eval, foldProd_zero]
        rw [show (fun i => eval (Function.update σ (b + 1) i) A (tBE vl) + 1) = fun _ => tB L + 1 from
          funext fun i => by rw [eval_tBE (by upd; exact hlσ)], pp_const]
      have htB : tB L + 1 ≤ V := by unfold tB; have := Nat.div_le_self (L + 2) 3; omega
      have hBn : Bdd V σ A (.prod (b + 1) (.lit (Gs K0 d * Gs K0 d * (Gs K0 d * Gs K0 d))) (.lit 0)
          (.add (tBE vl) (.lit 1))) := by
        refine B_nprodK (x := b + 1) (n := .lit (Gs K0 d * Gs K0 d * (Gs K0 d * Gs K0 d)))
          (b := .add (tBE vl) (.lit 1)) (c := tB L + 1) (B_lit R.hg4) (fun j _ => ⟨?_, ?_⟩) (by omega) R.hC
        · have hl' : Function.update σ (b + 1) j vl = L := by upd; exact hlσ
          refine B_add (B_div (B_add (B_var (by rw [hl']; omega)) (B_lit (by omega)) ?_) (B_lit (by omega)))
            (B_lit (by omega)) ?_
          · show Function.update σ (b + 1) j vl + 2 ≤ V; rw [hl']; exact hl2
          · show eval (Function.update σ (b + 1) j) A (tBE vl) + 1 ≤ V; rw [eval_tBE hl']; exact htB
        · show eval (Function.update σ (b + 1) j) A (tBE vl) + 1 = tB L + 1
          rw [eval_tBE (by upd; exact hlσ)]
      rw [deepEx]
      refine B_zsum (by rw [hmσ]; omega) (by rw [hmσ]; exact hmV) hBn fun c hc => ?_
      rw [hn] at hc
      set σ1 := Function.update σ b c
      have h1 : Ag b σ σ1 := (Ag.refl b σ).upd le_rfl c
      have hc1 : σ1 b = c := by simp [σ1]
      have hl1 : σ1 vl = L := by simp only [σ1]; upd; exact hlσ
      rw [LevelEx.pre]
      refine B_lett (LnE_bdd R.hLn hl1) ?_
      rw [LevelEx.eval_LnE hl1]
      set σ2 := Function.update σ1 (b + 1) (Lnext P.K P.G L)
      have a2 : Ag b σ σ2 := h1.upd (by omega) _
      have GH := R.grid (le_trans hc.le R.hC) (LevelEx.gp P) rfl
      have hL1 : Lnext P.K P.G L + 1 ≤ V :=
        le_trans Nat.lt_two_pow_self (two_pow_le_of (Nat.le_mul_of_pos_right _ hK0) R.hLK)
      have hcw : ∀ {N : Net (ZMod m) P.G}, N.Fits (P.G ^ 3 * L) → ∀ x < P.K ^ P.G, ∀ γ γ' : Fin P.K, γ < γ' →
          (N.coarsen (chiOf P.K P.G x hK0)).c γ γ' ≤ V := fun hf _ _ γ γ' h =>
        le_trans (Net.coarsen_c_le_total _ _ γ γ' h) (le_trans (Net.total_le_fits _ hf) R.htot)
      have hvm2 : P.vm < P.b + 2 := by have := H.hvm; have := H.hBT; omega
      have Hg2 := LevelEx.gridHyp H a2 (show σ2 P.b = c from by
        show Function.update σ1 (b + 1) _ b = c; rw [Function.update_of_ne (by omega)]; exact hc1)
      have hTB2 : TBdd V BT σ2 A vγ vΘ TE (P.G * P.G) := hTB'.congr (a2.mono hBT)
      have hr2 := GridEx.row_rep Hg2 hc
      have hE2 := GridEx.grid_bdd GH Hg2 hTB2 false
      refine B_lett (GroupEx.search_bdd (S := LevelEx.gs P false) hK0 hg hm hr2 hE2 hvm2
        (show P.b + 1 < P.b + 2 by omega) (show P.b + 2 ≤ P.b + 2 by omega) (show P.b + 2 ≤ P.b + 3 by omega)
        (show P.b + 2 ≤ P.b + 4 by omega) (show P.b + 2 ≠ P.b + 3 by omega) (show P.b + 2 ≠ P.b + 4 by omega)
        (show P.b + 3 ≠ P.b + 4 by omega) (show P.b + 2 < P.b + 6 by omega) (show P.b + 3 < P.b + 6 by omega)
        (show P.b + 4 < P.b + 6 by omega) (show σ2 (P.b + 1) = Lnext P.K P.G L from Function.update_self _ _ _) R.hKg hGG R.hKG R.hg1
        hL1 (hcw (rowNet_fits _ _)) (Ag.refl _ _)) ?_
      rw [GroupEx.eval_searchE (S := LevelEx.gs P false) hK0 hg hm hr2 hvm2 (show P.b + 1 < P.b + 2 by omega)
        (show P.b + 2 ≤ P.b + 2 by omega) (show P.b + 2 ≤ P.b + 3 by omega) (show P.b + 2 ≤ P.b + 4 by omega)
        (show P.b + 2 ≠ P.b + 3 by omega) (show P.b + 2 ≠ P.b + 4 by omega) (show P.b + 3 ≠ P.b + 4 by omega)
        (show P.b + 2 < P.b + 6 by omega) (show P.b + 3 < P.b + 6 by omega) (show P.b + 4 < P.b + 6 by omega)
        (show σ2 (P.b + 1) = Lnext P.K P.G L from Function.update_self _ _ _) (Ag.refl _ _)]
      set σ3 := Function.update σ2 (P.b + 4)
        (firstGood (okG (rowNet (toGrid T) (restrictC ((phiEquiv P.G (tB L)).symm ⟨c, hc⟩)))
          P.K (Lnext P.K P.G L) hK0) (P.K ^ P.G) (P.K ^ P.G))
      have a3 : Ag b σ σ3 := a2.upd (by omega) _
      have hc3b : σ3 P.b = c := by
        show Function.update σ2 (b + 4) _ b = c; rw [Function.update_of_ne (by omega)]
        show Function.update σ1 (b + 1) _ b = c; rw [Function.update_of_ne (by omega)]; exact hc1
      have Hg3 := LevelEx.gridHyp H a3 hc3b
      have hTB3 : TBdd V BT σ3 A vγ vΘ TE (P.G * P.G) := hTB'.congr (a3.mono hBT)
      have hc3 := GridEx.col_rep Hg3 hc
      have hE3 := GridEx.grid_bdd GH Hg3 hTB3 true
      have hL3 : σ3 (P.b + 1) = Lnext P.K P.G L := by
        show Function.update σ2 (b + 4) _ (b + 1) = _; rw [Function.update_of_ne (by omega)]
        exact Function.update_self _ _ _
      refine B_lett (GroupEx.search_bdd (S := LevelEx.gs P true) hK0 hg hm hc3 hE3 hvm2
        (show P.b + 1 < P.b + 2 by omega) (show P.b + 2 ≤ P.b + 2 by omega) (show P.b + 2 ≤ P.b + 3 by omega)
        (show P.b + 2 ≤ P.b + 5 by omega) (show P.b + 2 ≠ P.b + 3 by omega) (show P.b + 2 ≠ P.b + 5 by omega)
        (show P.b + 3 ≠ P.b + 5 by omega) (show P.b + 2 < P.b + 6 by omega) (show P.b + 3 < P.b + 6 by omega)
        (show P.b + 5 < P.b + 6 by omega) hL3 R.hKg hGG R.hKG R.hg1
        hL1 (hcw (colNet_fits _ _)) (Ag.refl _ _)) ?_
      show Bdd V (Function.update σ3 (P.b + 5) (eval σ3 A (GroupEx.searchE (LevelEx.gs P true) (P.b + 2) (P.b + 3))))
        A _
      rw [GroupEx.eval_searchE (S := LevelEx.gs P true) hK0 hg hm hc3 hvm2 (show P.b + 1 < P.b + 2 by omega)
        (show P.b + 2 ≤ P.b + 2 by omega) (show P.b + 2 ≤ P.b + 3 by omega) (show P.b + 2 ≤ P.b + 5 by omega)
        (show P.b + 2 ≠ P.b + 3 by omega) (show P.b + 2 ≠ P.b + 5 by omega) (show P.b + 3 ≠ P.b + 5 by omega)
        (show P.b + 2 < P.b + 6 by omega) (show P.b + 3 < P.b + 6 by omega) (show P.b + 5 < P.b + 6 by omega)
        hL3 (Ag.refl _ _)]
      set σ4 := Function.update σ3 (P.b + 5)
        (firstGood (okG (colNet (toGrid T) (restrictC ((phiEquiv P.G (tB L)).symm ⟨c, hc⟩)))
          P.K (Lnext P.K P.G L) hK0) (P.K ^ P.G) (P.K ^ P.G))
      have a4 : Ag b σ σ4 := a3.upd (by omega) _
      have e1 : σ4 (b + 1) = Lnext (Kb K0 d) (Gs K0 d) L := by
        show Function.update σ3 (b + 5) _ (b + 1) = _; rw [Function.update_of_ne (by omega)]; exact hL3
      have ec : σ4 b = c := by
        show Function.update σ3 (b + 5) _ b = c; rw [Function.update_of_ne (by omega)]; exact hc3b
      have er : σ4 (b + 4) = firstGood (okG (rowNet (toGrid T) (restrictC ((phiEquiv P.G (tB L)).symm ⟨c, hc⟩)))
          P.K (Lnext P.K P.G L) hK0) (P.K ^ P.G) (P.K ^ P.G) := by
        show Function.update σ3 (b + 5) _ (b + 4) = _; rw [Function.update_of_ne (by omega)]
        exact Function.update_self _ _ _
      have ecl : σ4 (b + 5) = firstGood (okG (colNet (toGrid T) (restrictC ((phiEquiv P.G (tB L)).symm ⟨c, hc⟩)))
          P.K (Lnext P.K P.G L) hK0) (P.K ^ P.G) (P.K ^ P.G) := Function.update_self _ _ _
      have hT4 := LevelEx.level_rep H hc a4 ec e1 er ecl
      have hTB4 := nextTE_bdd H hTB' R hc a4 ec e1 er ecl
      exact deep_bdd K0 hK hm d (b + 100) (b + 6) vm (b + 1) (b + 62) (b + 63) _ _ _ σ4 hT4 hTB4 hR.2
        (by rw [a4 vm (by omega), hmσ]) e1 (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega) σ4 (Ag.refl _ _)

end Factoring.Aux
