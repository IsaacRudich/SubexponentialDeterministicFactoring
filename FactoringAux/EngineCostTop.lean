/-
The cost of the counting expression: value bounds of the top (`topE`).

* `mul_nbdd`: the multiplication network's value bounds in `NBdd` form (per-field lemmas).
* `wMG`, `gsz_le_w`, `Wc`, **`cluster_s_le`**: a cluster's settings, counted with the true gate sizes (linear gates
  `≤ 2^(2 A fw)`, carry gates `≤ 2^(2 fw)`), are at most `2^Wc`, `Wc ≈ 10 A² fw / g`.
* `sE_bdd`, `L0E_bdd`, `nodesE_bdd`, `clχE_bdd`; `TopReq`; **`topE_bdd`**.

Not an audit surface.
-/
module

public import FactoringAux.EngineCostDeep
public import FactoringAux.EngineTop

@[expose] public section

namespace Factoring.Aux

open Finset Ex SB MulEx

/-! ### The multiplication network -/

theorem mul_nbdd {B s n k u vm vs V : ℕ} {σ₀ : ℕ → ℕ} {A : ℕ → ℕ → ℕ}
    (hs : σ₀ vs = s) (hn : σ₀ 0 = n) (hk : σ₀ 2 = k) (hkn : k ≤ n) (hnL : n ≤ pL s * pL s) (hvs : vs < B)
    (h2 : 2 < B) (hu : B ≤ u) (hA : ∀ a j, A a j ≤ 1) (hV : (2 ^ pL s) ^ (16 * pA s) ≤ V) :
    NBdd V B σ₀ A (NVars.std u) (mulNEx u vm vs) (mulNodes s) where
  sz σ hσ ha := B_szE hV ((hσ vs hvs).trans hs) (by omega) ha
  W σ hσ ha hz := by
    have h : σ vs = s := (hσ vs hvs).trans hs
    have h0 : σ 0 = n := (hσ 0 (by omega)).trans hn
    have h2' : σ 2 = k := (hσ 2 h2).trans hk
    exact B_sel hV h (by omega) ha (fun _ => B_faW hV h (by omega) (by omega) h0 h2' hkn hnL hA ha hz)
      (fun _ _ => V_ge hV (by norm_num)) (fun _ _ => V_ge hV (by norm_num)) (fun _ _ => V_ge hV (by norm_num))
      (fun h4 => B_cW hV h (by omega) (by omega) h0 h2' hkn hnL hA ha hz h4)
  c σ hσ hab hb := B_cE hV ((hσ vs hvs).trans hs) (by omega) (lt_trans hab hb) hb
  l σ hσ hab hb hz hq := B_lr hV ((hσ vs hvs).trans hs) (by omega) (by omega) (by omega) (lt_trans hab hb) hb
    (lt_trans hab hb) hb hz hq
  r σ hσ hab hb hz hq := B_lr hV ((hσ vs hvs).trans hs) (by omega) (by omega) (by omega) hb (lt_trans hab hb)
    (lt_trans hab hb) hb hz hq

/-! ### The clusters' sizes -/

/-- The bits of a gate. -/
def wMG (s : ℕ) : MG (pA s) → ℕ
  | .carry _ => 2 * fw s
  | _ => 2 * pA s * fw s

theorem gsz_le_w (s : ℕ) (i : MG (pA s)) : gsz s i ≤ 2 ^ wMG s i := by
  have hmain : ∀ i : MG (pA s), gsz s i ≤ 2 ^ (2 * pA s * fw s) := fun i => by
    have h1 := mulSz_le s (MG.enum (pA s) i : ℕ)
    have h2 := mulSz_fin s (MG.enum (pA s) i)
    rw [Equiv.symm_apply_apply] at h2
    exact h2 ▸ h1
  cases i with
  | carry j =>
      show pM s * 2 ^ fw s ≤ 2 ^ (2 * fw s)
      calc pM s * 2 ^ fw s ≤ 2 ^ fw s * 2 ^ fw s := Nat.mul_le_mul_right _ (pM_le_fw s)
        _ = 2 ^ (2 * fw s) := by rw [← pow_add]; ring_nf
  | faP r => exact hmain _
  | faQ r => exact hmain _
  | mid r => exact hmain _
  | ib r => exact hmain _

/-- The bits of a cluster. -/
def Wc (s g : ℕ) : ℕ := 8 * (pA s / g + 2) * pA s * fw s + 2 * (pA s * pA s / g + 2) * fw s

/-- **A cluster has at most `2^Wc` settings.** -/
theorem cluster_s_le (s m N k x g : ℕ) (hg : 0 < g) (γ : Fin g) :
    ((mulCoding s m N k x).coarsen (fun a => clMG s g hg ((MG.enum (pA s)).symm a))).s γ ≤ 2 ^ Wc s g := by
  refine le_trans (coarsen_s_le _ _ γ (fun a => wMG s ((MG.enum (pA s)).symm a)) fun a _ => ?_)
    (Nat.pow_le_pow_right (by norm_num) ?_)
  · exact (mulSz_fin s a).trans_le (gsz_le_w s _)
  · refine le_trans (le_of_eq (Fintype.sum_equiv (MG.enum (pA s)).symm _
      (fun i => if clMG s g hg i = γ then wMG s i else 0) fun _ => rfl)) ?_
    rw [sum_MG]
    simp only [clMG, wMG, Fin.ext_iff]
    have h1 := kind_sum_le (pA s) g (2 * pA s * fw s) hg γ
    have h4 := kind_sum_le (pA s * pA s) g (2 * fw s) hg γ
    unfold Wc
    nlinarith

/-! ### The parameter `s` -/

theorem sIter_le (n : ℕ) : ∀ j, 2 ^ (4 * iterF (sStep n) 0 j + 2) ≤ 16 * n + 4
  | 0 => by simp [iterF]
  | j + 1 => by
      have ih := sIter_le n j
      show 2 ^ (4 * sStep n j (iterF (sStep n) 0 j) + 2) ≤ 16 * n + 4
      generalize iterF (sStep n) 0 j = X at ih ⊢
      unfold sStep
      split_ifs with h
      · rw [show 4 * (X + 1) + 2 = (4 * X + 2) + 4 by ring, pow_add]; norm_num; omega
      · exact ih

theorem sE_bdd {V : ℕ} {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ} (hV : 16 * σ 0 + 4 ≤ V) : Bdd V σ A sE := by
  set n := σ 0
  have key : (fun j s => eval (Function.update (Function.update σ 13 j) 14 s) A
      (.ifLt (pow2 15 (.add (.mul (.lit 4) (.var 14)) (.lit 2))) (.var 0) (.add (.var 14) (.lit 1)) (.var 14))) =
      sStep n := by
    funext j s
    rw [eval_ifLt', eval_pow2]
    simp only [Ex.eval]
    have e14 : Function.update (Function.update σ 13 j) 14 s 14 = s := by simp
    have e0 : Function.update (Function.update σ 13 j) 14 s 0 = σ 0 := by simp
    simp only [e14, e0]
    rfl
  refine ⟨show σ 0 ≤ V by omega, show 0 ≤ V by omega, fun j _ => ?_⟩
  rw [key]
  change Bdd V (Function.update (Function.update σ 13 j) 14 (iterF (sStep n) 0 j)) A _
  have hs := sIter_le n j
  generalize iterF (sStep n) 0 j = X at hs ⊢
  set σ' := Function.update (Function.update σ 13 j) 14 X
  have e14 : σ' 14 = X := by simp [σ']
  have e0 : σ' 0 = n := by simp [σ', n]
  have hX : 4 * X + 2 < 2 ^ (4 * X + 2) := Nat.lt_two_pow_self
  have B14 : Bdd V σ' A (.var 14) := show σ' 14 ≤ V by rw [e14]; omega
  refine B_ifLt (B_pow2 (B_add (B_mul (B_lit (by omega)) B14 (by show 4 * σ' 14 ≤ V; rw [e14]; omega))
    (B_lit (by omega)) (by show 4 * σ' 14 + 2 ≤ V; rw [e14]; omega)) (by omega)
    (by show 2 ^ (4 * σ' 14 + 2) ≤ V; rw [e14]; omega)) (show σ' 0 ≤ V by rw [e0]; omega)
    (fun _ => B_add B14 (B_lit (by omega)) (by show σ' 14 + 1 ≤ V; rw [e14]; omega)) (fun _ => B14)

/-! ### Small expressions of the top -/

section Small

variable {V s : ℕ} {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ}

theorem nodesE_bdd (hV : (2 ^ pL s) ^ (16 * pA s) ≤ V) (h : σ 11 = s) : Bdd V σ A nodesE := by
  have BA : Bdd V σ A (AE 16 11) := B_AE hV h
  have eA : eval σ A (AE 16 11) = pA s := eval_AE h
  have hN : ∀ x, x ≤ mulNodes s → x ≤ V := fun x hx => PV hV (le_trans hx (nodes_P s)) (by norm_num)
  unfold nodesE
  refine B_add BA (B_add BA (B_add BA (B_add BA (B_mul BA BA ?_) ?_) ?_) ?_) ?_ <;>
    simp only [Ex.eval, eA] <;> exact hN _ (by unfold mulNodes; omega)

theorem clχE_bdd {g : ℕ} (hV : (2 ^ pL s) ^ (16 * pA s) ≤ V) (h : σ 11 = s) (h16 : σ 16 < mulNodes s)
    (hgN : g * mulNodes s ≤ V) (hgV : g ≤ V) : Bdd V σ A (clχE g) := by
  have BA : Bdd V σ A (AE 16 11) := B_AE hV h
  have eA : eval σ A (AE 16 11) = pA s := eval_AE h
  have B16 : Bdd V σ A (.var 16) := show σ 16 ≤ V from PV hV (le_trans h16.le (nodes_P s)) (by norm_num)
  have hm : ∀ x, x ≤ σ 16 → x * g ≤ V := fun x hx =>
    le_trans (Nat.mul_le_mul_right _ (le_trans hx h16.le)) (by rw [mul_comm]; exact hgN)
  have Bi : ∀ c, c ≤ 4 → Bdd V σ A (.div (.mul (.sub (.var 16) (kA 16 11 c)) (.lit g)) (AE 16 11)) := fun c hc =>
    B_div (B_mul (B_sub B16 (B_kA hV h hc)) (B_lit hgV) (by simp only [Ex.eval]; exact hm _ (Nat.sub_le _ _))) BA
  unfold clχE
  refine B_sel hV h (by norm_num) h16 (fun _ => B_div (B_mul B16 (B_lit hgV) (hm _ le_rfl)) BA)
    (fun _ _ => Bi 1 (by norm_num)) (fun _ _ => Bi 2 (by norm_num)) (fun _ _ => Bi 3 (by norm_num))
    (fun _ => B_div (B_mul (B_sub B16 (B_kA hV h (by norm_num))) (B_lit hgV)
      (by simp only [Ex.eval]; exact hm _ (Nat.sub_le _ _))) (B_mul BA BA ?_))
  simp only [eA]; exact PV hV (P_mul s (pA_P s) (pA_P s)) (by norm_num)

/-- The bound required for the top width's expression. -/
def L0V (K g s : ℕ) : ℕ := (K ^ 3 + 10 * K + 30 * g + 30) * (2 ^ pL s) ^ 7

theorem L0E_bdd {K g : ℕ} (hV : (2 ^ pL s) ^ (16 * pA s) ≤ V) (h : σ 11 = s) (hL0 : L0V K g s ≤ V) :
    Bdd V σ A (L0E K g) := by
  have BA : Bdd V σ A (AE 9 11) := B_AE hV h
  have eA : eval σ A (AE 9 11) = pA s := eval_AE h
  have Bf : Bdd V σ A (fwE 9 11) := B_fwE hV h
  have ef : eval σ A (fwE 9 11) = fw s := eval_fwE h
  set a := pA s
  set f := fw s
  set P := 2 ^ pL s
  have ha : a ≤ P := by have := pA_P s; simpa using this
  have hf : f ≤ P ^ 5 := fw_P s
  have h2a : 2 ≤ a := two_le_pA s
  have hP : 1 ≤ P := one_le_P s
  have hZ : a * a * f ≤ P ^ 7 := by
    calc a * a * f ≤ P * P * P ^ 5 := Nat.mul_le_mul (Nat.mul_le_mul ha ha) hf
      _ = P ^ 7 := by ring
  have hP7 : 1 ≤ P ^ 7 := Nat.one_le_pow _ _ hP
  have hY : ∀ x, x ≤ (K ^ 3 + 10 * K + 30 * g + 30) * P ^ 7 → x ≤ V := fun x hx => le_trans hx hL0
  have hv5 : a / g + 2 ≤ 2 * a := by have := Nat.div_le_self a g; omega
  have hv8 : 7 * (a / g + 2) * a * f ≤ 14 * P ^ 7 := by
    calc 7 * (a / g + 2) * a * f ≤ 7 * (2 * a) * a * f :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hv5))
      _ = 14 * (a * a * f) := by ring
      _ ≤ 14 * P ^ 7 := Nat.mul_le_mul_left _ hZ
  have haa : 2 ≤ a * a := by nlinarith
  have hv9 : a * a / g + 2 ≤ 2 * (a * a) := by have := Nat.div_le_self (a * a) g; omega
  have hv11 : 3 * (a * a / g + 2) * f ≤ 6 * P ^ 7 := by
    calc 3 * (a * a / g + 2) * f ≤ 3 * (2 * (a * a)) * f := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hv9)
      _ = 6 * (a * a * f) := by ring
      _ ≤ 6 * P ^ 7 := Nat.mul_le_mul_left _ hZ
  have hcl : 7 * (a / g + 2) * a * f + 3 * (a * a / g + 2) * f ≤ 20 * P ^ 7 := by omega
  have hgcl : g * (7 * (a / g + 2) * a * f + 3 * (a * a / g + 2) * f) ≤ 20 * (g * P ^ 7) := by
    calc _ ≤ g * (20 * P ^ 7) := Nat.mul_le_mul_left _ hcl
      _ = 20 * (g * P ^ 7) := by ring
  have hK10 : K * (10 * (a * a) * f) ≤ 10 * (K * P ^ 7) := by
    calc K * (10 * (a * a) * f) = 10 * (K * (a * a * f)) := by ring
      _ ≤ 10 * (K * P ^ 7) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hZ)
  have hexp : (K ^ 3 + 10 * K + 30 * g + 30) * P ^ 7 = K ^ 3 * P ^ 7 + 10 * (K * P ^ 7) + 30 * (g * P ^ 7) +
      30 * P ^ 7 := by ring
  have hK3 : K ^ 3 ≤ K ^ 3 * P ^ 7 := Nat.le_mul_of_pos_right _ hP7
  have hKP : K ≤ K * P ^ 7 := Nat.le_mul_of_pos_right _ hP7
  have hgP : g ≤ g * P ^ 7 := Nat.le_mul_of_pos_right _ hP7
  have haP : a ≤ P ^ 7 := le_trans ha (Nat.le_self_pow (by norm_num) _)
  have haaP : a * a ≤ P ^ 7 := le_trans (Nat.le_mul_of_pos_right _ (by unfold f fw; omega)) hZ
  have h7 : 7 * (a / g + 2) * a ≤ 14 * P ^ 7 :=
    le_trans (Nat.le_mul_of_pos_right _ (by unfold f fw; omega)) hv8
  have h3 : 3 * (a * a / g + 2) ≤ 6 * P ^ 7 :=
    le_trans (Nat.le_mul_of_pos_right _ (by unfold f fw; omega)) hv11
  have h10 : 10 * (a * a) ≤ 10 * P ^ 7 := Nat.mul_le_mul_left _ haaP
  have h10f : 10 * (a * a) * f ≤ 10 * P ^ 7 := by
    calc 10 * (a * a) * f = 10 * (a * a * f) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ hZ
  have h75 : 7 * (a / g + 2) ≤ 14 * P ^ 7 := le_trans (Nat.le_mul_of_pos_right _ (by omega)) h7
  unfold L0E clPE
  refine B_div (B_add (B_mul (B_lit ?_) (B_mul (B_mul (B_lit ?_) (B_mul BA BA ?_) ?_) Bf ?_) ?_)
    (B_mul (B_lit ?_) (B_add (B_mul (B_mul (B_mul (B_lit ?_) (B_add (B_div BA (B_lit ?_)) (B_lit ?_) ?_) ?_) BA ?_)
      Bf ?_) (B_mul (B_mul (B_lit ?_) (B_add (B_div (B_mul BA BA ?_) (B_lit ?_)) (B_lit ?_) ?_) ?_) Bf ?_) ?_) ?_)
    ?_) (B_lit ?_)
  all_goals try simp only [Ex.eval, eA, ef]
  all_goals refine hY _ ?_
  all_goals rw [hexp]
  all_goals omega

end Small

/-! ### The top -/

theorem rowB_le (s : ℕ) (i : MG (pA s)) : rowB s i ≤ 3 * pA s * fw s := by
  have := two_le_pA s
  cases i <;> simp only [rowB] <;> nlinarith

theorem mulNet_fits (s : ℕ) (R : Type*) [CommRing R] (N k x : ℕ) :
    (mulNet s R N k x).Fits (3 * pA s * fw s) := fun a =>
  le_trans (mulNet_row_le s R N k x a) (rowB_le s _)

/-- What the top needs of `V` (besides the chain's `DeepReq`). -/
structure TopReq (V m K0 ℓ n : ℕ) : Prop where
  hm : 1 < m
  mul : (2 ^ pL (sOf n)) ^ (16 * pA (sOf n)) ≤ V
  mm : m * m ≤ V
  hn : 16 * n + 4 ≤ V
  hL0 : L0V (Kb K0 ℓ) (Gs K0 ℓ) (sOf n) ≤ V
  hKg : Kb K0 ℓ ^ Gs K0 ℓ ≤ V
  hKG : Kb K0 ℓ * Gs K0 ℓ ≤ V
  hgg : Gs K0 ℓ * Gs K0 ℓ ≤ V
  hg1 : 2 * Gs K0 ℓ + 1 ≤ V
  hgN : Gs K0 ℓ * mulNodes (sOf n) ≤ V
  hWc : 2 ^ Wc (sOf n) (Gs K0 ℓ) ≤ V
  hclP : 2 ^ clP (sOf n) (Gs K0 ℓ) ≤ V
  hgrp : 2 ^ (Wc (sOf n) (Gs K0 ℓ) * (2 * Gs K0 ℓ / Kb K0 ℓ)) ≤ V
  hLK : 2 ^ (Ltop (Kb K0 ℓ) (Gs K0 ℓ) (sOf n) * Kb K0 ℓ) ≤ V
  deep : DeepReq V m K0 ℓ (Ltop (Kb K0 ℓ) (Gs K0 ℓ) (sOf n))

/-- The clusters' value bounds. -/
theorem cluster_bdd {V m K0 ℓ n k : ℕ} {A : ℕ → ℕ → ℕ} (R : TopReq V m K0 ℓ n) (hA : ∀ a j, A a j ≤ 1)
    {σ₀ : ℕ → ℕ} (h10 : σ₀ 10 = m) (h11 : σ₀ 11 = sOf n) (hn : σ₀ 0 = n) (hk : σ₀ 2 = k) (hkn : k ≤ n)
    (hg : 0 < Gs K0 ℓ) :
    CoarsenBddHyp V m 13 σ₀ A (clPc (Gs K0 ℓ))
      (mulNet (sOf n) (ZMod m) (numCells (A 0) 1 n) k (numCells (A 1) k (n - k)))
      (mulCoding (sOf n) m (numCells (A 0) 1 n) k (numCells (A 1) k (n - k)))
      (fun a => clMG (sOf n) (Gs K0 ℓ) hg ((MG.enum (pA (sOf n))).symm a)) := by
  have hV := R.mul
  have hgV : Gs K0 ℓ ≤ V := le_trans (Nat.le_mul_of_pos_left _ hg) R.hgg
  exact
    { E := mul_nbdd (vm := 10) h11 hn hk hkn (sOf_spec n) (show 11 < 13 by norm_num) (by norm_num) (show 13 ≤ 16 by norm_num)
        hA hV
      gE := fun σ hσ => nodesE_bdd hV (by rw [hσ 11 (by norm_num), h11])
      χE := fun σ hσ hu => clχE_bdd hV (by rw [hσ 11 (by norm_num), h11]) hu R.hgN hgV
      mm := R.mm
      KV := hgV
      gg := PV hV (P_mul _ (nodes_P _) (nodes_P _)) (by norm_num)
      sz := fun γ => le_trans (cluster_s_le _ m _ k _ _ hg γ) R.hWc
      cw := fun γ γ' h => two_pow_le_of (Net.c_le_fits _ (clusterNet_fits _ (ZMod m) _ k _ _ hg) γ γ' h) R.hclP
      cin := fun a b h _ => two_pow_le_of (Net.c_le_fits _ (mulNet_fits _ (ZMod m) _ k _) a b h) (by
        refine le_trans ?_ hV
        rw [← pow_mul]
        refine Nat.pow_le_pow_right (by norm_num) ?_
        have h1 := two_le_pA (sOf n)
        have h2 : 1 ≤ pL (sOf n) := le_trans (by omega) (pA_le_pL (sOf n))
        unfold fw pm
        nlinarith) }

/-- **Value bounds of the top.** -/
theorem topE_bdd {V m K0 ℓ n k : ℕ} {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ} (hK : 2 ≤ K0) (R : TopReq V m K0 ℓ n)
    (hA : ∀ a j, A a j ≤ 1) (h10 : σ 10 = m) (hn : σ 0 = n) (hk : σ 2 = k) (hkn : k ≤ n) :
    Bdd V σ A (topE K0 ℓ) := by
  set K := Kb K0 ℓ
  set g := Gs K0 ℓ
  set s := sOf n
  set L := Ltop K g s
  have hm := R.hm
  have hK2 : 2 ≤ K := Kb_ge K0 hK ℓ
  have hK0 : 0 < K := by omega
  have hg : 0 < g := by show 0 < 3 * K ^ 8; positivity
  have hV := R.mul
  have hL1 : L + 1 ≤ V := le_trans Nat.lt_two_pow_self (two_pow_le_of (Nat.le_mul_of_pos_right _ hK0) R.hLK)
  have hLK1 : 2 ^ L ≤ V := two_pow_le_of (Nat.le_mul_of_pos_right _ hK0) R.hLK
  have htot : 10 * (pA s * pA s) * fw s ≤ V := by
    refine PV hV (a := 9) ?_ (by norm_num)
    have h10 : 10 ≤ (2 ^ pL s) ^ 2 := by have := four_le_P s; nlinarith
    calc 10 * (pA s * pA s) * fw s ≤ (2 ^ pL s) ^ 2 * ((2 ^ pL s) ^ 1 * (2 ^ pL s) ^ 1) * (2 ^ pL s) ^ 5 :=
          Nat.mul_le_mul (Nat.mul_le_mul h10 (Nat.mul_le_mul (pA_P s) (pA_P s))) (fw_P s)
      _ = (2 ^ pL s) ^ 9 := by ring
  rw [topE]
  refine B_lett (sE_bdd (by rw [hn]; exact R.hn)) ?_
  rw [eval_sE, hn]
  set σ1 := Function.update σ 11 s
  have e11 : σ1 11 = s := by simp [σ1]
  refine B_lett (L0E_bdd hV e11 R.hL0) ?_
  rw [eval_L0E e11]
  set σ2 := Function.update σ1 12 L
  have H2 := clusterHyp (A := A) (σ₀ := σ2) hm hg (by simp [σ2, σ1, h10]) (by simp [σ2, σ1, s]) (by simp [σ2, σ1, hn])
    (by simp [σ2, σ1, hk]) hkn (sOf_spec n)
  have Hb2 := cluster_bdd R hA (σ₀ := σ2) (by simp [σ2, σ1, h10]) (by simp [σ2, σ1, s]) (by simp [σ2, σ1, hn])
    (by simp [σ2, σ1, hk]) hkn hg
  have hr2 := coarsen_rep H2 (show 10 < 13 by norm_num)
  have hE2 := coarsen_bdd H2 Hb2 (show 10 < 13 by norm_num)
  set CN := clusterNet s (ZMod m) (numCells (A 0) 1 n) k (numCells (A 1) k (n - k)) g hg
  have hcw : ∀ x < K ^ g, ∀ γ γ' : Fin K, γ < γ' → (CN.coarsen (chiOf K g x hK0)).c γ γ' ≤ V :=
    fun _ _ γ γ' h => le_trans (Net.coarsen_c_le_total _ _ γ γ' h)
      (le_trans (clusterNet_total_le s _ _ k _ g hg) htot)
  refine B_lett (GroupEx.search_bdd (S := gsTop K g) hK0 hg hm hr2 hE2 (show 10 < 13 by norm_num)
    (show 12 < 13 by norm_num) (show 13 ≤ 13 by norm_num) (show 13 ≤ 14 by norm_num) (show 13 ≤ 15 by norm_num)
    (show (13 : ℕ) ≠ 14 by norm_num) (show (13 : ℕ) ≠ 15 by norm_num) (show (14 : ℕ) ≠ 15 by norm_num)
    (show 13 < 26 by norm_num) (show 14 < 26 by norm_num) (show 15 < 26 by norm_num) (show σ2 12 = L by simp [σ2])
    R.hKg R.hgg R.hKG R.hg1 hL1 hcw (Ag.refl _ _)) ?_
  rw [GroupEx.eval_searchE (S := gsTop K g) (L := L) hK0 hg hm hr2 (show 10 < 13 by norm_num)
    (show 12 < 13 by norm_num) (show 13 ≤ 13 by norm_num) (show 13 ≤ 14 by norm_num) (show 13 ≤ 15 by norm_num)
    (show (13 : ℕ) ≠ 14 by norm_num) (show (13 : ℕ) ≠ 15 by norm_num) (show (14 : ℕ) ≠ 15 by norm_num)
    (show 13 < 26 by norm_num) (show 14 < 26 by norm_num) (show 15 < 26 by norm_num) (show σ2 12 = L by simp [σ2])
    (Ag.refl _ _)]
  set xf := firstGood (okG CN K L hK0) (K ^ g) (K ^ g)
  set σ3 := Function.update σ2 15 xf
  have H3 := clusterHyp (A := A) (σ₀ := σ3) hm hg (by simp [σ3, σ2, σ1, h10]) (by simp [σ3, σ2, σ1, s])
    (by simp [σ3, σ2, σ1, hn]) (by simp [σ3, σ2, σ1, hk]) hkn (sOf_spec n)
  have Hb3 := cluster_bdd R hA (σ₀ := σ3) (by simp [σ3, σ2, σ1, h10]) (by simp [σ3, σ2, σ1, s])
    (by simp [σ3, σ2, σ1, hn]) (by simp [σ3, σ2, σ1, hk]) hkn hg
  have hr3 := (coarsen_rep H3 (show 10 < 13 by norm_num)).mono (show 13 ≤ 16 by norm_num)
  have hE3 := (coarsen_bdd H3 Hb3 (show 10 < 13 by norm_num)).mono (show 13 ≤ 16 by norm_num)
  have hT := GroupEx.group_rep (S := gsTop K g) (x := xf) (L := L) hK0 hg hm hr3 (show 10 < 16 by norm_num)
    (show 15 < 16 by norm_num) (show 12 < 16 by norm_num) (show 16 ≤ 26 by norm_num) (show σ3 15 = xf by simp [σ3])
    (show σ3 12 = L by simp [σ3, σ2])
  obtain ⟨x0, hx0, hok⟩ := good_exists CN (clP s g) (10 * (pA s * pA s) * fw s)
    (clusterNet_fits s _ _ k _ g hg) (clusterNet_total_le s _ _ k _ g hg) hK2 rfl
  have hsp := firstGood_spec (okG CN K L hK0) (le_refl (K ^ g)) ⟨x0, hx0, hok⟩
  have hTB := GroupEx.tab_bdd (S := gsTop K g) (x := xf) (L := L) hK0 hg hm hr3 hE3 (show 10 < 16 by norm_num)
    (show 15 < 16 by norm_num) (show 12 < 16 by norm_num) (show 16 ≤ 26 by norm_num) (show σ3 15 = xf by simp [σ3])
    (show σ3 12 = L by simp [σ3, σ2]) (le_trans hsp.1.le R.hKg) R.hKg R.hgg R.mm (fun γ => ?_)
    (fun γ γ' h => two_pow_le_of (hsp.2.2 γ γ' h) hLK1)
    (fun a b h _ => two_pow_le_of (Net.c_le_fits _ (clusterNet_fits s (ZMod m) _ k _ g hg) a b h) R.hclP) R.hLK
  · exact deep_bdd K0 hK hm ℓ 100 16 10 12 82 83 _ L _ σ3 hT hTB R.deep (by simp [σ3, σ2, σ1, h10])
      (by simp [σ3, σ2]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) σ3 (Ag.refl _ _)
  · refine le_trans (coarsen_s_le_unif _ _ γ (Wc s g) (2 * g / K) (fun a => cluster_s_le s m _ k _ g hg a) ?_)
      R.hgrp
    rw [Nat.le_div_iff_mul_le hK0, mul_comm]
    exact hsp.2.1 γ

end Factoring.Aux
