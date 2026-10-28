/-
The cost of the counting expression: value bounds of `mainE`.

* `mlE_bdd`, `dmE_lt`, `dmE_bdd`, `c1E_bdd`; `MainReq` (what `V` must satisfy for an input length `n`);
  **`mainE_bdd`**, **`mainE_cost_le`**: `cost ≤ (64 (V+1)^3)^(24 ℓ + 84)`.

Not an audit surface.
-/
module

public import FactoringAux.EngineCostTop
public import FactoringAux.EngineDpMain
public import FactoringAux.EngineBitVB

@[expose] public section

namespace Factoring.Aux

open Finset Ex SB

variable {V : ℕ} {A : ℕ → ℕ → ℕ}

theorem tBE_bdd {σ : ℕ → ℕ} {vl L : ℕ} (hl : σ vl = L) (hL : L + 2 ≤ V) (h3 : 3 ≤ V) : Bdd V σ A (tBE vl) :=
  B_div (B_add (B_var (by rw [hl]; omega)) (B_lit (by omega)) (by show σ vl + 2 ≤ V; rw [hl]; exact hL)) (B_lit h3)

theorem LevelReq.small {m K G lam : ℕ} (R : LevelReq V m K G lam) : lam + 2 ≤ V ∧ 64 ≤ V :=
  ⟨(lam_facts R.dec.hD R.dec.h64).1, R.dec.h64⟩

/-- `mlE` along the chain. -/
theorem mlE_bdd {m K0 : ℕ} : ∀ (d vL b L : ℕ) (σ : ℕ → ℕ), DeepReq V m K0 d L → mlogN K0 d L ≤ V → vL < b →
    σ vL = L → Bdd V σ A (mlE K0 d vL b)
  | 0, _, _, _, _, _, _, _, _ => Nat.zero_le V
  | d + 1, vL, b, L, σ, hR, hM, hb, hl => by
      have R : LevelReq V m (Kb K0 d) (Gs K0 d) L := hR.1
      obtain ⟨hL2, h64⟩ := R.small
      have hG4 : 2 * Gs K0 d ^ 4 ≤ V := by
        have := R.hLn
        have h1 : 2 * Gs K0 d ^ 4 ≤ (12 * Gs K0 d ^ 3 + 11 * Gs K0 d ^ 4 + 24 * Gs K0 d ^ 4 + Gs K0 d * Gs K0 d ^ 3 +
            Kb K0 d ^ 3 + 12) * (L + 1) := le_trans (by omega) (Nat.le_mul_of_pos_right _ (by omega))
        exact le_trans h1 (le_trans (Nat.le_mul_of_pos_left _ (by omega)) this)
      have hval : eval σ A (mlE K0 (d + 1) vL b) = mlogN K0 (d + 1) L := eval_mlE K0 (d + 1) vL b L σ hb hl
      have hrec : eval (Function.update σ (b + 1) (eval σ A (LevelEx.LnE (lpOf K0 d 0 vL)))) A (mlE K0 d (b + 1) (b + 2))
          = mlogN K0 d (Lnext (Kb K0 d) (Gs K0 d) L) := by
        rw [LevelEx.eval_LnE hl]
        exact eval_mlE K0 d (b + 1) (b + 2) _ _ (by omega) (Function.update_self _ _ _)
      have hsum : mlogN K0 (d + 1) L = 2 * Gs K0 d ^ 4 * tB L + mlogN K0 d (Lnext (Kb K0 d) (Gs K0 d) L) := rfl
      unfold mlE
      refine B_add (B_mul (B_lit hG4) (tBE_bdd hl hL2 (by omega)) ?_) ?_ ?_
      · show 2 * Gs K0 d ^ 4 * eval σ A (tBE vL) ≤ V
        rw [eval_tBE hl]; omega
      · refine B_lett (LnE_bdd (P := lpOf K0 d 0 vL) R.hLn hl) ?_
        rw [LevelEx.eval_LnE hl]
        exact mlE_bdd d (b + 1) (b + 2) _ _ hR.2 (by show mlogN K0 d (Lnext (Kb K0 d) (Gs K0 d) L) ≤ V; omega)
          (by omega) (Function.update_self _ _ _)
      · show eval σ A (.mul (.lit (2 * Gs K0 d ^ 4)) (tBE vL)) +
          eval (Function.update σ (b + 1) (eval σ A (LevelEx.LnE (lpOf K0 d 0 vL)))) A (mlE K0 d (b + 1) (b + 2)) ≤ V
        rw [hrec]; simp only [Ex.eval]; rw [eval_tBE hl]; omega

theorem dmE_lt {K0 : ℕ} {σ : ℕ → ℕ} (d vL b vm : ℕ) (hm : 1 < σ vm) : eval σ A (dmE K0 d vL b vm) < σ vm := by
  cases d with
  | zero => exact hm
  | succ d => rw [dmE]; exact lt_zmul (by omega)

/-- `dmE` along the chain. -/
theorem dmE_bdd {m K0 : ℕ} (hm : 1 < m) (hmm : m * m ≤ V) : ∀ (d vL b vm L : ℕ) (σ : ℕ → ℕ), DeepReq V m K0 d L →
    σ vm = m → vL < b → vm < b → σ vL = L → Bdd V σ A (dmE K0 d vL b vm)
  | 0, _, _, _, _, _, _, _, _, _, _ => show 1 ≤ V by nlinarith
  | d + 1, vL, b, vm, L, σ, hR, hvm, hb, hvb, hl => by
      have R : LevelReq V m (Kb K0 d) (Gs K0 d) L := hR.1
      obtain ⟨hL2, h64⟩ := R.small
      have hmV : m ≤ V := R.dec.mV
      have hmult := R.hmult
      set G := Gs K0 d
      have hG4 : G * G * (G * G) = G ^ 4 := by ring
      have hm1 : 1 < σ vm := by rw [hvm]; exact hm
      have hvar : ∀ j, Function.update σ b j vm = m := fun j => by rw [Function.update_of_ne (by omega)]; exact hvm
      have hvar' : ∀ j, Function.update σ b j vL = L := fun j => by rw [Function.update_of_ne (by omega)]; exact hl
      have hmod : ∀ (j : ℕ) (e : Ex), Bdd V (Function.update σ b j) A e →
          Bdd V (Function.update σ b j) A (.mod e (.var vm)) := fun j e he =>
        B_mod he (B_var (by rw [hvar]; exact hmV))
      have hcard : (rects G).card ≤ G ^ 4 := rects_le G
      have hnr : nonRects G ≤ G ^ 4 := nonRects_le G
      have hX : G * G * (G * G) ≤ (tB L + 1) * (G * G * (G * G)) := Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
      have hXV : G * G * (G * G) ≤ V := by omega
      have hnrV : nonRects G ≤ V := le_trans hnr (by rw [← hG4]; exact hXV)
      have hcV : (rects G).card ≤ V := le_trans hcard (by rw [← hG4]; exact hXV)
      have htc : tB L * (rects G).card ≤ V := by
        have : tB L * (rects G).card ≤ (tB L + 1) * (G * G * (G * G)) :=
          Nat.mul_le_mul (Nat.le_succ _) (by rw [hG4]; exact hcard)
        omega
      have ht1 : tB L + 1 ≤ V := by unfold tB; have := Nat.div_le_self (L + 2) 3; omega
      have Bm : Bdd V σ A (multE G vL vm b) := by
        unfold multE
        refine B_zmul (B_zprod (by omega) (by rw [hvm]; exact hmV) (by omega)
          (B_lit hnrV) fun j _ => hmod j _ (B_add (tBE_bdd (hvar' j) hL2 (by omega))
            (B_lit (by omega)) ?_)) (B_zprod (by omega) (by rw [hvm]; exact hmV) (by omega)
              (B_mul (tBE_bdd hl hL2 (by omega)) (B_lit hcV) ?_)
              fun j _ => hmod j _ (B_lit (by omega))) (by rw [hvm]; exact hmV) ?_
        · show eval (Function.update σ b j) A (tBE vL) + 1 ≤ V
          rw [eval_tBE (hvar' j)]; exact ht1
        · show eval σ A (tBE vL) * (rects G).card ≤ V
          rw [eval_tBE hl]; exact htc
        · exact le_trans (Nat.mul_le_mul (lt_zprod hm1).le (lt_zprod hm1).le) (by rw [hvm]; exact hmm)
      rw [dmE]
      refine B_zmul Bm (B_lett (LnE_bdd (P := lpOf K0 d vm vL) R.hLn hl) ?_) (by rw [hvm]; exact hmV) ?_
      · rw [LevelEx.eval_LnE hl]
        exact dmE_bdd hm hmm d (b + 1) (b + 2) vm _ _ hR.2 (by rw [Function.update_of_ne (by omega)]; exact hvm)
          (by omega) (by omega) (Function.update_self _ _ _)
      · rw [eval_lett]
        have h1 : eval σ A (multE G vL vm b) < m := by rw [← hvm]; unfold multE; exact lt_zmul (by omega)
        have h2 := dmE_lt (K0 := K0) (A := A) (σ := Function.update σ (b + 1) (eval σ A (LevelEx.LnE (lpOf K0 d vm vL))))
          d (b + 1) (b + 2) vm (by rw [Function.update_of_ne (by omega)]; exact hm1)
        rw [Function.update_of_ne (by omega), hvm] at h2
        exact le_trans (Nat.mul_le_mul h1.le h2.le) hmm

theorem c1E_bdd {σ : ℕ → ℕ} (hA : ∀ a j, A a j ≤ 1) (hkn : σ 2 < σ 0) (hn : σ 0 ≤ V) : Bdd V σ A c1E := by
  have hV1 : 1 ≤ V := by omega
  unfold c1E
  refine B_ifLt (B_lit (Nat.zero_le _)) (B_var (by omega)) (fun _ => B_ifEq ?_ (B_lit (Nat.zero_le _)) (B_lit hV1)
    (B_lit (Nat.zero_le _))) fun _ => B_lit (Nat.zero_le _)
  refine B_nsum' (c := 1) (B_sub (B_var hn) (B_var (by omega))) (fun j hj => ⟨?_, ?_⟩) ?_
  · replace hj : j < σ 0 - σ 2 := hj
    have e8 : Function.update σ 8 j 8 = j := by simp
    have e0 : Function.update σ 8 j 0 = σ 0 := by simp
    have e2 : Function.update σ 8 j 2 = σ 2 := by simp
    exact B_xBit (B_var (by rw [e8]; omega)) (by rw [e2]; omega) (by rw [e0]; exact hn)
      (by show Function.update σ 8 j 8 + Function.update σ 8 j 2 ≤ V; rw [e8, e2]; omega) hA hV1
  · rw [eval_xBit]; cases Nat.testBit _ _ <;> simp
  · show (σ 0 - σ 2) * 1 ≤ V; omega

/-! ### The counting expression -/

/-- The modulus bound `M` of `mainE` at input length `n`. -/
def Mof (K0 ℓ n : ℕ) : ℕ := n + mlogN K0 ℓ (Ltop (Kb K0 ℓ) (Gs K0 ℓ) (sOf n)) + 4

/-- What `V` must satisfy at input length `n`. -/
structure MainReq (V K0 ℓ n : ℕ) : Prop where
  top : ∀ m, 2 ≤ m → m ≤ 2 * Mof K0 ℓ n + 1 → TopReq V m K0 ℓ n
  hM : 2 * Mof K0 ℓ n + 1 ≤ V

/-- **Value bounds of the counting expression.** -/
theorem mainE_bdd {K0 ℓ n : ℕ} (hK : 2 ≤ K0) (R : MainReq V K0 ℓ n) {σ : ℕ → ℕ} (hA : ∀ a j, A a j ≤ 1)
    (hn : σ 0 = n) (hkn : σ 2 < σ 0) : Bdd V σ A (mainE K0 ℓ) := by
  set L := Ltop (Kb K0 ℓ) (Gs K0 ℓ) (sOf n)
  have hMof : Mof K0 ℓ n = n + mlogN K0 ℓ L + 4 := rfl
  have R2 := R.top 2 le_rfl (by omega)
  have hM := R.hM
  have hnV : n ≤ V := by omega
  rw [mainE]
  refine B_lett (sE_bdd (by rw [hn]; exact R2.hn)) ?_
  rw [eval_sE, hn]
  set σ1 := Function.update σ 11 (sOf n)
  have e11 : σ1 11 = sOf n := by simp [σ1]
  refine B_lett (L0E_bdd R2.mul e11 R2.hL0) ?_
  rw [eval_L0E e11]
  set σ2 := Function.update σ1 12 L
  have e12 : σ2 12 = L := by simp [σ2]
  have e0 : σ2 0 = n := by simp [σ2, σ1, hn]
  have hml : mlogN K0 ℓ L ≤ V := by omega
  have hval : eval σ2 A (.add (.add (.var 0) (mlE K0 ℓ 12 30)) (.lit 4)) = Mof K0 ℓ n := by
    simp only [Ex.eval]; rw [eval_mlE K0 ℓ 12 30 L σ2 (by norm_num) e12, e0]; rfl
  refine B_lett (B_add (B_add (B_var (by rw [e0]; exact hnV)) (mlE_bdd ℓ 12 30 L σ2 R2.deep hml (by norm_num) e12)
    (by simp only [Ex.eval]; rw [eval_mlE K0 ℓ 12 30 L σ2 (by norm_num) e12, e0]; omega))
    (B_lit (by omega)) (by show eval σ2 A (.add (.add (.var 0) (mlE K0 ℓ 12 30)) (.lit 4)) ≤ V; rw [hval]; omega)) ?_
  rw [hval]
  set σ3 := Function.update σ2 9 (Mof K0 ℓ n)
  have e9 : σ3 9 = Mof K0 ℓ n := by simp [σ3]
  refine B_ifLt (B_lit (Nat.zero_le _)) ?_ (fun _ => B_lit (Nat.zero_le _)) fun _ => B_lit (by omega)
  refine B_nsum' (c := 1) (B_add (B_mul (B_lit (by omega)) (B_var (by rw [e9]; omega)) (by
    show 2 * σ3 9 ≤ V; rw [e9]; omega)) (B_lit (by omega)) (by show 2 * σ3 9 + 1 ≤ V; rw [e9]; omega))
    (fun m hm => ?_) (by show (2 * σ3 9 + 1) * 1 ≤ V; rw [e9]; omega)
  replace hm : m < 2 * Mof K0 ℓ n + 1 := by simpa [Ex.eval, e9] using hm
  set σm := Function.update σ3 10 m
  have f10 : σm 10 = m := by simp [σm]
  have f0 : σm 0 = n := by simp [σm, σ3, σ2, σ1, hn]
  have f2 : σm 2 = σ 2 := by simp [σm, σ3, σ2, σ1]
  have f12 : σm 12 = L := by simp [σm, σ3, σ2]
  refine ⟨B_ifLt (B_var (by rw [f10]; omega)) (B_lit (by omega)) (fun _ => B_lit (Nat.zero_le _)) fun h2 => ?_, ?_⟩
  · replace h2 : 2 ≤ m := by simp only [Ex.eval, f10] at h2; omega
    have Rm := R.top m h2 (by omega)
    have hmV : m ≤ V := le_trans (Nat.le_mul_of_pos_left _ (by omega)) Rm.mm
    refine B_ifEq (topE_bdd hK Rm hA f10 f0 f2 (by omega)) (B_zmul (dmE_bdd Rm.hm Rm.mm ℓ 12 30 10 L σm Rm.deep
      f10 (by norm_num) (by norm_num) f12) (c1E_bdd hA (by rw [f2, f0, ← hn]; exact hkn) (by rw [f0]; exact hnV))
      (by rw [f10]; exact hmV) ?_) (B_lit (Nat.zero_le _)) (B_lit (by omega))
    have h1 := dmE_lt (K0 := K0) (A := A) ℓ 12 30 10 (show 1 < σm 10 by rw [f10]; omega)
    have h2 : eval σm A c1E ≤ 1 := by
      unfold c1E; rw [eval_ifLt']; split_ifs
      · rw [eval_ifEq]; split_ifs <;> simp [Ex.eval]
      · simp [Ex.eval]
    rw [f10] at h1
    calc eval σm A (dmE K0 ℓ 12 30 10) * eval σm A c1E ≤ m * 1 := Nat.mul_le_mul h1.le h2
      _ ≤ V := by omega
  · rw [eval_ifLt']; split_ifs
    · simp [Ex.eval]
    · rw [eval_ifEq]; split_ifs <;> simp [Ex.eval]

/-- **The cost of the counting expression**, from its value bound. -/
theorem mainE_cost_le {K0 ℓ n k : ℕ} (hK : 2 ≤ K0) (R : MainReq V K0 ℓ n) (hkn : k < n) (hA : ∀ a j, A a j ≤ 1) :
    cost (envNK n k) A (mainE K0 ℓ) ≤ (64 * (V + 1) ^ 3) ^ (24 * ℓ + 84) := by
  have hB := mainE_bdd hK R hA (σ := envNK n k) (by simp [envNK]) (by simp [envNK]; omega)
  refine le_trans (cost_le_of_Bdd A _ _ hB) (Nat.pow_le_pow_right ?_ (mainE_dp K0 ℓ))
  have := Nat.one_le_pow 3 (V + 1) (by omega); omega

end Factoring.Aux
