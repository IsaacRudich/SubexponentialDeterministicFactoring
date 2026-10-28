/-
Value bounds of the written-out clique (`CliqueEx.tab`).

* **`clique_bdd`**: from `NBdd` of the network, `m·m ≤ V`, `2^(L·K) ≤ V` and bounds of `kE`, `LE`:
  `TBdd V B σ₀ A P.w (P.w + 1) (CliqueEx.tab P) K`.

Not an audit surface.
-/
module

public import FactoringAux.EngineBddBase

@[expose] public section

namespace Factoring.Aux

open Finset Ex SB CliqueEx

/-- **The written-out clique: every value is at most `V`.** -/
theorem clique_bdd {V m B K L : ℕ} {σ₀ : ℕ → ℕ} {A : ℕ → ℕ → ℕ} {P : KP} {N : Net (ZMod m) K} {κ : Coding N}
    (H : CliqueHyp m B σ₀ A P N κ L) (hE : NBdd V B σ₀ A (NVars.std P.u) P.E K)
    (hkE : ∀ σ, Ag B σ₀ σ → Bdd V σ A P.kE) (hLE : ∀ σ, Ag B σ₀ σ → Bdd V σ A P.LE)
    (hmm : m * m ≤ V) (hLK : 2 ^ (L * K) ≤ V) :
    TBdd V B σ₀ A P.w (P.w + 1) (CliqueEx.tab P) K := by
  intro σ hσ hγ hQ
  have hu := H.hu; have hw := H.hw; have hm := H.hm; have hvm := H.hvm
  have hmσ : σ P.vm = m := by rw [hσ _ hvm]; exact H.rep.hm
  have hmV : m ≤ V := le_trans (Nat.le_mul_of_pos_left m (by omega)) hmm
  have h2V : 2 ≤ V := by omega
  have hK1 : 1 ≤ K := by omega
  have hLKL : L ≤ L * K := Nat.le_mul_of_pos_right _ hK1
  have h2L : 2 ^ L ≤ V := le_trans (Nat.pow_le_pow_right (by norm_num) hLKL) hLK
  have hL1 : L + 1 ≤ V := le_trans (Nat.lt_two_pow_self (n := L)) h2L
  have hKV : K ≤ V := by have := le_of_B (hkE σ hσ); rwa [H.kE σ hσ] at this
  set γ : Fin K := ⟨σ P.w, hγ⟩
  set Q := σ (P.w + 1)
  unfold tab
  have hsz : Ex.eval σ A (.lett P.u (.var P.w) P.E.sz) = κ.s γ := by
    simp only [Ex.eval]
    exact H.rep.sz _ (hσ.upd hu _) γ (by simp [NVars.std, γ])
  refine B_zsum (by omega) (by rw [hmσ]; exact hmV)
    (B_lett (B_var (by omega)) (hE.sz _ (hσ.upd hu _) (by simp [NVars.std]; exact hγ))) fun c hc => ?_
  rw [hsz] at hc
  set σ1 := Function.update σ (P.u + 2) c
  have a1 : Ag B σ₀ σ1 := hσ.upd (by omega) _
  refine B_lett (B_var (by simp only [σ1]; upd; omega)) ?_
  have e1w : σ1 P.w = γ := by simp only [σ1]; upd; rfl
  rw [show Ex.eval σ1 A (.var P.w) = γ from e1w]
  set σ2 := Function.update σ1 P.u γ
  have a2 : Ag B σ₀ σ2 := a1.upd hu _
  have e2u : σ2 P.u = γ := by simp [σ2]
  have e2z : σ2 (P.u + 2) = c := by simp only [σ2, σ1]; upd
  have e2w : σ2 P.w = γ := by simp only [σ2, σ1]; upd; rfl
  have e2Q : σ2 (P.w + 1) = Q := by simp only [σ2, σ1]; upd; rfl
  have e2m : σ2 P.vm = m := by simp only [σ2, σ1]; upd; exact hmσ
  have hcV : c ≤ V := le_trans hc.le (by have := le_of_B (hE.sz _ (hσ.upd hu _) (by simp [NVars.std]; exact hγ)); simp only [Ex.eval] at hsz; rw [hsz] at this; exact this)
  have BW : Bdd V σ2 A P.E.W := hE.W σ2 a2 (by simp [NVars.std, e2u]) (by simp [NVars.std, e2z]; exact hcV)
  have ltW : Ex.eval σ2 A P.E.W < m := H.rep.W_lt a2 γ (by simp [NVars.std, e2u]) (by simp [NVars.std, e2z]; exact hc)
  have Bk : ∀ σ', Ag B σ₀ σ' → Bdd V σ' A P.kE := hkE
  -- the padded left factor at pair (γ, j), γ < j
  have padL_B : ∀ j < K, Bdd V (Function.update σ2 (P.u + 1) j) A
      (.ifLt (.var P.u) (.var (P.u + 1)) (padL P) (.lit 1)) := by
    intro j hj
    set σ3 := Function.update σ2 (P.u + 1) j
    have a3 : Ag B σ₀ σ3 := a2.upd (by omega) _
    have e3u : σ3 P.u = γ := by simp only [σ3]; upd; exact e2u
    have e3b : σ3 (P.u + 1) = j := by simp [σ3]
    refine B_ifLt' (B_var (by rw [e3u]; omega)) (B_var (by rw [e3b]; omega)) (fun hlt => ?_) (fun _ => B_lit (by omega))
    simp only [Ex.eval, e3u, e3b] at hlt
    have Bc : Bdd V σ3 A P.E.c := hE.c σ3 a3 (by simp [NVars.std, e3u, e3b]; exact hlt) (by simp [NVars.std, e3b]; exact hj)
    have ec : Ex.eval σ3 A P.E.c = N.c γ ⟨j, hj⟩ := H.rep.c σ3 a3 γ ⟨j, hj⟩ hlt (by simp [NVars.std, e3u]) (by simp [NVars.std, e3b])
    unfold padL
    refine B_ifLt' Bc (B_add (hLE σ3 a3) (B_lit (by omega)) (by rw [H.LE σ3 a3]; simp only [Ex.eval]; omega))
      (fun hcL => ?_) (fun _ => B_lit (by omega))
    simp only [Ex.eval, H.LE σ3 a3, ec] at hcL
    have hjL : L * j ≤ L * K := Nat.mul_le_mul_left _ hj.le
    have h2j : 2 ^ (L * j) ≤ V := le_trans (Nat.pow_le_pow_right (by norm_num) hjL) hLK
    have Bq : Bdd V σ3 A (blkQ P (P.u + 1)) := by
      unfold blkQ
      refine B_div (B_var (by simp only [σ3]; upd; rw [e2Q]; exact hQ)) (B_pow2 (B_mul (hLE σ3 a3) (B_var (by omega)) ?_) h2V ?_)
      · rw [H.LE σ3 a3]; simp only [Ex.eval, e3b]; exact le_trans (Nat.lt_two_pow_self (n := L * j)).le h2j
      · simp only [Ex.eval, H.LE σ3 a3, e3b]; exact h2j
    have eq : Ex.eval σ3 A (blkQ P (P.u + 1)) ≤ V := le_of_B Bq
    refine B_lett Bq ?_
    set σ4 := Function.update σ3 (P.u + 3) (Ex.eval σ3 A (blkQ P (P.u + 1)))
    have a4 : Ag B σ₀ σ4 := a3.upd (by omega) _
    have e4u : σ4 P.u = γ := by simp only [σ4]; upd; exact e3u
    have e4b : σ4 (P.u + 1) = j := by simp only [σ4]; upd; exact e3b
    have e4z : σ4 (P.u + 2) = c := by simp only [σ4, σ3]; upd; exact e2z
    have e4m : σ4 P.vm = m := by simp only [σ4, σ3]; upd; exact e2m
    have e4q : σ4 (P.u + 3) ≤ V := by simp only [σ4]; upd; exact eq
    have Bc4 : Bdd V σ4 A P.E.c := hE.c σ4 a4 (by simp [NVars.std, e4u, e4b]; exact hlt) (by simp [NVars.std, e4b]; exact hj)
    have ec4 : Ex.eval σ4 A P.E.c = N.c γ ⟨j, hj⟩ := H.rep.c σ4 a4 γ ⟨j, hj⟩ hlt (by simp [NVars.std, e4u]) (by simp [NVars.std, e4b])
    have Bl : Bdd V σ4 A P.E.l := hE.l σ4 a4 (by simp [NVars.std, e4u, e4b]; exact hlt) (by simp [NVars.std, e4b]; exact hj)
      (by simp [NVars.std, e4z]; exact hcV) (by simp [NVars.std]; exact e4q)
    have ltl : Ex.eval σ4 A P.E.l < m := H.rep.l_lt a4 γ ⟨j, hj⟩ hlt (by simp [NVars.std, e4u]) (by simp [NVars.std, e4b])
      (by simp [NVars.std, e4z]; exact hc)
    have Bu : Bdd V σ4 A (unitE P) := by
      unfold unitE
      refine B_ifEq (B_mod (B_div (B_var e4q) (B_pow2 Bc4 h2V ?_)) (B_pow2 (B_sub (hLE σ4 a4) Bc4) h2V ?_))
        (B_lit (Nat.zero_le _)) (B_lit (by omega)) (B_lit (Nat.zero_le _))
      · rw [ec4]; exact le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) h2L
      · simp only [Ex.eval, ec4, H.LE σ4 a4]; exact le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) h2L
    have lu : Ex.eval σ4 A (unitE P) ≤ 1 := by unfold unitE; exact ifEq_le (by simp [Ex.eval]) (by simp [Ex.eval])
    exact B_zmul Bl Bu (by rw [e4m]; exact hmV) (le_trans (Nat.mul_le_mul ltl.le lu) (by omega))
  -- the padded right factor at pair (j, γ), j < γ
  have padR_B : ∀ j < K, Bdd V (Function.update σ2 P.u j) A
      (.ifLt (.var P.u) (.var P.w) (.lett (P.u + 1) (.var P.w) (padR P)) (.lit 1)) := by
    intro j hj
    set σ3 := Function.update σ2 P.u j
    have a3 : Ag B σ₀ σ3 := a2.upd hu _
    have e3w : σ3 P.w = γ := by simp only [σ3]; upd; exact e2w
    have e3u : σ3 P.u = j := by simp [σ3]
    refine B_ifLt' (B_var (by rw [e3u]; omega)) (B_var (by rw [e3w]; omega)) (fun hlt => ?_) (fun _ => B_lit (by omega))
    simp only [Ex.eval, e3u, e3w] at hlt
    refine B_lett (B_var (by rw [e3w]; omega)) ?_
    simp only [Ex.eval, e3w]
    set σ4 := Function.update σ3 (P.u + 1) γ
    have a4 : Ag B σ₀ σ4 := a3.upd (by omega) _
    have e4u : σ4 P.u = j := by simp only [σ4]; upd; exact e3u
    have e4b : σ4 (P.u + 1) = γ := by simp [σ4]
    have hlt' : (⟨j, hj⟩ : Fin K) < γ := hlt
    have Bc : Bdd V σ4 A P.E.c := hE.c σ4 a4 (by simp [NVars.std, e4u, e4b]; exact hlt) (by simp [NVars.std, e4b])
    have ec : Ex.eval σ4 A P.E.c = N.c ⟨j, hj⟩ γ := H.rep.c σ4 a4 ⟨j, hj⟩ γ hlt' (by simp [NVars.std, e4u]) (by simp [NVars.std, e4b])
    unfold padR
    refine B_ifLt' Bc (B_add (hLE σ4 a4) (B_lit (by omega)) (by rw [H.LE σ4 a4]; simp only [Ex.eval]; omega))
      (fun hcL => ?_) (fun _ => B_lit (by omega))
    simp only [Ex.eval, H.LE σ4 a4, ec] at hcL
    have hjL : L * j ≤ L * K := Nat.mul_le_mul_left _ hj.le
    have h2j : 2 ^ (L * j) ≤ V := le_trans (Nat.pow_le_pow_right (by norm_num) hjL) hLK
    have Bq : Bdd V σ4 A (blkQ P P.u) := by
      unfold blkQ
      refine B_div (B_var (by simp only [σ4, σ3]; upd; rw [e2Q]; exact hQ)) (B_pow2 (B_mul (hLE σ4 a4) (B_var (by omega)) ?_) h2V ?_)
      · rw [H.LE σ4 a4]; simp only [Ex.eval, e4u]; exact le_trans (Nat.lt_two_pow_self (n := L * j)).le h2j
      · simp only [Ex.eval, H.LE σ4 a4, e4u]; exact h2j
    have eq : Ex.eval σ4 A (blkQ P P.u) ≤ V := le_of_B Bq
    refine B_lett Bq ?_
    set σ5 := Function.update σ4 (P.u + 3) (Ex.eval σ4 A (blkQ P P.u))
    have a5 : Ag B σ₀ σ5 := a4.upd (by omega) _
    have e5u : σ5 P.u = j := by simp only [σ5]; upd; exact e4u
    have e5b : σ5 (P.u + 1) = γ := by simp only [σ5]; upd; exact e4b
    have e5z : σ5 (P.u + 2) = c := by simp only [σ5, σ4, σ3]; upd; exact e2z
    have e5m : σ5 P.vm = m := by simp only [σ5, σ4, σ3]; upd; exact e2m
    have e5q : σ5 (P.u + 3) ≤ V := by simp only [σ5]; upd; exact eq
    have Bc5 : Bdd V σ5 A P.E.c := hE.c σ5 a5 (by simp [NVars.std, e5u, e5b]; exact hlt) (by simp [NVars.std, e5b])
    have ec5 : Ex.eval σ5 A P.E.c = N.c ⟨j, hj⟩ γ := H.rep.c σ5 a5 ⟨j, hj⟩ γ hlt' (by simp [NVars.std, e5u]) (by simp [NVars.std, e5b])
    have Br : Bdd V σ5 A P.E.r := hE.r σ5 a5 (by simp [NVars.std, e5u, e5b]; exact hlt) (by simp [NVars.std, e5b])
      (by simp [NVars.std, e5z]; exact hcV) (by simp [NVars.std]; exact e5q)
    have ltr : Ex.eval σ5 A P.E.r < m := H.rep.r_lt a5 ⟨j, hj⟩ γ hlt' (by simp [NVars.std, e5u]) (by simp [NVars.std, e5b])
      (by simp [NVars.std, e5z]; exact hc)
    have Bu : Bdd V σ5 A (unitE P) := by
      unfold unitE
      refine B_ifEq (B_mod (B_div (B_var e5q) (B_pow2 Bc5 h2V ?_)) (B_pow2 (B_sub (hLE σ5 a5) Bc5) h2V ?_))
        (B_lit (Nat.zero_le _)) (B_lit (by omega)) (B_lit (Nat.zero_le _))
      · rw [ec5]; exact le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) h2L
      · simp only [Ex.eval, ec5, H.LE σ5 a5]; exact le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) h2L
    have lu : Ex.eval σ5 A (unitE P) ≤ 1 := by unfold unitE; exact ifEq_le (by simp [Ex.eval]) (by simp [Ex.eval])
    exact B_zmul Br Bu (by rw [e5m]; exact hmV) (le_trans (Nat.mul_le_mul ltr.le lu) (by omega))
  have hm2 : 0 < σ2 P.vm := by rw [e2m]; omega
  have hm2' : 1 < σ2 P.vm := by rw [e2m]; omega
  have Bp1 : Bdd V σ2 A (zprod (P.u + 1) P.kE P.vm (.ifLt (.var P.u) (.var (P.u + 1)) (padL P) (.lit 1))) :=
    B_zprod hm2 (by rw [e2m]; exact hmV) (by omega) (Bk σ2 a2) fun j hj => padL_B j (by rw [H.kE σ2 a2] at hj; exact hj)
  have Bp2 : Bdd V σ2 A (zprod P.u P.kE P.vm (.ifLt (.var P.u) (.var P.w) (.lett (P.u + 1) (.var P.w) (padR P)) (.lit 1))) :=
    B_zprod hm2 (by rw [e2m]; exact hmV) (by omega) (Bk σ2 a2) fun j hj => padR_B j (by rw [H.kE σ2 a2] at hj; exact hj)
  have l1 := lt_zprod (σ := σ2) (A := A) (x := P.u + 1) (n := P.kE)
    (b := .ifLt (.var P.u) (.var (P.u + 1)) (padL P) (.lit 1)) hm2'
  have l2 := lt_zprod (σ := σ2) (A := A) (x := P.u) (n := P.kE)
    (b := .ifLt (.var P.u) (.var P.w) (.lett (P.u + 1) (.var P.w) (padR P)) (.lit 1)) hm2'
  have l3 := lt_zmul (σ := σ2) (A := A) (vm := P.vm) (e := P.E.W)
    (f := zprod (P.u + 1) P.kE P.vm (.ifLt (.var P.u) (.var (P.u + 1)) (padL P) (.lit 1))) hm2
  rw [e2m] at l1 l2 l3
  exact B_zmul (B_zmul BW Bp1 (by rw [e2m]; exact hmV) (le_trans (Nat.mul_le_mul ltW.le l1.le) hmm)) Bp2
    (by rw [e2m]; exact hmV) (le_trans (Nat.mul_le_mul l3.le l2.le) hmm)

end Factoring.Aux
