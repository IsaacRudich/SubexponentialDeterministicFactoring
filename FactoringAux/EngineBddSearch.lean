/-
Value bounds of the group search (`GroupEx.searchE`).

* `okE_bdd`: the goodness test of the grouping code `x < K^g` held in `vχ`.
* **`search_bdd`**: in the setting of `eval_searchE`, every value met by `searchE S vx vs` is at most `V`.

Not an audit surface.
-/
module

public import FactoringAux.EngineBddCoarsen

@[expose] public section

namespace Factoring.Aux

open Finset Ex SB GroupEx

namespace GroupEx

variable {V m : ℕ} {S : GS} {σ₀ : ℕ → ℕ} {A : ℕ → ℕ → ℕ} {N : Net (ZMod m) S.g} {κ : Coding N}

theorem nprod_le_one {σ : ℕ → ℕ} {x : ℕ} {n b : Ex} (h : ∀ j, eval (Function.update σ x j) A b ≤ 1) :
    eval σ A (nprod x n b) ≤ 1 := by
  rw [eval_nprod]; exact pp_le_one fun i _ => h i

theorem B_chiE {σ : ℕ → ℕ} (hKg : S.K ^ S.g ≤ V) (hgV : S.g ≤ V) (hK : 0 < S.K) (hg : 0 < S.g) (hx : σ S.vχ ≤ V)
    (hu : σ S.u < S.g) : Bdd V σ A (chiE S) := by
  have hKV : S.K ≤ V := le_trans (Nat.le_self_pow (by omega) _) hKg
  unfold chiE
  refine B_mod (B_div (B_var hx) ?_) (B_lit hKV)
  exact B_nprodK (x := S.u + 45) (n := .var S.u) (b := .lit S.K) (c := S.K) (B_var (by omega))
    (fun j _ => ⟨B_lit hKV, rfl⟩) hK
    (le_trans (Nat.pow_le_pow_right hK (show σ S.u ≤ S.g by omega)) hKg)

/-- The goodness test of the code in `vχ`. -/
theorem okE_bdd (hK : 0 < S.K) (hg : 0 < S.g) (hm : 1 < m) {B : ℕ}
    (h : NRep m S.vm B σ₀ A (NVars.std S.u) S.E N κ) (hE : NBdd V B σ₀ A (NVars.std S.u) S.E S.g)
    (hχ : S.vχ < B) (hL : S.vL < B) (hu : B ≤ S.u) {x L : ℕ} (hx : σ₀ S.vχ = x) (hxK : x < S.K ^ S.g)
    (hLσ : σ₀ S.vL = L) (hKg : S.K ^ S.g ≤ V) (hgg : S.g * S.g ≤ V) (hKgV : S.K * S.g ≤ V)
    (hg1 : 2 * S.g + 1 ≤ V) (hL1 : L + 1 ≤ V)
    (hcw : ∀ γ γ' : Fin S.K, γ < γ' → (N.coarsen (chiOf S.K S.g x hK)).c γ γ' ≤ V)
    {σ : ℕ → ℕ} (hσ : Ag B σ₀ σ) : Bdd V σ A (okE S) := by
  have H := coarsenHyp hK hg hm h hχ hu hx
  have hKV : S.K ≤ V := le_trans (Nat.le_self_pow (by omega) _) hKg
  have hV1 : 1 ≤ V := by omega
  have hxV : σ S.vχ ≤ V := by rw [hσ _ hχ, hx]; omega
  have hχE : ∀ σ', Ag B σ₀ σ' → σ' S.u < S.g → Bdd V σ' A (chiE S) := fun σ' h' hu' =>
    B_chiE hKg (le_trans (Nat.le_mul_of_pos_left _ hg) hgg) hK hg (by rw [h' _ hχ, hx]; omega) hu'
  unfold okE
  refine ⟨B_nprod01 (B_lit hKV) (fun γ hγ => ⟨?_, ?_⟩) hV1, B_nprod01 (B_lit hKV) (fun γ hγ => ⟨?_, ?_⟩) hV1, ?_⟩
  · -- the group sizes
    simp only [Ex.eval] at hγ
    set σ1 := Function.update σ (S.u + 54) γ
    have a1 : Ag B σ₀ σ1 := hσ.upd (by omega) _
    have Bs : Bdd V σ1 A (nsum S.u (.lit S.g) (ifEq (chiE S) (.var (S.u + 54)) (.lit 1) (.lit 0))) := by
      refine B_nsum' (c := 1) (B_lit (by omega)) (fun a ha => ⟨?_, ?_⟩) (by simp only [Ex.eval]; omega)
      · simp only [Ex.eval] at ha
        exact B_ifEq (hχE _ (a1.upd hu _) (by simp only [Function.update_self]; exact ha))
          (B_var (by upd; simp only [σ1]; upd; omega)) (B_lit hV1) (B_lit (Nat.zero_le _))
      · exact ifEq_le (by simp [Ex.eval]) (by simp [Ex.eval])
    have hs : eval σ1 A (nsum S.u (.lit S.g) (ifEq (chiE S) (.var (S.u + 54)) (.lit 1) (.lit 0))) ≤ S.g := by
      rw [eval_nsum]
      refine le_trans (Ex.sum_le_card_mul (B := 1) fun a _ => ifEq_le (by simp [Ex.eval]) (by simp [Ex.eval])) ?_
      simp [Ex.eval]
    exact B_ifLt' (B_mul (B_lit hKV) Bs (by simp only [Ex.eval]; exact le_trans (Nat.mul_le_mul_left _ hs) hKgV))
      (B_lit hg1) (fun _ => B_lit hV1) (fun _ => B_lit (Nat.zero_le _))
  · exact ifLt_le (by simp [Ex.eval]) (by simp [Ex.eval])
  · -- the coarse widths
    simp only [Ex.eval] at hγ
    have a1 : Ag B σ₀ (Function.update σ (S.u + 46) γ) := hσ.upd (by omega) _
    refine B_nprod01 (B_lit hKV) (fun γ' hγ' => ⟨?_, ?_⟩) hV1
    · simp only [Ex.eval] at hγ'
      set σ2 := Function.update (Function.update σ (S.u + 46) γ) (S.u + 47) γ'
      have a2 : Ag B σ₀ σ2 := a1.upd (by omega) _
      have e1 : σ2 (S.u + 46) = γ := by simp only [σ2]; upd
      have e2 : σ2 (S.u + 47) = γ' := by simp only [σ2]; upd
      refine B_ifLt' (B_var (by rw [e1]; omega)) (B_var (by rw [e2]; omega)) (fun hlt => ?_) (fun _ => B_lit hV1)
      simp only [Ex.eval, e1, e2] at hlt
      have hLV : σ2 S.vL ≤ V := by rw [a2 _ hL, hLσ]; omega
      refine B_ifLt' ?_ (B_add (B_var hLV) (B_lit hV1) (by simp only [Ex.eval]; rw [a2 _ hL, hLσ]; exact hL1))
        (fun _ => B_lit hV1) (fun _ => B_lit (Nat.zero_le _))
      exact coarsenC_bdd (P := Pc S) H hχE (fun _ _ => B_lit (le_trans (Nat.le_mul_of_pos_left _ hg) hgg))
        (fun σ' h' hab hb => hE.c σ' h' hab hb) hgg hKV a2 ⟨γ, hγ⟩ ⟨γ', hγ'⟩ e1 e2 (hcw _ _ hlt)
    · exact ifLt_le (ifLt_le (by simp [Ex.eval]) (by simp [Ex.eval])) (by simp [Ex.eval])
  · refine nprod_le_one fun j' => ?_
    exact ifLt_le (ifLt_le (by simp [Ex.eval]) (by simp [Ex.eval])) (by simp [Ex.eval])
  · refine le_trans (Nat.mul_le_mul (nprod_le_one fun j => ?_) (nprod_le_one fun j => nprod_le_one fun j' => ?_))
      (show 1 * 1 ≤ V by omega)
    · exact ifLt_le (by simp [Ex.eval]) (by simp [Ex.eval])
    · exact ifLt_le (ifLt_le (by simp [Ex.eval]) (by simp [Ex.eval])) (by simp [Ex.eval])

/-- **The group search: every value is at most `V`** (setting of `eval_searchE`). -/
theorem search_bdd (hK : 0 < S.K) (hg : 0 < S.g) (hm : 1 < m) {B0 : ℕ}
    (h : NRep m S.vm B0 σ₀ A (NVars.std S.u) S.E N κ) (hE : NBdd V B0 σ₀ A (NVars.std S.u) S.E S.g)
    (hvm : S.vm < B0) (hL : S.vL < B0) {vx vs L : ℕ}
    (h1 : B0 ≤ vx) (h2 : B0 ≤ vs) (h3 : B0 ≤ S.vχ) (d1 : vx ≠ vs) (d2 : vx ≠ S.vχ) (d3 : vs ≠ S.vχ)
    (u1 : vx < S.u) (_u2 : vs < S.u) (u3 : S.vχ < S.u) (hLσ : σ₀ S.vL = L)
    (hKg : S.K ^ S.g ≤ V) (hgg : S.g * S.g ≤ V) (hKgV : S.K * S.g ≤ V) (hg1 : 2 * S.g + 1 ≤ V) (hL1 : L + 1 ≤ V)
    (hcw : ∀ x < S.K ^ S.g, ∀ γ γ' : Fin S.K, γ < γ' → (N.coarsen (chiOf S.K S.g x hK)).c γ γ' ≤ V)
    {σ : ℕ → ℕ} (hσ : Ag B0 σ₀ σ) : Bdd V σ A (searchE S vx vs) := by
  set n := S.K ^ S.g
  set F : ℕ → ℕ → ℕ := fun j s => eval (Function.update (Function.update σ vx j) vs s) A
    (ifEq (.var vs) (.lit n) (.lett S.vχ (.var vx) (ifEq (okE S) (.lit 1) (.var vx) (.var vs))) (.var vs))
  have hF : ∀ j < n, ∀ s ≤ n, F j s ≤ n := by
    intro j hj s hs
    simp only [F]
    refine ifEq_le ?_ (by simp [Ex.eval, hs])
    rw [eval_lett]
    refine ifEq_le ?_ ?_ <;> simp only [Ex.eval] <;> upd
    · omega
    · simp [hs]
  have hst : ∀ j ≤ n, iterF F n j ≤ n := by
    intro j
    induction j with
    | zero => intro _; exact le_rfl
    | succ j ih => intro hj; exact hF j (by omega) _ (ih (by omega))
  refine ⟨B_lit hKg, B_lit hKg, fun j hj => ?_⟩
  change j < n at hj
  show Bdd V (Function.update (Function.update σ vx j) vs (iterF F n j)) A _
  set s := iterF F n j
  have hs : s ≤ n := hst j hj.le
  set σ1 := Function.update (Function.update σ vx j) vs s
  have a1 : Ag B0 σ₀ σ1 := (hσ.upd h1 _).upd h2 _
  have ex : σ1 vx = j := by simp only [σ1]; rw [Function.update_of_ne d1]; simp
  have es : σ1 vs = s := by simp [σ1]
  have Bx : Bdd V σ1 A (.var vx) := B_var (by rw [ex]; omega)
  have Bs : Bdd V σ1 A (.var vs) := B_var (by rw [es]; omega)
  refine B_ifEq Bs (B_lit hKg) (B_lett Bx ?_) Bs
  rw [show eval σ1 A (.var vx) = j from ex]
  set σ2 := Function.update σ1 S.vχ j
  have a2 : Ag B0 σ₀ σ2 := a1.upd h3 _
  have hrep := (h.congr hvm a2).mono (show B0 ≤ S.u by omega)
  have hE2 := (hE.congr a2).mono (show B0 ≤ S.u by omega)
  have Bok := okE_bdd (B := S.u) (σ₀ := σ2) (σ := σ2) (x := j) (L := L) hK hg hm hrep hE2 u3 (by omega) le_rfl
    (by simp [σ2]) hj (by rw [a2 _ hL, hLσ]) hKg hgg hKgV hg1 hL1 (hcw j hj) (Ag.refl _ _)
  have Bx2 : Bdd V σ2 A (.var vx) := B_var (by simp only [σ2]; rw [Function.update_of_ne d2, ex]; omega)
  have Bs2 : Bdd V σ2 A (.var vs) := B_var (by simp only [σ2]; rw [Function.update_of_ne d3, es]; omega)
  exact B_ifEq Bok (B_lit (by omega)) Bx2 Bs2

end GroupEx

end Factoring.Aux
