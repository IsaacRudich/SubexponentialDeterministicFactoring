/-
The chain as one expression: the brute force at the bottom (`bruteE`, **`brute_rep`**) and the nested sums over the
choice codes of every level (`deepEx`, **`deep_rep`**: its value represents `deepVal`).

Not an audit surface.
-/
module

public import FactoringAux.EngineLevelEx

@[expose] public section

namespace Factoring.Aux

open Finset Ex

/-! ### The brute force -/

/-- A clique's array of strings as one number: string `(γ, γ')` at block `γ' + Kγ`. -/
def bruteEquiv (K L : ℕ) : (Fin K → Fin K → Bits L) ≃ Fin (2 ^ (L * (K * K))) :=
  (Equiv.curry (Fin K) (Fin K) (Bits L)).symm.trans
    ((Equiv.arrowCongr finProdFinEquiv (Equiv.refl _)).trans (blkEquiv L (K * K)))

theorem bruteEquiv_symm {K L : ℕ} (x : Fin (2 ^ (L * (K * K)))) (γ γ' : Fin K) :
    (bruteEquiv K L).symm x γ γ' = bdec L (x / 2 ^ (L * (γ' + K * γ))) := by
  show (blkEquiv L (K * K)).symm x (finProdFinEquiv (γ, γ')) = _
  rw [blkEquiv_symm, finProdFinEquiv_apply_val]

/-- Block `(γ, γ')` of a brute-force code. -/
def blkK (L K x γ γ' : ℕ) : ℕ := x / 2 ^ (L * (γ' + K * γ)) % 2 ^ L

/-- A clique table read at a node index and a block code. -/
def tabK {m K L : ℕ} (T : Clique (ZMod m) K L) (γ Q : ℕ) : ZMod m :=
  if h : γ < K then T ⟨γ, h⟩ (thetaOf L Q) else 0

/-- The summand of the brute force. -/
def bruteF {m K L : ℕ} (T : Clique (ZMod m) K L) (x : ℕ) : ZMod m :=
  (∏ γ ∈ range K, if blkK L K x γ γ = 0 then tabK T γ (x / 2 ^ (L * (K * γ))) else 0) *
    ∏ γ ∈ range K, ∏ γ' ∈ range K, if γ < γ' then (if blkK L K x γ γ' = blkK L K x γ' γ then 1 else 0) else 1

theorem value_brute {m K L : ℕ} (T : Clique (ZMod m) K L) :
    T.value = ∑ x ∈ range (2 ^ (L * (K * K))), bruteF T x := by
  unfold Clique.value
  rw [sum_equiv_range (bruteEquiv K L)]
  refine sum_congr rfl fun x hx => ?_
  rw [dif_pos (mem_range.mp hx)]
  set X : Fin (2 ^ (L * (K * K))) := ⟨x, mem_range.mp hx⟩
  have hb : ∀ γ γ' : Fin K, (bruteEquiv K L).symm X γ γ' = bdec L (blkK L K x γ γ') := fun γ γ' => by
    rw [bruteEquiv_symm, blkK, bdec_mod]
  unfold bruteF
  congr 1
  · rw [prod_fin_range]
    refine prod_congr rfl fun γ hγ => ?_
    have hγ' := mem_range.mp hγ
    rw [dif_pos hγ']
    have hΘ : (bruteEquiv K L).symm X ⟨γ, hγ'⟩ = thetaOf L (x / 2 ^ (L * (K * γ))) := by
      funext γ'
      rw [bruteEquiv_symm, thetaOf, Nat.div_div_eq_div_mul, ← pow_add, ← mul_add, add_comm (K * γ)]
    simp only [hb]
    rw [hΘ, tabK, dif_pos hγ']
    simp only [Fac.bdec_eq_zero, blkK, Nat.mod_mod]
    by_cases h : x / 2 ^ (L * (γ + K * γ)) % 2 ^ L = 0 <;> simp [h]
  · rw [prod_pairs_range]
    refine prod_congr rfl fun γ hγ => prod_congr rfl fun γ' hγ' => ?_
    rw [dif_pos ⟨mem_range.mp hγ, mem_range.mp hγ'⟩]
    simp only [hb, bdec_eq_iff, blkK, Nat.mod_mod]
    by_cases h1 : γ < γ' <;>
      by_cases h2 : x / 2 ^ (L * (γ' + K * γ)) % 2 ^ L = x / 2 ^ (L * (γ + K * γ')) % 2 ^ L <;> simp [h1, h2]

namespace Ex

/-- Block `(i, j)` of the code in `b` (width in `vL`). -/
def blkKE (b vL K : ℕ) (i j : Ex) : Ex :=
  .mod (.div (.var b) (pow2 (b + 3) (.mul (.var vL) (.add j (.mul (.lit K) i))))) (pow2 (b + 3) (.var vL))

/-- The brute force over the codes of a `(K, L)`-clique's strings (scratch from `b`). -/
def bruteE (b vm vL vγ vΘ K : ℕ) (TE : Ex) : Ex :=
  zsum b (pow2 (b + 1) (.mul (.var vL) (.lit (K * K)))) vm (zmul vm
    (zprod (b + 1) (.lit K) vm (ifEq (blkKE b vL K (.var (b + 1)) (.var (b + 1))) (.lit 0)
      (.lett vγ (.var (b + 1)) (.lett vΘ (.div (.var b) (pow2 (b + 3) (.mul (.var vL) (.mul (.lit K) (.var (b + 1))))))
        TE)) (.lit 0)))
    (zprod (b + 1) (.lit K) vm (zprod (b + 2) (.lit K) vm (.ifLt (.var (b + 1)) (.var (b + 2))
      (ifEq (blkKE b vL K (.var (b + 1)) (.var (b + 2))) (blkKE b vL K (.var (b + 2)) (.var (b + 1))) (.lit 1) (.lit 0))
      (.lit 1)))))

end Ex

theorem eval_blkKE {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ} {b vL K L : ℕ} (hL : σ vL = L) (i j : Ex) :
    eval σ A (blkKE b vL K i j) = blkK L K (σ b) (eval σ A i) (eval σ A j) := by
  simp only [blkKE, Ex.eval, eval_pow2, hL, blkK]

/-- **The brute force** represents the clique's value. -/
theorem brute_rep {m BT b vm vL vγ vΘ K L : ℕ} {σ₀ : ℕ → ℕ} {A : ℕ → ℕ → ℕ} {TE : Ex} {T : Clique (ZMod m) K L}
    (hm : 1 < m) (hT : TRep m BT σ₀ A vγ vΘ TE T) (hσm : σ₀ vm = m) (hσL : σ₀ vL = L) (hvm : vm < BT)
    (hγ : BT ≤ vγ) (hΘ : BT ≤ vΘ) (hγΘ : vγ ≠ vΘ) (hLγ : vL ≠ vγ) (hBT : BT ≤ b) (hL : vL < b) (hγb : vγ < b)
    (hΘb : vΘ < b) {σ : ℕ → ℕ} (hσ : Ag b σ₀ σ) :
    ZR m (eval σ A (bruteE b vm vL vγ vΘ K TE)) T.value := by
  have hmσ : σ vm = m := by rw [hσ _ (by omega), hσm]
  have hLσ : σ vL = L := by rw [hσ _ hL, hσL]
  rw [value_brute]
  refine ZR_zsum hmσ (by omega) b (by rw [eval_pow2]; simp only [Ex.eval, hLσ]) _ fun x _ => ?_
  set σ1 := Function.update σ b x
  have m1 : σ1 vm = m := by simp only [σ1]; upd; exact hmσ
  have l1 : σ1 vL = L := by simp only [σ1]; upd; exact hLσ
  have x1 : σ1 b = x := by simp [σ1]
  unfold bruteF
  refine ZR_zmul m1 (by omega) ?_ ?_
  · refine ZR_zprod m1 hm (b + 1) rfl _ fun γ hγK => ?_
    replace hγK : γ < K := hγK
    set σ2 := Function.update σ1 (b + 1) γ
    have l2 : σ2 vL = L := by simp only [σ2]; upd; exact l1
    have x2 : σ2 b = x := by simp only [σ2]; upd; exact x1
    have g2 : eval σ2 A (.var (b + 1)) = γ := by simp [σ2, Ex.eval]
    rw [eval_ifEq, eval_blkKE l2, g2, x2]
    simp only [Ex.eval]
    by_cases hz : blkK L K x γ γ = 0
    · simp only [hz, if_true]
      have g2' : σ2 (b + 1) = γ := g2
      simp only [g2', Ex.eval, eval_pow2]
      have hγ2 : Function.update σ2 vγ γ (b + 1) = γ := by upd; simp [σ2]
      have hx3 : Function.update σ2 vγ γ b = x := by upd; exact x2
      have hl3 : Function.update σ2 vγ γ vL = L := by rw [Function.update_of_ne hLγ]; exact l2
      simp only [hγ2, hx3, hl3]
      have a3 : Ag BT σ₀ (Function.update (Function.update σ2 vγ γ) vΘ (x / 2 ^ (L * (K * γ)))) :=
        ((((hσ.mono hBT).upd (by omega) x).upd (by omega) γ).upd hγ γ).upd hΘ _
      have := hT _ a3 ⟨γ, hγK⟩ (x / 2 ^ (L * (K * γ))) (by rw [Function.update_of_ne hγΘ]; simp) (by simp)
      rw [tabK, dif_pos hγK]
      exact this
    · simp only [hz, if_false]
      exact ZR_zero (by omega)
  · refine ZR_zprod m1 hm (b + 1) rfl _ fun γ hγ => ?_
    refine ZR_zprod (by upd; exact m1) hm (b + 2) rfl _ fun γ' hγ' => ?_
    set σ2 := Function.update (Function.update σ1 (b + 1) γ) (b + 2) γ'
    have l2 : σ2 vL = L := by simp only [σ2]; upd; exact l1
    have x2 : σ2 b = x := by simp only [σ2]; upd; exact x1
    have g1 : eval σ2 A (.var (b + 1)) = γ := by simp only [σ2, Ex.eval]; upd
    have g2 : eval σ2 A (.var (b + 2)) = γ' := by simp only [σ2, Ex.eval]; upd
    rw [eval_ifLt', g1, g2]
    by_cases hlt : γ < γ'
    · rw [if_pos hlt, if_pos hlt, eval_ifEq, eval_blkKE l2, eval_blkKE l2, g1, g2, x2]
      exact ZR_ite (ZR_one hm) (ZR_zero (by omega))
    · rw [if_neg hlt, if_neg hlt]; exact ZR_one hm

namespace Ex

/-- The chain from depth `d`: the choice codes of every level, then the brute force (scratch from `b`). -/
def deepEx (K0 : ℕ) : (d b vm vl vγ vΘ : ℕ) → Ex → Ex
  | 0, b, vm, vl, vγ, vΘ, TE => bruteE b vm vl vγ vΘ (Kb K0 0) TE
  | d + 1, b, vm, vl, vγ, vΘ, TE =>
      zsum b (.prod (b + 1) (.lit (Gs K0 d * Gs K0 d * (Gs K0 d * Gs K0 d))) (.lit 0) (.add (tBE vl) (.lit 1))) vm
        (LevelEx.pre ⟨b, vm, vl, vγ, vΘ, Kb K0 d, Gs K0 d, TE⟩
          (deepEx K0 d (b + 100) vm (b + 1) (b + 62) (b + 63)
            (LevelEx.nextTE ⟨b, vm, vl, vγ, vΘ, Kb K0 d, Gs K0 d, TE⟩)))

end Ex

/-- **The chain as an expression** represents `deepVal`. -/
theorem deep_rep {m : ℕ} {A : ℕ → ℕ → ℕ} (K0 : ℕ) (hK : 2 ≤ K0) (hm : 1 < m) :
    ∀ (d b BT vm vl vγ vΘ : ℕ) (TE : Ex) (L : ℕ) (T : Clique (ZMod m) (Kb K0 d) L) (σ₀ : ℕ → ℕ),
      TRep m BT σ₀ A vγ vΘ TE T → σ₀ vm = m → σ₀ vl = L → vm < BT → BT ≤ vγ → BT ≤ vΘ → vγ ≠ vΘ → vl ≠ vγ →
      BT ≤ b → vl < b → vγ < b → vΘ < b → ∀ σ, Ag b σ₀ σ →
      ZR m (eval σ A (deepEx K0 d b vm vl vγ vΘ TE)) (deepVal K0 hK d L T)
  | 0, b, BT, vm, vl, vγ, vΘ, TE, L, T, σ₀, hT, hσm, hσl, hvm, hγ, hΘ, hγΘ, hlγ, hBT, hl, hγb, hΘb, σ, hσ =>
      brute_rep hm hT hσm hσl hvm hγ hΘ hγΘ hlγ hBT hl hγb hΘb hσ
  | d + 1, b, BT, vm, vl, vγ, vΘ, TE, L, T, σ₀, hT, hσm, hσl, hvm, hγ, hΘ, hγΘ, hlγ, hBT, hl, hγb, hΘb, σ, hσ => by
      have hmσ : σ vm = m := by rw [hσ _ (by omega), hσm]
      have hlσ : σ vl = L := by rw [hσ _ hl, hσl]
      set P : LP := ⟨b, vm, vl, vγ, vΘ, Kb K0 d, Gs K0 d, TE⟩
      have H : LevelHyp m BT σ A P L T :=
        { hm := hm, hK := Kb_ge K0 hK d, hG := rfl, rep := hT.congr (hσ.mono hBT), vm := hmσ, vl := hlσ,
          hvm := hvm, hγ := hγ, hΘ := hΘ, hγΘ := hγΘ, hlγ := hlγ, hBT := hBT, hl := hl, hγb := hγb, hΘb := hΘb }
      set N := (tB L + 1) ^ (Gs K0 d * Gs K0 d * (Gs K0 d * Gs K0 d))
      have hn : eval σ A (.prod (b + 1) (.lit (Gs K0 d * Gs K0 d * (Gs K0 d * Gs K0 d))) (.lit 0)
          (.add (tBE vl) (.lit 1))) = N := by
        simp only [Ex.eval, foldProd_zero]
        rw [show (fun i => eval (Function.update σ (b + 1) i) A (tBE vl) + 1) = fun _ => tB L + 1 from
          funext fun i => by rw [eval_tBE (by upd; exact hlσ)], pp_const]
      have hsum : deepVal K0 hK (d + 1) L T = ∑ c ∈ range N, if h : c < N then
          deepVal K0 hK d (Lnext (Kb K0 d) (Gs K0 d) L)
            (nextT (Kb K0 d) (by have := Kb_ge K0 hK d; omega) T ⟨c, h⟩) else 0 := by
        simp only [deepVal]
        rw [← Fin.sum_univ_eq_sum_range]
        exact sum_congr rfl fun c _ => by rw [dif_pos c.2]
      rw [hsum, deepEx]
      refine ZR_zsum hmσ (by omega) b hn _ fun c hc => ?_
      rw [dif_pos hc]
      set σ1 := Function.update σ b c
      have h1 : Ag b σ σ1 := (Ag.refl b σ).upd le_rfl c
      have hc1 : σ1 b = c := by simp [σ1]
      rw [LevelEx.eval_pre H hc h1 hc1]
      set σ4 := Function.update (Function.update (Function.update σ1 (b + 1)
        (Lnext (Kb K0 d) (Gs K0 d) L)) (b + 4)
        (firstGood (okG (rowNet (toGrid T) (restrictC ((phiEquiv (Gs K0 d) (tB L)).symm ⟨c, hc⟩)))
          (Kb K0 d) (Lnext (Kb K0 d) (Gs K0 d) L) (by have := Kb_ge K0 hK d; omega)) (Kb K0 d ^ Gs K0 d)
          (Kb K0 d ^ Gs K0 d))) (b + 5)
        (firstGood (okG (colNet (toGrid T) (restrictC ((phiEquiv (Gs K0 d) (tB L)).symm ⟨c, hc⟩)))
          (Kb K0 d) (Lnext (Kb K0 d) (Gs K0 d) L) (by have := Kb_ge K0 hK d; omega)) (Kb K0 d ^ Gs K0 d)
          (Kb K0 d ^ Gs K0 d))
      have a4 : Ag b σ σ4 := ((h1.upd (by omega) _).upd (by omega) _).upd (by omega) _
      have e1 : σ4 (b + 1) = Lnext (Kb K0 d) (Gs K0 d) L :=
        (Function.update_of_ne (a := b + 1) (a' := b + 5) (by omega) _ _).trans
          ((Function.update_of_ne (a := b + 1) (a' := b + 4) (by omega) _ _).trans (Function.update_self _ _ _))
      have hT4 := LevelEx.level_rep H hc a4
        ((Function.update_of_ne (a := b) (a' := b + 5) (by omega) _ _).trans
          ((Function.update_of_ne (a := b) (a' := b + 4) (by omega) _ _).trans
          ((Function.update_of_ne (a := b) (a' := b + 1) (by omega) _ _).trans hc1))) e1
        ((Function.update_of_ne (a := b + 4) (a' := b + 5) (by omega) _ _).trans (Function.update_self _ _ _))
        (Function.update_self _ _ _)
      exact deep_rep K0 hK hm d (b + 100) (b + 6) vm (b + 1) (b + 62) (b + 63) _ _ _ σ4 hT4
        (by rw [a4 vm (by omega), hmσ]) e1 (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega) σ4 (Ag.refl _ _)

end Factoring.Aux
