/-
The written-out clique of a network (`Net.toClique`, eq. (26)) as an expression.

* `TRep`: an expression (arguments `vγ`, `vΘ`) represents a clique table `T : Clique (ZMod m) K L` in a context if at
  node `γ` and code `Q` it evaluates to `T γ Θ`, where `Θ γ' = bdec L (Q / 2^(L γ'))` (the `L`-bit blocks of `Q`).
* `CliqueEx.tab`: from expressions representing `(N, κ)` (arguments `u … u+3`) and an expression for `L`, the table
  of `N.toClique L` (arguments `w`, `w+1`, scratch `w+2`, `w+3`).  **`clique_rep`**.

Not an audit surface.
-/
module

public import FactoringAux.EngineCoarsenEx

@[expose] public section

namespace Factoring.Aux

open Finset Ex

/-- The blocks of a clique argument code. -/
def thetaOf (L Q : ℕ) {K : ℕ} : Fin K → Bits L := fun γ' => bdec L (Q / 2 ^ (L * γ'))

/-- **An expression representing a clique table.** -/
def TRep (m B : ℕ) (σ₀ : ℕ → ℕ) (A : ℕ → ℕ → ℕ) (vγ vΘ : ℕ) (T : Ex) {K L : ℕ} (Tab : Clique (ZMod m) K L) :
    Prop :=
  ∀ σ, Ag B σ₀ σ → ∀ (γ : Fin K) (Q : ℕ), σ vγ = γ → σ vΘ = Q → ZR m (Ex.eval σ A T) (Tab γ (thetaOf L Q))

/-- The data of the clique expressions. -/
structure KP where
  /-- Inner argument base. -/
  u : ℕ
  /-- Table argument base. -/
  w : ℕ
  /-- The modulus variable. -/
  vm : ℕ
  /-- Inner expressions. -/
  E : NEx
  /-- Number of nodes. -/
  kE : Ex
  /-- The label width. -/
  LE : Ex

namespace CliqueEx

variable (P : KP)

/-- The string of `Θ γ'` for `γ' = var j`: `Q / 2^(L γ')`. -/
def blkQ (j : ℕ) : Ex := .div (.var (P.w + 1)) (pow2 (P.w + 2) (.mul P.LE (.var j)))

/-- `[q / 2^c mod 2^(L−c) = 0]` for `q = var (u+3)`. -/
def unitE : Ex :=
  ifEq (.mod (.div (.var (P.u + 3)) (pow2 (P.w + 2) P.E.c)) (pow2 (P.w + 2) (.sub P.LE P.E.c))) (.lit 0) (.lit 1) (.lit 0)

/-- The padded left function of the pair `(u, u+1)` at `Θ (u+1)`. -/
def padL : Ex :=
  .ifLt P.E.c (.add P.LE (.lit 1)) (.lett (P.u + 3) (blkQ P (P.u + 1)) (zmul P.vm P.E.l (unitE P))) (.lit 0)

/-- The padded right function of the pair `(u, u+1)` at `Θ u`. -/
def padR : Ex :=
  .ifLt P.E.c (.add P.LE (.lit 1)) (.lett (P.u + 3) (blkQ P P.u) (zmul P.vm P.E.r (unitE P))) (.lit 0)

/-- The table. -/
def tab : Ex :=
  zsum (P.u + 2) (.lett P.u (.var P.w) P.E.sz) P.vm (.lett P.u (.var P.w)
    (zmul P.vm (zmul P.vm P.E.W (zprod (P.u + 1) P.kE P.vm (.ifLt (.var P.u) (.var (P.u + 1)) (padL P) (.lit 1))))
      (zprod P.u P.kE P.vm (.ifLt (.var P.u) (.var P.w) (.lett (P.u + 1) (.var P.w) (padR P)) (.lit 1)))))

end CliqueEx

section Proofs

variable {m B K L : ℕ} {σ₀ : ℕ → ℕ} {A : ℕ → ℕ → ℕ} {P : KP} {N : Net (ZMod m) K} {κ : Coding N}

open CliqueEx

/-- Hypotheses of the clique expressions. -/
structure CliqueHyp (m B : ℕ) (σ₀ : ℕ → ℕ) (A : ℕ → ℕ → ℕ) (P : KP) {K : ℕ} (N : Net (ZMod m) K)
    (κ : Coding N) (L : ℕ) : Prop where
  rep : NRep m P.vm B σ₀ A (NVars.std P.u) P.E N κ
  kE : ∀ σ, Ag B σ₀ σ → Ex.eval σ A P.kE = K
  LE : ∀ σ, Ag B σ₀ σ → Ex.eval σ A P.LE = L
  hu : B ≤ P.u
  hw : P.u + 4 ≤ P.w
  hm : 1 < m
  hvm : P.vm < B

theorem bdec_div_pow (L Q a : ℕ) : bdec L (Q / 2 ^ (L * a)) = thetaOf L Q (K := a + 1) ⟨a, by omega⟩ := rfl

theorem eval_unitE (H : CliqueHyp m B σ₀ A P N κ L) {σ : ℕ → ℕ} (hσ : Ag B σ₀ σ) (c : ℕ)
    (hc : Ex.eval σ A P.E.c = c) :
    Ex.eval σ A (unitE P) = if σ (P.u + 3) / 2 ^ c % 2 ^ (L - c) = 0 then 1 else 0 := by
  unfold unitE
  rw [eval_ifEq]
  simp only [Ex.eval, eval_pow2, hc, H.LE σ hσ]

theorem pad_l_ZR {X Y : Type*} {c : ℕ} (F : Fac (ZMod m) X Y c) (h : c ≤ L) (x : X) (q v : ℕ) (hm : 1 < m)
    (hv : ZR m v (F.l x (bdec c q))) :
    ZR m ((v * (if q / 2 ^ c % 2 ^ (L - c) = 0 then 1 else 0)) % m) ((F.pad L h).l x (bdec L q)) := by
  rw [Fac.pad_l_bdec]
  refine ⟨Nat.mod_lt _ (by omega), ?_⟩
  rw [ZMod.natCast_mod, Nat.cast_mul, hv.2]
  split_ifs <;> simp

theorem pad_r_ZR {X Y : Type*} {c : ℕ} (F : Fac (ZMod m) X Y c) (h : c ≤ L) (y : Y) (q v : ℕ) (hm : 1 < m)
    (hv : ZR m v (F.r y (bdec c q))) :
    ZR m ((v * (if q / 2 ^ c % 2 ^ (L - c) = 0 then 1 else 0)) % m) ((F.pad L h).r y (bdec L q)) := by
  rw [Fac.pad_r_bdec]
  refine ⟨Nat.mod_lt _ (by omega), ?_⟩
  rw [ZMod.natCast_mod, Nat.cast_mul, hv.2]
  split_ifs <;> simp

theorem sum_equiv_range {X M : Type*} [Fintype X] [AddCommMonoid M] {n : ℕ} (e : X ≃ Fin n) (f : X → M) :
    ∑ x, f x = ∑ c ∈ range n, if h : c < n then f (e.symm ⟨c, h⟩) else 0 := by
  rw [← e.symm.sum_comp, Finset.sum_range]
  exact sum_congr rfl fun c _ => by rw [dif_pos c.2]

theorem padF_l {K' L' : ℕ} (N' : Net (ZMod m) K') (a b : Fin K') (z : N'.S a) (θ : Bits L') :
    (N'.padF L' a b).l z θ = if h : N'.c a b ≤ L' then ((N'.F a b).pad L' h).l z θ else 0 := by
  unfold Net.padF; split <;> rfl

theorem padF_r {K' L' : ℕ} (N' : Net (ZMod m) K') (a b : Fin K') (z : N'.S b) (θ : Bits L') :
    (N'.padF L' a b).r z θ = if h : N'.c a b ≤ L' then ((N'.F a b).pad L' h).r z θ else 0 := by
  unfold Net.padF; split <;> rfl

theorem prod_filter_range {M : Type*} [CommMonoid M] (p : Fin K → Prop) [DecidablePred p] (f : Fin K → M) :
    ∏ γ' ∈ univ.filter p, f γ' = ∏ j ∈ range K, if h : j < K then (if p ⟨j, h⟩ then f ⟨j, h⟩ else 1) else 1 := by
  rw [prod_filter, prod_fin_range]

/-- **The written-out clique, as an expression.** -/
theorem clique_rep (H : CliqueHyp m B σ₀ A P N κ L) : TRep m B σ₀ A P.w (P.w + 1) (tab P) (N.toClique L) := by
  intro σ hσ γ Q hγ hQ
  have hu := H.hu; have hw := H.hw; have hm := H.hm; have hvm := H.hvm
  have hmσ : σ P.vm = m := by rw [hσ _ hvm]; exact H.rep.hm
  unfold Net.toClique tab
  rw [sum_equiv_range (κ.e γ)]
  have hsz : Ex.eval σ A (.lett P.u (.var P.w) P.E.sz) = κ.s γ := by
    simp only [Ex.eval]
    exact H.rep.sz _ (hσ.upd hu _) γ (by simp [NVars.std, hγ])
  refine ZR_zsum hmσ (by omega) (P.u + 2) hsz _ fun c hc => ?_
  rw [dif_pos hc]
  set z := (κ.e γ).symm ⟨c, hc⟩
  simp only [Ex.eval]
  set σ2 := Function.update (Function.update σ (P.u + 2) c) P.u (Function.update σ (P.u + 2) c P.w)
  have hσ2w : Function.update σ (P.u + 2) c P.w = γ := by rw [upd_ne _ (by omega), hγ]
  have h2 : Ag B σ₀ σ2 := (hσ.upd (by omega) _).upd hu _
  have e2u : σ2 P.u = γ := by simp [σ2, hσ2w]
  have e2z : σ2 (P.u + 2) = κ.e γ z := by simp [σ2, z]
  have e2w : σ2 P.w = γ := by simp only [σ2]; rw [upd_ne _ (by omega), hσ2w]
  have e2Q : σ2 (P.w + 1) = Q := by simp only [σ2]; rw [upd_ne _ (by omega), upd_ne _ (by omega), hQ]
  have e2m : σ2 P.vm = m := by simp only [σ2]; rw [upd_ne _ (by omega), upd_ne _ (by omega), hmσ]
  refine ZR_zmul e2m (by omega) (ZR_zmul e2m (by omega) (H.rep.W σ2 h2 γ z e2u e2z) ?_) ?_
  · -- the pairs γ < γ'
    rw [prod_filter_range]
    refine ZR_zprod e2m H.hm (P.u + 1) (H.kE σ2 h2) _ fun j hj => ?_
    rw [dif_pos hj]
    set σ3 := Function.update σ2 (P.u + 1) j
    have h3 : Ag B σ₀ σ3 := h2.upd (by omega) j
    have e3u : σ3 P.u = γ := by simp only [σ3]; rw [upd_ne _ (by omega), e2u]
    have e3b : σ3 (P.u + 1) = (⟨j, hj⟩ : Fin K) := by simp [σ3]
    have e3m : σ3 P.vm = m := by simp only [σ3]; rw [upd_ne _ (by omega), e2m]
    simp only [Ex.eval, e3u, show σ3 (P.u + 1) = j from e3b]
    by_cases hlt : (γ : ℕ) < j
    · have hlt' : γ < (⟨j, hj⟩ : Fin K) := hlt
      rw [if_pos hlt, if_pos hlt', padF_l]
      unfold padL
      simp only [Ex.eval, H.rep.c σ3 h3 γ ⟨j, hj⟩ hlt' e3u e3b, H.LE σ3 h3]
      by_cases hcL : N.c γ ⟨j, hj⟩ ≤ L
      · rw [if_pos (by omega), dif_pos hcL]
        set q := Q / 2 ^ (L * j)
        have hq : Ex.eval σ3 A (blkQ P (P.u + 1)) = q := by
          unfold blkQ
          simp only [Ex.eval, eval_pow2, H.LE σ3 h3, e3b]
          rw [show σ3 (P.w + 1) = Q by simp only [σ3]; rw [upd_ne _ (by omega), e2Q]]
        rw [hq]
        set σ4 := Function.update σ3 (P.u + 3) q
        have h4 : Ag B σ₀ σ4 := h3.upd (by omega) q
        have e4u : σ4 P.u = γ := by simp only [σ4]; rw [upd_ne _ (by omega), e3u]
        have e4b : σ4 (P.u + 1) = (⟨j, hj⟩ : Fin K) := by simp only [σ4]; rw [upd_ne _ (by omega), e3b]
        have e4z : σ4 (P.u + 2) = κ.e γ z := by
          simp only [σ4, σ3]; rw [upd_ne _ (by omega), upd_ne _ (by omega), e2z]
        have e4m : σ4 P.vm = m := by simp only [σ4]; rw [upd_ne _ (by omega), e3m]
        simp only [zmul, Ex.eval, e4m]
        rw [eval_unitE H h4 _ (H.rep.c σ4 h4 γ ⟨j, hj⟩ hlt' e4u e4b), show σ4 (P.u + 3) = q by simp [σ4]]
        exact pad_l_ZR _ hcL z q _ H.hm (H.rep.l σ4 h4 γ ⟨j, hj⟩ hlt' z q e4u e4b e4z (by simp [σ4, NVars.std]))
      · rw [if_neg (by omega), dif_neg hcL]
        exact ZR_zero (by omega)
    · have hlt' : ¬ γ < (⟨j, hj⟩ : Fin K) := hlt
      rw [if_neg hlt, if_neg hlt']
      exact ZR_one H.hm
  · -- the pairs γ' < γ
    rw [prod_filter_range]
    refine ZR_zprod e2m H.hm P.u (H.kE σ2 h2) _ fun j hj => ?_
    rw [dif_pos hj]
    set σ3 := Function.update σ2 P.u j
    have h3 : Ag B σ₀ σ3 := h2.upd hu j
    have e3w : σ3 P.w = γ := by simp only [σ3]; rw [upd_ne _ (by omega), e2w]
    have e3m : σ3 P.vm = m := by simp only [σ3]; rw [upd_ne _ (by omega), e2m]
    simp only [Ex.eval, e3w, show σ3 P.u = j by simp [σ3]]
    by_cases hlt : j < (γ : ℕ)
    · have hlt' : (⟨j, hj⟩ : Fin K) < γ := hlt
      rw [if_pos hlt, if_pos hlt', padF_r]
      set σ4 := Function.update σ3 (P.u + 1) γ
      have h4 : Ag B σ₀ σ4 := h3.upd (by omega) _
      have e4a : σ4 P.u = (⟨j, hj⟩ : Fin K) := by simp only [σ4]; rw [upd_ne _ (by omega)]; simp [σ3]
      have e4b : σ4 (P.u + 1) = γ := by simp [σ4]
      have e4m : σ4 P.vm = m := by simp only [σ4]; rw [upd_ne _ (by omega), e3m]
      unfold padR
      simp only [Ex.eval, H.rep.c σ4 h4 ⟨j, hj⟩ γ hlt' e4a e4b, H.LE σ4 h4]
      by_cases hcL : N.c ⟨j, hj⟩ γ ≤ L
      · rw [if_pos (by omega), dif_pos hcL]
        set q := Q / 2 ^ (L * j)
        have hq : Ex.eval σ4 A (blkQ P P.u) = q := by
          unfold blkQ
          simp only [Ex.eval, eval_pow2, H.LE σ4 h4, e4a]
          rw [show σ4 (P.w + 1) = Q by
            simp only [σ4, σ3]; rw [upd_ne _ (by omega), upd_ne _ (by omega), e2Q]]
        rw [hq]
        set σ5 := Function.update σ4 (P.u + 3) q
        have h5 : Ag B σ₀ σ5 := h4.upd (by omega) q
        have e5a : σ5 P.u = (⟨j, hj⟩ : Fin K) := by simp only [σ5]; rw [upd_ne _ (by omega), e4a]
        have e5b : σ5 (P.u + 1) = γ := by simp only [σ5]; rw [upd_ne _ (by omega), e4b]
        have e5z : σ5 (P.u + 2) = κ.e γ z := by
          simp only [σ5, σ4, σ3]; rw [upd_ne _ (by omega), upd_ne _ (by omega), upd_ne _ (by omega), e2z]
        have e5m : σ5 P.vm = m := by simp only [σ5]; rw [upd_ne _ (by omega), e4m]
        simp only [zmul, Ex.eval, e5m]
        rw [eval_unitE H h5 _ (H.rep.c σ5 h5 ⟨j, hj⟩ γ hlt' e5a e5b), show σ5 (P.u + 3) = q by simp [σ5]]
        exact pad_r_ZR _ hcL z q _ H.hm (H.rep.r σ5 h5 ⟨j, hj⟩ γ hlt' z q e5a e5b e5z (by simp [σ5, NVars.std]))
      · rw [if_neg (by omega), dif_neg hcL]
        exact ZR_zero (by omega)
    · have hlt' : ¬ (⟨j, hj⟩ : Fin K) < γ := hlt
      rw [if_neg hlt, if_neg hlt']
      exact ZR_one H.hm

end Proofs

end Factoring.Aux
