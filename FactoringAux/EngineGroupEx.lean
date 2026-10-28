/-
The group step as expressions: from expressions representing a coded network on `g` nodes, the search for the first
good grouping code (`searchE`, **`eval_searchE`**) and the written-out clique of the grouped network
(**`group_rep`**, from `coarsen_rep` and `clique_rep`).

Layout (inner arguments `u … u+3`, the inner expressions use variables below `u + 45`): grouping loop variable
`u+45`, coarse arguments `u+46 … u+49` (scratch `u+50 … u+53`), the clique table's arguments `u+56`, `u+57`
(scratch `u+58`, `u+59`); the group-size loop uses `u+54`.

Not an audit surface.
-/
module

public import FactoringAux.EngineGroup
public import FactoringAux.EngineGridEx

@[expose] public section

namespace Factoring.Aux

open Finset Ex

/-! ### Changing the context of a representation -/

theorem NRep.mono {m vm B B' : ℕ} {σ₀ : ℕ → ℕ} {A : ℕ → ℕ → ℕ} {v : NVars} {E : NEx} {g : ℕ}
    {N : Net (ZMod m) g} {κ : Coding N} (h : NRep m vm B σ₀ A v E N κ) (hB : B ≤ B') :
    NRep m vm B' σ₀ A v E N κ where
  hm := h.hm
  sz σ hσ := h.sz σ (hσ.mono hB)
  W σ hσ := h.W σ (hσ.mono hB)
  c σ hσ := h.c σ (hσ.mono hB)
  l σ hσ := h.l σ (hσ.mono hB)
  r σ hσ := h.r σ (hσ.mono hB)

theorem NRep.congr {m vm B : ℕ} {σ₀ σ₀' : ℕ → ℕ} {A : ℕ → ℕ → ℕ} {v : NVars} {E : NEx} {g : ℕ}
    {N : Net (ZMod m) g} {κ : Coding N} (h : NRep m vm B σ₀ A v E N κ) (hvm : vm < B) (hσ : Ag B σ₀ σ₀') :
    NRep m vm B σ₀' A v E N κ where
  hm := by rw [hσ vm hvm, h.hm]
  sz σ h' := h.sz σ fun y hy => (h' y hy).trans (hσ y hy)
  W σ h' := h.W σ fun y hy => (h' y hy).trans (hσ y hy)
  c σ h' := h.c σ fun y hy => (h' y hy).trans (hσ y hy)
  l σ h' := h.l σ fun y hy => (h' y hy).trans (hσ y hy)
  r σ h' := h.r σ fun y hy => (h' y hy).trans (hσ y hy)

theorem TRep.congr {m B : ℕ} {σ₀ σ₀' : ℕ → ℕ} {A : ℕ → ℕ → ℕ} {vγ vΘ : ℕ} {T : Ex} {K L : ℕ}
    {Tab : Clique (ZMod m) K L} (h : TRep m B σ₀ A vγ vΘ T Tab) (hσ : Ag B σ₀ σ₀') : TRep m B σ₀' A vγ vΘ T Tab :=
  fun σ h' => h σ fun y hy => (h' y hy).trans (hσ y hy)

theorem TRep.mono {m B B' : ℕ} {σ₀ : ℕ → ℕ} {A : ℕ → ℕ → ℕ} {vγ vΘ : ℕ} {T : Ex} {K L : ℕ}
    {Tab : Clique (ZMod m) K L} (h : TRep m B σ₀ A vγ vΘ T Tab) (hB : B ≤ B') : TRep m B' σ₀ A vγ vΘ T Tab :=
  fun σ h' => h σ (h'.mono hB)

/-! ### The expressions -/

/-- The data of a group step. -/
structure GS where
  /-- Inner argument base. -/
  u : ℕ
  /-- The modulus. -/
  vm : ℕ
  /-- The variable holding the grouping code. -/
  vχ : ℕ
  /-- The variable holding the label width `L`. -/
  vL : ℕ
  /-- Nodes, groups. -/
  g : ℕ
  K : ℕ
  /-- The inner expressions. -/
  E : NEx

namespace GroupEx

variable (S : GS)

/-- Digit `var u` of the grouping code (radix `K`). -/
def chiE : Ex := .mod (.div (.var S.vχ) (.prod (S.u + 45) (.var S.u) (.lit 0) (.lit S.K))) (.lit S.K)

/-- The coarsening data. -/
def Pc : CP := ⟨S.u, S.u + 46, S.vm, S.E, .lit S.g, chiE S⟩

/-- The clique data. -/
def Pk : KP := ⟨S.u + 46, S.u + 56, S.vm, CoarsenEx.nex (Pc S), .lit S.K, .var S.vL⟩

/-- `1` iff the code in `vχ` is good. -/
def okE : Ex :=
  .mul (nprod (S.u + 54) (.lit S.K)
      (.ifLt (.mul (.lit S.K) (nsum S.u (.lit S.g) (ifEq (chiE S) (.var (S.u + 54)) (.lit 1) (.lit 0))))
        (.lit (2 * S.g + 1)) (.lit 1) (.lit 0)))
    (nprod (S.u + 46) (.lit S.K) (nprod (S.u + 47) (.lit S.K)
      (.ifLt (.var (S.u + 46)) (.var (S.u + 47))
        (.ifLt (CoarsenEx.c (Pc S)) (.add (.var S.vL) (.lit 1)) (.lit 1) (.lit 0)) (.lit 1))))

/-- The first good code (candidate `vx`, state `vs`). -/
def searchE (vx vs : ℕ) : Ex :=
  .iter vx vs (.lit (S.K ^ S.g)) (.lit (S.K ^ S.g))
    (ifEq (.var vs) (.lit (S.K ^ S.g)) (.lett S.vχ (.var vx) (ifEq (okE S) (.lit 1) (.var vx) (.var vs))) (.var vs))

/-- The table of the grouped network, written out (arguments `u+56`, `u+57`). -/
def tab : Ex := CliqueEx.tab (Pk S)

end GroupEx

theorem pp_indic (P : ℕ → Prop) [DecidablePred P] : ∀ n, pp (fun i => if P i then 1 else 0) n = if ∀ i < n, P i then 1 else 0
  | 0 => by simp [pp]
  | n + 1 => by
      simp only [pp, pp_indic P n]
      have key : (∀ i < n + 1, P i) ↔ (∀ i < n, P i) ∧ P n :=
        ⟨fun h => ⟨fun i hi => h i (by omega), h n (by omega)⟩, fun ⟨h1, h2⟩ i hi => by
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
          exacts [h1 i hi, h2]⟩
      split_ifs <;> simp_all

namespace GroupEx

variable {S : GS} {m B : ℕ} {σ₀ : ℕ → ℕ} {A : ℕ → ℕ → ℕ} {N : Net (ZMod m) S.g} {κ : Coding N}

theorem eval_chiE {σ : ℕ → ℕ} : eval σ A (chiE S) = σ S.vχ / S.K ^ σ S.u % S.K := by
  simp only [chiE, Ex.eval, foldProd_zero]
  rw [pp_const]

theorem coarsenHyp (hK : 0 < S.K) (hg : 0 < S.g) (hm : 1 < m) (h : NRep m S.vm B σ₀ A (NVars.std S.u) S.E N κ)
    (hχ : S.vχ < B) (hu : B ≤ S.u) {x : ℕ} (hx : σ₀ S.vχ = x) :
    CoarsenHyp m B σ₀ A (Pc S) N κ (chiOf S.K S.g x hK) where
  rep := h
  hg := hg
  gE _ _ := rfl
  χE σ hσ a ha := by
    show eval σ A (chiE S) = _
    rw [eval_chiE, hσ _ hχ, hx, show σ S.u = a from ha]
    rfl
  hu := hu
  hw := by simp [Pc]
  hm := hm

theorem card_chiOf {K g : ℕ} (hK : 0 < K) (x : ℕ) (γ : Fin K) :
    (univ.filter (fun a : Fin g => chiOf K g x hK a = γ)).card =
      ∑ a ∈ range g, if x / K ^ a % K = γ then 1 else 0 := by
  rw [Finset.card_filter, ← Fin.sum_univ_eq_sum_range (fun a => if x / K ^ a % K = (γ : ℕ) then 1 else 0)]
  refine sum_congr rfl fun a _ => ?_
  simp only [chiOf, Fin.ext_iff]

theorem eval_okE (hK : 0 < S.K) (hg : 0 < S.g) (hm : 1 < m) (h : NRep m S.vm B σ₀ A (NVars.std S.u) S.E N κ)
    (hχ : S.vχ < B) (hL : S.vL < B) (hu : B ≤ S.u) {x L : ℕ} (hx : σ₀ S.vχ = x) (hLσ : σ₀ S.vL = L)
    {σ : ℕ → ℕ} (hσ : Ag B σ₀ σ) :
    eval σ A (okE S) = if okG N S.K L hK x then 1 else 0 := by
  have H := coarsenHyp hK hg hm h hχ hu hx
  unfold okE
  rw [Ex.eval, eval_nprod, eval_nprod]
  have e1 : pp (fun γ => eval (Function.update σ (S.u + 54) γ) A
      (.ifLt (.mul (.lit S.K) (nsum S.u (.lit S.g) (ifEq (chiE S) (.var (S.u + 54)) (.lit 1) (.lit 0))))
        (.lit (2 * S.g + 1)) (.lit 1) (.lit 0))) S.K =
      if ∀ γ < S.K, S.K * (∑ a ∈ range S.g, if x / S.K ^ a % S.K = γ then 1 else 0) < 2 * S.g + 1 then 1 else 0 := by
    rw [← pp_indic]
    refine pp_congr fun γ _ => ?_
    rw [eval_ifLt']
    simp only [Ex.eval, eval_nsum]
    congr 2
    congr 1
    refine sum_congr rfl fun a _ => ?_
    rw [eval_ifEq, eval_chiE]
    simp only [Ex.eval]
    upd
    rw [hσ _ hχ, hx]
  have e2 : pp (fun γ => eval (Function.update σ (S.u + 46) γ) A (nprod (S.u + 47) (.lit S.K)
      (.ifLt (.var (S.u + 46)) (.var (S.u + 47))
        (.ifLt (CoarsenEx.c (Pc S)) (.add (.var S.vL) (.lit 1)) (.lit 1) (.lit 0)) (.lit 1)))) S.K =
      if ∀ γ < S.K, ∀ γ' < S.K, γ < γ' → (if hh : γ < S.K ∧ γ' < S.K then
        (N.coarsen (chiOf S.K S.g x hK)).c ⟨γ, hh.1⟩ ⟨γ', hh.2⟩ else 0) < L + 1 then 1 else 0 := by
    rw [← pp_indic]
    refine pp_congr fun γ hγ => ?_
    rw [eval_nprod, ← pp_indic]
    refine pp_congr fun γ' hγ' => ?_
    replace hγ' : γ' < S.K := hγ'
    set σ2 := Function.update (Function.update σ (S.u + 46) γ) (S.u + 47) γ'
    have eγ : eval σ2 A (.var (S.u + 46)) = γ := by simp only [Ex.eval, σ2]; upd
    have eγ' : eval σ2 A (.var (S.u + 47)) = γ' := by simp only [Ex.eval, σ2]; upd
    have eL : eval σ2 A (.add (.var S.vL) (.lit 1)) = L + 1 := by
      simp only [Ex.eval, σ2]; upd; rw [hσ _ hL, hLσ]
    rw [eval_ifLt', eγ, eγ']
    by_cases hlt : γ < γ'
    · rw [if_pos hlt, eval_ifLt', coarsen_c H (σ := σ2)
        ((hσ.upd (show B ≤ S.u + 46 by omega) γ).upd (show B ≤ S.u + 46 + 1 by omega) γ')
        ⟨γ, hγ⟩ ⟨γ', hγ'⟩ (show σ2 (S.u + 46) = γ from eγ) (show σ2 (S.u + 46 + 1) = γ' from eγ'), eL]
      simp only [dif_pos (show γ < S.K ∧ γ' < S.K from ⟨hγ, hγ'⟩)]
      by_cases hc : (N.coarsen (chiOf S.K S.g x hK)).c ⟨γ, hγ⟩ ⟨γ', hγ'⟩ < L + 1
      · simp [hc, Ex.eval]
      · simp [hc, hlt, Ex.eval]
    · rw [if_neg hlt]; simp [hlt, Ex.eval]
  rw [show eval σ A (.lit S.K) = S.K from rfl, e1, e2]
  have k1 : (∀ γ < S.K, S.K * (∑ a ∈ range S.g, if x / S.K ^ a % S.K = γ then 1 else 0) < 2 * S.g + 1) ↔
      ∀ γ : Fin S.K, S.K * (univ.filter (fun a => chiOf S.K S.g x hK a = γ)).card ≤ 2 * S.g :=
    ⟨fun h γ => by rw [card_chiOf]; exact Nat.lt_succ_iff.mp (h γ γ.2),
     fun h γ hγ => Nat.lt_succ_iff.mpr (by have := h ⟨γ, hγ⟩; rwa [card_chiOf] at this)⟩
  have k2 : (∀ γ < S.K, ∀ γ' < S.K, γ < γ' → (if hh : γ < S.K ∧ γ' < S.K then
        (N.coarsen (chiOf S.K S.g x hK)).c ⟨γ, hh.1⟩ ⟨γ', hh.2⟩ else 0) < L + 1) ↔
      ∀ γ γ' : Fin S.K, γ < γ' → (N.coarsen (chiOf S.K S.g x hK)).c γ γ' ≤ L :=
    ⟨fun h γ γ' hlt => by
      have := h γ γ.2 γ' γ'.2 hlt; rw [dif_pos ⟨γ.2, γ'.2⟩] at this; simp only [Fin.eta] at this; omega,
     fun h γ hγ γ' hγ' hlt => by rw [dif_pos ⟨hγ, hγ'⟩]; have := h ⟨γ, hγ⟩ ⟨γ', hγ'⟩ hlt; omega⟩
  unfold okG
  simp only [k1, k2]
  by_cases a1 : ∀ γ : Fin S.K, S.K * (univ.filter (fun a => chiOf S.K S.g x hK a = γ)).card ≤ 2 * S.g
  · by_cases a2 : ∀ γ γ' : Fin S.K, γ < γ' → (N.coarsen (chiOf S.K S.g x hK)).c γ γ' ≤ L
    · rw [if_pos a1, if_pos a2]; exact (if_pos ⟨a1, a2⟩).symm
    · rw [if_pos a1, if_neg a2]; exact (if_neg (fun h => a2 h.2)).symm
  · rw [if_neg a1, zero_mul]; exact (if_neg (fun h => a1 h.1)).symm

theorem eval_searchE (hK : 0 < S.K) (hg : 0 < S.g) (hm : 1 < m) {B0 : ℕ}
    (h : NRep m S.vm B0 σ₀ A (NVars.std S.u) S.E N κ) (hvm : S.vm < B0) (hL : S.vL < B0) {vx vs L : ℕ}
    (h1 : B0 ≤ vx) (h2 : B0 ≤ vs) (h3 : B0 ≤ S.vχ) (d1 : vx ≠ vs) (d2 : vx ≠ S.vχ) (d3 : vs ≠ S.vχ)
    (u1 : vx < S.u) (u2 : vs < S.u) (u3 : S.vχ < S.u) (hLσ : σ₀ S.vL = L) {σ : ℕ → ℕ} (hσ : Ag B0 σ₀ σ) :
    eval σ A (searchE S vx vs) = firstGood (okG N S.K L hK) (S.K ^ S.g) (S.K ^ S.g) := by
  rw [searchE, eval_iter]
  show iterF _ (S.K ^ S.g) (S.K ^ S.g) = _
  unfold firstGood
  congr 1
  funext x st
  rw [eval_ifEq]
  have es : eval (Function.update (Function.update σ vx x) vs st) A (.var vs) = st := by simp [Ex.eval]
  rw [es]
  unfold fgStep
  set σ2 := Function.update (Function.update (Function.update σ vx x) vs st) S.vχ x
  have a2 : Ag B0 σ₀ σ2 := ((hσ.upd h1 x).upd h2 st).upd h3 x
  have hrep := (h.congr hvm a2).mono (show B0 ≤ S.u by omega)
  have hok := eval_okE (B := S.u) (σ₀ := σ2) (σ := σ2) (x := x) (L := L) hK hg hm hrep u3 (by omega) le_rfl
    (by simp [σ2]) (by rw [a2 _ hL, hLσ]) (Ag.refl _ _)
  rw [show eval (Function.update (Function.update σ vx x) vs st) A (.lit (S.K ^ S.g)) = S.K ^ S.g from rfl]
  by_cases hs : st = S.K ^ S.g
  · rw [if_pos hs, eval_lett]
    have ex : eval (Function.update (Function.update σ vx x) vs st) A (.var vx) = x := by
      simp [Ex.eval, Function.update_of_ne d1]
    rw [ex, eval_ifEq, hok]
    have ex2 : eval σ2 A (.var vx) = x := by simp [σ2, Ex.eval, Function.update_of_ne d2, Function.update_of_ne d1]
    have es2 : eval σ2 A (.var vs) = st := by simp [σ2, Ex.eval, Function.update_of_ne d3]
    rw [ex2, es2]
    by_cases ho : okG N S.K L hK x
    · simp [ho, hs, Ex.eval]
    · simp [ho, hs, Ex.eval]
  · rw [if_neg hs]; simp [hs]

/-- **The grouped network, written out**, for any grouping code `x` in `vχ`. -/
theorem group_rep (hK : 0 < S.K) (hg : 0 < S.g) (hm : 1 < m) (h : NRep m S.vm B σ₀ A (NVars.std S.u) S.E N κ)
    (hvm : S.vm < B) (hχ : S.vχ < B) (hL : S.vL < B) (hu : B ≤ S.u) {x L : ℕ} (hx : σ₀ S.vχ = x)
    (hLσ : σ₀ S.vL = L) :
    TRep m B σ₀ A (S.u + 56) (S.u + 57) (tab S) ((N.coarsen (chiOf S.K S.g x hK)).toClique L) :=
  clique_rep (P := Pk S) (B := B) (L := L)
    { rep := coarsen_rep (coarsenHyp hK hg hm h hχ hu hx) hvm
      kE := fun _ _ => rfl
      LE := fun σ hσ => by show σ S.vL = L; rw [hσ _ hL, hLσ]
      hu := by show B ≤ S.u + 46; omega
      hw := by show S.u + 46 + 4 ≤ S.u + 56; omega
      hm := hm
      hvm := hvm }

end GroupEx

end Factoring.Aux
