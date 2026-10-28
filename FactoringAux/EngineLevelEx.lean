/-
One level of the chain as expressions: from a table expression of a `(G², λ)`-clique, the table of `nextT` (the
smaller of the row and column networks of a choice code, grouped by its first good code, written out).

Layout (base `b`, the previous level's variables below `b`): `b` the choice code, `b+1` the next width `L'`
(grid context bound `b+2`), `b+2, b+3` the search variables, `b+4`, `b+5` the row and column grouping codes
(context bound `b+6`), grid arguments `b+6 …`, coarse arguments `b+52 …`, the new table's arguments `b+62`, `b+63`.

* `LevelEx.nextTE`, **`level_rep`**; `LevelEx.pre` (the `lett`s of `L'` and the two searches), **`eval_pre`**.

Not an audit surface.
-/
module

public import FactoringAux.EngineGroupEx

@[expose] public section

namespace Factoring.Aux

open Finset Ex

/-- The data of one level. -/
structure LP where
  /-- Base. -/
  b : ℕ
  /-- The modulus. -/
  vm : ℕ
  /-- The variable holding the table's width `λ`. -/
  vl : ℕ
  /-- The table's arguments. -/
  vγ : ℕ
  vΘ : ℕ
  /-- Groups and grid side (`G = 3K^8`). -/
  K : ℕ
  G : ℕ
  /-- The table. -/
  TE : Ex

namespace LevelEx

variable (P : LP)

def gp : GP := ⟨P.b + 6, P.vm, P.vl, P.b, P.vγ, P.vΘ, P.G, P.TE⟩

def gs (tr : Bool) : GS := ⟨P.b + 6, P.vm, if tr then P.b + 5 else P.b + 4, P.b + 1, P.G, P.K, GridEx.nex (gp P) tr⟩

/-- Half the total of the row (`false`) or column (`true`) network. -/
def UE (tr : Bool) : Ex :=
  nsum (P.b + 6) (.lit P.G) (nsum (P.b + 7) (.lit P.G)
    (.ifLt (.var (P.b + 6)) (.var (P.b + 7)) (GridEx.c (gp P) tr) (.lit 0)))

/-- The next table. -/
def nextTE : Ex := .ifLt (UE P false) (.add (UE P true) (.lit 1)) (GroupEx.tab (gs P false)) (GroupEx.tab (gs P true))

/-- `Lnext K G λ`. -/
def LnE : Ex :=
  .div (.add (.mul (.lit P.K) (.div (.add (.add (.mul (.lit (12 * P.G ^ 3)) (.var P.vl))
      (.mul (.lit (11 * P.G ^ 4)) (.var P.vl))) (.lit (24 * P.G ^ 4))) (.lit 12)))
    (.mul (.lit (P.G * P.G ^ 3)) (.var P.vl))) (.lit (P.K ^ 3))

/-- The `lett`s of a level before its body. -/
def pre (body : Ex) : Ex :=
  .lett (P.b + 1) (LnE P) (.lett (P.b + 4) (GroupEx.searchE (gs P false) (P.b + 2) (P.b + 3))
    (.lett (P.b + 5) (GroupEx.searchE (gs P true) (P.b + 2) (P.b + 3)) body))

end LevelEx

/-- Hypotheses of a level, on the context before it (variables below `b`). -/
structure LevelHyp (m BT : ℕ) (σ₀ : ℕ → ℕ) (A : ℕ → ℕ → ℕ) (P : LP) (lam : ℕ)
    (Tab : Clique (ZMod m) (P.G * P.G) lam) : Prop where
  hm : 1 < m
  hK : 2 ≤ P.K
  hG : P.G = 3 * P.K ^ 8
  rep : TRep m BT σ₀ A P.vγ P.vΘ P.TE Tab
  vm : σ₀ P.vm = m
  vl : σ₀ P.vl = lam
  hvm : P.vm < BT
  hγ : BT ≤ P.vγ
  hΘ : BT ≤ P.vΘ
  hγΘ : P.vγ ≠ P.vΘ
  hlγ : P.vl ≠ P.vγ
  hBT : BT ≤ P.b
  hl : P.vl < P.b
  hγb : P.vγ < P.b
  hΘb : P.vΘ < P.b

namespace LevelEx

variable {P : LP} {m BT lam : ℕ} {σ₀ : ℕ → ℕ} {A : ℕ → ℕ → ℕ} {Tab : Clique (ZMod m) (P.G * P.G) lam}

theorem gridHyp (H : LevelHyp m BT σ₀ A P lam Tab) {σ₁ : ℕ → ℕ} (h1 : Ag P.b σ₀ σ₁) {cc : ℕ} (hc : σ₁ P.b = cc) :
    GridEx.GridHyp m BT (P.b + 2) σ₁ A (gp P) lam cc Tab where
  hm := H.hm
  hg := by rw [show (gp P).g = P.G from rfl, H.hG]; have := H.hK; positivity
  rep := H.rep.congr (h1.mono H.hBT)
  vm := by rw [show (gp P).vm = P.vm from rfl, h1 _ (by have := H.hvm; have := H.hBT; omega), H.vm]
  vl := by rw [show (gp P).vl = P.vl from rfl, h1 _ H.hl, H.vl]
  vc := hc
  hvm := H.hvm
  hγ := H.hγ
  hΘ := H.hΘ
  hγΘ := H.hγΘ
  hlγ := H.hlγ
  hBT := by have := H.hBT; show BT ≤ P.b + 2; omega
  hl := by have := H.hl; show P.vl < P.b + 2; omega
  hc := by show P.b < P.b + 2; omega
  hγB := by have := H.hγb; show P.vγ < P.b + 2; omega
  hΘB := by have := H.hΘb; show P.vΘ < P.b + 2; omega
  hu := by show P.b + 2 ≤ P.b + 6; omega

theorem eval_UE {N : Net (ZMod m) P.G} {κ : Coding N} {B : ℕ} (tr : Bool)
    (h : NRep m P.vm B σ₀ A (NVars.std (P.b + 6)) (GridEx.nex (gp P) tr) N κ) (hB : B ≤ P.b + 6)
    {σ : ℕ → ℕ} (hσ : Ag B σ₀ σ) : eval σ A (UE P tr) = ∑ p ∈ pairs P.G, N.c p.1 p.2 := by
  rw [sum_pairs_range]
  unfold UE
  rw [eval_nsum]
  refine sum_congr rfl fun a ha => ?_
  rw [eval_nsum]
  refine sum_congr rfl fun a' ha' => ?_
  have ha2 : a < P.G := mem_range.mp ha
  have ha2' : a' < P.G := mem_range.mp ha'
  rw [dif_pos ⟨ha2, ha2'⟩, eval_ifLt']
  set σ2 := Function.update (Function.update σ (P.b + 6) a) (P.b + 7) a'
  have e6 : eval σ2 A (.var (P.b + 6)) = a := by simp only [Ex.eval, σ2]; upd
  have e7 : eval σ2 A (.var (P.b + 7)) = a' := by simp only [Ex.eval, σ2]; upd
  rw [e6, e7]
  split_ifs with hlt
  · exact h.c σ2 ((hσ.upd (by omega) a).upd (by omega) a') ⟨a, ha2⟩ ⟨a', ha2'⟩ hlt e6 e7
  · rfl

theorem level_rep (H : LevelHyp m BT σ₀ A P lam Tab) {cc : ℕ} (hcc : cc < (tB lam + 1) ^ (P.G * P.G * (P.G * P.G)))
    {σ₁ : ℕ → ℕ} (h1 : Ag P.b σ₀ σ₁) (hc : σ₁ P.b = cc) (hL : σ₁ (P.b + 1) = Lnext P.K P.G lam)
    (hr : σ₁ (P.b + 4) = firstGood (okG (rowNet (toGrid Tab) (restrictC ((phiEquiv P.G (tB lam)).symm ⟨cc, hcc⟩)))
      P.K (Lnext P.K P.G lam) (by have := H.hK; omega)) (P.K ^ P.G) (P.K ^ P.G))
    (hcl : σ₁ (P.b + 5) = firstGood (okG (colNet (toGrid Tab) (restrictC ((phiEquiv P.G (tB lam)).symm ⟨cc, hcc⟩)))
      P.K (Lnext P.K P.G lam) (by have := H.hK; omega)) (P.K ^ P.G) (P.K ^ P.G)) :
    TRep m (P.b + 6) σ₁ A (P.b + 62) (P.b + 63) (nextTE P) (nextT P.K (by have := H.hK; omega) Tab ⟨cc, hcc⟩) := by
  have Hg := gridHyp H h1 hc
  have hK0 : 0 < P.K := by have := H.hK; omega
  have hg : 0 < P.G := Hg.hg
  have hvm : P.vm < P.b + 6 := by have := H.hvm; have := H.hBT; omega
  have hr' : NRep m P.vm (P.b + 6) σ₁ A (NVars.std (P.b + 6)) (GridEx.nex (gp P) false)
      (rowNet (toGrid Tab) (restrictC ((phiEquiv P.G (tB lam)).symm ⟨cc, hcc⟩))) (rowCoding _ _) :=
    (GridEx.row_rep Hg hcc).mono (show P.b + 2 ≤ P.b + 6 by omega)
  have hc' : NRep m P.vm (P.b + 6) σ₁ A (NVars.std (P.b + 6)) (GridEx.nex (gp P) true)
      (colNet (toGrid Tab) (restrictC ((phiEquiv P.G (tB lam)).symm ⟨cc, hcc⟩))) (colCoding _ _) :=
    (GridEx.col_rep Hg hcc).mono (show P.b + 2 ≤ P.b + 6 by omega)
  intro σ hσ γ Q hγ hQ
  rw [nextTE, eval_ifLt', eval_UE false hr' le_rfl hσ]
  rw [show eval σ A (.add (UE P true) (.lit 1)) = eval σ A (UE P true) + 1 from rfl, eval_UE true hc' le_rfl hσ]
  unfold nextT
  rw [Net.total_eq, Net.total_eq]
  set Sr := ∑ p ∈ pairs P.G, (rowNet (toGrid Tab) (restrictC ((phiEquiv P.G (tB lam)).symm ⟨cc, hcc⟩))).c p.1 p.2
  set Sc := ∑ p ∈ pairs P.G, (colNet (toGrid Tab) (restrictC ((phiEquiv P.G (tB lam)).symm ⟨cc, hcc⟩))).c p.1 p.2
  by_cases h : Sr ≤ Sc
  · rw [if_pos (show Sr < Sc + 1 by omega), if_pos (show 2 * Sr ≤ 2 * Sc by omega)]
    exact GroupEx.group_rep (S := gs P false) hK0 hg H.hm hr' hvm (show P.b + 4 < P.b + 6 by omega)
      (show P.b + 1 < P.b + 6 by omega) le_rfl hr hL σ hσ γ Q hγ hQ
  · rw [if_neg (show ¬ Sr < Sc + 1 by omega), if_neg (show ¬ 2 * Sr ≤ 2 * Sc by omega)]
    exact GroupEx.group_rep (S := gs P true) hK0 hg H.hm hc' hvm (show P.b + 5 < P.b + 6 by omega)
      (show P.b + 1 < P.b + 6 by omega) le_rfl hcl hL σ hσ γ Q hγ hQ

theorem eval_LnE {σ : ℕ → ℕ} (hl : σ P.vl = lam) : eval σ A (LnE P) = Lnext P.K P.G lam := by
  simp only [LnE, Ex.eval, hl, Lnext, Umax]
  ring_nf

/-- **The `lett`s of a level** bind `L'` and the two first good codes. -/
theorem eval_pre (H : LevelHyp m BT σ₀ A P lam Tab) {cc : ℕ} (hcc : cc < (tB lam + 1) ^ (P.G * P.G * (P.G * P.G)))
    {σ₁ : ℕ → ℕ} (h1 : Ag P.b σ₀ σ₁) (hc : σ₁ P.b = cc) (body : Ex) :
    eval σ₁ A (pre P body) = eval (Function.update (Function.update (Function.update σ₁ (P.b + 1)
      (Lnext P.K P.G lam)) (P.b + 4)
      (firstGood (okG (rowNet (toGrid Tab) (restrictC ((phiEquiv P.G (tB lam)).symm ⟨cc, hcc⟩)))
        P.K (Lnext P.K P.G lam) (by have := H.hK; omega)) (P.K ^ P.G) (P.K ^ P.G))) (P.b + 5)
      (firstGood (okG (colNet (toGrid Tab) (restrictC ((phiEquiv P.G (tB lam)).symm ⟨cc, hcc⟩)))
        P.K (Lnext P.K P.G lam) (by have := H.hK; omega)) (P.K ^ P.G) (P.K ^ P.G))) A body := by
  have hK0 : 0 < P.K := by have := H.hK; omega
  have hvm : P.vm < P.b + 2 := by have := H.hvm; have := H.hBT; omega
  have hl1 : σ₁ P.vl = lam := by rw [h1 _ H.hl, H.vl]
  rw [pre, eval_lett, eval_LnE hl1, eval_lett]
  set σ2 := Function.update σ₁ (P.b + 1) (Lnext P.K P.G lam)
  have a2 : Ag P.b σ₀ σ2 := h1.upd (by omega) _
  have Hg2 := gridHyp H a2 (show σ2 P.b = cc by simp only [σ2]; upd; exact hc)
  have hr2 : NRep m P.vm (P.b + 2) σ2 A (NVars.std (P.b + 6)) (GridEx.nex (gp P) false)
      (rowNet (toGrid Tab) (restrictC ((phiEquiv P.G (tB lam)).symm ⟨cc, hcc⟩))) (rowCoding _ _) :=
    GridEx.row_rep Hg2 hcc
  rw [GroupEx.eval_searchE (S := gs P false) hK0 Hg2.hg H.hm hr2 hvm (show P.b + 1 < P.b + 2 by omega)
    (show P.b + 2 ≤ P.b + 2 by omega) (show P.b + 2 ≤ P.b + 3 by omega) (show P.b + 2 ≤ P.b + 4 by omega)
    (show P.b + 2 ≠ P.b + 3 by omega) (show P.b + 2 ≠ P.b + 4 by omega) (show P.b + 3 ≠ P.b + 4 by omega)
    (show P.b + 2 < P.b + 6 by omega) (show P.b + 3 < P.b + 6 by omega) (show P.b + 4 < P.b + 6 by omega)
    (show σ2 (P.b + 1) = Lnext P.K P.G lam by simp [σ2]) (Ag.refl _ _)]
  rw [eval_lett]
  set σ3 := Function.update σ2 (P.b + 4)
    (firstGood (okG (rowNet (toGrid Tab) (restrictC ((phiEquiv P.G (tB lam)).symm ⟨cc, hcc⟩)))
        P.K (Lnext P.K P.G lam) hK0) (P.K ^ P.G) (P.K ^ P.G))
  have a3 : Ag P.b σ₀ σ3 := a2.upd (by omega) _
  have Hg3 := gridHyp H a3 (show σ3 P.b = cc by simp only [σ3, σ2]; upd; exact hc)
  have hc3 : NRep m P.vm (P.b + 2) σ3 A (NVars.std (P.b + 6)) (GridEx.nex (gp P) true)
      (colNet (toGrid Tab) (restrictC ((phiEquiv P.G (tB lam)).symm ⟨cc, hcc⟩))) (colCoding _ _) :=
    GridEx.col_rep Hg3 hcc
  have hsc := GroupEx.eval_searchE (σ := σ3) (S := gs P true) hK0 Hg3.hg H.hm hc3 hvm (show P.b + 1 < P.b + 2 by omega)
    (show P.b + 2 ≤ P.b + 2 by omega) (show P.b + 2 ≤ P.b + 3 by omega) (show P.b + 2 ≤ P.b + 5 by omega)
    (show P.b + 2 ≠ P.b + 3 by omega) (show P.b + 2 ≠ P.b + 5 by omega) (show P.b + 3 ≠ P.b + 5 by omega)
    (show P.b + 2 < P.b + 6 by omega) (show P.b + 3 < P.b + 6 by omega) (show P.b + 5 < P.b + 6 by omega)
    (show σ3 (P.b + 1) = Lnext P.K P.G lam by simp only [σ3, σ2]; upd) (Ag.refl _ _)
  exact congrArg (fun v => eval (Function.update σ3 (P.b + 5) v) A body) hsc

end LevelEx

end Factoring.Aux
