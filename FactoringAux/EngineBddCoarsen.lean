/-
Value bounds of the coarsened network's expressions (`CoarsenEx.nex`).

* `coarsenC_bdd`: the coarse widths (used again by the group search), from the inner widths' bounds and the coarse
  width `≤ V`.
* **`coarsen_bdd`**: `NBdd` of `CoarsenEx.nex P` (arguments `P.w …`, `K` groups) from `NBdd` of the inner expressions
  and the hypotheses of `CoarsenBddHyp`.

Not an audit surface.
-/
module

public import FactoringAux.EngineBddBase

@[expose] public section

namespace Factoring.Aux

open Finset Ex SB CoarsenEx

theorem pp_mono_le {f : ℕ → ℕ} (hf : ∀ i, 0 < f i) {j : ℕ} : ∀ {n : ℕ}, j ≤ n → pp f j ≤ pp f n
  | 0, h => by rw [Nat.le_zero.mp h]
  | n + 1, h => by
      rcases Nat.lt_or_ge j (n + 1) with h' | h'
      · have := pp_mono_le hf (j := j) (n := n) (show j ≤ n by omega)
        simp only [pp]
        exact le_trans this (Nat.le_mul_of_pos_right _ (hf n))
      · rw [show j = n + 1 by omega]

theorem B_nprodV {V : ℕ} {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ} {x : ℕ} {n b : Ex} (hn : Bdd V σ A n)
    (hb : ∀ j < eval σ A n, Bdd V (Function.update σ x j) A b)
    (hV : ∀ j ≤ eval σ A n, pp (fun i => eval (Function.update σ x i) A b) j ≤ V) : Bdd V σ A (nprod x n b) :=
  ⟨hn, Nat.zero_le V, hb, fun j hj => by change foldProd _ 0 j ≤ V; rw [foldProd_zero]; exact hV j hj⟩

theorem offR_mono_le {ι : Type*} (c : ι → ℕ) (P : ι → Prop) [DecidablePred P] (f : ℕ → ι) {j n : ℕ} (h : j ≤ n) :
    offR c P f j ≤ offR c P f n :=
  Finset.sum_le_sum_of_subset (range_subset_range.mpr h)

section Coarse

variable {V m B g K : ℕ} {σ₀ : ℕ → ℕ} {A : ℕ → ℕ → ℕ} {P : CP} {N : Net (ZMod m) g} {κ : Coding N}
  {χ : Fin g → Fin K}

theorem sg_self {γ : Fin K} {a : Fin g} (h : χ a = γ) : κ.sg χ γ a = κ.s a := Coding.sg_mem κ χ γ h

theorem digE_le {σ : ℕ → ℕ} (grp : ℕ) : eval σ A (digE P grp) ≤ σ (P.w + 2) := by
  simp only [digE, Ex.eval]
  exact le_trans (Nat.mod_le _ _) (Nat.div_le_self _ _)

theorem digB_le {σ : ℕ → ℕ} (hw : P.u + 4 ≤ P.w) (grp : ℕ) : eval σ A (digB P grp) ≤ σ (P.w + 2) := by
  simp only [digB]
  rw [eval_lett]
  refine le_trans (digE_le grp) ?_
  rw [Function.update_of_ne (by omega)]

theorem digE_lt (H : CoarsenHyp m B σ₀ A P N κ χ) {σ : ℕ → ℕ} (hσ : Ag B σ₀ σ) {grp : ℕ} (hgrp : grp ≠ P.u)
    (γ : Fin K) (hγ : σ grp = γ) (a : Fin g) (ha : σ P.u = a) (hχ : χ a = γ) :
    eval σ A (digE P grp) < κ.s a := by
  rw [eval_digE H hσ hgrp γ hγ a ha, ← sg_self hχ]
  exact dgx_lt (Coding.sg_pos κ χ γ a) _

theorem digB_lt (H : CoarsenHyp m B σ₀ A P N κ χ) {σ : ℕ → ℕ} (hσ : Ag B σ₀ σ) {grp : ℕ} (hgrp : grp ≠ P.u)
    (γ : Fin K) (hγ : σ grp = γ) (b : Fin g) (hb : σ (P.u + 1) = b) (hχ : χ b = γ) :
    eval σ A (digB P grp) < κ.s b := by
  simp only [digB]
  rw [eval_lett]
  exact digE_lt H (hσ.upd H.hu _) hgrp γ (by rw [Function.update_of_ne hgrp, hγ]) b (by simp [Ex.eval, hb]) hχ

variable (H : CoarsenHyp m B σ₀ A P N κ χ) (hE : NBdd V B σ₀ A (NVars.std P.u) P.E g)
  (hχE : ∀ σ, Ag B σ₀ σ → σ P.u < g → Bdd V σ A P.χE)
include H hχE

theorem B_chiB {σ : ℕ → ℕ} (hσ : Ag B σ₀ σ) (hb : σ (P.u + 1) < g) (hbV : σ (P.u + 1) ≤ V) :
    Bdd V σ A (chiB P) :=
  B_lett (B_var hbV) (hχE _ (hσ.upd H.hu _) (by simp [Ex.eval]; exact hb))

theorem B_usedE {σ : ℕ → ℕ} (hσ : Ag B σ₀ σ) (ha : σ P.u < g) (hb : σ (P.u + 1) < g) (hgV : g ≤ V)
    (h1 : σ P.w ≤ V) (h2 : σ (P.w + 1) ≤ V) : Bdd V σ A (usedE P) := by
  have hV1 : 1 ≤ V := by omega
  have Ba := hχE σ hσ ha
  have Bb := B_chiB H hχE hσ hb (by omega)
  have L1 : Bdd V σ A (.lit 1) := B_lit hV1
  have L0 : Bdd V σ A (.lit 0) := B_lit (Nat.zero_le _)
  have W1 : Bdd V σ A (.var P.w) := B_var h1
  have W2 : Bdd V σ A (.var (P.w + 1)) := B_var h2
  unfold usedE crossE
  exact B_ifLt' (B_var (by omega)) (B_var (by omega))
    (fun _ => B_ifEq Ba W1 (B_ifEq Bb W2 L1 (B_ifEq Ba W2 (B_ifEq Bb W1 L1 L0) L0)) (B_ifEq Ba W2 (B_ifEq Bb W1 L1 L0) L0))
    (fun _ => L0)

include hE

omit H in
theorem B_sgE {σ : ℕ → ℕ} (hσ : Ag B σ₀ σ) (hV1 : 1 ≤ V) {grp : ℕ} (hg : σ grp ≤ V) (hu : σ P.u < g) :
    Bdd V σ A (sgE P grp) :=
  B_ifEq (hχE σ hσ hu) (B_var hg) (hE.sz σ hσ hu) (B_lit hV1)

theorem B_ppE (hsz : ∀ γ : Fin K, (κ.coarsen χ).s γ ≤ V) (hgV : g ≤ V) {σ : ℕ → ℕ} (hσ : Ag B σ₀ σ) {grp : ℕ}
    (hgrp : grp ≠ P.u) (γ : Fin K) (hγ : σ grp = γ) (hγV : (γ : ℕ) ≤ V) (hu : σ P.u < g) :
    Bdd V σ A (ppE P grp) := by
  have hV1 : 1 ≤ V := by omega
  have hupd : ∀ i, Function.update σ P.u i grp = γ := fun i => by rw [Function.update_of_ne hgrp, hγ]
  unfold ppE
  refine B_nprodV (B_var (by omega)) (fun j hj => B_sgE hE hχE (hσ.upd H.hu _) hV1 (by rw [hupd]; exact hγV)
    (by simp only [Function.update_self]; simp only [Ex.eval] at hj; omega)) fun j hj => ?_
  simp only [Ex.eval] at hj
  have e : pp (fun i => eval (Function.update σ P.u i) A (sgE P grp)) j = pp (κ.sg χ γ) j :=
    pp_congr fun i hi => eval_sgE H (hσ.upd H.hu i) γ (hupd i) ⟨i, by omega⟩ (by simp)
  rw [e]
  refine le_trans (pp_mono_le (Coding.sg_pos κ χ γ) (show j ≤ g by omega)) ?_
  have := hsz γ
  simp only [Coding.coarsen, dif_pos γ.2, Fin.eta] at this
  exact this

theorem B_digE (hsz : ∀ γ : Fin K, (κ.coarsen χ).s γ ≤ V) (hgV : g ≤ V) {σ : ℕ → ℕ} (hσ : Ag B σ₀ σ) {grp : ℕ}
    (hgrp : grp ≠ P.u) (γ : Fin K) (hγ : σ grp = γ) (hγV : (γ : ℕ) ≤ V) (hu : σ P.u < g) (hz : σ (P.w + 2) ≤ V) :
    Bdd V σ A (digE P grp) :=
  B_mod (B_div (B_var hz) (B_ppE H hE hχE hsz hgV hσ hgrp γ hγ hγV hu))
    (B_sgE hE hχE hσ (by omega) (by rw [hγ]; exact hγV) hu)

/-- The member's left factor function, read at its digit of the group code. -/
theorem B_digL (hsz : ∀ γ : Fin K, (κ.coarsen χ).s γ ≤ V) (hgV : g ≤ V) {σ : ℕ → ℕ} (hσ : Ag B σ₀ σ) {grp : ℕ}
    (hgrp : P.w ≤ grp) (γ : Fin K) (hγ : σ grp = γ) (hγV : (γ : ℕ) ≤ V) (hab : σ P.u < σ (P.u + 1))
    (hb : σ (P.u + 1) < g) (hz : σ (P.w + 2) ≤ V) (hq : σ (P.u + 3) ≤ V) :
    Bdd V σ A (.lett (P.u + 2) (digE P grp) P.E.l) := by
  have hu := H.hu; have hw := H.hw
  refine B_lett (B_digE H hE hχE hsz hgV hσ (by omega) γ hγ hγV (by omega) hz) ?_
  refine hE.l _ (hσ.upd (by omega) _) ?_ ?_ ?_ ?_ <;> simp only [NVars.std] <;> upd
  · exact hab
  · exact hb
  · exact le_trans (digE_le grp) hz
  · exact hq

/-- The member's right factor function, read at its digit of the group code. -/
theorem B_digR (hsz : ∀ γ : Fin K, (κ.coarsen χ).s γ ≤ V) (hgV : g ≤ V) {σ : ℕ → ℕ} (hσ : Ag B σ₀ σ) {grp : ℕ}
    (hgrp : P.w ≤ grp) (γ : Fin K) (hγ : σ grp = γ) (hγV : (γ : ℕ) ≤ V) (hab : σ P.u < σ (P.u + 1))
    (hb : σ (P.u + 1) < g) (hz : σ (P.w + 2) ≤ V) (hq : σ (P.u + 3) ≤ V) :
    Bdd V σ A (.lett (P.u + 2) (digB P grp) P.E.r) := by
  have hu := H.hu; have hw := H.hw
  refine B_lett (B_lett (B_var (by omega)) (B_digE H hE hχE hsz hgV (hσ.upd hu _) (by omega) γ
    (by upd; exact hγ) hγV (by simp only [Ex.eval]; upd; exact hb) (by upd; exact hz))) ?_
  refine hE.r _ (hσ.upd (by omega) _) ?_ ?_ ?_ ?_ <;> simp only [NVars.std] <;> upd
  · exact hab
  · exact hb
  · exact le_trans (digB_le hw grp) hz
  · exact hq

omit hE in
/-- The sum of the widths of the used pairs below `n`. -/
theorem B_usedSum (hgE : ∀ σ, Ag B σ₀ σ → Bdd V σ A P.gE) (hEc : ∀ σ, Ag B σ₀ σ → σ P.u < σ (P.u + 1) → σ (P.u + 1) < g → Bdd V σ A P.E.c)
    (hgg : g * g ≤ V) {σ : ℕ → ℕ} (hσ : Ag B σ₀ σ) (γ γ' : Fin K) (hγ : σ P.w = γ) (hγ' : σ (P.w + 1) = γ')
    (hcV : (N.coarsen χ).c γ γ' ≤ V) (hKV : K ≤ V) (kv : ℕ) (hkv : P.w + 4 ≤ kv) {n : Ex} (hn : Bdd V σ A n)
    (hnv : eval σ A n ≤ g * g) :
    Bdd V σ A (nsum kv n (atPair P kv (ifEq (usedE P) (.lit 1) P.E.c (.lit 0)))) := by
  have hu := H.hu; have hw := H.hw; have hg := H.hg
  have hgV : g ≤ V := le_trans (Nat.le_mul_of_pos_left g hg) hgg
  refine ⟨hn, Nat.zero_le V, fun j hj => ?_, fun j hj => ?_⟩
  · set σ1 := Function.update σ kv j
    have a1 : Ag B σ₀ σ1 := hσ.upd (by omega) j
    have e1 : σ1 kv = j := by simp [σ1]
    unfold atPair
    refine B_lett (B_mod (B_div (B_var (by rw [e1]; omega)) (hgE σ1 a1)) (hgE σ1 a1)) ?_
    rw [show eval σ1 A (.mod (.div (.var kv) P.gE) P.gE) = j / g % g by simp only [Ex.eval, H.gE σ1 a1, e1]]
    set σ2 := Function.update σ1 P.u (j / g % g)
    have a2 : Ag B σ₀ σ2 := a1.upd hu _
    have e2 : σ2 kv = j := by simp only [σ2]; upd; exact e1
    refine B_lett (B_mod (B_var (by rw [e2]; omega)) (hgE σ2 a2)) ?_
    rw [show eval σ2 A (.mod (.var kv) P.gE) = j % g by simp only [Ex.eval, H.gE σ2 a2, e2]]
    set σ3 := Function.update σ2 (P.u + 1) (j % g)
    have a3 : Ag B σ₀ σ3 := a2.upd (by omega) _
    have ea : σ3 P.u = (Net.pairOf g hg j).1 := by simp only [σ3, σ2]; upd; rfl
    have eb : σ3 (P.u + 1) = (Net.pairOf g hg j).2 := by simp only [σ3]; upd; rfl
    have ew : σ3 P.w = γ := by simp only [σ3, σ2, σ1]; upd; exact hγ
    have ew' : σ3 (P.w + 1) = γ' := by simp only [σ3, σ2, σ1]; upd; exact hγ'
    refine B_ifEq' (B_usedE H hχE a3 (by rw [ea]; exact Fin.isLt _) (by rw [eb]; exact Fin.isLt _) hgV
      (by rw [ew]; omega) (by rw [ew']; omega)) (B_lit (by omega)) (fun hU => ?_) (fun _ => B_lit (Nat.zero_le _))
    rw [eval_usedE H a3 γ γ' ew ew' _ _ ea eb] at hU
    have hU' : Net.UsedP χ γ γ' (Net.pairOf g hg j) := by
      by_contra h; rw [if_neg h] at hU; simp [Ex.eval] at hU
    exact hEc σ3 a3 (by rw [ea, eb]; exact hU'.1) (by rw [eb]; exact Fin.isLt _)
  · change foldSum _ 0 j ≤ V
    have := eval_usedSum H hσ γ γ' hγ hγ' kv hkv (.lit j)
    change foldSum _ 0 j = _ at this
    rw [this]
    refine le_trans (offR_mono_le _ _ _ (show j ≤ g * g by omega)) ?_
    rw [← Net.coarsen_c_code N hg χ γ γ']
    exact hcV

omit hE in
/-- **The coarse widths.** -/
theorem coarsenC_bdd (hgE : ∀ σ, Ag B σ₀ σ → Bdd V σ A P.gE) (hEc : ∀ σ, Ag B σ₀ σ → σ P.u < σ (P.u + 1) → σ (P.u + 1) < g → Bdd V σ A P.E.c)
    (hgg : g * g ≤ V) (hKV : K ≤ V) {σ : ℕ → ℕ} (hσ : Ag B σ₀ σ) (γ γ' : Fin K) (hγ : σ P.w = γ)
    (hγ' : σ (P.w + 1) = γ') (hcV : (N.coarsen χ).c γ γ' ≤ V) : Bdd V σ A (CoarsenEx.c P) := by
  unfold CoarsenEx.c
  refine B_usedSum H hχE hgE hEc hgg hσ γ γ' hγ hγ' hcV hKV (P.w + 4) le_rfl ⟨hgE σ hσ, hgE σ hσ, ?_⟩ ?_ <;>
    simp only [Ex.eval, H.gE σ hσ] <;> omega

end Coarse

/-- The bounds needed by the coarsened network. -/
structure CoarsenBddHyp (V m B : ℕ) (σ₀ : ℕ → ℕ) (A : ℕ → ℕ → ℕ) (P : CP) {g K : ℕ} (N : Net (ZMod m) g)
    (κ : Coding N) (χ : Fin g → Fin K) : Prop where
  E : NBdd V B σ₀ A (NVars.std P.u) P.E g
  gE : ∀ σ, Ag B σ₀ σ → Bdd V σ A P.gE
  χE : ∀ σ, Ag B σ₀ σ → σ P.u < g → Bdd V σ A P.χE
  mm : m * m ≤ V
  KV : K ≤ V
  gg : g * g ≤ V
  /-- The coarse sizes `∏_{χ a = γ} κ.s a`. -/
  sz : ∀ γ : Fin K, (κ.coarsen χ).s γ ≤ V
  /-- The coarse widths. -/
  cw : ∀ γ γ' : Fin K, γ < γ' → 2 ^ (N.coarsen χ).c γ γ' ≤ V
  /-- The inner widths inside one group. -/
  cin : ∀ a b : Fin g, a < b → χ a = χ b → 2 ^ N.c a b ≤ V

section Main

variable {V m B g K : ℕ} {σ₀ : ℕ → ℕ} {A : ℕ → ℕ → ℕ} {P : CP} {N : Net (ZMod m) g} {κ : Coding N}
  {χ : Fin g → Fin K} (H : CoarsenHyp m B σ₀ A P N κ χ) (Hb : CoarsenBddHyp V m B σ₀ A P N κ χ)
include H Hb

theorem CoarsenBddHyp.consts : 2 ≤ m ∧ m ≤ V ∧ 4 ≤ V ∧ g ≤ V := by
  have hm := H.hm; have hg := H.hg
  have := Hb.mm
  have h1 : m ≤ m * m := Nat.le_mul_of_pos_left m (by omega)
  have h2 : 4 ≤ m * m := by nlinarith
  exact ⟨hm, by omega, by omega, le_trans (Nat.le_mul_of_pos_left g hg) Hb.gg⟩

theorem coarseSz_bdd {σ : ℕ → ℕ} (hσ : Ag B σ₀ σ) (hγ : σ P.w < K) : Bdd V σ A (CoarsenEx.sz P) := by
  obtain ⟨_, _, h4, hgV⟩ := CoarsenBddHyp.consts H Hb
  have hu := H.hu; have hw := H.hw
  have hupd : ∀ i, Function.update σ P.u i P.w = σ P.w := fun i => by rw [Function.update_of_ne (by omega)]
  unfold CoarsenEx.sz
  refine B_nprodV (Hb.gE σ hσ) (fun j hj => B_sgE Hb.E Hb.χE (hσ.upd hu _) (by omega) (by rw [hupd]; have := Hb.KV; omega)
    (by simp only [Function.update_self]; rw [H.gE σ hσ] at hj; exact hj)) fun j hj => ?_
  rw [H.gE σ hσ] at hj
  have e : pp (fun i => eval (Function.update σ P.u i) A (sgE P P.w)) j = pp (κ.sg χ ⟨σ P.w, hγ⟩) j :=
    pp_congr fun i hi => eval_sgE H (hσ.upd hu i) ⟨σ P.w, hγ⟩ (hupd i) ⟨i, by omega⟩ (by simp)
  rw [e]
  refine le_trans (pp_mono_le (Coding.sg_pos κ χ _) hj) ?_
  have := Hb.sz ⟨σ P.w, hγ⟩
  simp only [Coding.coarsen, dif_pos hγ] at this
  exact this

theorem coarseW_bdd (hvm : P.vm < B) {σ : ℕ → ℕ} (hσ : Ag B σ₀ σ) (hγ : σ P.w < K) (hz : σ (P.w + 2) ≤ V) :
    Bdd V σ A (CoarsenEx.W P) := by
  obtain ⟨hm2, hmV, h4, hgV⟩ := CoarsenBddHyp.consts H Hb
  have hu := H.hu; have hw := H.hw; have hKV := Hb.KV
  have hmσ : σ P.vm = m := by rw [hσ _ hvm]; exact H.rep.hm
  set γ : Fin K := ⟨σ P.w, hγ⟩
  have hγV : (γ : ℕ) ≤ V := by simp only [γ]; omega
  -- the first product: the members' weights
  have P1 : Bdd V σ A (zprod P.u P.gE P.vm (ifEq P.χE (.var P.w) (.lett (P.u + 2) (digE P P.w) P.E.W) (.lit 1))) := by
    refine B_zprod (by omega) (by omega) (by omega) (Hb.gE σ hσ) fun j hj => ?_
    rw [H.gE σ hσ] at hj
    set σ1 := Function.update σ P.u j
    have a1 : Ag B σ₀ σ1 := hσ.upd hu _
    have e1u : σ1 P.u = j := by simp [σ1]
    have e1w : σ1 P.w = γ := by simp only [σ1]; upd; rfl
    have e1z : σ1 (P.w + 2) ≤ V := by simp only [σ1]; upd; exact hz
    refine B_ifEq' (Hb.χE σ1 a1 (by rw [e1u]; exact hj)) (B_var (by rw [e1w]; exact hγV))
      (fun _ => B_lett (B_digE H Hb.E Hb.χE Hb.sz hgV a1 (by omega) γ e1w hγV (by rw [e1u]; exact hj) e1z) ?_)
      (fun _ => B_lit (by omega))
    refine Hb.E.W _ (a1.upd (by omega) _) ?_ ?_ <;> simp only [NVars.std] <;> upd
    · rw [e1u]; exact hj
    · exact le_trans (digE_le _) e1z
  -- the second product: the pairs inside the group
  have P2 : Bdd V σ A (zprod P.u P.gE P.vm (zprod (P.u + 1) P.gE P.vm
      (.ifLt (.var P.u) (.var (P.u + 1))
        (ifEq P.χE (.var P.w) (ifEq (chiB P) (.var P.w)
          (zsum (P.u + 3) (pow2 (P.w + 6) P.E.c) P.vm
            (zmul P.vm (.lett (P.u + 2) (digE P P.w) P.E.l) (.lett (P.u + 2) (digB P P.w) P.E.r)))
          (.lit 1)) (.lit 1))
        (.lit 1)))) := by
    refine B_zprod (by omega) (by omega) (by omega) (Hb.gE σ hσ) fun a ha => ?_
    rw [H.gE σ hσ] at ha
    have a1 : Ag B σ₀ (Function.update σ P.u a) := hσ.upd hu _
    refine B_zprod (by upd; omega) (by upd; omega) (by omega) (Hb.gE _ a1) fun b hb => ?_
    rw [H.gE _ a1] at hb
    set σ2 := Function.update (Function.update σ P.u a) (P.u + 1) b
    have a2 : Ag B σ₀ σ2 := a1.upd (by omega) _
    have e2u : σ2 P.u = a := by simp only [σ2]; upd
    have e2b : σ2 (P.u + 1) = b := by simp only [σ2]; upd
    have e2w : σ2 P.w = γ := by simp only [σ2]; upd; rfl
    have e2z : σ2 (P.w + 2) ≤ V := by simp only [σ2]; upd; exact hz
    have e2m : σ2 P.vm = m := by simp only [σ2]; upd; exact hmσ
    refine B_ifLt' (B_var (by rw [e2u]; omega)) (B_var (by rw [e2b]; omega)) (fun hab => ?_) (fun _ => B_lit (by omega))
    simp only [Ex.eval, e2u, e2b] at hab
    have hab' : (⟨a, ha⟩ : Fin g) < ⟨b, hb⟩ := hab
    refine B_ifEq' (Hb.χE σ2 a2 (by rw [e2u]; exact ha)) (B_var (by rw [e2w]; exact hγV)) (fun hχa => ?_)
      (fun _ => B_lit (by omega))
    refine B_ifEq' (B_chiB H Hb.χE a2 (by rw [e2b]; exact hb) (by rw [e2b]; omega)) (B_var (by rw [e2w]; exact hγV))
      (fun hχb => ?_) (fun _ => B_lit (by omega))
    rw [H.χE σ2 a2 ⟨a, ha⟩ e2u] at hχa
    rw [eval_chiB H a2 ⟨b, hb⟩ e2b] at hχb
    simp only [Ex.eval, e2w] at hχa hχb
    have hχa' : χ ⟨a, ha⟩ = γ := Fin.ext hχa
    have hχb' : χ ⟨b, hb⟩ = γ := Fin.ext hχb
    have ec : eval σ2 A P.E.c = N.c ⟨a, ha⟩ ⟨b, hb⟩ := H.rep.c σ2 a2 _ _ hab' e2u e2b
    have h2c : 2 ^ N.c ⟨a, ha⟩ ⟨b, hb⟩ ≤ V := Hb.cin _ _ hab' (hχa'.trans hχb'.symm)
    refine B_zsum (by rw [e2m]; omega) (by rw [e2m]; omega)
      (B_pow2 (Hb.E.c σ2 a2 (by simp [NVars.std, e2u, e2b]; exact hab) (by simp [NVars.std, e2b]; exact hb)) (by omega)
        (by rw [ec]; exact h2c)) fun q hq => ?_
    rw [eval_pow2, ec] at hq
    set σ3 := Function.update σ2 (P.u + 3) q
    have a3 : Ag B σ₀ σ3 := a2.upd (by omega) _
    have e3u : σ3 P.u = a := by simp only [σ3]; upd; exact e2u
    have e3b : σ3 (P.u + 1) = b := by simp only [σ3]; upd; exact e2b
    have e3w : σ3 P.w = γ := by simp only [σ3]; upd; exact e2w
    have e3z : σ3 (P.w + 2) ≤ V := by simp only [σ3]; upd; exact e2z
    have e3q : σ3 (P.u + 3) ≤ V := by simp only [σ3]; upd; omega
    have e3m : σ3 P.vm = m := by simp only [σ3]; upd; exact e2m
    have hab3 : σ3 P.u < σ3 (P.u + 1) := by rw [e3u, e3b]; exact hab
    have hb3 : σ3 (P.u + 1) < g := by rw [e3b]; exact hb
    have lL : eval σ3 A (.lett (P.u + 2) (digE P P.w) P.E.l) < m := by
      rw [eval_lett]
      refine H.rep.l_lt (a3.upd (by omega) _) ⟨a, ha⟩ ⟨b, hb⟩ hab' (by simp only [NVars.std]; upd; exact e3u)
        (by simp only [NVars.std]; upd; exact e3b) ?_
      simp only [NVars.std]; upd
      exact digE_lt H a3 (by omega) γ e3w ⟨a, ha⟩ e3u hχa'
    have lR : eval σ3 A (.lett (P.u + 2) (digB P P.w) P.E.r) < m := by
      rw [eval_lett]
      refine H.rep.r_lt (a3.upd (by omega) _) ⟨a, ha⟩ ⟨b, hb⟩ hab' (by simp only [NVars.std]; upd; exact e3u)
        (by simp only [NVars.std]; upd; exact e3b) ?_
      simp only [NVars.std]; upd
      exact digB_lt H a3 (by omega) γ e3w ⟨b, hb⟩ e3b hχb'
    exact B_zmul (B_digL H Hb.E Hb.χE Hb.sz hgV a3 le_rfl γ e3w hγV hab3 hb3 e3z e3q)
      (B_digR H Hb.E Hb.χE Hb.sz hgV a3 le_rfl γ e3w hγV hab3 hb3 e3z e3q) (by rw [e3m]; omega)
      (le_trans (Nat.mul_le_mul lL.le lR.le) Hb.mm)
  unfold CoarsenEx.W
  have l1 := lt_zprod (σ := σ) (A := A) (x := P.u) (n := P.gE)
    (b := ifEq P.χE (.var P.w) (.lett (P.u + 2) (digE P P.w) P.E.W) (.lit 1)) (vm := P.vm) (by omega)
  have l2 := lt_zprod (σ := σ) (A := A) (x := P.u) (n := P.gE) (vm := P.vm) (b := zprod (P.u + 1) P.gE P.vm
      (.ifLt (.var P.u) (.var (P.u + 1))
        (ifEq P.χE (.var P.w) (ifEq (chiB P) (.var P.w)
          (zsum (P.u + 3) (pow2 (P.w + 6) P.E.c) P.vm
            (zmul P.vm (.lett (P.u + 2) (digE P P.w) P.E.l) (.lett (P.u + 2) (digB P P.w) P.E.r)))
          (.lit 1)) (.lit 1))
        (.lit 1))) (by omega)
  rw [hmσ] at l1 l2
  exact B_zmul P1 P2 (by omega) (le_trans (Nat.mul_le_mul l1.le l2.le) Hb.mm)

/-- The coarse factor functions' common frame (pairs, used test, offset); `Y` reads the member functions. -/
theorem B_coarseF (hvm : P.vm < B) {σ : ℕ → ℕ} (hσ : Ag B σ₀ σ) (γ γ' : Fin K) (hγ : σ P.w = γ)
    (hγ' : σ (P.w + 1) = γ') (hlt : γ < γ') (hq : σ (P.w + 3) ≤ V) (Y : Ex)
    (hY : ∀ σ', Ag B σ₀ σ' → σ' P.u < σ' (P.u + 1) → σ' (P.u + 1) < g → σ' P.w = γ → σ' (P.w + 1) = γ' →
      σ' (P.w + 2) = σ (P.w + 2) → σ' (P.u + 3) ≤ V → Bdd V σ' A Y) :
    Bdd V σ A (zprod (P.w + 4) (.mul P.gE P.gE) P.vm (atPair P (P.w + 4) (ifEq (usedE P) (.lit 1)
      (.lett (P.u + 3) (.div (.var (P.w + 3)) (pow2 (P.w + 6) (offE P))) Y) (.lit 1)))) := by
  obtain ⟨hm2, hmV, h4, hgV⟩ := CoarsenBddHyp.consts H Hb
  have hu := H.hu; have hw := H.hw; have hKV := Hb.KV; have hg := H.hg
  have hmσ : σ P.vm = m := by rw [hσ _ hvm]; exact H.rep.hm
  have h2c := Hb.cw γ γ' hlt
  have hcV : (N.coarsen χ).c γ γ' ≤ V := le_trans Nat.lt_two_pow_self.le h2c
  have Bgg : Bdd V σ A (.mul P.gE P.gE) := ⟨Hb.gE σ hσ, Hb.gE σ hσ, by rw [H.gE σ hσ]; exact Hb.gg⟩
  refine B_zprod (by omega) (by omega) (by omega) Bgg fun k hk => ?_
  simp only [Ex.eval, H.gE σ hσ] at hk
  set σ1 := Function.update σ (P.w + 4) k
  have a1 : Ag B σ₀ σ1 := hσ.upd (by omega) k
  have e1 : σ1 (P.w + 4) = k := by simp [σ1]
  unfold atPair
  refine B_lett (B_mod (B_div (B_var (by rw [e1]; have := Hb.gg; omega)) (Hb.gE σ1 a1)) (Hb.gE σ1 a1)) ?_
  rw [show eval σ1 A (.mod (.div (.var (P.w + 4)) P.gE) P.gE) = k / g % g by simp only [Ex.eval, H.gE σ1 a1, e1]]
  set σ2 := Function.update σ1 P.u (k / g % g)
  have a2 : Ag B σ₀ σ2 := a1.upd hu _
  have e2 : σ2 (P.w + 4) = k := by simp only [σ2]; upd; exact e1
  refine B_lett (B_mod (B_var (by rw [e2]; have := Hb.gg; omega)) (Hb.gE σ2 a2)) ?_
  rw [show eval σ2 A (.mod (.var (P.w + 4)) P.gE) = k % g by simp only [Ex.eval, H.gE σ2 a2, e2]]
  set σ3 := Function.update σ2 (P.u + 1) (k % g)
  have a3 : Ag B σ₀ σ3 := a2.upd (by omega) _
  have ea : σ3 P.u = (Net.pairOf g hg k).1 := by simp only [σ3, σ2]; upd; rfl
  have eb : σ3 (P.u + 1) = (Net.pairOf g hg k).2 := by simp only [σ3]; upd; rfl
  have ew : σ3 P.w = γ := by simp only [σ3, σ2, σ1]; upd; exact hγ
  have ew' : σ3 (P.w + 1) = γ' := by simp only [σ3, σ2, σ1]; upd; exact hγ'
  have ek : σ3 (P.w + 4) = k := by simp only [σ3]; upd; exact e2
  have ez : σ3 (P.w + 2) = σ (P.w + 2) := by simp only [σ3, σ2, σ1]; upd
  have eq3 : σ3 (P.w + 3) ≤ V := by simp only [σ3, σ2, σ1]; upd; exact hq
  refine B_ifEq' (B_usedE H Hb.χE a3 (by rw [ea]; exact Fin.isLt _) (by rw [eb]; exact Fin.isLt _) hgV
    (by rw [ew]; omega) (by rw [ew']; omega)) (B_lit (by omega)) (fun hU => ?_) (fun _ => B_lit (by omega))
  rw [eval_usedE H a3 γ γ' ew ew' _ _ ea eb] at hU
  have hU' : Net.UsedP χ γ γ' (Net.pairOf g hg k) := by
    by_contra h; rw [if_neg h] at hU; simp [Ex.eval] at hU
  have hoff : eval σ3 A (offE P) = offR (fun p => N.c p.1 p.2) (Net.UsedP χ γ γ') (Net.pairOf g hg) k := by
    unfold offE
    rw [eval_usedSum H a3 γ γ' ew ew' (P.w + 5) (by omega)]
    simp [Ex.eval, ek]
  have hoffc : 2 ^ eval σ3 A (offE P) ≤ V := by
    rw [hoff]
    refine le_trans (Nat.pow_le_pow_right (by norm_num) ?_) h2c
    rw [Net.coarsen_c_code N hg χ γ γ']
    exact offR_mono_le _ _ _ hk.le
  have Boff : Bdd V σ3 A (offE P) := by
    unfold offE
    exact B_usedSum H Hb.χE Hb.gE Hb.E.c Hb.gg a3 γ γ' ew ew' hcV hKV (P.w + 5) (by omega)
      (B_var (by rw [ek]; have := Hb.gg; omega)) (by simp only [Ex.eval, ek]; exact hk.le)
  refine B_lett (B_div (B_var eq3) (B_pow2 Boff (by omega) hoffc)) ?_
  refine hY _ (a3.upd (by omega) _) ?_ ?_ ?_ ?_ ?_ ?_ <;> upd
  · rw [ea, eb]; exact hU'.1
  · rw [eb]; exact Fin.isLt _
  · exact ew
  · exact ew'
  · exact ez
  · simp only [Ex.eval]; exact le_trans (Nat.div_le_self _ _) eq3

/-- **The coarsened network: every value is at most `V`.** -/
theorem coarsen_bdd (hvm : P.vm < B) : NBdd V B σ₀ A (NVars.std P.w) (CoarsenEx.nex P) K where
  sz σ hσ hγ := coarseSz_bdd H Hb hσ hγ
  W σ hσ hγ hz := coarseW_bdd H Hb hvm hσ hγ hz
  c σ hσ hab hb := by
    have h := Hb.cw ⟨σ P.w, by simp only [NVars.std] at hab hb; omega⟩ ⟨σ (P.w + 1), hb⟩ hab
    exact coarsenC_bdd H Hb.χE Hb.gE Hb.E.c Hb.gg Hb.KV hσ _ _ rfl rfl (le_trans Nat.lt_two_pow_self.le h)
  l σ hσ hab hb hz hq := by
    obtain ⟨_, _, _, hgV⟩ := CoarsenBddHyp.consts H Hb
    have hu := H.hu; have hw := H.hw; have hKV := Hb.KV
    simp only [NVars.std] at hab hb hz hq
    set γ : Fin K := ⟨σ P.w, by omega⟩
    have hγV : (γ : ℕ) ≤ V := by simp only [γ]; omega
    refine B_coarseF H Hb hvm hσ γ ⟨σ (P.w + 1), hb⟩ rfl rfl hab hq _
      fun σ' a' hab' hb' hw' hw1' hz' hq' => ?_
    exact B_ifEq (Hb.χE σ' a' (by omega)) (B_var (by rw [hw']; exact hγV))
      (B_digL H Hb.E Hb.χE Hb.sz hgV a' le_rfl γ hw' hγV hab' hb' (by rw [hz']; exact hz) hq')
      (B_ifEq (B_chiB H Hb.χE a' hb' (by omega)) (B_var (by rw [hw']; exact hγV))
        (B_digR H Hb.E Hb.χE Hb.sz hgV a' le_rfl γ hw' hγV hab' hb' (by rw [hz']; exact hz) hq')
        (B_lit (Nat.zero_le _)))
  r σ hσ hab hb hz hq := by
    obtain ⟨_, _, _, hgV⟩ := CoarsenBddHyp.consts H Hb
    have hu := H.hu; have hw := H.hw; have hKV := Hb.KV
    simp only [NVars.std] at hab hb hz hq
    set γ' : Fin K := ⟨σ (P.w + 1), hb⟩
    have hγV : (γ' : ℕ) ≤ V := by simp only [γ']; omega
    refine B_coarseF H Hb hvm hσ ⟨σ P.w, by omega⟩ γ' rfl rfl hab hq _
      fun σ' a' hab' hb' hw' hw1' hz' hq' => ?_
    exact B_ifEq (B_chiB H Hb.χE a' hb' (by omega)) (B_var (by rw [hw1']; exact hγV))
      (B_digR H Hb.E Hb.χE Hb.sz hgV a' (by omega) γ' hw1' hγV hab' hb' (by rw [hz']; exact hz) hq')
      (B_ifEq (Hb.χE σ' a' (by omega)) (B_var (by rw [hw1']; exact hγV))
        (B_digL H Hb.E Hb.χE Hb.sz hgV a' (by omega) γ' hw1' hγV hab' hb' (by rw [hz']; exact hz) hq')
        (B_lit (Nat.zero_le _)))

end Main

end Factoring.Aux
