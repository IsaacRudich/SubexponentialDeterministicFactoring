/-
The coarsened network (`Net.coarsen`, Lemma 1) as expressions: from expressions representing a coded network
`(N, κ)` (argument variables `u … u+3`) and an expression for the grouping `χ` (reading node `u`), expressions
representing `(N.coarsen χ, κ.coarsen χ)` (argument variables `w … w+3`, scratch `w+4 … w+7`).

* `digE`: the code of member `a` (`= u`) in the code of group `grp`: digit `a` in mixed radix `sg`.
* **`coarsen_rep`**: the representation statement.

Not an audit surface.
-/
module

public import FactoringAux.EngineNet

@[expose] public section

namespace Factoring.Aux

open Finset Ex

/-- The standard argument variables `u, u+1, u+2, u+3`. -/
def NVars.std (u : ℕ) : NVars := ⟨u, u + 1, u + 2, u + 3⟩

/-- The data of the coarsening expressions. -/
structure CP where
  /-- Inner argument base. -/
  u : ℕ
  /-- Coarse argument base. -/
  w : ℕ
  /-- The modulus variable. -/
  vm : ℕ
  /-- Inner expressions. -/
  E : NEx
  /-- Number of nodes. -/
  gE : Ex
  /-- The grouping (reads node `u`). -/
  χE : Ex

namespace CoarsenEx

variable (P : CP)

/-- `sg γ a` (node `a = P.u`, group in variable `grp`). -/
def sgE (grp : ℕ) : Ex := ifEq P.χE (.var grp) P.E.sz (.lit 1)

/-- `pp (sg γ) a`: the product over the nodes before `a = P.u`. -/
def ppE (grp : ℕ) : Ex := nprod P.u (.var P.u) (sgE P grp)

/-- The code of member `a = P.u` in the group code (variable `P.w+2`) of group `grp`. -/
def digE (grp : ℕ) : Ex := .mod (.div (.var (P.w + 2)) (ppE P grp)) (sgE P grp)

/-- The code of member `b = P.u+1`. -/
def digB (grp : ℕ) : Ex := .lett P.u (.var (P.u + 1)) (digE P grp)

/-- `χ b` for `b = P.u + 1`. -/
def chiB : Ex := .lett P.u (.var (P.u + 1)) P.χE

/-- `[χ a = g1 ∧ χ b = g2] ∨ [χ a = g2 ∧ χ b = g1]`, as `1`/`0`. -/
def crossE (g1 g2 : ℕ) : Ex :=
  ifEq P.χE (.var g1) (ifEq (chiB P) (.var g2) (.lit 1) (ifEq P.χE (.var g2) (ifEq (chiB P) (.var g1) (.lit 1) (.lit 0)) (.lit 0)))
    (ifEq P.χE (.var g2) (ifEq (chiB P) (.var g1) (.lit 1) (.lit 0)) (.lit 0))

/-- The pair `a < b` is used between groups `P.w`, `P.w+1`. -/
def usedE : Ex := .ifLt (.var P.u) (.var (P.u + 1)) (crossE P P.w (P.w + 1)) (.lit 0)

/-- Decode pair index `k` (variable `kv`) into `P.u, P.u+1` and continue with `body`. -/
def atPair (kv : ℕ) (body : Ex) : Ex :=
  .lett P.u (.mod (.div (.var kv) P.gE) P.gE) (.lett (P.u + 1) (.mod (.var kv) P.gE) body)

/-- The widths of the used pairs before pair `P.w+4`. -/
def offE : Ex := nsum (P.w + 5) (.var (P.w + 4)) (atPair P (P.w + 5) (ifEq (usedE P) (.lit 1) P.E.c (.lit 0)))

/-- The coarse sizes. -/
def sz : Ex := nprod P.u P.gE (sgE P P.w)

/-- The coarse weights. -/
def W : Ex :=
  zmul P.vm (zprod P.u P.gE P.vm (ifEq P.χE (.var P.w) (.lett (P.u + 2) (digE P P.w) P.E.W) (.lit 1)))
    (zprod P.u P.gE P.vm (zprod (P.u + 1) P.gE P.vm
      (.ifLt (.var P.u) (.var (P.u + 1))
        (ifEq P.χE (.var P.w) (ifEq (chiB P) (.var P.w)
          (zsum (P.u + 3) (pow2 (P.w + 6) P.E.c) P.vm
            (zmul P.vm (.lett (P.u + 2) (digE P P.w) P.E.l) (.lett (P.u + 2) (digB P P.w) P.E.r)))
          (.lit 1)) (.lit 1))
        (.lit 1))))

/-- The coarse widths. -/
def c : Ex := nsum (P.w + 4) (.mul P.gE P.gE) (atPair P (P.w + 4) (ifEq (usedE P) (.lit 1) P.E.c (.lit 0)))

/-- The coarse left factor functions. -/
def l : Ex :=
  zprod (P.w + 4) (.mul P.gE P.gE) P.vm (atPair P (P.w + 4) (ifEq (usedE P) (.lit 1)
    (.lett (P.u + 3) (.div (.var (P.w + 3)) (pow2 (P.w + 6) (offE P)))
      (ifEq P.χE (.var P.w) (.lett (P.u + 2) (digE P P.w) P.E.l)
        (ifEq (chiB P) (.var P.w) (.lett (P.u + 2) (digB P P.w) P.E.r) (.lit 0))))
    (.lit 1)))

/-- The coarse right factor functions. -/
def r : Ex :=
  zprod (P.w + 4) (.mul P.gE P.gE) P.vm (atPair P (P.w + 4) (ifEq (usedE P) (.lit 1)
    (.lett (P.u + 3) (.div (.var (P.w + 3)) (pow2 (P.w + 6) (offE P)))
      (ifEq (chiB P) (.var (P.w + 1)) (.lett (P.u + 2) (digB P (P.w + 1)) P.E.r)
        (ifEq P.χE (.var (P.w + 1)) (.lett (P.u + 2) (digE P (P.w + 1)) P.E.l) (.lit 0))))
    (.lit 1)))

/-- All of them. -/
def nex : NEx := ⟨sz P, W P, c P, l P, r P⟩

end CoarsenEx

section Proofs

variable {m B g K : ℕ} {σ₀ : ℕ → ℕ} {A : ℕ → ℕ → ℕ} {P : CP}
  {N : Net (ZMod m) g} {κ : Coding N} {χ : Fin g → Fin K}

open CoarsenEx

/-- Hypotheses shared by the proofs. -/
structure CoarsenHyp (m B : ℕ) (σ₀ : ℕ → ℕ) (A : ℕ → ℕ → ℕ) (P : CP) {g K : ℕ}
    (N : Net (ZMod m) g) (κ : Coding N) (χ : Fin g → Fin K) : Prop where
  rep : NRep m P.vm B σ₀ A (NVars.std P.u) P.E N κ
  hg : 0 < g
  gE : ∀ σ, Ag B σ₀ σ → Ex.eval σ A P.gE = g
  χE : ∀ σ, Ag B σ₀ σ → ∀ a : Fin g, σ P.u = a → Ex.eval σ A P.χE = χ a
  hu : B ≤ P.u
  hw : P.u + 4 ≤ P.w
  hm : 1 < m

theorem upd_ne {σ : ℕ → ℕ} {x y : ℕ} (v : ℕ) (h : y ≠ x) : Function.update σ x v y = σ y := by
  rw [Function.update_apply, if_neg h]

theorem eval_sgE (H : CoarsenHyp m B σ₀ A P N κ χ) {σ : ℕ → ℕ} (hσ : Ag B σ₀ σ) {grp : ℕ}
    (γ : Fin K) (hγ : σ grp = γ) (a : Fin g) (ha : σ P.u = a) :
    Ex.eval σ A (sgE P grp) = κ.sg χ γ a := by
  rw [sgE, eval_ifEq, H.χE σ hσ a ha]
  simp only [Ex.eval, hγ, Coding.sg, dif_pos a.2, Fin.eta]
  by_cases h : χ a = γ
  · rw [if_pos (by rw [h]), if_pos h, H.rep.sz σ hσ a ha]
  · rw [if_neg (fun h' => h (Fin.ext h')), if_neg h]

theorem eval_digE (H : CoarsenHyp m B σ₀ A P N κ χ) {σ : ℕ → ℕ} (hσ : Ag B σ₀ σ) {grp : ℕ}
    (hgrp : grp ≠ P.u) (γ : Fin K) (hγ : σ grp = γ) (a : Fin g) (ha : σ P.u = a) :
    Ex.eval σ A (digE P grp) = dgx (κ.sg χ γ) (σ (P.w + 2)) a := by
  unfold digE ppE
  simp only [Ex.eval, eval_nprod]
  rw [eval_sgE H hσ γ hγ a ha, ha]
  unfold dgx
  congr 2
  refine pp_congr fun i hi => ?_
  have hi' : i < g := lt_trans hi a.2
  exact eval_sgE H (hσ.upd H.hu i) (grp := grp) γ (by rw [upd_ne _ hgrp, hγ]) ⟨i, hi'⟩ (by simp)

theorem eval_chiB (H : CoarsenHyp m B σ₀ A P N κ χ) {σ : ℕ → ℕ} (hσ : Ag B σ₀ σ) (b : Fin g)
    (hb : σ (P.u + 1) = b) : Ex.eval σ A (chiB P) = χ b := by
  unfold chiB
  simp only [Ex.eval]
  exact H.χE _ (hσ.upd H.hu _) b (by simp [hb])

theorem eval_usedE (H : CoarsenHyp m B σ₀ A P N κ χ) {σ : ℕ → ℕ} (hσ : Ag B σ₀ σ) (γ γ' : Fin K)
    (hγ : σ P.w = γ) (hγ' : σ (P.w + 1) = γ') (a b : Fin g) (ha : σ P.u = a) (hb : σ (P.u + 1) = b) :
    Ex.eval σ A (usedE P) = if Net.UsedP χ γ γ' (a, b) then 1 else 0 := by
  have hχa := H.χE σ hσ a ha
  have hχb := eval_chiB H hσ b hb
  unfold usedE crossE
  simp only [Ex.eval, eval_ifEq, hχa, hχb, hγ, hγ', ha, hb]
  simp only [Net.UsedP, Net.Cross, Fin.lt_def, ← Fin.ext_iff]
  by_cases h1 : (a : ℕ) < b <;> by_cases h2 : χ a = γ <;> by_cases h3 : χ b = γ' <;> by_cases h4 : χ a = γ' <;>
    by_cases h5 : χ b = γ <;> simp [h1, h2, h3, h4, h5]

theorem pairOf_val (g : ℕ) (hg : 0 < g) (k : ℕ) :
    ((Net.pairOf g hg k).1 : ℕ) = k / g % g ∧ ((Net.pairOf g hg k).2 : ℕ) = k % g := ⟨rfl, rfl⟩

theorem eval_atPair (H : CoarsenHyp m B σ₀ A P N κ χ) {σ : ℕ → ℕ} (hσ : Ag B σ₀ σ) (kv : ℕ)
    (hkv : P.w + 4 ≤ kv) (body : Ex) :
    Ex.eval σ A (atPair P kv body) =
      Ex.eval (Function.update (Function.update σ P.u (σ kv / g % g)) (P.u + 1) (σ kv % g)) A body := by
  have hu := H.hu; have hw := H.hw
  unfold atPair
  simp only [Ex.eval]
  rw [H.gE σ hσ, H.gE _ (hσ.upd H.hu _), upd_ne _ (show kv ≠ P.u by omega)]

/-- The sum of the widths of the used pairs below `n`. -/
theorem eval_usedSum (H : CoarsenHyp m B σ₀ A P N κ χ) {σ : ℕ → ℕ} (hσ : Ag B σ₀ σ) (γ γ' : Fin K)
    (hγ : σ P.w = γ) (hγ' : σ (P.w + 1) = γ') (kv : ℕ) (hkv : P.w + 4 ≤ kv) (n : Ex) :
    Ex.eval σ A (nsum kv n (atPair P kv (ifEq (usedE P) (.lit 1) P.E.c (.lit 0)))) =
      offR (fun p => N.c p.1 p.2) (Net.UsedP χ γ γ') (Net.pairOf g H.hg) (Ex.eval σ A n) := by
  have hu := H.hu; have hw := H.hw
  rw [eval_nsum, offR]
  refine sum_congr rfl fun k _ => ?_
  set σ1 := Function.update σ kv k
  have h1 : Ag B σ₀ σ1 := hσ.upd (by omega) k
  have e1 : σ1 kv = k := by simp [σ1]
  rw [eval_atPair H h1 kv hkv, e1]
  set σ2 := Function.update (Function.update σ1 P.u (k / g % g)) (P.u + 1) (k % g)
  have h2 : Ag B σ₀ σ2 := (h1.upd hu _).upd (by omega) _
  have ha : σ2 P.u = (Net.pairOf g H.hg k).1 := by simp [σ2, Net.pairOf]
  have hb : σ2 (P.u + 1) = (Net.pairOf g H.hg k).2 := by simp [σ2, Net.pairOf]
  have hγ2 : σ2 P.w = γ := by simp [σ2, σ1, upd_ne _ (show P.w ≠ P.u + 1 by omega),
    upd_ne _ (show P.w ≠ P.u by omega), upd_ne _ (show P.w ≠ kv by omega), hγ]
  have hγ2' : σ2 (P.w + 1) = γ' := by simp [σ2, σ1, upd_ne _ (show P.w + 1 ≠ P.u + 1 by omega),
    upd_ne _ (show P.w + 1 ≠ P.u by omega), upd_ne _ (show P.w + 1 ≠ kv by omega), hγ']
  rw [eval_ifEq, eval_usedE H h2 γ γ' hγ2 hγ2' _ _ ha hb]
  by_cases hU : Net.UsedP χ γ γ' (Net.pairOf g H.hg k)
  · rw [if_pos hU, if_pos hU]
    simp only [Ex.eval, if_true]
    exact H.rep.c σ2 h2 _ _ hU.1 ha hb
  · rw [if_neg hU, if_neg hU]
    simp [Ex.eval]

theorem coarsen_sz (H : CoarsenHyp m B σ₀ A P N κ χ) {σ : ℕ → ℕ} (hσ : Ag B σ₀ σ) (γ : Fin K)
    (hγ : σ P.w = γ) : Ex.eval σ A (CoarsenEx.sz P) = (κ.coarsen χ).s γ := by
  have hu := H.hu; have hw := H.hw
  unfold CoarsenEx.sz
  rw [eval_nprod, H.gE σ hσ]
  simp only [Coding.coarsen, dif_pos γ.2, Fin.eta]
  refine pp_congr fun i hi => ?_
  exact eval_sgE H (hσ.upd H.hu i) γ (by rw [upd_ne _ (by omega), hγ]) ⟨i, hi⟩ (by simp)

theorem digit_eq (γ : Fin K) (z : (N.coarsen χ).S γ) (a : Fin g) (h : χ a = γ) :
    dgx (κ.sg χ γ) ((κ.coarsen χ).e γ z) a = κ.e a (z ⟨a, h⟩) := by
  have := Coding.coarsen_digit κ χ γ ((κ.coarsen χ).e γ z) ⟨a, h⟩
  rw [Equiv.symm_apply_apply] at this
  exact this.symm

/-- The member codes, in an environment holding the group code. -/
theorem eval_digE' (H : CoarsenHyp m B σ₀ A P N κ χ) {σ : ℕ → ℕ} (hσ : Ag B σ₀ σ) {grp : ℕ}
    (hgrp : grp ≠ P.u) (γ : Fin K) (hγ : σ grp = γ) (z : (N.coarsen χ).S γ)
    (hz : σ (P.w + 2) = (κ.coarsen χ).e γ z) (a : Fin g) (ha : σ P.u = a) (h : χ a = γ) :
    Ex.eval σ A (digE P grp) = κ.e a (z ⟨a, h⟩) := by
  rw [eval_digE H hσ hgrp γ hγ a ha, hz, digit_eq]

theorem eval_digB' (H : CoarsenHyp m B σ₀ A P N κ χ) {σ : ℕ → ℕ} (hσ : Ag B σ₀ σ) {grp : ℕ}
    (hgrp : grp ≠ P.u) (γ : Fin K) (hγ : σ grp = γ) (z : (N.coarsen χ).S γ)
    (hz : σ (P.w + 2) = (κ.coarsen χ).e γ z) (b : Fin g) (hb : σ (P.u + 1) = b) (h : χ b = γ) :
    Ex.eval σ A (digB P grp) = κ.e b (z ⟨b, h⟩) := by
  have hu := H.hu; have hw := H.hw
  unfold digB
  simp only [Ex.eval]
  exact eval_digE' H (hσ.upd hu _) hgrp γ (by rw [upd_ne _ (Ne.symm (Ne.symm hgrp)), hγ]) z
    (by rw [upd_ne _ (by omega), hz]) b (by simp [hb]) h

theorem coarsen_W (H : CoarsenHyp m B σ₀ A P N κ χ) (hvm : P.vm < B) {σ : ℕ → ℕ} (hσ : Ag B σ₀ σ)
    (γ : Fin K) (z : (N.coarsen χ).S γ) (hγ : σ P.w = γ) (hz : σ (P.w + 2) = (κ.coarsen χ).e γ z) :
    ZR m (Ex.eval σ A (CoarsenEx.W P)) ((N.coarsen χ).W γ z) := by
  have hu := H.hu; have hw := H.hw
  have hmσ : σ P.vm = m := by rw [hσ _ hvm]; exact H.rep.hm
  have hm := H.hm
  rw [Net.coarsen_W_code, prod_fin_range, prod_pairs_range]
  unfold CoarsenEx.W
  refine ZR_zmul hmσ (by omega) ?_ ?_
  · refine ZR_zprod hmσ H.hm P.u (H.gE σ hσ) _ fun j hj => ?_
    rw [dif_pos hj]
    have h1 : Ag B σ₀ (Function.update σ P.u j) := hσ.upd hu j
    have hw1 : Function.update σ P.u j P.w = γ := by rw [upd_ne _ (by omega), hγ]
    have hz1 : Function.update σ P.u j (P.w + 2) = (κ.coarsen χ).e γ z := by rw [upd_ne _ (by omega), hz]
    rw [eval_ifEq, H.χE _ h1 ⟨j, hj⟩ (by simp)]
    simp only [Ex.eval, hw1]
    by_cases h : χ ⟨j, hj⟩ = γ
    · rw [if_pos (by rw [h]), dif_pos h]
      refine H.rep.W _ (h1.upd (by omega) _) ⟨j, hj⟩ (z ⟨⟨j, hj⟩, h⟩) (by simp [NVars.std]) ?_
      simp only [NVars.std, Function.update_self]
      exact eval_digE' H h1 (by omega) γ hw1 z hz1 ⟨j, hj⟩ (by simp) h
    · rw [if_neg (fun h' => h (Fin.ext h')), dif_neg h]
      exact ZR_one H.hm
  · refine ZR_zprod hmσ H.hm P.u (H.gE σ hσ) _ fun a ha => ?_
    have h1 : Ag B σ₀ (Function.update σ P.u a) := hσ.upd hu a
    have hm1 : Function.update σ P.u a P.vm = m := by rw [upd_ne _ (by omega), hmσ]
    refine ZR_zprod hm1 H.hm (P.u + 1) (H.gE _ h1) _ fun b hb => ?_
    rw [dif_pos ⟨ha, hb⟩]
    set σ2 := Function.update (Function.update σ P.u a) (P.u + 1) b
    have h2 : Ag B σ₀ σ2 := h1.upd (by omega) b
    have e1 : σ2 P.u = (⟨a, ha⟩ : Fin g) := by simp [σ2]
    have e2 : σ2 (P.u + 1) = (⟨b, hb⟩ : Fin g) := by simp [σ2]
    have hw2 : σ2 P.w = γ := by simp only [σ2]; rw [upd_ne _ (by omega), upd_ne _ (by omega), hγ]
    have hz2 : σ2 (P.w + 2) = (κ.coarsen χ).e γ z := by
      simp only [σ2]; rw [upd_ne _ (by omega), upd_ne _ (by omega), hz]
    have hm2 : σ2 P.vm = m := by simp only [σ2]; rw [upd_ne _ (by omega), upd_ne _ (by omega), hmσ]
    simp only [Ex.eval]
    have ea : σ2 P.u = a := e1
    have eb : σ2 (P.u + 1) = b := e2
    simp only [ea, eb]
    by_cases hab : a < b
    · rw [if_pos hab, if_pos hab, eval_ifEq, H.χE σ2 h2 ⟨a, ha⟩ e1, eval_ifEq, eval_chiB H h2 ⟨b, hb⟩ e2]
      simp only [Ex.eval, hw2]
      by_cases hA : χ ⟨a, ha⟩ = γ
      · by_cases hB : χ ⟨b, hb⟩ = γ
        · rw [if_pos (by rw [hA]), if_pos (by rw [hB]), dif_pos ⟨hA, hB⟩]
          have hab' : (⟨a, ha⟩ : Fin g) < ⟨b, hb⟩ := hab
          have hc : Ex.eval σ2 A (pow2 (P.w + 6) P.E.c) = 2 ^ N.c ⟨a, ha⟩ ⟨b, hb⟩ := by
            rw [eval_pow2, H.rep.c σ2 h2 _ _ hab' e1 e2]
          unfold Net.Ψ Fac.eval
          rw [sum_bits_eq]
          refine ZR_zsum hm2 (by omega) (P.u + 3) hc _ fun q _ => ?_
          set σ3 := Function.update σ2 (P.u + 3) q
          have h3 : Ag B σ₀ σ3 := h2.upd (by omega) q
          have hm3 : σ3 P.vm = m := by simp only [σ3]; rw [upd_ne _ (by omega), hm2]
          have e31 : σ3 P.u = (⟨a, ha⟩ : Fin g) := by simp only [σ3]; rw [upd_ne _ (by omega), e1]
          have e32 : σ3 (P.u + 1) = (⟨b, hb⟩ : Fin g) := by simp only [σ3]; rw [upd_ne _ (by omega), e2]
          have hw3 : σ3 P.w = γ := by simp only [σ3]; rw [upd_ne _ (by omega), hw2]
          have hz3 : σ3 (P.w + 2) = (κ.coarsen χ).e γ z := by simp only [σ3]; rw [upd_ne _ (by omega), hz2]
          refine ZR_zmul hm3 (by omega) ?_ ?_
          · simp only [Ex.eval]
            refine H.rep.l _ (h3.upd (by omega) _) _ _ hab' (z ⟨⟨a, ha⟩, hA⟩) q
              (by simp only [NVars.std]; rw [upd_ne _ (by omega), e31]) (by simp only [NVars.std]; rw [upd_ne _ (by omega), e32])
              (by simp only [NVars.std]; rw [Function.update_self]; exact eval_digE' H h3 (by omega) γ hw3 z hz3 _ e31 hA)
              (by simp only [NVars.std]; rw [upd_ne _ (by omega)]; simp [σ3])
          · simp only [Ex.eval]
            refine H.rep.r _ (h3.upd (by omega) _) _ _ hab' (z ⟨⟨b, hb⟩, hB⟩) q
              (by simp only [NVars.std]; rw [upd_ne _ (by omega), e31]) (by simp only [NVars.std]; rw [upd_ne _ (by omega), e32])
              (by simp only [NVars.std]; rw [Function.update_self]; exact eval_digB' H h3 (by omega) γ hw3 z hz3 _ e32 hB)
              (by simp only [NVars.std]; rw [upd_ne _ (by omega)]; simp [σ3])
        · rw [if_pos (by rw [hA]), if_neg (fun h' => hB (Fin.ext h')), dif_neg (fun h' => hB h'.2)]
          exact ZR_one H.hm
      · rw [if_neg (fun h' => hA (Fin.ext h')), dif_neg (fun h' => hA h'.1)]
        exact ZR_one H.hm
    · rw [if_neg hab, if_neg hab]
      exact ZR_one H.hm

theorem coarsen_c (H : CoarsenHyp m B σ₀ A P N κ χ) {σ : ℕ → ℕ} (hσ : Ag B σ₀ σ) (γ γ' : Fin K)
    (hγ : σ P.w = γ) (hγ' : σ (P.w + 1) = γ') : Ex.eval σ A (CoarsenEx.c P) = (N.coarsen χ).c γ γ' := by
  unfold CoarsenEx.c
  rw [eval_usedSum H hσ γ γ' hγ hγ' (P.w + 4) le_rfl, Net.coarsen_c_code N H.hg]
  simp only [Ex.eval, H.gE σ hσ]

/-- The environment at pair `k` of the coarse factor functions. -/
theorem pair_env (H : CoarsenHyp m B σ₀ A P N κ χ) (hvm : P.vm < B) {σ : ℕ → ℕ} (hσ : Ag B σ₀ σ) (k : ℕ) :
    let σ2 := Function.update (Function.update (Function.update σ (P.w + 4) k) P.u (k / g % g)) (P.u + 1) (k % g)
    Ag B σ₀ σ2 ∧ σ2 P.u = (Net.pairOf g H.hg k).1 ∧ σ2 (P.u + 1) = (Net.pairOf g H.hg k).2 ∧
      σ2 (P.w + 4) = k ∧ (∀ y, P.w ≤ y → y < P.w + 4 → σ2 y = σ y) ∧ σ2 P.vm = σ P.vm := by
  have hu := H.hu; have hw := H.hw
  refine ⟨((hσ.upd (by omega) k).upd hu _).upd (by omega) _, by simp [Net.pairOf], by simp [Net.pairOf], ?_,
    fun y h1 h2 => ?_, ?_⟩
  · rw [upd_ne _ (by omega), upd_ne _ (by omega)]; simp
  · rw [upd_ne _ (by omega), upd_ne _ (by omega), upd_ne _ (by omega)]
  · rw [upd_ne _ (by omega), upd_ne _ (by omega), upd_ne _ (by omega)]

theorem orient_l1 {γ γ' : Fin K} {p : Fin g × Fin g} (z : (N.coarsen χ).S γ) (θ : Bits (N.c p.1 p.2))
    (h : χ p.1 = γ) : (N.orient χ γ γ' p).l z θ = (N.F p.1 p.2).l (z ⟨p.1, h⟩) θ := by
  simp only [Net.orient, dif_pos h]

theorem orient_l2 {γ γ' : Fin K} {p : Fin g × Fin g} (z : (N.coarsen χ).S γ) (θ : Bits (N.c p.1 p.2))
    (h1 : ¬ χ p.1 = γ) (h : χ p.2 = γ) : (N.orient χ γ γ' p).l z θ = (N.F p.1 p.2).r (z ⟨p.2, h⟩) θ := by
  simp only [Net.orient, dif_neg h1, dif_pos h]

theorem orient_l3 {γ γ' : Fin K} {p : Fin g × Fin g} (z : (N.coarsen χ).S γ) (θ : Bits (N.c p.1 p.2))
    (h1 : ¬ χ p.1 = γ) (h : ¬ χ p.2 = γ) : (N.orient χ γ γ' p).l z θ = 0 := by
  simp only [Net.orient, dif_neg h1, dif_neg h]

theorem orient_r1 {γ γ' : Fin K} {p : Fin g × Fin g} (z : (N.coarsen χ).S γ') (θ : Bits (N.c p.1 p.2))
    (h : χ p.2 = γ') : (N.orient χ γ γ' p).r z θ = (N.F p.1 p.2).r (z ⟨p.2, h⟩) θ := by
  simp only [Net.orient, dif_pos h]

theorem orient_r2 {γ γ' : Fin K} {p : Fin g × Fin g} (z : (N.coarsen χ).S γ') (θ : Bits (N.c p.1 p.2))
    (h1 : ¬ χ p.2 = γ') (h : χ p.1 = γ') : (N.orient χ γ γ' p).r z θ = (N.F p.1 p.2).l (z ⟨p.1, h⟩) θ := by
  simp only [Net.orient, dif_neg h1, dif_pos h]

theorem orient_r3 {γ γ' : Fin K} {p : Fin g × Fin g} (z : (N.coarsen χ).S γ') (θ : Bits (N.c p.1 p.2))
    (h1 : ¬ χ p.2 = γ') (h : ¬ χ p.1 = γ') : (N.orient χ γ γ' p).r z θ = 0 := by
  simp only [Net.orient, dif_neg h1, dif_neg h]

theorem coarsen_l (H : CoarsenHyp m B σ₀ A P N κ χ) (hvm : P.vm < B) {σ : ℕ → ℕ} (hσ : Ag B σ₀ σ)
    (γ γ' : Fin K) (z : (N.coarsen χ).S γ) (q : ℕ) (hγ : σ P.w = γ) (hγ' : σ (P.w + 1) = γ')
    (hz : σ (P.w + 2) = (κ.coarsen χ).e γ z) (hq : σ (P.w + 3) = q) :
    ZR m (Ex.eval σ A (CoarsenEx.l P)) (((N.coarsen χ).F γ γ').l z (bdec _ q)) := by
  have hu := H.hu; have hw := H.hw; have hm := H.hm
  have hmσ : σ P.vm = m := by rw [hσ _ hvm]; exact H.rep.hm
  rw [Net.coarsen_l_code N H.hg]
  unfold CoarsenEx.l
  refine ZR_zprod hmσ H.hm (P.w + 4) (by simp only [Ex.eval, H.gE σ hσ]) _ fun k _ => ?_
  have h1 : Ag B σ₀ (Function.update σ (P.w + 4) k) := hσ.upd (by omega) k
  rw [eval_atPair H h1 (P.w + 4) le_rfl, Function.update_self]
  obtain ⟨h2, ha, hb, hk, hrest, hvm2⟩ := pair_env H hvm hσ k
  generalize Function.update (Function.update (Function.update σ (P.w + 4) k) P.u (k / g % g)) (P.u + 1) (k % g)
    = σ2 at h2 ha hb hk hrest hvm2 ⊢
  have hw2 := (hrest P.w le_rfl (by omega)).trans hγ
  have hw2' := (hrest (P.w + 1) (by omega) (by omega)).trans hγ'
  have hz2 := (hrest (P.w + 2) (by omega) (by omega)).trans hz
  have hq2 := (hrest (P.w + 3) (by omega) (by omega)).trans hq
  rw [eval_ifEq, eval_usedE H h2 γ γ' hw2 hw2' _ _ ha hb]
  simp only [Prod.mk.eta]
  by_cases hU : Net.UsedP χ γ γ' (Net.pairOf g H.hg k)
  · rw [if_pos hU, if_pos hU]
    simp only [Ex.eval, if_true]
    have hoff : Ex.eval σ2 A (offE P) = offR (fun p => N.c p.1 p.2) (Net.UsedP χ γ γ') (Net.pairOf g H.hg) k := by
      unfold offE
      rw [eval_usedSum H h2 γ γ' hw2 hw2' (P.w + 5) (by omega)]
      simp [Ex.eval, hk]
    rw [eval_pow2, hoff, hq2]
    set q' := q / 2 ^ offR (fun p => N.c p.1 p.2) (Net.UsedP χ γ γ') (Net.pairOf g H.hg) k
    set σ3 := Function.update σ2 (P.u + 3) q'
    have h3 : Ag B σ₀ σ3 := h2.upd (by omega) _
    have ha3 : σ3 P.u = (Net.pairOf g H.hg k).1 := by simp only [σ3]; rw [upd_ne _ (by omega), ha]
    have hb3 : σ3 (P.u + 1) = (Net.pairOf g H.hg k).2 := by simp only [σ3]; rw [upd_ne _ (by omega), hb]
    have hw3 : σ3 P.w = γ := by simp only [σ3]; rw [upd_ne _ (by omega), hw2]
    have hz3 : σ3 (P.w + 2) = (κ.coarsen χ).e γ z := by simp only [σ3]; rw [upd_ne _ (by omega), hz2]
    have hq3 : σ3 (P.u + 3) = q' := by simp [σ3]
    rw [eval_ifEq, H.χE σ3 h3 _ ha3, eval_ifEq, eval_chiB H h3 _ hb3]
    simp only [Ex.eval, hw3]
    by_cases hA : χ (Net.pairOf g H.hg k).1 = γ
    · rw [if_pos (show ((χ (Net.pairOf g H.hg k).1 : Fin K) : ℕ) = γ by rw [hA]), orient_l1 z _ hA]
      refine H.rep.l _ (h3.upd (by omega) _) _ _ hU.1 _ q'
        (by simp only [NVars.std]; rw [upd_ne _ (by omega), ha3])
        (by simp only [NVars.std]; rw [upd_ne _ (by omega), hb3])
        (by simp only [NVars.std]; rw [Function.update_self]; exact eval_digE' H h3 (by omega) γ hw3 z hz3 _ ha3 hA)
        (by simp only [NVars.std]; rw [upd_ne _ (by omega), hq3])
    · rw [if_neg (fun h' => hA (Fin.ext h'))]
      by_cases hB : χ (Net.pairOf g H.hg k).2 = γ
      · rw [if_pos (show ((χ (Net.pairOf g H.hg k).2 : Fin K) : ℕ) = γ by rw [hB]), orient_l2 z _ hA hB]
        refine H.rep.r _ (h3.upd (by omega) _) _ _ hU.1 _ q'
          (by simp only [NVars.std]; rw [upd_ne _ (by omega), ha3])
          (by simp only [NVars.std]; rw [upd_ne _ (by omega), hb3])
          (by simp only [NVars.std]; rw [Function.update_self]; exact eval_digB' H h3 (by omega) γ hw3 z hz3 _ hb3 hB)
          (by simp only [NVars.std]; rw [upd_ne _ (by omega), hq3])
      · rw [if_neg (fun h' => hB (Fin.ext h')), orient_l3 z _ hA hB]
        exact ZR_zero (by omega)
  · rw [if_neg hU, if_neg hU]
    simp only [Ex.eval]
    exact ZR_one H.hm

theorem coarsen_r (H : CoarsenHyp m B σ₀ A P N κ χ) (hvm : P.vm < B) {σ : ℕ → ℕ} (hσ : Ag B σ₀ σ)
    (γ γ' : Fin K) (z : (N.coarsen χ).S γ') (q : ℕ) (hγ : σ P.w = γ) (hγ' : σ (P.w + 1) = γ')
    (hz : σ (P.w + 2) = (κ.coarsen χ).e γ' z) (hq : σ (P.w + 3) = q) :
    ZR m (Ex.eval σ A (CoarsenEx.r P)) (((N.coarsen χ).F γ γ').r z (bdec _ q)) := by
  have hu := H.hu; have hw := H.hw; have hm := H.hm
  have hmσ : σ P.vm = m := by rw [hσ _ hvm]; exact H.rep.hm
  rw [Net.coarsen_r_code N H.hg]
  unfold CoarsenEx.r
  refine ZR_zprod hmσ H.hm (P.w + 4) (by simp only [Ex.eval, H.gE σ hσ]) _ fun k _ => ?_
  have h1 : Ag B σ₀ (Function.update σ (P.w + 4) k) := hσ.upd (by omega) k
  rw [eval_atPair H h1 (P.w + 4) le_rfl, Function.update_self]
  obtain ⟨h2, ha, hb, hk, hrest, hvm2⟩ := pair_env H hvm hσ k
  generalize Function.update (Function.update (Function.update σ (P.w + 4) k) P.u (k / g % g)) (P.u + 1) (k % g)
    = σ2 at h2 ha hb hk hrest hvm2 ⊢
  have hw2 := (hrest P.w le_rfl (by omega)).trans hγ
  have hw2' := (hrest (P.w + 1) (by omega) (by omega)).trans hγ'
  have hz2 := (hrest (P.w + 2) (by omega) (by omega)).trans hz
  have hq2 := (hrest (P.w + 3) (by omega) (by omega)).trans hq
  rw [eval_ifEq, eval_usedE H h2 γ γ' hw2 hw2' _ _ ha hb]
  simp only [Prod.mk.eta]
  by_cases hU : Net.UsedP χ γ γ' (Net.pairOf g H.hg k)
  · rw [if_pos hU, if_pos hU]
    simp only [Ex.eval, if_true]
    have hoff : Ex.eval σ2 A (offE P) = offR (fun p => N.c p.1 p.2) (Net.UsedP χ γ γ') (Net.pairOf g H.hg) k := by
      unfold offE
      rw [eval_usedSum H h2 γ γ' hw2 hw2' (P.w + 5) (by omega)]
      simp [Ex.eval, hk]
    rw [eval_pow2, hoff, hq2]
    set q' := q / 2 ^ offR (fun p => N.c p.1 p.2) (Net.UsedP χ γ γ') (Net.pairOf g H.hg) k
    set σ3 := Function.update σ2 (P.u + 3) q'
    have h3 : Ag B σ₀ σ3 := h2.upd (by omega) _
    have ha3 : σ3 P.u = (Net.pairOf g H.hg k).1 := by simp only [σ3]; rw [upd_ne _ (by omega), ha]
    have hb3 : σ3 (P.u + 1) = (Net.pairOf g H.hg k).2 := by simp only [σ3]; rw [upd_ne _ (by omega), hb]
    have hw3 : σ3 (P.w + 1) = γ' := by simp only [σ3]; rw [upd_ne _ (by omega), hw2']
    have hz3 : σ3 (P.w + 2) = (κ.coarsen χ).e γ' z := by simp only [σ3]; rw [upd_ne _ (by omega), hz2]
    have hq3 : σ3 (P.u + 3) = q' := by simp [σ3]
    rw [eval_ifEq, eval_chiB H h3 _ hb3, eval_ifEq, H.χE σ3 h3 _ ha3]
    simp only [Ex.eval, hw3]
    by_cases hB : χ (Net.pairOf g H.hg k).2 = γ'
    · rw [if_pos (show ((χ (Net.pairOf g H.hg k).2 : Fin K) : ℕ) = γ' by rw [hB]), orient_r1 z _ hB]
      refine H.rep.r _ (h3.upd (by omega) _) _ _ hU.1 _ q'
        (by simp only [NVars.std]; rw [upd_ne _ (by omega), ha3])
        (by simp only [NVars.std]; rw [upd_ne _ (by omega), hb3])
        (by simp only [NVars.std]; rw [Function.update_self]; exact eval_digB' H h3 (by omega) γ' hw3 z hz3 _ hb3 hB)
        (by simp only [NVars.std]; rw [upd_ne _ (by omega), hq3])
    · rw [if_neg (fun h' => hB (Fin.ext h'))]
      by_cases hA : χ (Net.pairOf g H.hg k).1 = γ'
      · rw [if_pos (show ((χ (Net.pairOf g H.hg k).1 : Fin K) : ℕ) = γ' by rw [hA]), orient_r2 z _ hB hA]
        refine H.rep.l _ (h3.upd (by omega) _) _ _ hU.1 _ q'
          (by simp only [NVars.std]; rw [upd_ne _ (by omega), ha3])
          (by simp only [NVars.std]; rw [upd_ne _ (by omega), hb3])
          (by simp only [NVars.std]; rw [Function.update_self]; exact eval_digE' H h3 (by omega) γ' hw3 z hz3 _ ha3 hA)
          (by simp only [NVars.std]; rw [upd_ne _ (by omega), hq3])
      · rw [if_neg (fun h' => hA (Fin.ext h')), orient_r3 z _ hB hA]
        exact ZR_zero (by omega)
  · rw [if_neg hU, if_neg hU]
    simp only [Ex.eval]
    exact ZR_one H.hm

/-- **The coarsened network, as expressions.** -/
theorem coarsen_rep (H : CoarsenHyp m B σ₀ A P N κ χ) (hvm : P.vm < B) :
    NRep m P.vm B σ₀ A (NVars.std P.w) (CoarsenEx.nex P) (N.coarsen χ) (κ.coarsen χ) where
  hm := H.rep.hm
  sz σ hσ γ hγ := coarsen_sz H hσ γ hγ
  W σ hσ γ z hγ hz := coarsen_W H hvm hσ γ z hγ hz
  c σ hσ γ γ' _ hγ hγ' := coarsen_c H hσ γ γ' hγ hγ'
  l σ hσ γ γ' _ z q hγ hγ' hz hq := coarsen_l H hvm hσ γ γ' z q hγ hγ' hz hq
  r σ hσ γ γ' _ z q hγ hγ' hz hq := coarsen_r H hvm hσ γ γ' z q hγ hγ' hz hq

end Proofs

end Factoring.Aux
