/-
Codes for networks, and the coarsened network (`Net.coarsen`, Lemma 1) read at codes.

* `Coding N`: positive sizes `s` and `e a : N.S a ≃ Fin (s a)`.
* `Coding.coarsen κ χ`: the coding of the groups' settings, mixed radix over **all** nodes with size `1` off the group
  (`sg`), so no ranks are needed.  `coarsen_digit`: the code of member `a` is digit `a`.
* Products over a subtype, over `Fin g`, over `pairs g` as products over ranges (`prod_subtype_dite`,
  `prod_fin_range`, `prod_pairs_range`).
* `getElem_finRange_product`; **`plL_eq_range`** (a fold over a list given by an index function, closed form with
  block offsets `offR`).
* **`coarsen_l_code`**, `coarsen_r_code`: the factor functions of the coarsened network at a code, as products over
  the pair indices `k < g·g` (`k = a·g + b`) with offsets.  `coarsen_c_code`: the widths.

Not an audit surface.
-/
module

public import FactoringAux.EngineRep
public import FactoringAux.Lemma1

@[expose] public section

namespace Factoring.Aux

open Finset

variable {R : Type*} [CommRing R]

/-- Codes for the settings of a network. -/
structure Coding {g : ℕ} (N : Net R g) where
  /-- The number of settings of node `a` (by index). -/
  s : ℕ → ℕ
  /-- Positive. -/
  pos : ∀ a : Fin g, 0 < s a
  /-- The codes. -/
  e : ∀ a : Fin g, N.S a ≃ Fin (s a)

/-! ### Products over ranges -/

theorem prod_subtype_dite {g : ℕ} {M : Type*} [CommMonoid M] (p : Fin g → Prop) [DecidablePred p]
    (F : {a // p a} → M) : ∏ a : {a // p a}, F a = ∏ a : Fin g, if h : p a then F ⟨a, h⟩ else 1 := by
  have h1 : ∏ a ∈ univ.filter p, (if h : p a then F ⟨a, h⟩ else 1) = ∏ a : {a // p a}, F a := by
    rw [Finset.prod_subtype (p := p) (univ.filter p) (fun a => by simp)]
    exact prod_congr rfl fun a _ => dif_pos a.2
  rw [← h1, Finset.prod_filter_of_ne]
  intro a _ hne
  by_contra h
  exact hne (dif_neg h)

theorem prod_fin_range {g : ℕ} {M : Type*} [CommMonoid M] (f : Fin g → M) :
    ∏ a : Fin g, f a = ∏ a ∈ range g, if h : a < g then f ⟨a, h⟩ else 1 := by
  rw [← Fin.prod_univ_eq_prod_range (fun a => if h : a < g then f ⟨a, h⟩ else 1) g]
  exact prod_congr rfl fun a _ => by rw [dif_pos a.2]

theorem sum_fin_range {g : ℕ} {M : Type*} [AddCommMonoid M] (f : Fin g → M) :
    ∑ a : Fin g, f a = ∑ a ∈ range g, if h : a < g then f ⟨a, h⟩ else 0 := by
  rw [← Fin.sum_univ_eq_sum_range (fun a => if h : a < g then f ⟨a, h⟩ else 0) g]
  exact sum_congr rfl fun a _ => by rw [dif_pos a.2]

theorem prod_pairs_range {g : ℕ} {M : Type*} [CommMonoid M] (f : Fin g × Fin g → M) :
    ∏ p ∈ pairs g, f p = ∏ a ∈ range g, ∏ b ∈ range g,
      if h : a < g ∧ b < g then (if a < b then f (⟨a, h.1⟩, ⟨b, h.2⟩) else 1) else 1 := by
  rw [pairs, prod_filter, ← univ_product_univ, prod_product, prod_fin_range]
  refine prod_congr rfl fun a ha => ?_
  have ha' := mem_range.mp ha
  rw [dif_pos ha', prod_fin_range]
  refine prod_congr rfl fun b hb => ?_
  have hb' := mem_range.mp hb
  rw [dif_pos hb', dif_pos ⟨ha', hb'⟩]
  rfl

theorem sum_pairs_range {g : ℕ} {M : Type*} [AddCommMonoid M] (f : Fin g × Fin g → M) :
    ∑ p ∈ pairs g, f p = ∑ a ∈ range g, ∑ b ∈ range g,
      if h : a < g ∧ b < g then (if a < b then f (⟨a, h.1⟩, ⟨b, h.2⟩) else 0) else 0 := by
  rw [pairs, sum_filter, ← univ_product_univ, sum_product, sum_fin_range]
  refine sum_congr rfl fun a ha => ?_
  have ha' := mem_range.mp ha
  rw [dif_pos ha', sum_fin_range]
  refine sum_congr rfl fun b hb => ?_
  have hb' := mem_range.mp hb
  rw [dif_pos hb', dif_pos ⟨ha', hb'⟩]
  rfl

/-! ### The coding of a coarsened network -/

namespace Coding

variable {g K : ℕ} {N : Net R g}

/-- Sizes for the settings of group `γ`: node `i` counts with its size if it is in the group, else `1`. -/
def sg (κ : Coding N) (χ : Fin g → Fin K) (γ : Fin K) (i : ℕ) : ℕ :=
  if h : i < g then (if χ ⟨i, h⟩ = γ then κ.s i else 1) else 1

theorem sg_pos (κ : Coding N) (χ : Fin g → Fin K) (γ : Fin K) (i : ℕ) : 0 < sg κ χ γ i := by
  unfold sg; split_ifs with h1 h2
  · exact κ.pos ⟨i, h1⟩
  · exact Nat.one_pos
  · exact Nat.one_pos

theorem sg_mem (κ : Coding N) (χ : Fin g → Fin K) (γ : Fin K) {a : Fin g} (h : χ a = γ) :
    sg κ χ γ a = κ.s a := by simp [sg, h]

theorem sg_nmem (κ : Coding N) (χ : Fin g → Fin K) (γ : Fin K) {a : Fin g} (h : ¬ χ a = γ) :
    sg κ χ γ a = 1 := by simp [sg, h]

/-- The group's settings as a family over all nodes. -/
def midE (κ : Coding N) (χ : Fin g → Fin K) (γ : Fin K) :
    (∀ a : {a // χ a = γ}, N.S a) ≃ (∀ i : Fin g, Fin (sg κ χ γ i)) where
  toFun z i := if h : χ i = γ then Fin.cast (sg_mem κ χ γ h).symm (κ.e i (z ⟨i, h⟩))
    else ⟨0, by rw [sg_nmem κ χ γ h]; exact Nat.one_pos⟩
  invFun w a := (κ.e a).symm (Fin.cast (sg_mem κ χ γ a.2) (w a))
  left_inv z := by
    funext a
    simp only [dif_pos a.2]
    simp
  right_inv w := by
    funext i
    by_cases h : χ i = γ
    · simp only [dif_pos h]
      apply Fin.ext
      simp
    · simp only [dif_neg h]
      apply Fin.ext
      have h1 := (w i).2
      have h2 := sg_nmem κ χ γ h
      show 0 = (w i).val
      omega

/-- The coding of the coarsened network. -/
def coarsen (κ : Coding N) (χ : Fin g → Fin K) : Coding (N.coarsen χ) where
  s γ := if h : γ < K then pp (sg κ χ ⟨γ, h⟩) g else 1
  pos γ := by rw [dif_pos γ.2]; exact pp_pos fun i _ => sg_pos κ χ γ i
  e γ := (midE κ χ γ).trans ((codeEquiv (sg κ χ γ) g fun i _ => sg_pos κ χ γ i).trans
    (finCongr (by rw [dif_pos γ.2])))

/-- **The code of a member is a digit of the group's code.** -/
theorem coarsen_digit (κ : Coding N) (χ : Fin g → Fin K) (γ : Fin K) (c : Fin ((κ.coarsen χ).s γ))
    (a : {a // χ a = γ}) :
    ((κ.e a (((κ.coarsen χ).e γ).symm c a) : Fin (κ.s a)) : ℕ) = dgx (sg κ χ γ) c a := by
  rw [show ((κ.coarsen χ).e γ).symm c = (κ.midE χ γ).symm ((codeEquiv (κ.sg χ γ) g fun i _ => sg_pos κ χ γ i).symm
      ⟨c, by have := c.2; simp only [coarsen, dif_pos γ.2] at this; exact this⟩) from rfl]
  simp only [midE, Equiv.coe_fn_symm_mk, Equiv.apply_symm_apply, Fin.val_cast, codeEquiv_symm_apply]

end Coding

/-! ### Folds over lists, closed form -/

theorem getElem_finRange_product (g k : ℕ) (hk : k < (List.finRange g ×ˢ List.finRange g).length) :
    (List.finRange g ×ˢ List.finRange g)[k] =
      (⟨k / g, by rw [List.length_product, List.length_finRange] at hk; exact Nat.div_lt_of_lt_mul hk⟩,
       ⟨k % g, by rw [List.length_product, List.length_finRange] at hk
                  exact Nat.mod_lt _ (Nat.pos_of_ne_zero (by rintro rfl; simp at hk))⟩) := by
  have key : ∀ (l : List (Fin g)) (k : ℕ) (hk : k < (l ×ˢ List.finRange g).length),
      (l ×ˢ List.finRange g)[k] = (l[k / g]'(by
          rw [List.length_product, List.length_finRange] at hk
          exact Nat.div_lt_of_lt_mul (by rwa [mul_comm] at hk)),
        ⟨k % g, by rw [List.length_product, List.length_finRange] at hk
                   exact Nat.mod_lt _ (Nat.pos_of_ne_zero (by rintro rfl; simp at hk))⟩) := by
    intro l
    induction l with
    | nil => intro k hk; simp at hk
    | cons a l ih =>
        intro k hk
        have hg : 0 < g := by
          rcases Nat.eq_zero_or_pos g with h | h
          · subst h; simp at hk
          · exact h
        simp only [List.product_cons]
        rw [List.getElem_append]
        split_ifs with h1
        · simp only [List.length_map, List.length_finRange] at h1
          simp [Nat.div_eq_of_lt h1, Nat.mod_eq_of_lt h1]
        · simp only [List.length_map, List.length_finRange] at h1
          rw [ih]
          have e1 : (k - g) / g + 1 = k / g := by
            rw [← Nat.add_div_right _ hg, Nat.sub_add_cancel (by omega)]
          have e2 : (k - g) % g = k % g := by
            conv_rhs => rw [show k = (k - g) + g by omega, Nat.add_mod_right]
          simp only [List.length_map, List.length_finRange]
          simp only [Prod.mk.injEq]
          constructor
          · simp only [← e1, List.getElem_cons_succ]
          · exact Fin.ext e2
  rw [key]
  simp [List.getElem_finRange]

section Fold

variable {X Y ι : Type*} (c : ι → ℕ) (F : ∀ i, Fac R X Y (c i)) (P : ι → Prop) [DecidablePred P]

/-- The offset of item `k`: the widths of the used items before it. -/
def offR (f : ℕ → ι) (k : ℕ) : ℕ := ∑ j ∈ range k, if P (f j) then c (f j) else 0

theorem offR_succ (f : ℕ → ι) (k : ℕ) :
    offR c P f (k + 1) = (if P (f 0) then c (f 0) else 0) + offR c P (fun j => f (j + 1)) k := by
  unfold offR
  rw [sum_range_succ']
  ring

/-- **A block-consuming fold in closed form.** -/
theorem plL_eq_range (x : X) : ∀ (L : List ι) (f : ℕ → ι), (∀ k (h : k < L.length), L[k] = f k) → ∀ q,
    Fac.plL c F P x L q = ∏ k ∈ range L.length,
      if P (f k) then (F (f k)).l x (bdec (c (f k)) (q / 2 ^ offR c P f k)) else 1
  | [], _, _, _ => by simp [Fac.plL]
  | i :: L, f, hf, q => by
      have h0 : i = f 0 := hf 0 (by simp)
      have hf' : ∀ k (h : k < L.length), L[k] = f (k + 1) := fun k h => hf (k + 1) (by simp; omega)
      subst h0
      rw [List.length_cons, prod_range_succ']
      simp only [Fac.plL]
      have off0 : offR c P f 0 = 0 := by simp [offR]
      rw [off0, pow_zero, Nat.div_one]
      by_cases hP : P (f 0)
      · rw [if_pos hP, if_pos hP, plL_eq_range x L _ hf' (q / 2 ^ c (f 0)), mul_comm]
        congr 1
        refine prod_congr rfl fun k _ => ?_
        simp only [offR_succ, if_pos hP, pow_add, Nat.div_div_eq_div_mul]
      · rw [if_neg hP, if_neg hP, plL_eq_range x L _ hf' q, mul_one]
        refine prod_congr rfl fun k _ => ?_
        simp only [offR_succ, if_neg hP, zero_add]

theorem plR_eq_range (y : Y) : ∀ (L : List ι) (f : ℕ → ι), (∀ k (h : k < L.length), L[k] = f k) → ∀ q,
    Fac.plR c F P y L q = ∏ k ∈ range L.length,
      if P (f k) then (F (f k)).r y (bdec (c (f k)) (q / 2 ^ offR c P f k)) else 1
  | [], _, _, _ => by simp [Fac.plR]
  | i :: L, f, hf, q => by
      have h0 : i = f 0 := hf 0 (by simp)
      have hf' : ∀ k (h : k < L.length), L[k] = f (k + 1) := fun k h => hf (k + 1) (by simp; omega)
      subst h0
      rw [List.length_cons, prod_range_succ']
      simp only [Fac.plR]
      have off0 : offR c P f 0 = 0 := by simp [offR]
      rw [off0, pow_zero, Nat.div_one]
      by_cases hP : P (f 0)
      · rw [if_pos hP, if_pos hP, plR_eq_range y L _ hf' (q / 2 ^ c (f 0)), mul_comm]
        congr 1
        refine prod_congr rfl fun k _ => ?_
        simp only [offR_succ, if_pos hP, pow_add, Nat.div_div_eq_div_mul]
      · rw [if_neg hP, if_neg hP, plR_eq_range y L _ hf' q, mul_one]
        refine prod_congr rfl fun k _ => ?_
        simp only [offR_succ, if_neg hP, zero_add]

theorem plL_filter (Q : ι → Prop) [DecidablePred Q] (x : X) : ∀ (L : List ι) (q : ℕ),
    Fac.plL c F P x (L.filter (fun i => decide (Q i))) q = Fac.plL c F (fun i => Q i ∧ P i) x L q
  | [], _ => rfl
  | i :: L, q => by
      by_cases hQ : Q i
      · by_cases hP : P i <;> simp [hQ, hP, Fac.plL, plL_filter Q x L]
      · simp [hQ, Fac.plL, plL_filter Q x L]

theorem plR_filter (Q : ι → Prop) [DecidablePred Q] (y : Y) : ∀ (L : List ι) (q : ℕ),
    Fac.plR c F P y (L.filter (fun i => decide (Q i))) q = Fac.plR c F (fun i => Q i ∧ P i) y L q
  | [], _ => rfl
  | i :: L, q => by
      by_cases hQ : Q i
      · by_cases hP : P i <;> simp [hQ, hP, Fac.plR, plR_filter Q y L]
      · simp [hQ, Fac.plR, plR_filter Q y L]

end Fold

/-! ### The coarsened network at codes -/

namespace Net

variable {g K : ℕ}

/-- The pair with index `k = a·g + b` (`g > 0`). -/
def pairOf (g : ℕ) (hg : 0 < g) (k : ℕ) : Fin g × Fin g := (⟨k / g % g, Nat.mod_lt _ hg⟩, ⟨k % g, Nat.mod_lt _ hg⟩)

/-- A pair used between groups `γ`, `γ'`. -/
abbrev UsedP (χ : Fin g → Fin K) (γ γ' : Fin K) (p : Fin g × Fin g) : Prop := p.1 < p.2 ∧ Cross χ γ γ' p

theorem crossList_eq (χ : Fin g → Fin K) (γ γ' : Fin K) :
    crossList χ γ γ' = (List.finRange g ×ˢ List.finRange g).filter (fun p => decide (UsedP χ γ γ' p)) := by
  unfold crossList pairsList UsedP
  rw [List.filter_filter]
  congr 1
  funext p
  simp only [Bool.decide_and, Bool.and_comm]

theorem pairOf_get (g : ℕ) (hg : 0 < g) (k : ℕ) (hk : k < (List.finRange g ×ˢ List.finRange g).length) :
    (List.finRange g ×ˢ List.finRange g)[k] = pairOf g hg k := by
  rw [getElem_finRange_product]
  have hk' : k / g < g := by
    rw [List.length_product, List.length_finRange] at hk; exact Nat.div_lt_of_lt_mul hk
  simp [pairOf, Nat.mod_eq_of_lt hk']

/-- **The left factor function of the coarsened network at a code.** -/
theorem coarsen_l_code (N : Net R g) (hg : 0 < g) (χ : Fin g → Fin K) (γ γ' : Fin K) (z : (N.coarsen χ).S γ)
    (q : ℕ) :
    ((N.coarsen χ).F γ γ').l z (bdec _ q) = ∏ k ∈ range (g * g),
      if UsedP χ γ γ' (pairOf g hg k) then
        (N.orient χ γ γ' (pairOf g hg k)).l z
          (bdec _ (q / 2 ^ offR (fun p => N.c p.1 p.2) (UsedP χ γ γ') (pairOf g hg) k))
      else 1 := by
  refine (Fac.prodList_l (fun p : Fin g × Fin g => N.c p.1 p.2) (fun p => N.orient χ γ γ' p) z
    (crossList χ γ γ') q).trans ?_
  refine (Fac.plA_filter (fun p : Fin g × Fin g => N.c p.1 p.2) (fun p => N.orient χ γ γ' p) (Cross χ γ γ') z
    (pairsList g) q).trans ?_
  refine (plL_filter _ _ _ (fun p : Fin g × Fin g => p.1 < p.2) z (List.finRange g ×ˢ List.finRange g) q).trans ?_
  refine (plL_eq_range _ _ _ z _ (pairOf g hg) (pairOf_get g hg) q).trans ?_
  rw [List.length_product, List.length_finRange]

/-- The right factor function of the coarsened network at a code. -/
theorem coarsen_r_code (N : Net R g) (hg : 0 < g) (χ : Fin g → Fin K) (γ γ' : Fin K) (z : (N.coarsen χ).S γ')
    (q : ℕ) :
    ((N.coarsen χ).F γ γ').r z (bdec _ q) = ∏ k ∈ range (g * g),
      if UsedP χ γ γ' (pairOf g hg k) then
        (N.orient χ γ γ' (pairOf g hg k)).r z
          (bdec _ (q / 2 ^ offR (fun p => N.c p.1 p.2) (UsedP χ γ γ') (pairOf g hg) k))
      else 1 := by
  refine (Fac.prodList_r (fun p : Fin g × Fin g => N.c p.1 p.2) (fun p => N.orient χ γ γ' p) z
    (crossList χ γ γ') q).trans ?_
  refine (Fac.plB_filter (fun p : Fin g × Fin g => N.c p.1 p.2) (fun p => N.orient χ γ γ' p) (Cross χ γ γ') z
    (pairsList g) q).trans ?_
  refine (plR_filter _ _ _ (fun p : Fin g × Fin g => p.1 < p.2) z (List.finRange g ×ˢ List.finRange g) q).trans ?_
  refine (plR_eq_range _ _ _ z _ (pairOf g hg) (pairOf_get g hg) q).trans ?_
  rw [List.length_product, List.length_finRange]

/-- The widths of the coarsened network. -/
theorem coarsen_c_code (N : Net R g) (hg : 0 < g) (χ : Fin g → Fin K) (γ γ' : Fin K) :
    (N.coarsen χ).c γ γ' = offR (fun p => N.c p.1 p.2) (UsedP χ γ γ') (pairOf g hg) (g * g) := by
  show ((crossList χ γ γ').map (fun p => N.c p.1 p.2)).sum = _
  rw [crossList_eq]
  have : ∀ (L : List (Fin g × Fin g)) (f : ℕ → Fin g × Fin g), (∀ k (h : k < L.length), L[k] = f k) →
      ((L.filter (fun p => decide (UsedP χ γ γ' p))).map (fun p => N.c p.1 p.2)).sum =
        offR (fun p => N.c p.1 p.2) (UsedP χ γ γ') f L.length := by
    intro L
    induction L with
    | nil => intro f _; simp [offR]
    | cons i L ih =>
        intro f hf
        have h0 : i = f 0 := hf 0 (by simp)
        have hf' : ∀ k (h : k < L.length), L[k] = f (k + 1) := fun k h => hf (k + 1) (by simp; omega)
        rw [List.length_cons, offR_succ, ← ih _ hf', ← h0]
        by_cases hP : UsedP χ γ γ' i <;> simp [List.filter_cons, hP]
  rw [this _ (pairOf g hg) (pairOf_get g hg), List.length_product, List.length_finRange]

/-- The weight of the coarsened network. -/
theorem coarsen_W_code (N : Net R g) (χ : Fin g → Fin K) (γ : Fin K) (z : (N.coarsen χ).S γ) :
    (N.coarsen χ).W γ z = (∏ a : Fin g, if h : χ a = γ then N.W a (z ⟨a, h⟩) else 1) *
      ∏ p ∈ pairs g, (if h : χ p.1 = γ ∧ χ p.2 = γ then N.Ψ p.1 p.2 (z ⟨p.1, h.1⟩) (z ⟨p.2, h.2⟩) else 1) := by
  show (∏ a : {a // χ a = γ}, N.W a (z a)) * _ = _
  rw [prod_subtype_dite (fun a => χ a = γ) (fun a => N.W a (z a))]

end Net

end Factoring.Aux
