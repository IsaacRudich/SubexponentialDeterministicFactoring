/-
Networks (the paper's Definition 2, value part) and their coarsening by a grouping (the value half of Lemma 1).

* `Net R g`: nodes `Fin g`; node `a` has a finite set of settings `S a` and a weight `W a : S a → R`; each pair
  `a < b` has an explicit factorization `F a b` through `c a b` bits (`Fac`, from `Bits`), whose value is the pair
  factor `Ψ_{a,b}`.  The value (24) is `∑_z ∏_a W_a(z_a) ∏_{a<b} Ψ_{a,b}(z_a, z_b)` (`Net.value`).
* `Net.coarsen χ`: for a grouping `χ : Fin g → Fin K`, the network on the groups: a setting of group `γ` is a setting
  of each of its nodes, its weight is the product of its nodes' weights and of the pair factors inside the group, and
  the factorization of a pair of groups is the product (`Fac.prodList`) of the factorizations of the pairs of nodes
  between them, through `Y_{γ,γ'} = ∑ c_{a,b}` bits.  `value_coarsen`: the value is unchanged.

Costs (`Fits`, the total `U`) are in `Grouping.lean`; the passage to a written-out clique is in `Clique.lean`.

Not an audit surface.
-/
module

public import FactoringAux.Bits
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Data.List.ProdSigma

@[expose] public section

namespace Factoring.Aux

open Finset

/-! ### More factorization combinators -/

namespace Fac

variable {R : Type*} [CommSemiring R] {X Y : Type*}

/-- The two sides exchanged. -/
def swap {c : ℕ} (f : Fac R X Y c) : Fac R Y X c := ⟨f.r, f.l⟩

@[simp] theorem eval_swap {c : ℕ} (f : Fac R X Y c) (x : X) (y : Y) : f.swap.eval y x = f.eval x y := by
  simp only [eval, swap, mul_comm]

/-- The product of a list of factorizations, through the sum of their lengths (blocks in list order). -/
def prodList {ι : Type*} (c : ι → ℕ) (F : ∀ i, Fac R X Y (c i)) : (l : List ι) → Fac R X Y (l.map c).sum
  | [] => one.cast (by simp)
  | i :: l => ((F i).mul (prodList c F l)).cast (by simp)

@[simp] theorem eval_prodList {ι : Type*} (c : ι → ℕ) (F : ∀ i, Fac R X Y (c i)) (l : List ι) (x : X) (y : Y) :
    (prodList c F l).eval x y = (l.map fun i => (F i).eval x y).prod := by
  induction l with
  | nil => simp [prodList]
  | cons i l ih => simp [prodList, eval_mul, ih]

/-- `[θ = 0]` on both sides: value `1`, through any number of bits (used to pad). -/
def unit (d : ℕ) : Fac R X Y d :=
  ⟨fun _ θ => if θ = zeroBits d then 1 else 0, fun _ θ => if θ = zeroBits d then 1 else 0⟩

@[simp] theorem eval_unit (d : ℕ) (x : X) (y : Y) : (unit d : Fac R X Y d).eval x y = 1 := by
  simp [eval, unit]

/-- Pad to `L ≥ c` bits: the extra bits must be `0`. -/
def pad {c : ℕ} (f : Fac R X Y c) (L : ℕ) (h : c ≤ L) : Fac R X Y L :=
  (f.mul (unit (L - c))).cast (by omega)

@[simp] theorem eval_pad {c : ℕ} (f : Fac R X Y c) (L : ℕ) (h : c ≤ L) (x : X) (y : Y) :
    (f.pad L h).eval x y = f.eval x y := by
  simp [pad, eval_mul]

end Fac

/-! ### Pairs -/

/-- The pairs `a < b` of nodes. -/
def pairs (g : ℕ) : Finset (Fin g × Fin g) := univ.filter (fun p => p.1 < p.2)

@[simp] theorem mem_pairs {g : ℕ} {p : Fin g × Fin g} : p ∈ pairs g ↔ p.1 < p.2 := by simp [pairs]

/-- The pairs `a < b`, as a list (lexicographic). -/
def pairsList (g : ℕ) : List (Fin g × Fin g) :=
  (List.finRange g ×ˢ List.finRange g).filter (fun p => decide (p.1 < p.2))

theorem pairsList_nodup (g : ℕ) : (pairsList g).Nodup :=
  ((List.nodup_finRange g).product (List.nodup_finRange g)).filter _

theorem mem_pairsList {g : ℕ} {p : Fin g × Fin g} : p ∈ pairsList g ↔ p.1 < p.2 := by
  rcases p with ⟨a, b⟩
  simp [pairsList, List.mem_product]

/-! ### Networks -/

/-- A network on `Fin g` (Definition 2, without the cost parameters). -/
structure Net (R : Type*) [CommRing R] (g : ℕ) where
  /-- The settings of each node. -/
  S : Fin g → Type
  /-- They are finite, -/
  fS : ∀ a, Fintype (S a)
  /-- with decidable equality. -/
  dS : ∀ a, DecidableEq (S a)
  /-- The node weights. -/
  W : ∀ a, S a → R
  /-- Shared bits of each pair (used for `a < b`). -/
  c : Fin g → Fin g → ℕ
  /-- The factorization of each pair factor (used for `a < b`). -/
  F : ∀ a b, Fac R (S a) (S b) (c a b)

attribute [instance] Net.fS Net.dS

namespace Net

variable {R : Type*} [CommRing R] {g : ℕ}

/-- The pair factor `Ψ_{a,b}`. -/
def Ψ (N : Net R g) (a b : Fin g) (za : N.S a) (zb : N.S b) : R := (N.F a b).eval za zb

/-- The value of a network, eq. (24). -/
def value (N : Net R g) : R :=
  ∑ z : (∀ a, N.S a), (∏ a, N.W a (z a)) * ∏ p ∈ pairs g, N.Ψ p.1 p.2 (z p.1) (z p.2)

/-! ### Coarsening by a grouping -/

variable {K : ℕ}

/-- `p` joins groups `γ` and `γ'` (in either orientation). -/
def Cross (χ : Fin g → Fin K) (γ γ' : Fin K) (p : Fin g × Fin g) : Prop :=
  (χ p.1 = γ ∧ χ p.2 = γ') ∨ (χ p.1 = γ' ∧ χ p.2 = γ)

instance (χ : Fin g → Fin K) (γ γ' : Fin K) : DecidablePred (Cross χ γ γ') := fun _ => by
  unfold Cross; infer_instance

/-- The pairs of nodes between groups `γ` and `γ'`, in the order of `pairsList`. -/
def crossList (χ : Fin g → Fin K) (γ γ' : Fin K) : List (Fin g × Fin g) :=
  (pairsList g).filter (fun p => decide (Cross χ γ γ' p))

/-- The factorization of pair `p` between the settings of groups `γ` and `γ'`, in the right orientation. -/
def orient (N : Net R g) (χ : Fin g → Fin K) (γ γ' : Fin K) (p : Fin g × Fin g) :
    Fac R (∀ a : {a // χ a = γ}, N.S a) (∀ a : {a // χ a = γ'}, N.S a) (N.c p.1 p.2) where
  l z θ := if h : χ p.1 = γ then (N.F p.1 p.2).l (z ⟨p.1, h⟩) θ
    else if h : χ p.2 = γ then (N.F p.1 p.2).r (z ⟨p.2, h⟩) θ else 0
  r z θ := if h : χ p.2 = γ' then (N.F p.1 p.2).r (z ⟨p.2, h⟩) θ
    else if h : χ p.1 = γ' then (N.F p.1 p.2).l (z ⟨p.1, h⟩) θ else 0

/-- The network on the groups. -/
def coarsen (N : Net R g) (χ : Fin g → Fin K) : Net R K where
  S γ := ∀ a : {a // χ a = γ}, N.S a
  fS _ := inferInstance
  dS _ := inferInstance
  W γ z := (∏ a : {a // χ a = γ}, N.W a (z a)) *
    ∏ p ∈ pairs g, (if h : χ p.1 = γ ∧ χ p.2 = γ then N.Ψ p.1 p.2 (z ⟨p.1, h.1⟩) (z ⟨p.2, h.2⟩) else 1)
  c γ γ' := ((crossList χ γ γ').map (fun p => N.c p.1 p.2)).sum
  F γ γ' := Fac.prodList (fun p => N.c p.1 p.2) (fun p => N.orient χ γ γ' p) (crossList χ γ γ')

theorem coarsen_F_eval (N : Net R g) (χ : Fin g → Fin K) (γ γ' : Fin K) (z : (N.coarsen χ).S γ)
    (z' : (N.coarsen χ).S γ') :
    ((N.coarsen χ).F γ γ').eval z z' = ((crossList χ γ γ').map fun p => (N.orient χ γ γ' p).eval z z').prod :=
  Fac.eval_prodList _ _ _ _ _

/-- Spread a global setting over the groups. -/
def spread (N : Net R g) (χ : Fin g → Fin K) (z : ∀ a, N.S a) : ∀ γ, (N.coarsen χ).S γ :=
  fun _ a => z a

/-- `spread` is a bijection. -/
def spreadEquiv (N : Net R g) (χ : Fin g → Fin K) : (∀ a, N.S a) ≃ (∀ γ, (N.coarsen χ).S γ) where
  toFun := N.spread χ
  invFun z' a := z' (χ a) ⟨a, rfl⟩
  left_inv _ := rfl
  right_inv z' := by
    funext γ a
    rcases a with ⟨a, rfl⟩
    rfl

theorem eval_orient (N : Net R g) (χ : Fin g → Fin K) {γ γ' : Fin K} (hne : γ ≠ γ') {p : Fin g × Fin g}
    (hp : Cross χ γ γ' p) (z : ∀ a, N.S a) :
    (N.orient χ γ γ' p).eval (N.spread χ z γ) (N.spread χ z γ') = N.Ψ p.1 p.2 (z p.1) (z p.2) := by
  rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · simp only [Fac.eval, orient, spread, dif_pos h1, dif_pos h2, Ψ]
  · have h1' : χ p.1 ≠ γ := h1 ▸ Ne.symm hne
    have h2' : χ p.2 ≠ γ' := h2 ▸ hne
    simp only [Fac.eval, orient, spread, dif_neg h1', dif_pos h2, dif_neg h2', dif_pos h1, Ψ]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

/-- The key of a pair: its two groups, in order. -/
def key (χ : Fin g → Fin K) (p : Fin g × Fin g) : Fin K × Fin K := (min (χ p.1) (χ p.2), max (χ p.1) (χ p.2))

theorem cross_iff (χ : Fin g → Fin K) (p : Fin g × Fin g) (q : Fin K × Fin K) :
    (q ∈ pairs K ∧ Cross χ q.1 q.2 p) ↔ (χ p.1 ≠ χ p.2 ∧ key χ p = q) := by
  rcases q with ⟨γ, γ'⟩
  simp only [mem_pairs, Cross, key, Prod.mk.injEq]
  constructor
  · rintro ⟨hlt, (⟨h1, h2⟩ | ⟨h1, h2⟩)⟩ <;> subst h1 h2
    · exact ⟨hlt.ne, min_eq_left hlt.le, max_eq_right hlt.le⟩
    · exact ⟨hlt.ne', min_eq_right hlt.le, max_eq_left hlt.le⟩
  · rintro ⟨hne, h1, h2⟩
    rcases lt_or_gt_of_ne hne with h | h
    · rw [min_eq_left h.le] at h1; rw [max_eq_right h.le] at h2
      subst h1 h2; exact ⟨h, Or.inl ⟨rfl, rfl⟩⟩
    · rw [min_eq_right h.le] at h1; rw [max_eq_left h.le] at h2
      subst h1 h2; exact ⟨h, Or.inr ⟨rfl, rfl⟩⟩

/-- Lemma 1, the value: grouping does not change the value. -/
theorem value_coarsen (N : Net R g) (χ : Fin g → Fin K) : (N.coarsen χ).value = N.value := by
  unfold value
  rw [← (N.spreadEquiv χ).sum_comp]
  refine Finset.sum_congr rfl fun z _ => ?_
  show (∏ γ, (N.coarsen χ).W γ (N.spread χ z γ)) *
      ∏ q ∈ pairs K, ((N.coarsen χ).F q.1 q.2).eval (N.spread χ z q.1) (N.spread χ z q.2) = _
  -- the pair factors between groups
  have hcross : ∀ q ∈ pairs K, ((N.coarsen χ).F q.1 q.2).eval (N.spread χ z q.1) (N.spread χ z q.2) =
      ∏ p ∈ pairs g, (if Cross χ q.1 q.2 p then N.Ψ p.1 p.2 (z p.1) (z p.2) else 1) := by
    intro q hq
    have hne : q.1 ≠ q.2 := (mem_pairs.mp hq).ne
    rw [coarsen_F_eval, crossList, ← Finset.prod_filter, ← List.prod_toFinset _ ((pairsList_nodup g).filter _)]
    · refine Finset.prod_congr ?_ fun p hp => ?_
      · ext p; simp [mem_pairsList]
      · exact eval_orient N χ hne (Finset.mem_filter.mp hp).2 z
  rw [Finset.prod_congr rfl hcross, Finset.prod_comm]
  -- the weights and the pair factors inside groups
  have hW : ∏ γ, (N.coarsen χ).W γ (N.spread χ z γ) =
      (∏ a, N.W a (z a)) * ∏ p ∈ pairs g, (if χ p.1 = χ p.2 then N.Ψ p.1 p.2 (z p.1) (z p.2) else 1) := by
    simp only [coarsen, spread]
    rw [Finset.prod_mul_distrib, Fintype.prod_fiberwise χ (fun a => N.W a (z a)), Finset.prod_comm]
    congr 1
    refine Finset.prod_congr rfl fun p _ => ?_
    by_cases h : χ p.1 = χ p.2
    · rw [if_pos h, Finset.prod_eq_single (χ p.1)]
      · rw [dif_pos ⟨rfl, h.symm⟩]
      · intro γ _ hγ; rw [dif_neg (fun h' => hγ h'.1.symm)]
      · simp
    · rw [if_neg h]
      exact Finset.prod_eq_one fun γ _ => dif_neg (fun h' => h (h'.1.trans h'.2.symm))
  have hX : ∀ p ∈ pairs g, ∏ q ∈ pairs K, (if Cross χ q.1 q.2 p then N.Ψ p.1 p.2 (z p.1) (z p.2) else 1) =
      if χ p.1 ≠ χ p.2 then N.Ψ p.1 p.2 (z p.1) (z p.2) else 1 := by
    intro p _
    rw [← Finset.prod_filter]
    have : (pairs K).filter (fun q => Cross χ q.1 q.2 p) =
        if χ p.1 ≠ χ p.2 then {key χ p} else ∅ := by
      ext q
      rw [Finset.mem_filter, cross_iff]
      split_ifs with h <;> simp [h, eq_comm]
    rw [this]
    split_ifs <;> simp
  rw [hW, Finset.prod_congr rfl hX, mul_assoc, ← Finset.prod_mul_distrib]
  congr 2
  funext p
  by_cases h : χ p.1 = χ p.2 <;> simp [h]

end Net

end Factoring.Aux
