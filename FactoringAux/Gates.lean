/-
Gate networks as networks ("functional circuits", in the form the clustering uses).

A gate network `GNet R ι` on a finite index type `ι`: gate `i` has finite settings `S i` and a weight `W i`
(`0` or `1`); each ordered pair `(i, j)` has a width `c i j` (symmetric) and a message `v i j : S i → ℕ` below
`2^(c i j)` (so `0` when the gates do not talk).  Gates `i ≠ j` agree on `z` when `v i j (z i) = v j i (z j)`.

* `bnum`: the number a bit string writes (`bitsEquiv : Bits c ≃ Fin (2^c)`).
* `Fac.numTest c v v'`: the equality test of two messages through `c` bits; `eval_numTest`.
* `GNet.toNet e`: for an enumeration `e : ι ≃ Fin g`, the network whose pair factors are these tests.
* **`value_toNet`**: its value is the number of `Good` settings (every weight `1`, every pair agreeing).

Not an audit surface.
-/
module

public import FactoringAux.Net
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

namespace Factoring.Aux

open Finset

/-- `Bits c ≃ Fin (2^c)`, bit `i` of weight `2^i`. -/
def bitsEquiv (c : ℕ) : Bits c ≃ Fin (2 ^ c) :=
  (Equiv.arrowCongr (Equiv.refl _) finTwoEquiv.symm).trans finFunctionFinEquiv

/-- The number a bit string writes. -/
def bnum {c : ℕ} (θ : Bits c) : ℕ := (bitsEquiv c θ).val

namespace Fac

variable {R : Type*} [CommRing R] {X Y : Type*}

/-- The equality test of the messages `v x` and `v' y`, through `c` bits. -/
def numTest (c : ℕ) (v : X → ℕ) (v' : Y → ℕ) : Fac R X Y c :=
  ⟨fun x θ => if v x = bnum θ then 1 else 0, fun y θ => if v' y = bnum θ then 1 else 0⟩

theorem eval_numTest (c : ℕ) (v : X → ℕ) (v' : Y → ℕ) (x : X) (y : Y) :
    (numTest c v v' : Fac R X Y c).eval x y = if v x = v' y ∧ v' y < 2 ^ c then 1 else 0 := by
  unfold eval numTest
  simp only [ite_mul, one_mul, zero_mul]
  refine (Fintype.sum_equiv (bitsEquiv c) _ (fun t : Fin (2 ^ c) =>
    if v x = t.val then (if v' y = t.val then (1 : R) else 0) else 0) (fun θ => rfl)).trans ?_
  by_cases h : v' y < 2 ^ c
  · rw [Finset.sum_eq_single ⟨v' y, h⟩]
    · by_cases he : v x = v' y <;> simp [he, h]
    · intro t _ ht
      have : v' y ≠ t.val := fun e => ht (Fin.ext e.symm)
      simp [this]
    · simp
  · rw [if_neg (fun hh => h hh.2)]
    refine Finset.sum_eq_zero fun t _ => ?_
    have : v' y ≠ t.val := fun e => h (e ▸ t.isLt)
    simp [this]

end Fac

/-- A gate network on `ι`. -/
structure GNet (R : Type*) [CommRing R] (ι : Type) where
  /-- The settings of each gate. -/
  S : ι → Type
  /-- They are finite, -/
  fS : ∀ i, Fintype (S i)
  /-- with decidable equality. -/
  dS : ∀ i, DecidableEq (S i)
  /-- The weights (`0` or `1`). -/
  W : ∀ i, S i → R
  /-- The width of the messages between two gates. -/
  c : ι → ι → ℕ
  /-- The message gate `i` sends to gate `j`. -/
  v : ∀ i : ι, ι → S i → ℕ

attribute [instance] GNet.fS GNet.dS

namespace GNet

variable {R : Type*} [CommRing R] {ι : Type} {g : ℕ}

/-- The network of a gate network, for an enumeration of the gates. -/
def toNet (G : GNet R ι) (e : ι ≃ Fin g) : Net R g where
  S a := G.S (e.symm a)
  fS _ := inferInstance
  dS _ := inferInstance
  W _ z := G.W _ z
  c a b := G.c (e.symm a) (e.symm b)
  F a b := Fac.numTest _ (G.v (e.symm a) (e.symm b)) (G.v (e.symm b) (e.symm a))

/-- A setting of every gate is good: every weight is `1` and every two gates agree. -/
def Good (G : GNet R ι) (z : ∀ i, G.S i) : Prop :=
  (∀ i, G.W i (z i) = 1) ∧ ∀ i j, i ≠ j → G.v i j (z i) = G.v j i (z j)

open Classical in
/-- **The value of a gate network is the number of good settings.** -/
theorem value_toNet [Fintype ι] (G : GNet R ι) (e : ι ≃ Fin g)
    (hW : ∀ i z, G.W i z = 0 ∨ G.W i z = 1) (hv : ∀ i j z, G.v i j z < 2 ^ G.c i j) :
    (G.toNet e).value = ((univ.filter G.Good).card : R) := by
  rw [← Finset.sum_boole]
  unfold Net.value
  symm
  refine Fintype.sum_equiv (Equiv.piCongrLeft' (fun i => G.S i) e) _ _ (fun z => ?_)
  symm
  -- the weights
  have hW1 : ∀ i, G.W i (z i) = if G.W i (z i) = 1 then 1 else 0 := by
    intro i
    rcases hW i (z i) with h | h
    · by_cases h1 : G.W i (z i) = 1
      · rw [if_pos h1, h1]
      · rw [if_neg h1, h]
    · rw [if_pos h, h]
  have hWprod : (∏ a, (G.toNet e).W a ((Equiv.piCongrLeft' (fun i => G.S i) e) z a)) =
      if ∀ i, G.W i (z i) = 1 then 1 else 0 := by
    have : (∏ a, (G.toNet e).W a ((Equiv.piCongrLeft' (fun i => G.S i) e) z a)) = ∏ i, G.W i (z i) :=
      (Fintype.prod_equiv e.symm _ _ fun a => rfl)
    rw [this, Finset.prod_congr rfl fun i _ => hW1 i, Finset.prod_boole]
    simp
  -- the pairs
  have hP : ∀ p ∈ pairs g, (G.toNet e).Ψ p.1 p.2 ((Equiv.piCongrLeft' (fun i => G.S i) e) z p.1)
      ((Equiv.piCongrLeft' (fun i => G.S i) e) z p.2) =
      if G.v (e.symm p.1) (e.symm p.2) (z (e.symm p.1)) = G.v (e.symm p.2) (e.symm p.1) (z (e.symm p.2))
      then 1 else 0 := by
    intro p _
    have := Fac.eval_numTest (R := R) (G.c (e.symm p.1) (e.symm p.2)) (G.v (e.symm p.1) (e.symm p.2))
      (G.v (e.symm p.2) (e.symm p.1)) (z (e.symm p.1)) (z (e.symm p.2))
    refine this.trans ?_
    have hb := hv (e.symm p.1) (e.symm p.2) (z (e.symm p.1))
    by_cases h : G.v (e.symm p.1) (e.symm p.2) (z (e.symm p.1)) =
        G.v (e.symm p.2) (e.symm p.1) (z (e.symm p.2))
    · rw [if_pos ⟨h, h ▸ hb⟩, if_pos h]
    · rw [if_neg (fun hh => h hh.1), if_neg h]
  rw [hWprod, Finset.prod_congr rfl hP, Finset.prod_boole]
  have hpairs : (∀ p ∈ pairs g, G.v (e.symm p.1) (e.symm p.2) (z (e.symm p.1)) =
      G.v (e.symm p.2) (e.symm p.1) (z (e.symm p.2))) ↔ ∀ i j, i ≠ j → G.v i j (z i) = G.v j i (z j) := by
    constructor
    · intro h i j hij
      obtain ⟨a, rfl⟩ := e.symm.surjective i
      obtain ⟨b, rfl⟩ := e.symm.surjective j
      have hne : a ≠ b := fun h' => hij (by rw [h'])
      rcases lt_or_gt_of_ne hne with hl | hl
      · exact h (a, b) (mem_pairs.mpr hl)
      · exact (h (b, a) (mem_pairs.mpr hl)).symm
    · intro h p hp
      exact h _ _ (fun h' => (ne_of_lt (mem_pairs.mp hp)) (e.symm.injective h'))
  simp only [hpairs]
  unfold Good
  by_cases h1 : ∀ i, G.W i (z i) = 1 <;> by_cases h2 : ∀ i j, i ≠ j → G.v i j (z i) = G.v j i (z j) <;>
    simp [h1, h2]

end GNet

end Factoring.Aux
