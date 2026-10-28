/-
Bit strings and explicit factorizations (the paper's Definition 1, with the factor functions kept as data).

* `Bits n`: strings of `n` bits, `Fin n → Bool`.
* `Fac R X Y c`: two functions `l : X → Bits c → R`, `r : Y → Bits c → R`; its value at `(x, y)` is
  `∑ θ, l x θ * r y θ` (`Fac.eval`).  `F` *factors through `c` bits* (`FactorsThrough`) if some `Fac` has value `F`.
* Combinators, each with its value lemma:
  - `mul`  (through `a + b` bits): value = product of values (the paper's observation (a));
  - `add`  (through `a + 1` bits, one selector bit): value = sum of values;
  - `zero` (value 0), `one` (through 0 bits, value 1), `comp` (precompose both sides), `cast` (rename the length);
  - `ofEquiv` (a side that is itself `c` bits factors trivially: `F(z, z') = ∑ θ [z = θ] F(θ, z')`).

The factor functions are explicit, so a program can evaluate them; nothing here is noncomputable.

Not an audit surface.
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Tactic.Ring

@[expose] public section

namespace Factoring.Aux

open Finset

/-- Strings of `n` bits. -/
abbrev Bits (n : ℕ) := Fin n → Bool

/-- The all-zero string. -/
def zeroBits (n : ℕ) : Bits n := fun _ => false

/-- An explicit factorization through `c` bits: the left functions read `X`, the right ones read `Y`. -/
structure Fac (R : Type*) (X Y : Type*) (c : ℕ) where
  /-- The left factor functions. -/
  l : X → Bits c → R
  /-- The right factor functions. -/
  r : Y → Bits c → R

namespace Fac

variable {R : Type*} [CommSemiring R] {X Y X' Y' : Type*}

/-- The function a factorization represents. -/
def eval {c : ℕ} (f : Fac R X Y c) (x : X) (y : Y) : R := ∑ θ : Bits c, f.l x θ * f.r y θ

/-- Pointwise product, through `a + b` bits: the first `a` bits index `f`, the last `b` index `g`. -/
def mul {a b : ℕ} (f : Fac R X Y a) (g : Fac R X Y b) : Fac R X Y (a + b) where
  l x θ := f.l x (fun i => θ (Fin.castAdd b i)) * g.l x (fun i => θ (Fin.natAdd a i))
  r y θ := f.r y (fun i => θ (Fin.castAdd b i)) * g.r y (fun i => θ (Fin.natAdd a i))

theorem eval_mul {a b : ℕ} (f : Fac R X Y a) (g : Fac R X Y b) (x : X) (y : Y) :
    (f.mul g).eval x y = f.eval x y * g.eval x y := by
  unfold eval mul
  rw [← (Fin.appendEquiv a b).sum_comp, Fintype.sum_prod_type, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun θ₁ _ => Finset.sum_congr rfl fun θ₂ _ => ?_
  simp only [Fin.appendEquiv, Equiv.coe_fn_mk, Fin.append_left, Fin.append_right]
  ring

/-- Sum, through `a + 1` bits: the last bit selects `f` (true) or `g` (false). -/
def add {a : ℕ} (f g : Fac R X Y a) : Fac R X Y (a + 1) where
  l x θ := if θ (Fin.last a) then f.l x (Fin.init θ) else g.l x (Fin.init θ)
  r y θ := if θ (Fin.last a) then f.r y (Fin.init θ) else g.r y (Fin.init θ)

theorem eval_add {a : ℕ} (f g : Fac R X Y a) (x : X) (y : Y) :
    (f.add g).eval x y = f.eval x y + g.eval x y := by
  unfold eval add
  rw [← (Fin.snocEquiv (fun _ => Bool)).sum_comp, Fintype.sum_prod_type, Fintype.sum_bool]
  simp [Fin.snocEquiv, Fin.init_snoc, Fin.snoc_last]

/-- The zero function, through any number of bits. -/
def zero (c : ℕ) : Fac R X Y c := ⟨fun _ _ => 0, fun _ _ => 0⟩

@[simp] theorem eval_zero (c : ℕ) (x : X) (y : Y) : (zero c : Fac R X Y c).eval x y = 0 := by
  simp [eval, zero]

/-- The constant `1`, through no bits. -/
def one : Fac R X Y 0 := ⟨fun _ _ => 1, fun _ _ => 1⟩

@[simp] theorem eval_one (x : X) (y : Y) : (one : Fac R X Y 0).eval x y = 1 := by
  simp [eval, one]

/-- Precompose both sides. -/
def comp {c : ℕ} (f : Fac R X Y c) (p : X' → X) (q : Y' → Y) : Fac R X' Y' c :=
  ⟨fun x => f.l (p x), fun y => f.r (q y)⟩

@[simp] theorem eval_comp {c : ℕ} (f : Fac R X Y c) (p : X' → X) (q : Y' → Y) (x : X') (y : Y') :
    (f.comp p q).eval x y = f.eval (p x) (q y) := rfl

/-- Rename the number of bits along an equality. -/
def cast {a b : ℕ} (h : a = b) (f : Fac R X Y a) : Fac R X Y b := h ▸ f

@[simp] theorem eval_cast {a b : ℕ} (h : a = b) (f : Fac R X Y a) (x : X) (y : Y) :
    (f.cast h).eval x y = f.eval x y := by
  subst h; rfl

/-- If the left side is itself `c` bits (through `e`), every function factors through `c` bits:
`F(z, z') = ∑ θ [e z = θ] F(e⁻¹ θ, z')`. -/
def ofEquiv {c : ℕ} (e : X ≃ Bits c) (F : X → Y → R) : Fac R X Y c where
  l x θ := if e x = θ then 1 else 0
  r y θ := F (e.symm θ) y

@[simp] theorem eval_ofEquiv {c : ℕ} (e : X ≃ Bits c) (F : X → Y → R) (x : X) (y : Y) :
    (ofEquiv e F).eval x y = F x y := by
  simp [eval, ofEquiv]

end Fac

/-- Definition 1: `F` factors through `c` bits. -/
def FactorsThrough {R : Type*} [CommSemiring R] {X Y : Type*} (F : X → Y → R) (c : ℕ) : Prop :=
  ∃ f : Fac R X Y c, ∀ x y, F x y = f.eval x y

end Factoring.Aux
