/-
Networks as expressions.

* `Ag B σ₀ σ`: `σ` agrees with the context `σ₀` below `B` (the variables of the enclosing levels).
* `NEx`, `NVars`, **`NRep`**: expressions `sz, W, c, l, r` over argument variables `(a, b, z, q)` represent a coded
  network `(N, κ)` in the context `σ₀` if, for every `σ` agreeing with `σ₀` below `B` whose argument variables hold
  `a, b, (the code of) z, q`, they evaluate to the size, the weight, the width and the factor functions at the
  string of `q` (as elements of `ZMod m`, `m` the value of the variable `vm`).
* Small expression helpers with value lemmas: `ifEq`, `pow2`, `nprod`/`nsum` (no reduction).

Not an audit surface.
-/
module

public import FactoringAux.EngineCoarsen

@[expose] public section

namespace Factoring.Aux

open Finset

/-- `σ` agrees with `σ₀` below `B`. -/
def Ag (B : ℕ) (σ₀ σ : ℕ → ℕ) : Prop := ∀ y < B, σ y = σ₀ y

theorem Ag.upd {B : ℕ} {σ₀ σ : ℕ → ℕ} (h : Ag B σ₀ σ) {x : ℕ} (hx : B ≤ x) (v : ℕ) :
    Ag B σ₀ (Function.update σ x v) := fun y hy => by
  rw [Function.update_apply, if_neg (by omega)]; exact h y hy

theorem Ag.mono {B B' : ℕ} {σ₀ σ : ℕ → ℕ} (h : Ag B' σ₀ σ) (hB : B ≤ B') : Ag B σ₀ σ :=
  fun y hy => h y (by omega)

theorem Ag.refl (B : ℕ) (σ₀ : ℕ → ℕ) : Ag B σ₀ σ₀ := fun _ _ => rfl

namespace Ex

/-- `if e = f then u else v`. -/
def ifEq (e f u v : Ex) : Ex := .ifLt e f v (.ifLt f e v u)

/-- `2^e` (loop variable `x`). -/
def pow2 (x : ℕ) (e : Ex) : Ex := .prod x e (.lit 0) (.lit 2)

/-- `∏_{x<n} b`, no reduction. -/
def nprod (x : ℕ) (n b : Ex) : Ex := .prod x n (.lit 0) b

/-- `∑_{x<n} b`, no reduction. -/
def nsum (x : ℕ) (n b : Ex) : Ex := .sum x n (.lit 0) b

variable {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ}

theorem eval_ifEq (e f u v : Ex) :
    eval σ A (ifEq e f u v) = if eval σ A e = eval σ A f then eval σ A u else eval σ A v := by
  simp only [ifEq, eval]
  split_ifs <;> omega

theorem foldProd_zero (f : ℕ → ℕ) : ∀ n, foldProd f 0 n = pp f n
  | 0 => rfl
  | n + 1 => by simp [foldProd, pp, foldProd_zero f n]

theorem pp_congr {f f' : ℕ → ℕ} : ∀ {n : ℕ}, (∀ i < n, f i = f' i) → pp f n = pp f' n
  | 0, _ => rfl
  | n + 1, h => by simp only [pp]; rw [pp_congr fun i hi => h i (by omega), h n (by omega)]

theorem pp_const (k : ℕ) : ∀ n, pp (fun _ => k) n = k ^ n
  | 0 => rfl
  | n + 1 => by simp [pp, pp_const k n, pow_succ]

theorem foldSum_zero (f : ℕ → ℕ) (n : ℕ) : foldSum f 0 n = ∑ i ∈ range n, f i := by
  rw [foldSum_eq, Nat.mod_zero]

theorem eval_pow2 (x : ℕ) (e : Ex) : eval σ A (pow2 x e) = 2 ^ eval σ A e := by
  simp only [pow2, eval, foldProd_zero]
  exact pp_const 2 _

theorem eval_nprod (x : ℕ) (n b : Ex) :
    eval σ A (nprod x n b) = pp (fun i => eval (Function.update σ x i) A b) (eval σ A n) := by
  simp only [nprod, eval, foldProd_zero]

theorem eval_nsum (x : ℕ) (n b : Ex) :
    eval σ A (nsum x n b) = ∑ i ∈ range (eval σ A n), eval (Function.update σ x i) A b := by
  simp only [nsum, eval, foldSum_zero]

end Ex

/-- The expressions of a network. -/
structure NEx where
  /-- Size of node `a`. -/
  sz : Ex
  /-- Weight of node `a` at code `z`. -/
  W : Ex
  /-- Width of the pair `a < b`. -/
  c : Ex
  /-- Left factor function of `a < b` at code `z` (of `a`) and string code `q`. -/
  l : Ex
  /-- Right factor function of `a < b` at code `z` (of `b`) and string code `q`. -/
  r : Ex

/-- The argument variables of a network's expressions. -/
structure NVars where
  /-- First node. -/
  a : ℕ
  /-- Second node. -/
  b : ℕ
  /-- A setting code. -/
  z : ℕ
  /-- A string code. -/
  q : ℕ

/-- **Expressions representing a coded network** in the context `σ₀` (bound `B`). -/
structure NRep (m vm B : ℕ) (σ₀ : ℕ → ℕ) (A : ℕ → ℕ → ℕ) (v : NVars) (E : NEx) {g : ℕ}
    (N : Net (ZMod m) g) (κ : Coding N) : Prop where
  hm : σ₀ vm = m
  sz : ∀ σ, Ag B σ₀ σ → ∀ a : Fin g, σ v.a = a → Ex.eval σ A E.sz = κ.s a
  W : ∀ σ, Ag B σ₀ σ → ∀ (a : Fin g) (z : N.S a), σ v.a = a → σ v.z = κ.e a z →
    ZR m (Ex.eval σ A E.W) (N.W a z)
  c : ∀ σ, Ag B σ₀ σ → ∀ a b : Fin g, a < b → σ v.a = a → σ v.b = b → Ex.eval σ A E.c = N.c a b
  l : ∀ σ, Ag B σ₀ σ → ∀ a b : Fin g, a < b → ∀ (z : N.S a) (q : ℕ), σ v.a = a → σ v.b = b →
    σ v.z = κ.e a z → σ v.q = q → ZR m (Ex.eval σ A E.l) ((N.F a b).l z (bdec _ q))
  r : ∀ σ, Ag B σ₀ σ → ∀ a b : Fin g, a < b → ∀ (z : N.S b) (q : ℕ), σ v.a = a → σ v.b = b →
    σ v.z = κ.e b z → σ v.q = q → ZR m (Ex.eval σ A E.r) ((N.F a b).r z (bdec _ q))

end Factoring.Aux
