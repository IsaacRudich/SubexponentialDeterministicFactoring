/-
The representation layer of the counting engine.

* `ZR m v x`: the number `v < m` represents `x : ZMod m`.  Expressions for the ring operations modulo the value of a
  variable (`zadd`, `zmul`, `zneg`, `zsum`, `zprod`), the equality test `eqE`, and their value lemmas.
* Factorizations read at codes: `Fac.l_cast`, `l_mul_bdec`, `unit_l_bdec`; **`prodList_filter_l`** (and `_r`): the
  left function of a product over a filtered list, at the string of a code `q`, is the fold `plL` that consumes one
  block of `q` per used factor.

Not an audit surface.
-/
module

public import FactoringAux.EngineBound
public import FactoringAux.EngineCode
public import FactoringAux.Net
public import Mathlib.Data.ZMod.Basic

@[expose] public section

namespace Factoring.Aux

open Finset

/-- `v < m` represents `x`. -/
def ZR (m v : ℕ) (x : ZMod m) : Prop := v < m ∧ ((v : ℕ) : ZMod m) = x

theorem ZR_mod {m v : ℕ} (hm : 0 < m) : ZR m (v % m) (v : ZMod m) := ⟨Nat.mod_lt _ hm, ZMod.natCast_mod v m⟩

theorem ZR.eq {m v : ℕ} {x y : ZMod m} (h : ZR m v x) (h' : ZR m v y) : x = y := h.2.symm.trans h'.2

namespace Ex

/-- `(e + f) mod m`. -/
def zadd (vm : ℕ) (e f : Ex) : Ex := .mod (.add e f) (.var vm)
/-- `(e · f) mod m`. -/
def zmul (vm : ℕ) (e f : Ex) : Ex := .mod (.mul e f) (.var vm)
/-- `(m − e) mod m`. -/
def zneg (vm : ℕ) (e : Ex) : Ex := .mod (.sub (.var vm) e) (.var vm)
/-- `1` if `e = f`, else `0`. -/
def eqE (e f : Ex) : Ex := .ifLt e f (.lit 0) (.ifLt f e (.lit 0) (.lit 1))
/-- `∑_{x<n} b mod m`. -/
def zsum (x : ℕ) (n : Ex) (vm : ℕ) (b : Ex) : Ex := .sum x n (.var vm) b
/-- `∏_{x<n} b mod m`. -/
def zprod (x : ℕ) (n : Ex) (vm : ℕ) (b : Ex) : Ex := .prod x n (.var vm) b
/-- `if 0 < c then u else v`. -/
def pos (c u v : Ex) : Ex := .ifLt (.lit 0) c u v

variable {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ} {m vm : ℕ}

theorem eval_eqE (e f : Ex) : eval σ A (eqE e f) = if eval σ A e = eval σ A f then 1 else 0 := by
  simp only [eqE, eval]
  split_ifs <;> omega

theorem eval_pos (c u v : Ex) : eval σ A (pos c u v) = if 0 < eval σ A c then eval σ A u else eval σ A v := by
  by_cases h : 0 < eval σ A c <;> simp [pos, eval, h]

theorem ZR_zadd (hm : σ vm = m) (hm0 : 0 < m) {e f : Ex} {x y : ZMod m} (he : ZR m (eval σ A e) x)
    (hf : ZR m (eval σ A f) y) : ZR m (eval σ A (zadd vm e f)) (x + y) := by
  simp only [zadd, eval, hm]
  refine ⟨Nat.mod_lt _ hm0, ?_⟩
  rw [ZMod.natCast_mod, Nat.cast_add, he.2, hf.2]

theorem ZR_zmul (hm : σ vm = m) (hm0 : 0 < m) {e f : Ex} {x y : ZMod m} (he : ZR m (eval σ A e) x)
    (hf : ZR m (eval σ A f) y) : ZR m (eval σ A (zmul vm e f)) (x * y) := by
  simp only [zmul, eval, hm]
  refine ⟨Nat.mod_lt _ hm0, ?_⟩
  rw [ZMod.natCast_mod, Nat.cast_mul, he.2, hf.2]

theorem ZR_zneg (hm : σ vm = m) (hm0 : 0 < m) {e : Ex} {x : ZMod m} (he : ZR m (eval σ A e) x) :
    ZR m (eval σ A (zneg vm e)) (-x) := by
  simp only [zneg, eval, hm]
  refine ⟨Nat.mod_lt _ hm0, ?_⟩
  rw [ZMod.natCast_mod, Nat.cast_sub he.1.le, ZMod.natCast_self, zero_sub, he.2]

theorem ZR_lit {k : ℕ} (hk : k < m) : ZR m (eval σ A (.lit k)) (k : ZMod m) := ⟨hk, rfl⟩

theorem ZR_zsum (hm : σ vm = m) (hm0 : 0 < m) (x : ℕ) {n b : Ex} {N : ℕ} (hn : eval σ A n = N) (F : ℕ → ZMod m)
    (hb : ∀ j < N, ZR m (eval (Function.update σ x j) A b) (F j)) :
    ZR m (eval σ A (zsum x n vm b)) (∑ j ∈ range N, F j) := by
  simp only [zsum, eval, hm, hn, foldSum_eq]
  refine ⟨Nat.mod_lt _ hm0, ?_⟩
  rw [ZMod.natCast_mod, Nat.cast_sum]
  exact sum_congr rfl fun j hj => (hb j (mem_range.mp hj)).2

theorem ZR_zprod (hm : σ vm = m) (hm1 : 1 < m) (x : ℕ) {n b : Ex} {N : ℕ} (hn : eval σ A n = N) (F : ℕ → ZMod m)
    (hb : ∀ j < N, ZR m (eval (Function.update σ x j) A b) (F j)) :
    ZR m (eval σ A (zprod x n vm b)) (∏ j ∈ range N, F j) := by
  simp only [zprod, eval, hm, hn]
  rcases Nat.eq_zero_or_pos N with h0 | h0
  · subst h0; exact ⟨by simp [foldProd]; omega, by simp [foldProd]⟩
  · rw [foldProd_eq _ _ _ h0]
    refine ⟨Nat.mod_lt _ (by omega), ?_⟩
    rw [ZMod.natCast_mod, Nat.cast_prod]
    exact prod_congr rfl fun j hj => (hb j (mem_range.mp hj)).2

theorem ZR_ite {c : Prop} [Decidable c] {u v : ℕ} {x y : ZMod m} (hu : ZR m u x) (hv : ZR m v y) :
    ZR m (if c then u else v) (if c then x else y) := by
  split_ifs <;> assumption

theorem ZR_one (hm1 : 1 < m) : ZR m 1 1 := ⟨hm1, Nat.cast_one⟩

theorem ZR_zero (hm0 : 0 < m) : ZR m 0 0 := ⟨hm0, Nat.cast_zero⟩

end Ex

/-! ### Factorizations read at codes -/

namespace Fac

variable {R : Type*} [CommSemiring R] {X Y : Type*}

theorem l_cast {a b : ℕ} (h : a = b) (f : Fac R X Y a) (x : X) (θ : Bits b) :
    (f.cast h).l x θ = f.l x (fun i => θ (Fin.cast h i)) := by subst h; rfl

theorem r_cast {a b : ℕ} (h : a = b) (f : Fac R X Y a) (y : Y) (θ : Bits b) :
    (f.cast h).r y θ = f.r y (fun i => θ (Fin.cast h i)) := by subst h; rfl

theorem bdec_low (a b q : ℕ) : (fun i : Fin a => bdec (a + b) q (Fin.castAdd b i)) = bdec a q := rfl

theorem bdec_high (a b q : ℕ) : (fun i : Fin b => bdec (a + b) q (Fin.natAdd a i)) = bdec b (q / 2 ^ a) := by
  funext i
  simp [bdec, Nat.testBit_div_two_pow, Nat.add_comm]

theorem l_mul_bdec {a b : ℕ} (f : Fac R X Y a) (g : Fac R X Y b) (x : X) (q : ℕ) :
    (f.mul g).l x (bdec (a + b) q) = f.l x (bdec a q) * g.l x (bdec b (q / 2 ^ a)) := by
  simp only [mul, bdec_high]; rfl

theorem r_mul_bdec {a b : ℕ} (f : Fac R X Y a) (g : Fac R X Y b) (y : Y) (q : ℕ) :
    (f.mul g).r y (bdec (a + b) q) = f.r y (bdec a q) * g.r y (bdec b (q / 2 ^ a)) := by
  simp only [mul, bdec_high]; rfl

theorem bdec_cast {a b : ℕ} (h : a = b) (q : ℕ) : (fun i => bdec b q (Fin.cast h i)) = bdec a q := rfl

theorem bdec_eq_zero (d q : ℕ) : bdec d q = zeroBits d ↔ q % 2 ^ d = 0 := by
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_mod_two_pow, Nat.zero_testBit]
    by_cases hi : i < d
    · have := congrFun h ⟨i, hi⟩
      simp only [bdec, zeroBits] at this
      simp [hi, this]
    · simp [hi]
  · intro h
    funext i
    have := congrArg (fun v => v.testBit i) h
    simp only [Nat.testBit_mod_two_pow, Nat.zero_testBit, i.2, decide_true, Bool.true_and] at this
    simp [bdec, zeroBits, this]

theorem unit_l_bdec (d : ℕ) (x : X) (q : ℕ) :
    (unit d : Fac R X Y d).l x (bdec d q) = if q % 2 ^ d = 0 then 1 else 0 := by
  simp only [unit, bdec_eq_zero]

theorem unit_r_bdec (d : ℕ) (y : Y) (q : ℕ) :
    (unit d : Fac R X Y d).r y (bdec d q) = if q % 2 ^ d = 0 then 1 else 0 := by
  simp only [unit, bdec_eq_zero]

/-- Padding, read at a code. -/
theorem pad_l_bdec {c : ℕ} (f : Fac R X Y c) (L : ℕ) (h : c ≤ L) (x : X) (q : ℕ) :
    (f.pad L h).l x (bdec L q) = f.l x (bdec c q) * if q / 2 ^ c % 2 ^ (L - c) = 0 then 1 else 0 := by
  unfold pad
  rw [l_cast, bdec_cast, l_mul_bdec, unit_l_bdec]

theorem pad_r_bdec {c : ℕ} (f : Fac R X Y c) (L : ℕ) (h : c ≤ L) (y : Y) (q : ℕ) :
    (f.pad L h).r y (bdec L q) = f.r y (bdec c q) * if q / 2 ^ c % 2 ^ (L - c) = 0 then 1 else 0 := by
  unfold pad
  rw [r_cast, bdec_cast, r_mul_bdec, unit_r_bdec]

section PL

variable {ι : Type*} (c : ι → ℕ) (F : ∀ i, Fac R X Y (c i)) (P : ι → Prop) [DecidablePred P]

/-- The left functions of the used factors, each on its block of `q`. -/
def plL (x : X) : List ι → ℕ → R
  | [], _ => 1
  | i :: L, q => if P i then (F i).l x (bdec (c i) q) * plL x L (q / 2 ^ c i) else plL x L q

/-- The right functions of the used factors, each on its block of `q`. -/
def plR (y : Y) : List ι → ℕ → R
  | [], _ => 1
  | i :: L, q => if P i then (F i).r y (bdec (c i) q) * plR y L (q / 2 ^ c i) else plR y L q

/-- All factors used. -/
def plA (x : X) : List ι → ℕ → R
  | [], _ => 1
  | i :: L, q => (F i).l x (bdec (c i) q) * plA x L (q / 2 ^ c i)

/-- All factors used, right side. -/
def plB (y : Y) : List ι → ℕ → R
  | [], _ => 1
  | i :: L, q => (F i).r y (bdec (c i) q) * plB y L (q / 2 ^ c i)

theorem prodList_l (x : X) : ∀ (L : List ι) (q : ℕ), (prodList c F L).l x (bdec _ q) = plA c F x L q
  | [], q => by simp [prodList, plA, l_cast, one]
  | i :: L, q => by
      simp only [prodList, plA]
      rw [l_cast, bdec_cast, l_mul_bdec, prodList_l x L]

theorem prodList_r (y : Y) : ∀ (L : List ι) (q : ℕ), (prodList c F L).r y (bdec _ q) = plB c F y L q
  | [], q => by simp [prodList, plB, r_cast, one]
  | i :: L, q => by
      simp only [prodList, plB]
      rw [r_cast, bdec_cast, r_mul_bdec, prodList_r y L]

theorem plA_filter (x : X) : ∀ (L : List ι) (q : ℕ), plA c F x (L.filter (fun i => decide (P i))) q = plL c F P x L q
  | [], q => rfl
  | i :: L, q => by
      by_cases hP : P i
      · simp only [List.filter_cons, hP, decide_true, if_true, plA, plL, plA_filter x L]
      · simp [List.filter_cons, hP, plL, plA_filter x L]

theorem plB_filter (y : Y) : ∀ (L : List ι) (q : ℕ), plB c F y (L.filter (fun i => decide (P i))) q = plR c F P y L q
  | [], q => rfl
  | i :: L, q => by
      by_cases hP : P i
      · simp only [List.filter_cons, hP, decide_true, if_true, plB, plR, plB_filter y L]
      · simp [List.filter_cons, hP, plR, plB_filter y L]

theorem prodList_filter_l (x : X) (L : List ι) (q : ℕ) :
    (prodList c F (L.filter (fun i => decide (P i)))).l x (bdec _ q) = plL c F P x L q := by
  rw [prodList_l, plA_filter]

theorem prodList_filter_r (y : Y) (L : List ι) (q : ℕ) :
    (prodList c F (L.filter (fun i => decide (P i)))).r y (bdec _ q) = plR c F P y L q := by
  rw [prodList_r, plB_filter]

end PL

end Fac

end Factoring.Aux
