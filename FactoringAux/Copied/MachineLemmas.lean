/-
Adapted from the authors' related work.
Only the 55 declarations that the copied PLIB uses, directly or transitively, in their original order.

Not an audit surface.
-/
module

public import FactoringAux.Copied.Machine
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Bound
-- Mathlib modules the original declarations reach indirectly:
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Finite.List
public import Mathlib.Algebra.Order.Field.Basic

@[expose] public section

-- `Factoring.Aux.Copied.Aux` repeats `Aux`: kept, since the copied PLIB writes `Aux.<name>`.
set_option linter.dupNamespace false

namespace Factoring.Aux.Copied.Aux

open Factoring.Aux.Copied

theorem run_seq (s t : Program) (σ : Memory) :
    Program.run (.seq s t) σ =
      ((Program.run t (Program.run s σ).1).1,
        (Program.run s σ).2 + (Program.run t (Program.run s σ).1).2 + 1) := rfl

theorem run_ifLt (x y : ℕ) (s e : Program) (σ : Memory) :
    Program.run (.ifLt x y s e) σ =
      ((if σ x < σ y then Program.run s σ else Program.run e σ).1,
        (if σ x < σ y then Program.run s σ else Program.run e σ).2 + 1) := rfl

theorem run_ifZero (x : ℕ) (s e : Program) (σ : Memory) :
    Program.run (.ifZero x s e) σ =
      ((if σ x = 0 then Program.run s σ else Program.run e σ).1,
        (if σ x = 0 then Program.run s σ else Program.run e σ).2 + 1) := rfl

/-- One iteration of a loop: set the counter, run the body, charge a step. -/
def loopF (body : Program) (c : ℕ) (acc : Memory × ℕ) (i : ℕ) : Memory × ℕ :=
  ((Program.run body (acc.1.set c i)).1, acc.2 + (Program.run body (acc.1.set c i)).2 + 1)

theorem run_loop (b c : ℕ) (body : Program) (σ : Memory) :
    Program.run (.loop b c body) σ = (List.range (σ b)).foldl (loopF body c) (σ, 1) := rfl

/-- Setting one cell keeps a bound that the new value respects. -/
theorem memory_set_le {σ : Memory} {m r v : ℕ} (h : ∀ i, σ i ≤ m) (hv : v ≤ m) :
    ∀ i, σ.set r v i ≤ m := by
  intro i
  rw [Memory.set]
  split
  · exact hv
  · exact h i

/-- The memory after `j` iterations of a loop body. -/
def loopMem (body : Program) (c : ℕ) : ℕ → Memory → Memory
  | 0, σ => σ
  | j + 1, σ => (Program.run body ((loopMem body c j σ).set c j)).1

/-- What those `j` iterations cost, the entry step included. -/
def loopCost (body : Program) (c : ℕ) : ℕ → Memory → ℕ
  | 0, _ => 1
  | j + 1, σ => loopCost body c j σ + (Program.run body ((loopMem body c j σ).set c j)).2 + 1

theorem run_loop_eq (b c : ℕ) (body : Program) (σ : Memory) :
    Program.run (.loop b c body) σ = (loopMem body c (σ b) σ, loopCost body c (σ b) σ) := by
  rw [run_loop]
  suffices h : ∀ k : ℕ, (List.range k).foldl (loopF body c) (σ, 1)
      = (loopMem body c k σ, loopCost body c k σ) from h (σ b)
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [List.range_succ, List.foldl_append, ih]
      simp only [List.foldl_cons, List.foldl_nil, loopF, loopMem, loopCost]

/-- A block of instructions, run in order. -/
def seqs : List Program → Program
  | [] => .skip
  | p :: ps => .seq p (seqs ps)

theorem run_seqs_cons (p : Program) (ps : List Program) (σ : Memory) :
    Program.run (seqs (p :: ps)) σ =
      ((Program.run (seqs ps) (Program.run p σ).1).1,
        (Program.run p σ).2 + (Program.run (seqs ps) (Program.run p σ).1).2 + 1) := rfl

theorem memory_set_set (σ : Memory) (r x y : ℕ) : (σ.set r x).set r y = σ.set r y := by
  funext i; simp only [Memory.set]; split <;> rfl

theorem memory_set_eq_self (σ : Memory) (r : ℕ) : σ.set r (σ r) = σ := by
  funext i
  simp only [Memory.set]
  split
  · rename_i h; rw [h]
  · rfl

/-- `dst := k`, for a literal `k`. -/
def setK (dst k : ℕ) : Program := seqs (.zero dst :: List.replicate k (.incr dst))

theorem run_incrs (dst : ℕ) : ∀ (j : ℕ) (τ : Memory),
    Program.run (seqs (List.replicate j (.incr dst))) τ = (τ.set dst (τ dst + j), 2 * j + 1) := by
  intro j
  induction j with
  | zero => intro τ; simp [seqs, Program.run, memory_set_eq_self]
  | succ j ih =>
      intro τ
      have hincr : Program.run (Program.incr dst) τ = (τ.set dst (τ dst + 1), 1) := rfl
      rw [List.replicate_succ, run_seqs_cons, hincr, ih (τ.set dst (τ dst + 1))]
      simp only [Prod.mk.injEq]
      refine ⟨?_, by omega⟩
      have hd : (τ.set dst (τ dst + 1)) dst = τ dst + 1 := by simp [Memory.set]
      rw [memory_set_set, hd]
      congr 1
      omega

theorem run_setK (dst k : ℕ) (σ : Memory) :
    Program.run (setK dst k) σ = (σ.set dst k, 2 * k + 3) := by
  have hzero : Program.run (Program.zero dst) σ = (σ.set dst 0, 1) := rfl
  rw [setK, run_seqs_cons, hzero, run_incrs]
  simp only [Prod.mk.injEq]
  refine ⟨?_, by omega⟩
  rw [memory_set_set]
  congr 1
  simp [Memory.set]

theorem memory_set_get_ne (σ : Memory) {r a : ℕ} (x : ℕ) (h : a ≠ r) : (σ.set r x) a = σ a := by
  simp [Memory.set, h]

theorem memory_set_get (σ : Memory) (r x : ℕ) : (σ.set r x) r = x := by simp [Memory.set]

/-- The memory a block of instructions ends with. -/
theorem run_seqs_mem (ps : List Program) (σ : Memory) :
    (Program.run (seqs ps) σ).1 = ps.foldl (fun τ p => (Program.run p τ).1) σ := by
  induction ps generalizing σ with
  | nil => rfl
  | cons p ps ih => rw [run_seqs_cons, List.foldl_cons]; exact ih _

/-- What a block costs. -/
def seqsCost : List Program → Memory → ℕ
  | [], _ => 1
  | p :: ps, σ => (Program.run p σ).2 + seqsCost ps (Program.run p σ).1 + 1

theorem run_seqs_cost (ps : List Program) (σ : Memory) :
    (Program.run (seqs ps) σ).2 = seqsCost ps σ := by
  induction ps generalizing σ with
  | nil => rfl
  | cons p ps ih => rw [run_seqs_cons, ih]; rfl

theorem run_zero_mem (d : ℕ) (τ : Memory) : (Program.run (.zero d) τ).1 = τ.set d 0 := rfl

theorem run_copy_mem (d s : ℕ) (τ : Memory) :
    (Program.run (.copy d s) τ).1 = τ.set d (τ s) := rfl

theorem run_skip_mem (τ : Memory) : (Program.run .skip τ).1 = τ := rfl

theorem run_setK_mem (d b : ℕ) (τ : Memory) :
    (Program.run (setK d b) τ).1 = τ.set d b := by rw [run_setK]

theorem run_ifZero_mem (x : ℕ) (s e : Program) (τ : Memory) :
    (Program.run (.ifZero x s e) τ).1
      = if τ x = 0 then (Program.run s τ).1 else (Program.run e τ).1 := by
  rw [run_ifZero]; exact apply_ite Prod.fst _ _ _

theorem run_loop_mem (b c : ℕ) (body : Program) (τ : Memory) :
    (Program.run (.loop b c body) τ).1 = loopMem body c (τ b) τ := by rw [run_loop_eq]

theorem run_ifLt_mem (x y : ℕ) (s e : Program) (τ : Memory) :
    (Program.run (.ifLt x y s e) τ).1
      = if τ x < τ y then (Program.run s τ).1 else (Program.run e τ).1 := by
  rw [run_ifLt]; exact apply_ite Prod.fst _ _ _

theorem cost_zero (d : ℕ) (τ : Memory) : (Program.run (.zero d) τ).2 = 1 := rfl

theorem cost_copy (d s : ℕ) (τ : Memory) : (Program.run (.copy d s) τ).2 = 1 := rfl

theorem cost_skip (τ : Memory) : (Program.run .skip τ).2 = 1 := rfl

theorem cost_setK (d b : ℕ) (τ : Memory) : (Program.run (setK d b) τ).2 = 2 * b + 3 := by
  rw [run_setK]

theorem cost_ifZero (x : ℕ) (s e : Program) (τ : Memory) :
    (Program.run (.ifZero x s e) τ).2
      = (if τ x = 0 then (Program.run s τ).2 else (Program.run e τ).2) + 1 := by
  rw [run_ifZero]
  exact congrArg (· + 1) (apply_ite Prod.snd (τ x = 0) (Program.run s τ) (Program.run e τ))

theorem run_store_mem (b i s : ℕ) (τ : Memory) :
    (Program.run (.store b i s) τ).1 = τ.set (b + τ i) (τ s) := rfl

theorem cost_store (b i s : ℕ) (τ : Memory) : (Program.run (.store b i s) τ).2 = 1 := rfl

theorem run_load_mem (d b i : ℕ) (τ : Memory) :
    (Program.run (.load d b i) τ).1 = τ.set d (τ (b + τ i)) := rfl

theorem cost_load (d b i : ℕ) (τ : Memory) : (Program.run (.load d b i) τ).2 = 1 := rfl

theorem cost_ifLt (x y : ℕ) (s e : Program) (τ : Memory) :
    (Program.run (.ifLt x y s e) τ).2
      = (if τ x < τ y then (Program.run s τ).2 else (Program.run e τ).2) + 1 := by
  rw [run_ifLt]
  exact congrArg (· + 1) (apply_ite Prod.snd (τ x < τ y) (Program.run s τ) (Program.run e τ))

/-- Bounded by a polynomial in the input length. -/
def Poly (g : ℕ → ℕ) : Prop := ∃ c d : ℕ, ∀ n, g n ≤ c * (n + 1) ^ d

theorem Poly.of_le {g h : ℕ → ℕ} (hh : Poly h) (hle : ∀ n, g n ≤ h n) : Poly g := by
  obtain ⟨c, d, hc⟩ := hh
  exact ⟨c, d, fun n => le_trans (hle n) (hc n)⟩

theorem Poly.const (k : ℕ) : Poly (fun _ => k) :=
  ⟨k, 0, fun n => by simp⟩

theorem Poly.id : Poly (fun n => n) :=
  ⟨1, 1, fun n => by simp⟩

theorem Poly.add {g h : ℕ → ℕ} (hg : Poly g) (hh : Poly h) : Poly (fun n => g n + h n) := by
  obtain ⟨c1, d1, h1⟩ := hg
  obtain ⟨c2, d2, h2⟩ := hh
  refine ⟨c1 + c2, max d1 d2, fun n => ?_⟩
  have e1 : c1 * (n + 1) ^ d1 ≤ c1 * (n + 1) ^ (max d1 d2) :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (le_max_left _ _))
  have e2 : c2 * (n + 1) ^ d2 ≤ c2 * (n + 1) ^ (max d1 d2) :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (le_max_right _ _))
  have f1 := h1 n
  have f2 := h2 n
  have e3 : (c1 + c2) * (n + 1) ^ (max d1 d2)
      = c1 * (n + 1) ^ (max d1 d2) + c2 * (n + 1) ^ (max d1 d2) := by ring
  show g n + h n ≤ (c1 + c2) * (n + 1) ^ (max d1 d2)
  omega

theorem Poly.mul {g h : ℕ → ℕ} (hg : Poly g) (hh : Poly h) : Poly (fun n => g n * h n) := by
  obtain ⟨c1, d1, h1⟩ := hg
  obtain ⟨c2, d2, h2⟩ := hh
  refine ⟨c1 * c2, d1 + d2, fun n => ?_⟩
  show g n * h n ≤ c1 * c2 * (n + 1) ^ (d1 + d2)
  calc g n * h n ≤ (c1 * (n + 1) ^ d1) * (c2 * (n + 1) ^ d2) :=
        Nat.mul_le_mul (h1 n) (h2 n)
    _ = c1 * c2 * (n + 1) ^ (d1 + d2) := by rw [pow_add]; ring

theorem Poly.pow {g : ℕ → ℕ} (hg : Poly g) : ∀ k : ℕ, Poly (fun n => (g n) ^ k)
  | 0 => Poly.of_le (Poly.const 1) (fun n => by simp)
  | k + 1 => Poly.of_le (Poly.mul (Poly.pow hg k) hg) (fun n => by rw [pow_succ])

theorem poly_pow (J : ℕ) : Poly (fun n => (n + 1) ^ J) := ⟨1, J, fun n => by simp⟩

theorem le_of_val_le {σ : Memory} {V K : ℕ} (hV : ∀ r, σ r ≤ V) (h : V ≤ K) :
    ∀ r, σ r ≤ K := fun r => le_trans (hV r) h

/-- **Values grow by at most one per step.**  `incr` is the only instruction
that makes a register larger, and it adds one, so nothing can exceed its
starting bound by more than the steps taken. -/
theorem run_val_le : ∀ (M : Program) (σ : Memory) (V : ℕ), (∀ r, σ r ≤ V) →
    ∀ r, (Program.run M σ).1 r ≤ V + (Program.run M σ).2 := by
  intro M
  induction M with
  | skip => intro σ V hV r; exact le_trans (hV r) (Nat.le_add_right _ _)
  | zero d =>
      intro σ V hV
      exact memory_set_le (le_of_val_le hV (Nat.le_add_right _ _)) (Nat.zero_le _)
  | incr d =>
      intro σ V hV
      exact memory_set_le (le_of_val_le hV (Nat.le_add_right _ _))
        (Nat.succ_le_succ (hV d))
  | decr d =>
      intro σ V hV
      exact memory_set_le (le_of_val_le hV (Nat.le_add_right _ _))
        (le_trans (Nat.sub_le _ _) (le_trans (hV d) (Nat.le_add_right _ _)))
  | copy d s =>
      intro σ V hV
      exact memory_set_le (le_of_val_le hV (Nat.le_add_right _ _))
        (le_trans (hV s) (Nat.le_add_right _ _))
  | load d b i =>
      intro σ V hV
      exact memory_set_le (le_of_val_le hV (Nat.le_add_right _ _))
        (le_trans (hV _) (Nat.le_add_right _ _))
  | store b i s =>
      intro σ V hV
      exact memory_set_le (le_of_val_le hV (Nat.le_add_right _ _))
        (le_trans (hV s) (Nat.le_add_right _ _))
  | seq s t ihs iht =>
      intro σ V hV r
      have h2 := iht (Program.run s σ).1 (V + (Program.run s σ).2) (ihs σ V hV) r
      rw [run_seq]
      simp only
      omega
  | ifLt a b t e iht ihe =>
      intro σ V hV r
      rw [run_ifLt_mem, cost_ifLt]
      by_cases h : σ a < σ b
      · simp only [if_pos h]
        have := iht σ V hV r
        omega
      · simp only [if_neg h]
        have := ihe σ V hV r
        omega
  | ifZero a t e iht ihe =>
      intro σ V hV r
      rw [run_ifZero_mem, cost_ifZero]
      by_cases h : σ a = 0
      · simp only [if_pos h]
        have := iht σ V hV r
        omega
      · simp only [if_neg h]
        have := ihe σ V hV r
        omega
  | loop b c body ihb =>
      intro σ V hV r
      rw [run_loop_eq]
      simp only
      have key : ∀ j : ℕ, j ≤ σ b → ∀ r,
          loopMem body c j σ r ≤ V + loopCost body c j σ := by
        intro j
        induction j with
        | zero => intro _ r; exact le_trans (hV r) (Nat.le_add_right _ _)
        | succ j ih =>
            intro hj r
            have ihj := ih (le_trans (Nat.le_succ j) hj)
            have hjb : j < σ b := hj
            have hset : ∀ r, ((loopMem body c j σ).set c j) r
                ≤ V + loopCost body c j σ :=
              memory_set_le ihj
                (le_trans (le_trans (Nat.le_of_lt hjb) (hV b)) (Nat.le_add_right _ _))
            have := ihb ((loopMem body c j σ).set c j) (V + loopCost body c j σ) hset r
            show loopMem body c (j + 1) σ r ≤ V + loopCost body c (j + 1) σ
            rw [loopMem, loopCost]
            omega
      exact key (σ b) (le_refl _) r

theorem run_incr_mem' (d : ℕ) (τ : Memory) :
    (Program.run (.incr d) τ).1 = τ.set d (τ d + 1) := rfl

theorem run_decr_mem (d : ℕ) (τ : Memory) : (Program.run (.decr d) τ).1 = τ.set d (τ d - 1) := rfl

theorem cost_seq (s t : Program) (σ : Memory) :
    (Program.run (.seq s t) σ).2
      = (Program.run s σ).2 + (Program.run t (Program.run s σ).1).2 + 1 := rfl

theorem cost_incr (d : ℕ) (τ : Memory) : (Program.run (.incr d) τ).2 = 1 := rfl

theorem cost_decr (d : ℕ) (τ : Memory) : (Program.run (.decr d) τ).2 = 1 := rfl

theorem cost_loop (b c : ℕ) (body : Program) (τ : Memory) :
    (Program.run (.loop b c body) τ).2 = loopCost body c (τ b) τ := by rw [run_loop_eq]

theorem runsInPolyTime_of_poly {M : Program} {g : ℕ → ℕ} (hg : Poly g)
    (h : ∀ xs : List Bool, steps M xs ≤ g xs.length) : RunsInPolyTime M := by
  obtain ⟨c, d, hc⟩ := hg
  exact ⟨c, d, fun xs => le_trans (h xs) (hc xs.length)⟩

end Factoring.Aux.Copied.Aux
