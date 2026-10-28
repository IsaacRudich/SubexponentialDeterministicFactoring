/-
FactoringAux/SProg/Compile.lean — L1′, first half: `SProg` compiled to flat code, run on any machine
that executes the flat instructions one per step.

Not audited.

The flat code has two instructions, `push k b next` and `read k t f e` (pop stack `k`, jump to `t`,
`f` or `e`), plus `halt`.  `code p start next` places `p` at addresses `start, …, start + size p - 1`,
leaving to `next`; `entry p start next` is where it starts.  The theorem `iterate_cost` says that any
machine `step` simulating the flat instructions one per step (`Simulates`) runs a well-formed `p` from
its entry to `next` in exactly `cost p s` steps, ending with the stacks `exec p s`.  So the compile is
linear: one machine step per unit of source cost.
-/
module

public import FactoringAux.SProg.Basic
public import Mathlib.Logic.Function.Iterate

@[expose] public section

namespace Factoring.Aux
namespace SProg

open Function

/-- Flat instructions. -/
inductive Instr
  | push (k : ℕ) (b : Bool) (next : ℕ)
  | read (k : ℕ) (t f e : ℕ)
  | halt

/-- Number of flat instructions of a program. -/
def size : SProg → ℕ
  | skip => 0
  | push _ _ => 1
  | read _ pt pf pe => 1 + size pt + size pf + size pe
  | seq p q => size p + size q
  | loop _ pt pf => 1 + size pt + size pf

/-- The entry address of `p` placed at `start` and leaving to `next`. -/
def entry : SProg → ℕ → ℕ → ℕ
  | skip, _, next => next
  | push _ _, start, _ => start
  | read _ _ _ _, start, _ => start
  | seq p q, start, next => entry p start (entry q (start + size p) next)
  | loop _ _ _, start, _ => start

/-- The flat code of `p` placed at `start` and leaving to `next`, as a function of the address (it is
meaningful for addresses `start ≤ i < start + size p`). -/
def code : SProg → ℕ → ℕ → ℕ → Instr
  | skip, _, _, _ => .halt
  | push k b, _, next, _ => .push k b next
  | read k pt pf pe, start, next, i =>
      if i = start then
        .read k (entry pt (start + 1) next) (entry pf (start + 1 + size pt) next)
          (entry pe (start + 1 + size pt + size pf) next)
      else if i < start + 1 + size pt then code pt (start + 1) next i
      else if i < start + 1 + size pt + size pf then code pf (start + 1 + size pt) next i
      else code pe (start + 1 + size pt + size pf) next i
  | seq p q, start, next, i =>
      if i < start + size p then code p start (entry q (start + size p) next) i
      else code q (start + size p) next i
  | loop k pt pf, start, next, i =>
      if i = start then
        .read k (entry pt (start + 1) start) (entry pf (start + 1 + size pt) start) next
      else if i < start + 1 + size pt then code pt (start + 1) start i
      else code pf (start + 1 + size pt) start i

/-- `C` contains the code of `p`, placed at `start` and leaving to `next`. -/
def Loaded (C : ℕ → Instr) : SProg → ℕ → ℕ → Prop
  | skip, _, _ => True
  | push k b, start, next => C start = .push k b next
  | read k pt pf pe, start, next =>
      C start = .read k (entry pt (start + 1) next) (entry pf (start + 1 + size pt) next)
          (entry pe (start + 1 + size pt + size pf) next) ∧
        Loaded C pt (start + 1) next ∧ Loaded C pf (start + 1 + size pt) next ∧
        Loaded C pe (start + 1 + size pt + size pf) next
  | seq p q, start, next =>
      Loaded C p start (entry q (start + size p) next) ∧ Loaded C q (start + size p) next
  | loop k pt pf, start, next =>
      C start = .read k (entry pt (start + 1) start) (entry pf (start + 1 + size pt) start) next ∧
        Loaded C pt (start + 1) start ∧ Loaded C pf (start + 1 + size pt) start

theorem loaded_of_code {C : ℕ → Instr} :
    ∀ (p : SProg) (start next : ℕ),
      (∀ i, start ≤ i → i < start + size p → C i = code p start next i) → Loaded C p start next
  | skip, _, _, _ => trivial
  | push k b, start, next, h => by
      have := h start (Nat.le_refl _) (by simp [size]); simpa [code, Loaded] using this
  | read k pt pf pe, start, next, h => by
      refine ⟨?_, loaded_of_code pt _ _ fun i h1 h2 => ?_, loaded_of_code pf _ _ fun i h1 h2 => ?_,
        loaded_of_code pe _ _ fun i h1 h2 => ?_⟩
      · have := h start (Nat.le_refl _) (by simp [size]; omega); simpa [code, Loaded] using this
      · rw [h i (by omega) (by simp [size]; omega), code, if_neg (by omega), if_pos h2]
      · rw [h i (by omega) (by simp [size]; omega), code, if_neg (by omega), if_neg (by omega),
          if_pos h2]
      · rw [h i (by omega) (by simp [size]; omega), code, if_neg (by omega), if_neg (by omega),
          if_neg (by omega)]
  | seq p q, start, next, h => by
      refine ⟨loaded_of_code p _ _ fun i h1 h2 => ?_, loaded_of_code q _ _ fun i h1 h2 => ?_⟩
      · rw [h i h1 (by simp [size]; omega), code, if_pos h2]
      · rw [h i (by omega) (by simp [size] at h2 ⊢; omega), code, if_neg (by omega)]
  | loop k pt pf, start, next, h => by
      refine ⟨?_, loaded_of_code pt _ _ fun i h1 h2 => ?_, loaded_of_code pf _ _ fun i h1 h2 => ?_⟩
      · have := h start (Nat.le_refl _) (by simp [size]; omega); simpa [code, Loaded] using this
      · rw [h i (by omega) (by simp [size]; omega), code, if_neg (by omega), if_pos h2]
      · rw [h i (by omega) (by simp [size]; omega), code, if_neg (by omega), if_neg (by omega)]

/-- The flat `read`: next address and stacks. -/
def readNext (k t f e : ℕ) (s : Stacks) : ℕ × Stacks :=
  match s k with
  | true :: l => (t, update s k l)
  | false :: l => (f, update s k l)
  | [] => (e, s)

/-- `step` executes each flat instruction of `C` in one step, the configuration at address `pc`
with stacks `s` being `enc pc s`. -/
structure Simulates (C : ℕ → Instr) {α : Type*} (step : α → Option α) (enc : ℕ → Stacks → α) :
    Prop where
  push : ∀ pc s k b n, C pc = .push k b n → step (enc pc s) = some (enc n (update s k (b :: s k)))
  read : ∀ pc s k t f e, C pc = .read k t f e →
    step (enc pc s) = some (enc (readNext k t f e s).1 (readNext k t f e s).2)

section Correct

variable {C : ℕ → Instr} {α : Type*} {step : α → Option α} {enc : ℕ → Stacks → α}

/-- One step of the iterated machine on a live configuration. -/
private theorem iter_one (x : α) (y : Option α) (h : step x = y) :
    (flip Option.bind step) (some x) = y := by
  simpa [flip] using h

theorem iterate_loop (hS : Simulates C step enc) {k start next a b : ℕ}
    (hC : C start = .read k a b next) {f : Bool → Stacks → Stacks} {c : Bool → Stacks → ℕ}
    (hbody : ∀ (x : Bool) s, (flip Option.bind step)^[c x s] (some (enc (bif x then a else b) s)) =
      some (enc start (f x s)))
    (hframe : ∀ x s, f x s k = s k) :
    ∀ (l : List Bool) (s : Stacks), s k = l →
      (flip Option.bind step)^[loopCost k f c l s] (some (enc start s)) =
        some (enc next (loopExec k f l s))
  | [], s, hs => by
      have := hS.read start s k a b next hC
      simp only [readNext, hs] at this
      simp only [loopCost, Function.iterate_one, loopExec]
      exact iter_one _ _ this
  | x :: l, s, hs => by
      have hstep := hS.read start s k a b next hC
      simp only [loopCost, loopExec]
      rw [show 1 + c x (update s k l) + loopCost k f c l (f x (update s k l)) =
          loopCost k f c l (f x (update s k l)) + (c x (update s k l) + 1) by omega,
        Function.iterate_add_apply, Function.iterate_succ_apply]
      have h1 : (flip Option.bind step) (some (enc start s)) =
          some (enc (bif x then a else b) (update s k l)) := by
        apply iter_one
        rw [hstep]
        cases x <;> simp [readNext, hs]
      rw [h1, hbody, iterate_loop hS hC hbody hframe l]
      rw [hframe, update_self]

/-- Linear compile: `p` runs from its entry to `next` in exactly `cost p s` machine steps. -/
theorem iterate_cost (hS : Simulates C step enc) :
    ∀ (p : SProg) (start next : ℕ) (s : Stacks), Loaded C p start next → p.WF = true →
      (flip Option.bind step)^[p.cost s] (some (enc (entry p start next) s)) =
        some (enc next (p.exec s))
  | skip, _, _, _, _, _ => rfl
  | push k b, start, next, s, hL, _ => by
      simp only [cost, Function.iterate_one, entry, exec]
      exact iter_one _ _ (hS.push _ _ _ _ _ hL)
  | read k pt pf pe, start, next, s, hL, hwf => by
      obtain ⟨hC, hpt, hpf, hpe⟩ := hL
      simp only [WF, Bool.and_eq_true] at hwf
      obtain ⟨⟨wt, wf⟩, we⟩ := hwf
      have hstep := hS.read start s k _ _ _ hC
      simp only [entry]
      rcases hs : s k with _ | ⟨x, l⟩
      · rw [cost_read_nil hs, exec_read_nil hs, Nat.add_comm, Function.iterate_succ_apply,
          iter_one _ _ hstep]
        simp only [readNext, hs]
        exact iterate_cost hS pe _ _ _ hpe we
      · cases x
        · rw [cost_read_false hs, exec_read_false hs, Nat.add_comm, Function.iterate_succ_apply,
            iter_one _ _ hstep]
          simp only [readNext, hs]
          exact iterate_cost hS pf _ _ _ hpf wf
        · rw [cost_read_true hs, exec_read_true hs, Nat.add_comm, Function.iterate_succ_apply,
            iter_one _ _ hstep]
          simp only [readNext, hs]
          exact iterate_cost hS pt _ _ _ hpt wt
  | seq p q, start, next, s, hL, hwf => by
      obtain ⟨hp, hq⟩ := hL
      simp only [WF, Bool.and_eq_true] at hwf
      simp only [cost, exec, entry]
      rw [Nat.add_comm, Function.iterate_add_apply, iterate_cost hS p _ _ _ hp hwf.1,
        iterate_cost hS q _ _ _ hq hwf.2]
  | loop k pt pf, start, next, s, hL, hwf => by
      obtain ⟨hC, hpt, hpf⟩ := hL
      simp only [WF, Bool.and_eq_true, Bool.not_eq_true'] at hwf
      obtain ⟨⟨⟨ut, uf⟩, wt⟩, wf⟩ := hwf
      simp only [cost, exec, entry]
      refine iterate_loop hS hC (fun x s => ?_) (fun x s => ?_) (s k) s rfl
      · cases x
        · exact iterate_cost hS pf _ _ _ hpf wf
        · exact iterate_cost hS pt _ _ _ hpt wt
      · cases x
        · exact exec_frame pf s uf
        · exact exec_frame pt s ut

end Correct

end SProg

end Factoring.Aux
