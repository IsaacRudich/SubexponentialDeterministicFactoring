/-
FactoringAux/SProg/Lib.lean — small `SProg` routines with exact specifications: sequences, `move`,
`clear`, `copy`, `readBit`; and a cost bound for loops.

Not audited.
-/
module

public import FactoringAux.SProg.Basic
public import Mathlib.Tactic.SplitIfs
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace Factoring.Aux
namespace SProg

open Function

/-- Equality of two stack assignments built by `update`: compare pointwise.  With a list of facts,
only those facts are used (faster when the context has large hypotheses). -/
macro "stacks_ext" : tactic =>
  `(tactic| (funext j; simp only [Function.update_apply]; split_ifs <;> simp_all))

/-- `stacks_ext` using only the given facts. -/
macro "stacks_ext_with" " [" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (funext j; simp only [Function.update_apply]; split_ifs <;> (try subst j) <;>
      first | with_reducible rfl | (simp [$ts,*]; done) | (simp only [] at *; done) | omega))

/-! ### Sequences -/

/-- Run the programs one after the other. -/
def seqs : List SProg → SProg
  | [] => skip
  | p :: ps => seq p (seqs ps)

@[simp] theorem exec_seqs_nil (s : Stacks) : (seqs []).exec s = s := rfl
@[simp] theorem exec_seqs_cons (p : SProg) (ps : List SProg) (s : Stacks) :
    (seqs (p :: ps)).exec s = (seqs ps).exec (p.exec s) := rfl
@[simp] theorem cost_seqs_nil (s : Stacks) : (seqs []).cost s = 0 := rfl
@[simp] theorem cost_seqs_cons (p : SProg) (ps : List SProg) (s : Stacks) :
    (seqs (p :: ps)).cost s = p.cost s + (seqs ps).cost (p.exec s) := rfl

@[simp] theorem exec_skip (s : Stacks) : skip.exec s = s := rfl
@[simp] theorem cost_skip (s : Stacks) : skip.cost s = 0 := rfl
@[simp] theorem exec_push (k : ℕ) (b : Bool) (s : Stacks) :
    (push k b).exec s = update s k (b :: s k) := rfl
@[simp] theorem cost_push (k : ℕ) (b : Bool) (s : Stacks) : (push k b).cost s = 1 := rfl
@[simp] theorem exec_seq (p q : SProg) (s : Stacks) : (seq p q).exec s = q.exec (p.exec s) := rfl
@[simp] theorem cost_seq (p q : SProg) (s : Stacks) :
    (seq p q).cost s = p.cost s + q.cost (p.exec s) := rfl

theorem exec_loop (k : ℕ) (pt pf : SProg) (s : Stacks) :
    (loop k pt pf).exec s = loopExec k (fun b => bif b then pt.exec else pf.exec) (s k) s := rfl
theorem cost_loop (k : ℕ) (pt pf : SProg) (s : Stacks) :
    (loop k pt pf).cost s = loopCost k (fun b => bif b then pt.exec else pf.exec)
      (fun b => bif b then pt.cost else pf.cost) (s k) s := rfl

@[simp] theorem loopExec_nil (k : ℕ) (f : Bool → Stacks → Stacks) (s : Stacks) :
    loopExec k f [] s = s := rfl
@[simp] theorem loopExec_cons (k : ℕ) (f : Bool → Stacks → Stacks) (b : Bool) (l : List Bool)
    (s : Stacks) : loopExec k f (b :: l) s = loopExec k f l (f b (update s k l)) := rfl
@[simp] theorem loopCost_nil (k : ℕ) (f : Bool → Stacks → Stacks) (c : Bool → Stacks → ℕ)
    (s : Stacks) : loopCost k f c [] s = 1 := rfl
@[simp] theorem loopCost_cons (k : ℕ) (f : Bool → Stacks → Stacks) (c : Bool → Stacks → ℕ)
    (b : Bool) (l : List Bool) (s : Stacks) :
    loopCost k f c (b :: l) s = 1 + c b (update s k l) + loopCost k f c l (f b (update s k l)) :=
  rfl

/-- A loop whose bodies cost at most `B` costs at most `(B + 1) · length + 1`. -/
theorem loopCost_le {k : ℕ} {f : Bool → Stacks → Stacks} {c : Bool → Stacks → ℕ} {B : ℕ}
    (hc : ∀ b s, c b s ≤ B) : ∀ (l : List Bool) (s : Stacks), loopCost k f c l s ≤ (B + 1) * l.length + 1
  | [], _ => by simp
  | b :: l, s => by
      have h1 := loopCost_le (k := k) (f := f) hc l (f b (update s k l))
      have h2 := hc b (update s k l)
      simp only [loopCost_cons, List.length_cons, Nat.mul_succ]
      omega

/-! ### `readBit` -/

/-- Pop the top of stack `k` and continue with `f` of it (an empty stack reads as `false`). -/
def readBit (k : ℕ) (f : Bool → SProg) : SProg := read k (f true) (f false) (f false)

theorem exec_readBit {k : ℕ} {f : Bool → SProg} {s : Stacks} {x : Bool} {l : List Bool}
    (h : s k = x :: l) : (readBit k f).exec s = (f x).exec (update s k l) := by
  cases x
  · exact exec_read_false h
  · exact exec_read_true h

theorem cost_readBit {k : ℕ} {f : Bool → SProg} {s : Stacks} {x : Bool} {l : List Bool}
    (h : s k = x :: l) : (readBit k f).cost s = 1 + (f x).cost (update s k l) := by
  cases x
  · exact cost_read_false h
  · exact cost_read_true h

theorem exec_readBit_nil {k : ℕ} {f : Bool → SProg} {s : Stacks}
    (h : s k = []) : (readBit k f).exec s = (f false).exec s := exec_read_nil h

theorem cost_readBit_nil {k : ℕ} {f : Bool → SProg} {s : Stacks}
    (h : s k = []) : (readBit k f).cost s = 1 + (f false).cost s := cost_read_nil h

/-! ### `move`, `clear`, `copy` -/

/-- Pop every symbol of `a` and push it on `b` (`b` gets `a` reversed on top). -/
def move (a b : ℕ) : SProg := loop a (push b true) (push b false)

/-- Empty stack `a`. -/
def clear (a : ℕ) : SProg := loop a skip skip

/-- Pop one symbol of `k` (if any). -/
def pop (k : ℕ) : SProg := read k skip skip skip

/-- Put a copy of `a` on top of `b`, through the empty stack `t`; `a` is restored. -/
def copy (a b t : ℕ) : SProg :=
  seq (move a t) (loop t (seq (push a true) (push b true)) (seq (push a false) (push b false)))

theorem exec_move {a b : ℕ} (hab : a ≠ b) (s : Stacks) :
    (move a b).exec s = update (update s a []) b ((s a).reverse ++ s b) := by
  rw [move, exec_loop]
  suffices H : ∀ (l : List Bool) (s : Stacks), s a = l →
      loopExec a (fun x => bif x then (push b true).exec else (push b false).exec) l s =
        update (update s a []) b (l.reverse ++ s b) from H _ s rfl
  intro l
  induction l with
  | nil => intro s hs; rw [loopExec_nil]; rw [← hs]; stacks_ext
  | cons x l ih =>
      intro s hs
      rw [loopExec_cons]
      have e : (bif x then (push b true).exec else (push b false).exec) (update s a l) =
          update (update s a l) b (x :: s b) := by
        cases x <;> simp [update_of_ne (Ne.symm hab)]
      rw [e, ih _ (by simp [update_of_ne hab])]
      stacks_ext

theorem cost_move (a b : ℕ) (hab : a ≠ b) (s : Stacks) :
    (move a b).cost s = 2 * (s a).length + 1 := by
  rw [move, cost_loop]
  suffices H : ∀ (l : List Bool) (s : Stacks),
      loopCost a (fun x => bif x then (push b true).exec else (push b false).exec)
        (fun x => bif x then (push b true).cost else (push b false).cost) l s = 2 * l.length + 1
    from H _ s
  intro l
  induction l with
  | nil => intro s; rfl
  | cons x l ih => intro s; rw [loopCost_cons, ih]; cases x <;> simp <;> ring

theorem exec_clear (a : ℕ) (s : Stacks) : (clear a).exec s = update s a [] := by
  rw [clear, exec_loop]
  suffices H : ∀ (l : List Bool) (s : Stacks), s a = l →
      loopExec a (fun x => bif x then skip.exec else skip.exec) l s = update s a [] from H _ s rfl
  intro l
  induction l with
  | nil => intro s hs; rw [loopExec_nil, ← hs, update_eq_self]
  | cons x l ih =>
      intro s hs
      rw [loopExec_cons]
      have e : (bif x then skip.exec else skip.exec) (update s a l) = update s a l := by
        cases x <;> rfl
      rw [e, ih _ (by simp)]
      simp

theorem cost_clear (a : ℕ) (s : Stacks) : (clear a).cost s = (s a).length + 1 := by
  rw [clear, cost_loop]
  suffices H : ∀ (l : List Bool) (s : Stacks),
      loopCost a (fun x => bif x then skip.exec else skip.exec)
        (fun x => bif x then skip.cost else skip.cost) l s = l.length + 1 from H _ s
  intro l
  induction l with
  | nil => intro s; rfl
  | cons x l ih => intro s; rw [loopCost_cons, ih]; cases x <;> simp <;> ring

theorem exec_pop_cons {k : ℕ} {s : Stacks} {x : Bool} {l : List Bool} (h : s k = x :: l) :
    (pop k).exec s = update s k l := by
  cases x
  · rw [pop, exec_read_false h]; rfl
  · rw [pop, exec_read_true h]; rfl

theorem cost_pop_le (k : ℕ) (s : Stacks) : (pop k).cost s ≤ 1 := by
  rw [pop]; unfold cost; split <;> simp

theorem exec_copy {a b t : ℕ} (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) (s : Stacks)
    (ht : s t = []) : (copy a b t).exec s = update s b (s a ++ s b) := by
  rw [copy, exec_seq, exec_move hat, exec_loop]
  suffices H : ∀ (l : List Bool) (s' : Stacks), s' t = l →
      loopExec t (fun x => bif x then (seq (push a true) (push b true)).exec
        else (seq (push a false) (push b false)).exec) l s' =
        update (update (update s' t []) a (l.reverse ++ s' a)) b (l.reverse ++ s' b) by
    rw [H _ _ rfl]
    simp only [update_self, ht, List.append_nil, List.reverse_reverse]
    have h1 : update (update s a []) t (s a).reverse b = s b := by
      rw [update_of_ne hbt, update_of_ne (Ne.symm hab)]
    rw [h1]
    stacks_ext
  intro l
  induction l with
  | nil => intro s' hs; rw [loopExec_nil, ← hs]; stacks_ext
  | cons x l ih =>
      intro s' hs
      rw [loopExec_cons]
      have e : (bif x then (seq (push a true) (push b true)).exec
          else (seq (push a false) (push b false)).exec) (update s' t l) =
          update (update (update s' t l) a (x :: s' a)) b (x :: s' b) := by
        cases x <;> simp [update_of_ne hat, update_of_ne hbt, update_of_ne (Ne.symm hab)]
      rw [e, ih _ (by simp [update_of_ne (Ne.symm hat), update_of_ne (Ne.symm hbt)])]
      stacks_ext

theorem cost_copy {a b t : ℕ} (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) (s : Stacks)
    (ht : s t = []) : (copy a b t).cost s = 5 * (s a).length + 2 := by
  rw [copy, cost_seq, cost_move a t hat, exec_move hat, cost_loop]
  suffices H : ∀ (l : List Bool) (s' : Stacks),
      loopCost t (fun x => bif x then (seq (push a true) (push b true)).exec
        else (seq (push a false) (push b false)).exec)
        (fun x => bif x then (seq (push a true) (push b true)).cost
          else (seq (push a false) (push b false)).cost) l s' = 3 * l.length + 1 by
    rw [H]; simp [ht]; ring
  intro l
  induction l with
  | nil => intro s; rfl
  | cons x l ih => intro s; rw [loopCost_cons, ih]; cases x <;> simp <;> ring

end SProg

end Factoring.Aux

namespace Factoring.Aux
namespace SProg

open Function

/-! ### Loop-free programs: a static cost bound -/

/-- `p` has no loop. -/
def LoopFree : SProg → Bool
  | skip => true
  | push _ _ => true
  | read _ pt pf pe => LoopFree pt && LoopFree pf && LoopFree pe
  | seq p q => LoopFree p && LoopFree q
  | loop _ _ _ => false

/-- The longest path through a loop-free program. -/
def lfBound : SProg → ℕ
  | skip => 0
  | push _ _ => 1
  | read _ pt pf pe => 1 + max (lfBound pt) (max (lfBound pf) (lfBound pe))
  | seq p q => lfBound p + lfBound q
  | loop _ _ _ => 0

theorem cost_le_lfBound : ∀ (p : SProg) (s : Stacks), p.LoopFree = true → p.cost s ≤ p.lfBound
  | skip, _, _ => le_refl _
  | push _ _, _, _ => le_refl _
  | read k pt pf pe, s, h => by
      simp only [LoopFree, Bool.and_eq_true] at h
      obtain ⟨⟨h1, h2⟩, h3⟩ := h
      rcases hs : s k with _ | ⟨x, l⟩
      · rw [cost_read_nil hs]
        have := cost_le_lfBound pe s h3
        simp only [lfBound]; omega
      · cases x
        · rw [cost_read_false hs]
          have := cost_le_lfBound pf (update s k l) h2
          simp only [lfBound]; omega
        · rw [cost_read_true hs]
          have := cost_le_lfBound pt (update s k l) h1
          simp only [lfBound]; omega
  | seq p q, s, h => by
      simp only [LoopFree, Bool.and_eq_true] at h
      have := cost_le_lfBound p s h.1
      have := cost_le_lfBound q (p.exec s) h.2
      simp only [cost_seq, lfBound]; omega
  | loop _ _ _, _, h => by simp [LoopFree] at h

/-- `loop k (push j b) (push j b)`: push `b` on `j` once per symbol of `k`. -/
theorem exec_loop_push {k j : ℕ} (hkj : k ≠ j) (b : Bool) (s : Stacks) :
    (loop k (push j b) (push j b)).exec s =
      update (update s k []) j (List.replicate (s k).length b ++ s j) := by
  rw [exec_loop]
  suffices H : ∀ (l : List Bool) (s : Stacks), s k = l →
      loopExec k (fun x => bif x then (push j b).exec else (push j b).exec) l s =
        update (update s k []) j (List.replicate l.length b ++ s j) from H _ s rfl
  intro l
  induction l with
  | nil => intro s hs; rw [loopExec_nil, ← hs]; stacks_ext
  | cons x l ih =>
      intro s hs
      rw [loopExec_cons]
      have e : (bif x then (push j b).exec else (push j b).exec) (update s k l) =
          update (update s k l) j (b :: s j) := by
        cases x <;> simp [update_of_ne (Ne.symm hkj)]
      rw [e, ih _ (by simp [update_of_ne hkj])]
      simp only [List.length_cons, List.replicate_succ', List.append_assoc, List.singleton_append]
      stacks_ext

theorem cost_loop_push {k j : ℕ} (b : Bool) (s : Stacks) :
    (loop k (push j b) (push j b)).cost s = 2 * (s k).length + 1 := by
  rw [cost_loop]
  suffices H : ∀ (l : List Bool) (s : Stacks),
      loopCost k (fun x => bif x then (push j b).exec else (push j b).exec)
        (fun x => bif x then (push j b).cost else (push j b).cost) l s = 2 * l.length + 1
    from H _ s
  intro l
  induction l with
  | nil => intro s; rfl
  | cons x l ih => intro s; rw [loopCost_cons, ih]; cases x <;> simp <;> ring

end SProg

end Factoring.Aux
