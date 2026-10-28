/-
FactoringAux/SProg/Local.lean — locality: a program commutes with updates of stacks it does not use,
and a well-formed loop is a fold of its bodies over the loop stack.

Not audited.
-/
module

public import FactoringAux.SProg.Lib

@[expose] public section

namespace Factoring.Aux
namespace SProg

open Function

theorem loopExec_update {k j : ℕ} (hkj : k ≠ j) {f : Bool → Stacks → Stacks} (x : List Bool)
    (hf : ∀ b s, f b (update s j x) = update (f b s) j x) :
    ∀ (l : List Bool) (s : Stacks), loopExec k f l (update s j x) = update (loopExec k f l s) j x
  | [], _ => rfl
  | b :: l, s => by
      rw [loopExec_cons, loopExec_cons, update_comm (Ne.symm hkj), hf,
        loopExec_update hkj x hf l]

theorem loopCost_update {k j : ℕ} (hkj : k ≠ j) {f : Bool → Stacks → Stacks}
    {c : Bool → Stacks → ℕ} (x : List Bool)
    (hf : ∀ b s, f b (update s j x) = update (f b s) j x)
    (hc : ∀ b s, c b (update s j x) = c b s) :
    ∀ (l : List Bool) (s : Stacks), loopCost k f c l (update s j x) = loopCost k f c l s
  | [], _ => rfl
  | b :: l, s => by
      rw [loopCost_cons, loopCost_cons, update_comm (Ne.symm hkj), hf, hc,
        loopCost_update hkj x hf hc l]

/-- A program commutes with updates of a stack it does not use. -/
theorem exec_update {j : ℕ} (x : List Bool) :
    ∀ (p : SProg) (s : Stacks), p.uses j = false → p.exec (update s j x) = update (p.exec s) j x
  | skip, _, _ => rfl
  | push k b, s, h => by
      simp only [uses, beq_eq_false_iff_ne] at h
      simp only [exec_push, update_of_ne h]
      exact update_comm (Ne.symm h) _ _ _
  | read k pt pf pe, s, h => by
      simp only [uses, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at h
      obtain ⟨⟨⟨hk, h1⟩, h2⟩, h3⟩ := h
      have hs : update s j x k = s k := update_of_ne hk _ _
      rcases e : s k with _ | ⟨b, l⟩
      · rw [exec_read_nil (by rw [hs, e]), exec_read_nil e, exec_update x pe s h3]
      · cases b
        · rw [exec_read_false (by rw [hs, e]), exec_read_false e, update_comm (Ne.symm hk),
            exec_update x pf _ h2]
        · rw [exec_read_true (by rw [hs, e]), exec_read_true e, update_comm (Ne.symm hk),
            exec_update x pt _ h1]
  | seq p q, s, h => by
      simp only [uses, Bool.or_eq_false_iff] at h
      rw [exec_seq, exec_seq, exec_update x p s h.1, exec_update x q _ h.2]
  | loop k pt pf, s, h => by
      simp only [uses, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at h
      obtain ⟨⟨hk, h1⟩, h2⟩ := h
      rw [exec_loop, exec_loop, update_of_ne hk]
      refine loopExec_update hk x (fun b s => ?_) _ _
      cases b
      · exact exec_update x pf s h2
      · exact exec_update x pt s h1

/-- The cost does not see a stack the program does not use. -/
theorem cost_update {j : ℕ} (x : List Bool) :
    ∀ (p : SProg) (s : Stacks), p.uses j = false → p.cost (update s j x) = p.cost s
  | skip, _, _ => rfl
  | push _ _, _, _ => rfl
  | read k pt pf pe, s, h => by
      simp only [uses, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at h
      obtain ⟨⟨⟨hk, h1⟩, h2⟩, h3⟩ := h
      have hs : update s j x k = s k := update_of_ne hk _ _
      rcases e : s k with _ | ⟨b, l⟩
      · rw [cost_read_nil (by rw [hs, e]), cost_read_nil e, cost_update x pe s h3]
      · cases b
        · rw [cost_read_false (by rw [hs, e]), cost_read_false e, update_comm (Ne.symm hk),
            cost_update x pf _ h2]
        · rw [cost_read_true (by rw [hs, e]), cost_read_true e, update_comm (Ne.symm hk),
            cost_update x pt _ h1]
  | seq p q, s, h => by
      simp only [uses, Bool.or_eq_false_iff] at h
      rw [cost_seq, cost_seq, cost_update x p s h.1, exec_update x p s h.1,
        cost_update x q _ h.2]
  | loop k pt pf, s, h => by
      simp only [uses, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at h
      obtain ⟨⟨hk, h1⟩, h2⟩ := h
      rw [cost_loop, cost_loop, update_of_ne hk]
      refine loopCost_update hk x (fun b s => ?_) (fun b s => ?_) _ _
      · cases b
        · exact exec_update x pf s h2
        · exact exec_update x pt s h1
      · cases b
        · exact cost_update x pf s h2
        · exact cost_update x pt s h1

/-! ### Well-formed loops are folds -/

/-- The cost of folding `F` over `l`, charging `C`. -/
def foldCost (F : Stacks → Bool → Stacks) (C : Stacks → Bool → ℕ) : Stacks → List Bool → ℕ
  | _, [] => 0
  | s, b :: l => C s b + foldCost F C (F s b) l

@[simp] theorem foldCost_nil (F : Stacks → Bool → Stacks) (C : Stacks → Bool → ℕ) (s : Stacks) :
    foldCost F C s [] = 0 := rfl
@[simp] theorem foldCost_cons (F : Stacks → Bool → Stacks) (C : Stacks → Bool → ℕ) (s : Stacks)
    (b : Bool) (l : List Bool) : foldCost F C s (b :: l) = C s b + foldCost F C (F s b) l := rfl

theorem foldCost_append (F : Stacks → Bool → Stacks) (C : Stacks → Bool → ℕ) :
    ∀ (s : Stacks) (l₁ l₂ : List Bool),
      foldCost F C s (l₁ ++ l₂) = foldCost F C s l₁ + foldCost F C (l₁.foldl F s) l₂
  | _, [], _ => by simp
  | s, b :: l, l₂ => by
      simp only [List.cons_append, foldCost_cons, List.foldl_cons, foldCost_append F C _ l l₂]
      omega

/-- One body of `loop k pt pf`, as a fold step. -/
def bodyF (pt pf : SProg) (s : Stacks) (b : Bool) : Stacks := (cond b pt pf).exec s

/-- Its cost. -/
def bodyC (pt pf : SProg) (s : Stacks) (b : Bool) : ℕ := (cond b pt pf).cost s

theorem foldl_bodyF_update {k : ℕ} {pt pf : SProg} (ht : pt.uses k = false)
    (hf : pf.uses k = false) (x : List Bool) :
    ∀ (l : List Bool) (s : Stacks), l.foldl (bodyF pt pf) (update s k x) =
      update (l.foldl (bodyF pt pf) s) k x
  | [], _ => rfl
  | b :: l, s => by
      have : bodyF pt pf (update s k x) b = update (bodyF pt pf s b) k x := by
        cases b
        · exact exec_update x pf s hf
        · exact exec_update x pt s ht
      rw [List.foldl_cons, List.foldl_cons, this, foldl_bodyF_update ht hf x l]

theorem foldCost_bodyF_update {k : ℕ} {pt pf : SProg} (ht : pt.uses k = false)
    (hf : pf.uses k = false) (x : List Bool) :
    ∀ (l : List Bool) (s : Stacks), foldCost (bodyF pt pf) (bodyC pt pf) (update s k x) l =
      foldCost (bodyF pt pf) (bodyC pt pf) s l
  | [], _ => rfl
  | b :: l, s => by
      have e1 : bodyF pt pf (update s k x) b = update (bodyF pt pf s b) k x := by
        cases b
        · exact exec_update x pf s hf
        · exact exec_update x pt s ht
      have e2 : bodyC pt pf (update s k x) b = bodyC pt pf s b := by
        cases b
        · exact cost_update x pf s hf
        · exact cost_update x pt s ht
      rw [foldCost_cons, foldCost_cons, e1, e2, foldCost_bodyF_update ht hf x l]

/-- **A well-formed loop is a fold**: run the bodies in turn over the symbols of stack `k`, then
empty it. -/
theorem exec_loop_fold {k : ℕ} {pt pf : SProg} (ht : pt.uses k = false) (hf : pf.uses k = false)
    (s : Stacks) : (loop k pt pf).exec s = update ((s k).foldl (bodyF pt pf) s) k [] := by
  rw [exec_loop]
  suffices H : ∀ (l : List Bool) (s : Stacks), s k = l →
      loopExec k (fun b => bif b then pt.exec else pf.exec) l s =
        update (l.foldl (bodyF pt pf) s) k [] from H _ s rfl
  intro l
  induction l with
  | nil => intro s hs; rw [loopExec_nil, List.foldl_nil, ← hs, update_eq_self]
  | cons b l ih =>
      intro s hs
      have e : (bif b then pt.exec else pf.exec) (update s k l) = update (bodyF pt pf s b) k l := by
        cases b
        · exact exec_update l pf s hf
        · exact exec_update l pt s ht
      rw [loopExec_cons, e, ih _ (by simp), List.foldl_cons, foldl_bodyF_update ht hf,
        update_idem]

theorem cost_loop_fold {k : ℕ} {pt pf : SProg} (ht : pt.uses k = false) (hf : pf.uses k = false)
    (s : Stacks) : (loop k pt pf).cost s =
      (s k).length + 1 + foldCost (bodyF pt pf) (bodyC pt pf) s (s k) := by
  rw [cost_loop]
  suffices H : ∀ (l : List Bool) (s : Stacks), s k = l →
      loopCost k (fun b => bif b then pt.exec else pf.exec)
        (fun b => bif b then pt.cost else pf.cost) l s =
        l.length + 1 + foldCost (bodyF pt pf) (bodyC pt pf) s l from H _ s rfl
  intro l
  induction l with
  | nil => intro s _; rfl
  | cons b l ih =>
      intro s hs
      have e : (bif b then pt.exec else pf.exec) (update s k l) = update (bodyF pt pf s b) k l := by
        cases b
        · exact exec_update l pf s hf
        · exact exec_update l pt s ht
      have ec : (bif b then pt.cost else pf.cost) (update s k l) = bodyC pt pf s b := by
        cases b
        · exact cost_update l pf s hf
        · exact cost_update l pt s ht
      rw [loopCost_cons, e, ec, ih _ (by simp), foldCost_cons, foldCost_bodyF_update ht hf]
      simp only [List.length_cons]
      omega

end SProg

end Factoring.Aux
