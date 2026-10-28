/-
FactoringAux/SProg/Basic.lean — basic facts about `SProg` semantics: the frame lemma (a program
does not change a stack it does not use).

Not audited.
-/
module

public import FactoringAux.SProg.Lang

@[expose] public section

namespace Factoring.Aux
namespace SProg

open Function

/-! ### Equations for `read` -/

theorem exec_read_true {k : ℕ} {pt pf pe : SProg} {s : Stacks} {l : List Bool}
    (h : s k = true :: l) : (read k pt pf pe).exec s = pt.exec (update s k l) := by
  simp [exec, h]

theorem exec_read_false {k : ℕ} {pt pf pe : SProg} {s : Stacks} {l : List Bool}
    (h : s k = false :: l) : (read k pt pf pe).exec s = pf.exec (update s k l) := by
  simp [exec, h]

theorem exec_read_nil {k : ℕ} {pt pf pe : SProg} {s : Stacks}
    (h : s k = []) : (read k pt pf pe).exec s = pe.exec s := by
  simp [exec, h]

theorem cost_read_true {k : ℕ} {pt pf pe : SProg} {s : Stacks} {l : List Bool}
    (h : s k = true :: l) : (read k pt pf pe).cost s = 1 + pt.cost (update s k l) := by
  simp [cost, h]

theorem cost_read_false {k : ℕ} {pt pf pe : SProg} {s : Stacks} {l : List Bool}
    (h : s k = false :: l) : (read k pt pf pe).cost s = 1 + pf.cost (update s k l) := by
  simp [cost, h]

theorem cost_read_nil {k : ℕ} {pt pf pe : SProg} {s : Stacks}
    (h : s k = []) : (read k pt pf pe).cost s = 1 + pe.cost s := by
  simp [cost, h]

theorem loopExec_frame {k j : ℕ} (hkj : k ≠ j) {f : Bool → Stacks → Stacks}
    (hf : ∀ b s, f b s j = s j) : ∀ (l : List Bool) (s : Stacks), loopExec k f l s j = s j
  | [], _ => rfl
  | b :: l, s => by
      rw [loopExec, loopExec_frame hkj hf l, hf, update_of_ne (Ne.symm hkj)]

/-- The frame lemma: a program leaves alone every stack it does not use. -/
theorem exec_frame {j : ℕ} : ∀ (p : SProg) (s : Stacks), p.uses j = false → p.exec s j = s j
  | skip, _, _ => rfl
  | push k b, s, h => by
      simp only [uses, beq_eq_false_iff_ne] at h
      simp [exec, update_of_ne (Ne.symm h)]
  | read k pt pf pe, s, h => by
      simp only [uses, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at h
      obtain ⟨⟨⟨hk, h1⟩, h2⟩, h3⟩ := h
      rcases hs : s k with _ | ⟨b, l⟩
      · rw [exec_read_nil hs, exec_frame pe _ h3]
      · cases b
        · rw [exec_read_false hs, exec_frame pf _ h2, update_of_ne (Ne.symm hk)]
        · rw [exec_read_true hs, exec_frame pt _ h1, update_of_ne (Ne.symm hk)]
  | seq p q, s, h => by
      simp only [uses, Bool.or_eq_false_iff] at h
      rw [exec, exec_frame q _ h.2, exec_frame p _ h.1]
  | loop k pt pf, s, h => by
      simp only [uses, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at h
      obtain ⟨⟨hk, h1⟩, h2⟩ := h
      rw [exec]
      refine loopExec_frame hk (fun b s => ?_) _ _
      cases b
      · exact exec_frame pf s h2
      · exact exec_frame pt s h1

end SProg

end Factoring.Aux
