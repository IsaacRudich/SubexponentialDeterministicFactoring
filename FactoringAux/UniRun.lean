/-
The uniform engine: running commands, seen through the scalars below `1000`.

Every expression of the engine is compiled with scratch from `1000`, so the scalars at or above `1000` are junk.
`vw s` is the scalar store cut at `1000`; on it a compiled expression, a copy or a constant act exactly as a
`Function.update`.

* `vw`, `vw_cset`, `vw_copy`, `vw_setK`, `eval_vw`.

Not an audit surface.
-/
module

public import FactoringAux.UniFill

@[expose] public section

namespace Factoring.Aux

open Factoring.Aux.Copied Factoring.Aux.Copied.PLib Ex

/-- The scalars below `1000`. -/
def vw (s : St) : ℕ → ℕ := fun y => if y < 1000 then s.sc y else 0

theorem vw_lt {s : St} {y : ℕ} (h : y < 1000) : vw s y = s.sc y := by simp [vw, h]

theorem eval_vw {e : Ex} (hv : VB 1000 e) (s : St) (A : ℕ → ℕ → ℕ) :
    eval s.sc A e = eval (vw s) A e ∧ cost s.sc A e = cost (vw s) A e :=
  Ex.congr A e _ _ (fun _ hy => (vw_lt hy).symm) hv

theorem vw_cset {e : Ex} {d : ℕ} (hv : VB 1000 e) (hd : d < 1000) (s : St) :
    vw (Cmd.run (cset e d) s).1 = Function.update (vw s) d (eval (vw s) s.ar e) ∧
      (Cmd.run (cset e d) s).1.ar = s.ar ∧ (Cmd.run (cset e d) s).2 ≤ cost (vw s) s.ar e := by
  obtain ⟨a1, a2, a3, a4⟩ := cset_spec e d s hv hd
  obtain ⟨e1, e2⟩ := eval_vw hv s s.ar
  refine ⟨funext fun y => ?_, a3, by rw [← e2]; exact a4⟩
  by_cases hy : y < 1000
  · by_cases hyd : y = d
    · subst hyd; rw [vw_lt hy, a1, e1]; simp
    · rw [vw_lt hy, a2 y hy hyd, Function.update_of_ne hyd, vw_lt hy]
  · simp only [vw, if_neg hy, Function.update_apply]
    split_ifs with h
    · omega
    · rfl

theorem vw_copy {x y : ℕ} (hx : x < 1000) (hy : y < 1000) (s : St) :
    vw (Cmd.run (.copy x y) s).1 = Function.update (vw s) x (vw s y) ∧ (Cmd.run (.copy x y) s).1.ar = s.ar ∧
      (Cmd.run (.copy x y) s).2 = 1 := by
  refine ⟨funext fun z => ?_, rfl, rfl⟩
  simp only [Cmd.run_copy, vw, St.setSc_sc, Function.update_apply]
  split_ifs <;> first | rfl | omega

theorem vw_setK {x k : ℕ} (hx : x < 1000) (s : St) :
    vw (Cmd.run (.setK x k) s).1 = Function.update (vw s) x k ∧ (Cmd.run (.setK x k) s).1.ar = s.ar ∧
      (Cmd.run (.setK x k) s).2 = 1 := by
  refine ⟨funext fun z => ?_, rfl, rfl⟩
  simp only [Cmd.run_setK, vw, St.setSc_sc, Function.update_apply]
  split_ifs <;> first | rfl | omega

end Factoring.Aux
