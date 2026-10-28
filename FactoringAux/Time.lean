/-
One compile: an explicit source cost gives explicit machine steps.

A source program (`Cmd`, the copied PLIB) whose source cost is at most `S xs` on every input compiles, once, by
`wrapFn`, to a `Program` taking at most `Q * (|xs| + k + S xs + 1) ^ 2` machine steps, with `Q` and `k` depending on
the source program only (`timeComp_wrapFn`).

**The rule this forces.**  The square is paid once per compile.  Every exponential-time part of the engine must
therefore be assembled at the source level and compiled once; a compiled routine that is `call`ed again pays the
square again.  `call` is for polynomial-time leaves only.


Not an audit surface.
-/
module

public import FactoringAux.Copied.PlibTop

@[expose] public section

namespace Factoring.Aux

open Factoring.Aux.Copied Factoring.Aux.Copied.PLib

/-- `M` computes `g` within `T xs` steps on every input `xs` (no polynomial asked). -/
def TimeComp (M : Program) (g : List Bool → List Bool) (T : List Bool → ℕ) : Prop :=
  ∀ xs, outOf (Program.run M (startingMemory xs)).1 = g xs ∧ steps M xs ≤ T xs

/-- **One compile.**  An explicit source cost `S` gives explicit machine steps, with constants `Q` and `k` that
depend on the source program only. -/
theorem timeComp_wrapFn (s : Cmd) (out : ℕ) (g : List Bool → List Bool) (S : List Bool → ℕ)
    (hg : ∀ xs, outOf ((srcOut s xs).ar out) = g xs) (hS : ∀ xs, srcCost s xs ≤ S xs) :
    ∃ Q k : ℕ, TimeComp (wrapFn s out) g (fun xs => Q * (xs.length + k + S xs + 1) ^ 2) := by
  refine ⟨preK (layOf s out) + costK (layOf s out) + 7 + epiK (layOf s out) + 2, s.kmax,
    fun xs => ⟨by rw [outOf_wrapFn, hg], ?_⟩⟩
  have hb := Cmd.run_bnd s (St.init xs) (xs.length + s.kmax)
    ((bnd_init xs).mono (Nat.le_add_right _ _)) (by omega)
  have hlen : (srcOut s xs).ar out 0 ≤ xs.length + s.kmax + srcCost s xs := hb.2 out 0
  have h1 := (run_wrapFn s out xs).2
  have h2 : preK (layOf s out) * (xs.length + 1) + 4
      + costK (layOf s out) * (xs.length + s.kmax + srcCost s xs) * srcCost s xs + 3
      ≤ (preK (layOf s out) + costK (layOf s out) + 7) * (xs.length + s.kmax + srcCost s xs + 1) ^ 2 :=
    sq_bound
  have h3 : epiK (layOf s out) * ((srcOut s xs).ar out 0 + 1)
      ≤ epiK (layOf s out) * (xs.length + s.kmax + srcCost s xs + 1) ^ 2 := by
    apply Nat.mul_le_mul_left
    nlinarith
  have h4 : 1 ≤ (xs.length + s.kmax + srcCost s xs + 1) ^ 2 := by nlinarith
  have h5 : (xs.length + s.kmax + srcCost s xs + 1) ^ 2 ≤ (xs.length + s.kmax + S xs + 1) ^ 2 :=
    Nat.pow_le_pow_left (by have := hS xs; omega) 2
  nlinarith

end Factoring.Aux
