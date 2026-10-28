/-
FactoringAux/SProg/Lang.lean — L1: the structured stack language `SProg` (syntax, semantics, cost).

Not audited.  Imports Mathlib only.

`SProg` programs act on stacks of `Bool`, indexed by `ℕ` (a program uses finitely many of them; the
head of a list is the top of the stack).  There are no other variables: finite control is the
position in the program text.

* `skip`                — do nothing (cost 0);
* `push k b`            — push `b` on stack `k` (cost 1);
* `read k pt pf pe`     — pop the top of stack `k` and branch on it: `pt` if it was `true`,
                          `pf` if it was `false`, `pe` if the stack was empty (cost 1 + the branch);
* `seq p q`             — `p`, then `q` (cost of `p` + cost of `q`);
* `loop k pt pf`        — while stack `k` is not empty, pop its top and run `pt` or `pf` according to
                          it (cost 1 per test, so `length + 1` plus the bodies).

The semantics `exec` is a total Lean function.  A `loop` runs once per symbol of stack `k` at entry,
and during the iteration on symbol `b :: l` the body starts with stack `k` equal to `l`.  This is what
the machine does whenever the bodies do not touch stack `k`; that condition is `SProg.WF`, and the
compilation theorem assumes it.

-/
module

public import Mathlib.Data.Nat.Notation
public import Mathlib.Logic.Function.Basic

@[expose] public section

namespace Factoring.Aux

/-- The stacks of an `SProg` computation: stack `k` is a list of `Bool`, top first. -/
abbrev Stacks := ℕ → List Bool

/-- Structured programs over `Bool` stacks. -/
inductive SProg
  /-- Do nothing. -/
  | skip
  /-- Push `b` on stack `k`. -/
  | push (k : ℕ) (b : Bool)
  /-- Pop the top of stack `k`; continue with `pt` (it was `true`), `pf` (it was `false`) or `pe`
  (stack `k` was empty). -/
  | read (k : ℕ) (pt pf pe : SProg)
  /-- Sequential composition. -/
  | seq (p q : SProg)
  /-- While stack `k` is not empty: pop its top and run `pt` (it was `true`) or `pf` (`false`). -/
  | loop (k : ℕ) (pt pf : SProg)
  deriving Inhabited

namespace SProg

/-- The final stacks of a loop over the list `l` (the content of the loop stack `k` at entry), with
bodies `f true`, `f false`. -/
def loopExec (k : ℕ) (f : Bool → Stacks → Stacks) : List Bool → Stacks → Stacks
  | [], s => s
  | b :: l, s => loopExec k f l (f b (Function.update s k l))

/-- The cost of a loop over the list `l`: one per test of the loop stack (`l.length + 1` tests), plus
the bodies. -/
def loopCost (k : ℕ) (f : Bool → Stacks → Stacks) (c : Bool → Stacks → ℕ) :
    List Bool → Stacks → ℕ
  | [], _ => 1
  | b :: l, s =>
      1 + c b (Function.update s k l) + loopCost k f c l (f b (Function.update s k l))

/-- The semantics: the final stacks. -/
def exec : SProg → Stacks → Stacks
  | skip, s => s
  | push k b, s => Function.update s k (b :: s k)
  | read k pt pf pe, s =>
      match s k with
      | true :: l => exec pt (Function.update s k l)
      | false :: l => exec pf (Function.update s k l)
      | [] => exec pe s
  | seq p q, s => exec q (exec p s)
  | loop k pt pf, s => loopExec k (fun b => bif b then exec pt else exec pf) (s k) s

/-- The cost: the number of basic steps (`push`, `read`, loop tests). -/
def cost : SProg → Stacks → ℕ
  | skip, _ => 0
  | push _ _, _ => 1
  | read k pt pf pe, s =>
      1 + match s k with
        | true :: l => cost pt (Function.update s k l)
        | false :: l => cost pf (Function.update s k l)
        | [] => cost pe s
  | seq p q, s => cost p s + cost q (exec p s)
  | loop k pt pf, s =>
      loopCost k (fun b => bif b then exec pt else exec pf)
        (fun b => bif b then cost pt else cost pf) (s k) s

/-- Final stacks and cost together. -/
def run (p : SProg) (s : Stacks) : Stacks × ℕ := (exec p s, cost p s)

/-- `p.uses k`: stack `k` occurs in `p`. -/
def uses (j : ℕ) : SProg → Bool
  | skip => false
  | push k _ => k == j
  | read k pt pf pe => k == j || uses j pt || uses j pf || uses j pe
  | seq p q => uses j p || uses j q
  | loop k pt pf => k == j || uses j pt || uses j pf

/-- Well-formed: no loop body uses its own loop stack.  (Then `exec` is what the machine does.) -/
def WF : SProg → Bool
  | skip => true
  | push _ _ => true
  | read _ pt pf pe => WF pt && WF pf && WF pe
  | seq p q => WF p && WF q
  | loop k pt pf => !uses k pt && !uses k pf && WF pt && WF pf

/-- Every stack index in `p` is `< n`. -/
def StacksBelow (n : ℕ) : SProg → Bool
  | skip => true
  | push k _ => decide (k < n)
  | read k pt pf pe => decide (k < n) && StacksBelow n pt && StacksBelow n pf && StacksBelow n pe
  | seq p q => StacksBelow n p && StacksBelow n q
  | loop k pt pf => decide (k < n) && StacksBelow n pt && StacksBelow n pf

/-- The stacks at the start: `l` on stack `0` (the input/output stack), every other stack empty. -/
def initStacks (l : List Bool) : Stacks := Function.update (fun _ => []) 0 l

end SProg

end Factoring.Aux
