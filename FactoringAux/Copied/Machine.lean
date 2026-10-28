/-
Adapted from the authors' related work.
Only the machine: `Memory`, `Memory.set`, `startingMemory`, `Program`, `Program.run`, `haltsNonZero`,
`YesStrings`, `steps`, `RunsInPolyTime`, `acceptedStrings` (the closure that the copied PLIB uses).

Not an audit surface.
-/
module

public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Basic

@[expose] public section

namespace Factoring.Aux.Copied

/-- Register contents.  Registers are numbered by `ℕ` and hold `ℕ`; unwritten
ones hold `0`. -/
abbrev Memory : Type := ℕ → ℕ

/-- `σ` with register `r` set to `v`. -/
def Memory.set (σ : Memory) (r v : ℕ) : Memory := fun i => if i = r then v else σ i

/-- Memory before the program runs: register `0` holds the input length, and
register `1 + k` holds bit `k`.

The length is given because past the input every register holds `0`, which a
program cannot tell apart from a `0` bit. -/
def startingMemory (xs : List Bool) : Memory := fun r =>
  if r = 0 then xs.length
  else if xs.getD (r - 1) false then 1 else 0

/-- A program.  These eleven instructions are the whole language, and none of
them carries a Lean function. -/
inductive Program where
  /-- Do nothing. -/
  | skip
  /-- Run `s`, then `t`. -/
  | seq (s t : Program)
  /-- `dst := 0`. -/
  | zero (dst : ℕ)
  /-- `dst := dst + 1`.  The only instruction that makes a value larger. -/
  | incr (dst : ℕ)
  /-- `dst := dst - 1`, stopping at `0`. -/
  | decr (dst : ℕ)
  /-- `dst := src`. -/
  | copy (dst src : ℕ)
  /-- `dst :=` the register numbered `base` plus `idx`'s value. -/
  | load (dst base idx : ℕ)
  /-- The register numbered `base` plus `idx`'s value `:= src`. -/
  | store (base idx src : ℕ)
  /-- Branch on `a < b`. -/
  | ifLt (a b : ℕ) (t e : Program)
  /-- Branch on `a = 0`. -/
  | ifZero (a : ℕ) (t e : Program)
  /-- Run `body` with `counter` taking `0, …, k-1`, where `k` is `bound`'s value
  on entry.  The only loop, so every program halts. -/
  | loop (bound counter : ℕ) (body : Program)
  deriving Inhabited

/-- Run a program: the memory it ends with, and the steps it took.  Each
instruction costs one step, plus whatever its parts cost. -/
def Program.run : Program → Memory → Memory × ℕ
  | .skip,           σ => (σ, 1)
  | .zero d,         σ => (σ.set d 0, 1)
  | .incr d,         σ => (σ.set d (σ d + 1), 1)
  | .decr d,         σ => (σ.set d (σ d - 1), 1)
  | .copy d s,       σ => (σ.set d (σ s), 1)
  | .load d b i,     σ => (σ.set d (σ (b + σ i)), 1)
  | .store b i s,    σ => (σ.set (b + σ i) (σ s), 1)
  | .seq s t,        σ =>
      let a := Program.run s σ
      let b := Program.run t a.1
      (b.1, a.2 + b.2 + 1)
  | .ifLt a b t e,   σ =>
      let r := if σ a < σ b then Program.run t σ else Program.run e σ
      (r.1, r.2 + 1)
  | .ifZero a t e,   σ =>
      let r := if σ a = 0 then Program.run t σ else Program.run e σ
      (r.1, r.2 + 1)
  | .loop b c body,  σ =>
      (List.range (σ b)).foldl
        (fun acc i =>
          let r := Program.run body (acc.1.set c i)
          (r.1, acc.2 + r.2 + 1))
        (σ, 1)

/-- `M` halts with register `0` non-zero on input `xs`.

Register `0` is the only possible place for an answer: the input occupies
registers `1` through its length, and that length is unbounded. -/
def haltsNonZero (M : Program) (xs : List Bool) : Prop :=
  (Program.run M (startingMemory xs)).1 0 ≠ 0

/-- The strings a question answers yes to.  Every other string is a no; there is
no separate record of them.

Membership is `Prop`-valued because most questions have no program that answers
them. -/
abbrev YesStrings : Type := Set (List Bool)

/-- Steps `M` takes on `xs` — the second half of what `Program.run` returns. -/
def steps (M : Program) (xs : List Bool) : ℕ :=
  (Program.run M (startingMemory xs)).2

/-- Steps bounded by `c * (length + 1) ^ d`, for `c` and `d` fixed before any
input is seen.

Quantified the other way round — for each input some `c` and `d` — it would hold
of every program, since every run is finite. -/
def RunsInPolyTime (M : Program) : Prop :=
  ∃ c d : ℕ, ∀ xs : List Bool, steps M xs ≤ c * (xs.length + 1) ^ d

/-- The set of strings `M` says yes to. -/
def acceptedStrings (M : Program) : YesStrings := {xs | haltsNonZero M xs}

end Factoring.Aux.Copied
