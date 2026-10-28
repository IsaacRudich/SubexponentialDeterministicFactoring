/-
Adapted from the authors' related work (the whole file).

Not an audit surface.
-/
/-
PLIB, part 1: a structured source language, its semantics, and a verified
compiler to `Program` with a proved cost model.

**Why a compiler.**  `Program` has unit-cost instructions but only `incr` makes a
value larger, so addition of two registers costs their value, and every program
names its registers by literal index while the input occupies registers
`1 … n` for unbounded `n`.  Hand-written programs therefore spend most of their
proofs on register frames, aliasing between regions and step counts.  The source language
here removes all three:

* **state**: scalars `sc : ℕ → ℕ` and arrays `ar : ℕ → ℕ → ℕ`, every array
  unbounded, no aliasing between any two of them;
* **semantics**: `Cmd.run`, a Lean function shaped exactly like `Program.run`
  (state and cost together), so source programs are verified against
  mathematics by ordinary Lean reasoning on `St`;
* **cost**: every source instruction costs one source step, except
  `call M a`, which costs `M`'s own steps.  `comp_ok` proves that the compiled
  program costs at most `costK L * (V + S) * S`, where `S` is the source cost and
  `V` bounds the values at the start; source values never exceed `V + S`
  (`run_bnd`).  So a source program with polynomially many steps compiles to a
  polynomial-time `Program`, and the consumer never counts machine steps.

The source instruction set is the machine's, lifted: literals, copy, incr, decr,
array read and write at a scalar index plus a literal offset, two branches, the
bounded loop (with the machine's own semantics: bound read on entry, counter
reset each turn) and `call M a`, which runs an arbitrary `Program` with array
`a` as its whole memory.  `call` is what reductions need: the adversary is a
`Program` from a hypothesis, and it runs as a subroutine on a string the source
program lays out in an array.

**Lay** (`Lay`): registers `0 … 3` are scratch, scalar `x` lives at
register `4 + x`, and cell `i` of array `a` at `B + a + A * i` with
`B = 4 + nv` and `A = na` the number of arrays -- the arrays interleaved, so all
of them are unbounded.  An array access costs `O(A * index)` machine steps for
the address, which is where `V` enters the cost.

Main results: `Cmd.run`, `run_bnd`, `compile`, `relocA`, `run_relocA`,
`comp_ok`.  The input prologue and the wrappers that turn a source program into
a decider or a function-computing program are in `PlibTop`.

Not an audit surface.
-/
module

public import FactoringAux.Copied.MachineLemmas

@[expose] public section

namespace Factoring.Aux.Copied.PLib

open Factoring.Aux.Copied Factoring.Aux.Copied.Aux

/-! ### The source language -/

/-- Source state: scalars and arrays, all `ℕ`-valued, all unbounded. -/
@[ext] structure St where
  /-- Scalar variables. -/
  sc : ℕ → ℕ
  /-- Arrays: `ar a i` is cell `i` of array `a`. -/
  ar : ℕ → ℕ → ℕ

namespace St

/-- Set scalar `x` to `v`. -/
def setSc (st : St) (x v : ℕ) : St := ⟨Function.update st.sc x v, st.ar⟩

/-- Replace array `a` by `f`. -/
def putAr (st : St) (a : ℕ) (f : ℕ → ℕ) : St := ⟨st.sc, Function.update st.ar a f⟩

/-- Set cell `i` of array `a` to `v`. -/
def setAr (st : St) (a i v : ℕ) : St := st.putAr a (Function.update (st.ar a) i v)

@[simp] theorem setSc_sc (st : St) (x v : ℕ) : (st.setSc x v).sc = Function.update st.sc x v := rfl
@[simp] theorem setSc_ar (st : St) (x v : ℕ) : (st.setSc x v).ar = st.ar := rfl
@[simp] theorem putAr_sc (st : St) (a : ℕ) (f : ℕ → ℕ) : (st.putAr a f).sc = st.sc := rfl
@[simp] theorem putAr_ar (st : St) (a : ℕ) (f : ℕ → ℕ) :
    (st.putAr a f).ar = Function.update st.ar a f := rfl
@[simp] theorem setAr_sc (st : St) (a i v : ℕ) : (st.setAr a i v).sc = st.sc := rfl
@[simp] theorem setAr_ar (st : St) (a i v : ℕ) :
    (st.setAr a i v).ar = Function.update st.ar a (Function.update (st.ar a) i v) := rfl

/-- Every value is at most `V`. -/
def Bnd (st : St) (V : ℕ) : Prop := (∀ x, st.sc x ≤ V) ∧ ∀ a i, st.ar a i ≤ V

theorem Bnd.mono {st : St} {V W : ℕ} (h : st.Bnd V) (hVW : V ≤ W) : st.Bnd W :=
  ⟨fun x => le_trans (h.1 x) hVW, fun a i => le_trans (h.2 a i) hVW⟩

end St

/-- Source commands.  Each is one machine idea; see the file header. -/
inductive Cmd where
  /-- Do nothing. -/
  | skip
  /-- `s` then `t`. -/
  | seq (s t : Cmd)
  /-- `x := k`. -/
  | setK (x k : ℕ)
  /-- `x := y`. -/
  | copy (x y : ℕ)
  /-- `x := x + 1`. -/
  | incr (x : ℕ)
  /-- `x := x - 1`, truncated. -/
  | decr (x : ℕ)
  /-- `x := a[i + o]`, `o` a literal offset. -/
  | rd (x a i o : ℕ)
  /-- `a[i + o] := y`, `o` a literal offset. -/
  | wr (a i o y : ℕ)
  /-- Branch on `x < y`. -/
  | ifLt (x y : ℕ) (s t : Cmd)
  /-- Branch on `x = 0`. -/
  | ifZero (x : ℕ) (s t : Cmd)
  /-- `for c < b do body`, with `Program.loop`'s semantics: `b` read on entry,
  `c` set to the turn's index at the start of every turn. -/
  | loop (b c : ℕ) (body : Cmd)
  /-- Run the machine program `M` with array `a` as its whole memory. -/
  | call (M : Program) (a : ℕ)
  deriving Inhabited

/-- Run a source command: the final state and the source cost.  Shaped exactly
like `Program.run`. -/
def Cmd.run : Cmd → St → St × ℕ
  | .skip, st => (st, 1)
  | .seq s t, st =>
      let a := Cmd.run s st
      let b := Cmd.run t a.1
      (b.1, a.2 + b.2 + 1)
  | .setK x k, st => (st.setSc x k, 1)
  | .copy x y, st => (st.setSc x (st.sc y), 1)
  | .incr x, st => (st.setSc x (st.sc x + 1), 1)
  | .decr x, st => (st.setSc x (st.sc x - 1), 1)
  | .rd x a i o, st => (st.setSc x (st.ar a (st.sc i + o)), 1)
  | .wr a i o y, st => (st.setAr a (st.sc i + o) (st.sc y), 1)
  | .ifLt x y s t, st =>
      let r := if st.sc x < st.sc y then Cmd.run s st else Cmd.run t st
      (r.1, r.2 + 1)
  | .ifZero x s t, st =>
      let r := if st.sc x = 0 then Cmd.run s st else Cmd.run t st
      (r.1, r.2 + 1)
  | .loop b c body, st =>
      (List.range (st.sc b)).foldl
        (fun acc i =>
          let r := Cmd.run body (acc.1.setSc c i)
          (r.1, acc.2 + r.2 + 1))
        (st, 1)
  | .call M a, st =>
      let r := Program.run M (st.ar a)
      (st.putAr a r.1, r.2 + 1)

/-! ### Unfolding -/

namespace Cmd

/-- The state after `j` turns of a source loop. -/
def loopSt (body : Cmd) (c : ℕ) : ℕ → St → St
  | 0, st => st
  | j + 1, st => (Cmd.run body ((loopSt body c j st).setSc c j)).1

/-- The source cost of `j` turns, the entry step included. -/
def loopCost (body : Cmd) (c : ℕ) : ℕ → St → ℕ
  | 0, _ => 1
  | j + 1, st => loopCost body c j st + (Cmd.run body ((loopSt body c j st).setSc c j)).2 + 1

theorem run_loop_eq (b c : ℕ) (body : Cmd) (st : St) :
    Cmd.run (.loop b c body) st = (loopSt body c (st.sc b) st, loopCost body c (st.sc b) st) := by
  show (List.range (st.sc b)).foldl _ (st, 1) = _
  suffices h : ∀ k : ℕ, (List.range k).foldl
      (fun acc i => ((Cmd.run body (acc.1.setSc c i)).1, acc.2 + (Cmd.run body (acc.1.setSc c i)).2 + 1))
      (st, 1) = (loopSt body c k st, loopCost body c k st) from h (st.sc b)
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [List.range_succ, List.foldl_append, ih]
      rfl

theorem run_skip (st : St) : Cmd.run .skip st = (st, 1) := rfl
theorem run_seq (s t : Cmd) (st : St) :
    Cmd.run (.seq s t) st = ((Cmd.run t (Cmd.run s st).1).1,
      (Cmd.run s st).2 + (Cmd.run t (Cmd.run s st).1).2 + 1) := rfl
theorem run_setK (x k : ℕ) (st : St) : Cmd.run (.setK x k) st = (st.setSc x k, 1) := rfl
theorem run_copy (x y : ℕ) (st : St) : Cmd.run (.copy x y) st = (st.setSc x (st.sc y), 1) := rfl
theorem run_incr (x : ℕ) (st : St) : Cmd.run (.incr x) st = (st.setSc x (st.sc x + 1), 1) := rfl
theorem run_decr (x : ℕ) (st : St) : Cmd.run (.decr x) st = (st.setSc x (st.sc x - 1), 1) := rfl
theorem run_rd (x a i o : ℕ) (st : St) :
    Cmd.run (.rd x a i o) st = (st.setSc x (st.ar a (st.sc i + o)), 1) := rfl
theorem run_wr (a i o y : ℕ) (st : St) :
    Cmd.run (.wr a i o y) st = (st.setAr a (st.sc i + o) (st.sc y), 1) := rfl
theorem run_ifLt (x y : ℕ) (s t : Cmd) (st : St) :
    Cmd.run (.ifLt x y s t) st =
      ((if st.sc x < st.sc y then Cmd.run s st else Cmd.run t st).1,
       (if st.sc x < st.sc y then Cmd.run s st else Cmd.run t st).2 + 1) := rfl
theorem run_ifZero (x : ℕ) (s t : Cmd) (st : St) :
    Cmd.run (.ifZero x s t) st =
      ((if st.sc x = 0 then Cmd.run s st else Cmd.run t st).1,
       (if st.sc x = 0 then Cmd.run s st else Cmd.run t st).2 + 1) := rfl
theorem run_call (M : Program) (a : ℕ) (st : St) :
    Cmd.run (.call M a) st = (st.putAr a (Program.run M (st.ar a)).1,
      (Program.run M (st.ar a)).2 + 1) := rfl

theorem one_le_cost : ∀ (s : Cmd) (st : St), 1 ≤ (Cmd.run s st).2
  | .skip, _ => le_refl _
  | .seq _ _, _ => by rw [run_seq]; omega
  | .setK _ _, _ => le_refl _
  | .copy _ _, _ => le_refl _
  | .incr _, _ => le_refl _
  | .decr _, _ => le_refl _
  | .rd _ _ _ _, _ => le_refl _
  | .wr _ _ _ _, _ => le_refl _
  | .ifLt _ _ _ _, _ => by rw [run_ifLt]; omega
  | .ifZero _ _ _, _ => by rw [run_ifZero]; omega
  | .loop b c body, st => by
      rw [run_loop_eq]
      induction (st.sc b) with
      | zero => exact le_refl _
      | succ j ih => simp only [loopCost]; omega
  | .call _ _, _ => by rw [run_call]; omega

theorem loopCost_mono (body : Cmd) (c : ℕ) (st : St) {i j : ℕ} (h : i ≤ j) :
    loopCost body c i st ≤ loopCost body c j st := by
  induction j with
  | zero => rw [Nat.le_zero.mp h]
  | succ j ih =>
      rcases Nat.lt_or_ge i (j + 1) with h' | h'
      · have := ih (by omega); simp only [loopCost]; omega
      · rw [show i = j + 1 by omega]

/-! ### Values grow by at most one per source step -/

/-- The largest literal a command writes. -/
def kmax : Cmd → ℕ
  | .seq s t => max (kmax s) (kmax t)
  | .setK _ k => k
  | .ifLt _ _ s t => max (kmax s) (kmax t)
  | .ifZero _ s t => max (kmax s) (kmax t)
  | .loop _ _ body => kmax body
  | _ => 0

theorem bnd_setSc {st : St} {V : ℕ} (h : st.Bnd V) {x v : ℕ} (hv : v ≤ V) :
    (st.setSc x v).Bnd V := by
  refine ⟨fun y => ?_, h.2⟩
  simp only [St.setSc_sc, Function.update_apply]
  split_ifs
  · exact hv
  · exact h.1 y

theorem bnd_putAr {st : St} {V : ℕ} (h : st.Bnd V) {a : ℕ} {f : ℕ → ℕ} (hf : ∀ i, f i ≤ V) :
    (st.putAr a f).Bnd V := by
  refine ⟨h.1, fun b i => ?_⟩
  simp only [St.putAr_ar, Function.update_apply]
  split_ifs
  · exact hf i
  · exact h.2 b i

theorem bnd_setAr {st : St} {V : ℕ} (h : st.Bnd V) {a i v : ℕ} (hv : v ≤ V) :
    (st.setAr a i v).Bnd V := by
  refine bnd_putAr h (fun j => ?_)
  simp only [Function.update_apply]
  split_ifs
  · exact hv
  · exact h.2 a j

/-- **Values grow by at most one per source step.**  So a source program's values
stay below its starting bound plus its source cost. -/
theorem run_bnd : ∀ (s : Cmd) (st : St) (V : ℕ), st.Bnd V → s.kmax ≤ V →
    (Cmd.run s st).1.Bnd (V + (Cmd.run s st).2)
  | .skip, st, V, h, _ => h.mono (by simp [run_skip])
  | .seq s t, st, V, h, hk => by
      have hk1 : s.kmax ≤ V := le_trans (le_max_left _ _) hk
      have hk2 : t.kmax ≤ V := le_trans (le_max_right _ _) hk
      have h1 := run_bnd s st V h hk1
      have h2 := run_bnd t (Cmd.run s st).1 _ h1 (le_trans hk2 (Nat.le_add_right _ _))
      rw [run_seq]
      exact h2.mono (by omega)
  | .setK x k, st, V, h, hk => by
      rw [run_setK]; exact bnd_setSc (h.mono (Nat.le_add_right _ _)) (by simp [kmax] at hk; omega)
  | .copy x y, st, V, h, _ => by
      rw [run_copy]; exact bnd_setSc (h.mono (Nat.le_add_right _ _)) (le_trans (h.1 y) (by omega))
  | .incr x, st, V, h, _ => by
      rw [run_incr]; exact bnd_setSc (h.mono (Nat.le_add_right _ _)) (by have := h.1 x; omega)
  | .decr x, st, V, h, _ => by
      rw [run_decr]; exact bnd_setSc (h.mono (Nat.le_add_right _ _)) (by have := h.1 x; omega)
  | .rd x a i o, st, V, h, _ => by
      rw [run_rd]
      exact bnd_setSc (h.mono (Nat.le_add_right _ _)) (le_trans (h.2 a _) (by omega))
  | .wr a i o y, st, V, h, _ => by
      rw [run_wr]
      exact bnd_setAr (h.mono (Nat.le_add_right _ _)) (le_trans (h.1 y) (by omega))
  | .ifLt x y s t, st, V, h, hk => by
      rw [run_ifLt]
      split_ifs
      · exact (run_bnd s st V h (le_trans (le_max_left _ _) hk)).mono (by omega)
      · exact (run_bnd t st V h (le_trans (le_max_right _ _) hk)).mono (by omega)
  | .ifZero x s t, st, V, h, hk => by
      rw [run_ifZero]
      split_ifs
      · exact (run_bnd s st V h (le_trans (le_max_left _ _) hk)).mono (by omega)
      · exact (run_bnd t st V h (le_trans (le_max_right _ _) hk)).mono (by omega)
  | .loop b c body, st, V, h, hk => by
      rw [run_loop_eq]
      have key : ∀ j, j ≤ st.sc b → (loopSt body c j st).Bnd (V + loopCost body c j st) := by
        intro j
        induction j with
        | zero => intro _; exact h.mono (Nat.le_add_right _ _)
        | succ j ih =>
            intro hj
            have hs : ((loopSt body c j st).setSc c j).Bnd (V + loopCost body c j st) :=
              bnd_setSc (ih (by omega)) (by have := h.1 b; omega)
            have := run_bnd body _ _ hs (le_trans (by simpa [kmax] using hk) (Nat.le_add_right _ _))
            exact this.mono (by simp only [loopCost]; omega)
      exact key _ (le_refl _)
  | .call M a, st, V, h, _ => by
      rw [run_call]
      refine bnd_putAr (h.mono (by omega)) (fun i => ?_)
      have := run_val_le M (st.ar a) V (h.2 a) i
      omega

/-! ### Which scalars and arrays a command names -/

/-- One more than the largest scalar named. -/
def nvars : Cmd → ℕ
  | .skip => 0
  | .seq s t => max (nvars s) (nvars t)
  | .setK x _ => x + 1
  | .copy x y => max x y + 1
  | .incr x => x + 1
  | .decr x => x + 1
  | .rd x _ i _ => max x i + 1
  | .wr _ i _ y => max i y + 1
  | .ifLt x y s t => max (max x y + 1) (max (nvars s) (nvars t))
  | .ifZero x s t => max (x + 1) (max (nvars s) (nvars t))
  | .loop b c body => max (max b c + 1) (nvars body)
  | .call _ _ => 0

/-- One more than the largest array named. -/
def narrs : Cmd → ℕ
  | .seq s t => max (narrs s) (narrs t)
  | .rd _ a _ _ => a + 1
  | .wr a _ _ _ => a + 1
  | .ifLt _ _ s t => max (narrs s) (narrs t)
  | .ifZero _ s t => max (narrs s) (narrs t)
  | .loop _ _ body => narrs body
  | .call _ a => a + 1
  | _ => 0

end Cmd

/-! ### Machine helpers -/

/-- `p`, `k` times. -/
def rep : ℕ → Program → Program
  | 0, _ => .skip
  | k + 1, p => .seq p (rep k p)

theorem run_rep_incr (r : ℕ) : ∀ (k : ℕ) (σ : Memory),
    Program.run (rep k (.incr r)) σ = (σ.set r (σ r + k), 2 * k + 1)
  | 0, σ => by simp [rep, Program.run, memory_set_eq_self]
  | k + 1, σ => by
      show ((Program.run (rep k (.incr r)) (σ.set r (σ r + 1))).1,
        1 + (Program.run (rep k (.incr r)) (σ.set r (σ r + 1))).2 + 1) = _
      rw [run_rep_incr r k, memory_set_set, memory_set_get]
      refine Prod.ext ?_ ?_
      · simp only; congr 1; omega
      · simp only; omega

theorem run_rep_decr (r : ℕ) : ∀ (k : ℕ) (σ : Memory),
    Program.run (rep k (.decr r)) σ = (σ.set r (σ r - k), 2 * k + 1)
  | 0, σ => by simp [rep, Program.run, memory_set_eq_self]
  | k + 1, σ => by
      show ((Program.run (rep k (.decr r)) (σ.set r (σ r - 1))).1,
        1 + (Program.run (rep k (.decr r)) (σ.set r (σ r - 1))).2 + 1) = _
      rw [run_rep_decr r k, memory_set_set, memory_set_get]
      refine Prod.ext ?_ ?_
      · simp only; congr 1; omega
      · simp only; omega

theorem run_seq_mem (s t : Program) (σ : Memory) :
    (Program.run (.seq s t) σ).1 = (Program.run t (Program.run s σ).1).1 := rfl

theorem memory_set_apply (σ : Memory) (r v p : ℕ) :
    (σ.set r v) p = if p = r then v else σ p := rfl

/-- `reg 1 := A * reg src`, using register `3` as the counter. -/
def mulTo (A src : ℕ) : Program := .seq (.zero 1) (.loop src 3 (rep A (.incr 1)))

theorem loopMem_mulBody (A : ℕ) (τ : Memory) : ∀ (j p : ℕ),
    loopMem (rep A (.incr 1)) 3 j τ p
      = if p = 1 then τ 1 + A * j else if p = 3 then (if j = 0 then τ 3 else j - 1) else τ p
  | 0, p => by
      show τ p = _
      split_ifs with h1 h3 <;> simp_all
  | j + 1, p => by
      show (Program.run (rep A (.incr 1)) ((loopMem (rep A (.incr 1)) 3 j τ).set 3 j)).1 p = _
      rw [run_rep_incr]
      simp only [memory_set_apply, loopMem_mulBody A τ j]
      split_ifs <;> (simp_all [Nat.mul_succ]; try omega)

theorem loopCost_mulBody (A : ℕ) (τ : Memory) : ∀ j : ℕ,
    loopCost (rep A (.incr 1)) 3 j τ = j * (2 * A + 2) + 1
  | 0 => by simp [loopCost]
  | j + 1 => by
      show loopCost (rep A (.incr 1)) 3 j τ
        + (Program.run (rep A (.incr 1)) ((loopMem (rep A (.incr 1)) 3 j τ).set 3 j)).2 + 1 = _
      rw [run_rep_incr, loopCost_mulBody A τ j]
      ring

theorem run_mulTo_apply {A src : ℕ} (h1 : src ≠ 1) (σ : Memory) (p : ℕ) :
    (Program.run (mulTo A src) σ).1 p
      = if p = 1 then A * σ src else if p = 3 then (if σ src = 0 then σ 3 else σ src - 1)
        else σ p := by
  show (Program.run (.loop src 3 (rep A (.incr 1))) (σ.set 1 0)).1 p = _
  rw [run_loop_eq]
  dsimp only
  rw [memory_set_apply, if_neg h1, loopMem_mulBody]
  simp only [memory_set_apply]
  split_ifs <;> simp_all

theorem cost_mulTo {A src : ℕ} (h1 : src ≠ 1) (σ : Memory) :
    (Program.run (mulTo A src) σ).2 = σ src * (2 * A + 2) + 3 := by
  show 1 + (Program.run (.loop src 3 (rep A (.incr 1))) (σ.set 1 0)).2 + 1 = _
  rw [run_loop_eq]
  dsimp only
  rw [memory_set_apply, if_neg h1, loopCost_mulBody]
  ring

theorem mulTo_frame {A src : ℕ} (h1 : src ≠ 1) (σ : Memory) {p : ℕ} (hp1 : p ≠ 1) (hp3 : p ≠ 3) :
    (Program.run (mulTo A src) σ).1 p = σ p := by
  rw [run_mulTo_apply h1, if_neg hp1, if_neg hp3]

theorem mulTo_one {A src : ℕ} (h1 : src ≠ 1) (σ : Memory) :
    (Program.run (mulTo A src) σ).1 1 = A * σ src := by
  rw [run_mulTo_apply h1, if_pos rfl]

/-! ### The layout -/

/-- Where a source state lives in memory: `nv` scalar registers from `4` on,
then `na` arrays interleaved with stride `na`. -/
structure Lay where
  /-- Number of scalars. -/
  nv : ℕ
  /-- Number of arrays. -/
  na : ℕ

namespace Lay

/-- The first array register. -/
def B (L : Lay) : ℕ := 4 + L.nv

/-- The register holding cell `i` of array `a`. -/
def cell (L : Lay) (a i : ℕ) : ℕ := L.B + a + L.na * i

/-- `σ` holds `st`: every scalar below `nv` and every array below `na`. -/
def Rel (L : Lay) (st : St) (σ : Memory) : Prop :=
  (∀ x, x < L.nv → σ (4 + x) = st.sc x) ∧ ∀ a, a < L.na → ∀ i, σ (L.cell a i) = st.ar a i

theorem four_le_cell (L : Lay) (a i : ℕ) : 4 ≤ L.cell a i := by
  unfold cell B; omega

theorem sreg_lt_cell (L : Lay) {x : ℕ} (hx : x < L.nv) (a i : ℕ) : 4 + x < L.cell a i := by
  unfold cell B; omega

@[simp] theorem cell_ne_zero (L : Lay) (a i : ℕ) : (L.cell a i = 0) = False := by
  have := L.four_le_cell a i; simp only [eq_iff_iff, iff_false]; omega
@[simp] theorem cell_ne_one (L : Lay) (a i : ℕ) : (L.cell a i = 1) = False := by
  have := L.four_le_cell a i; simp only [eq_iff_iff, iff_false]; omega
@[simp] theorem cell_ne_two (L : Lay) (a i : ℕ) : (L.cell a i = 2) = False := by
  have := L.four_le_cell a i; simp only [eq_iff_iff, iff_false]; omega
@[simp] theorem cell_ne_three (L : Lay) (a i : ℕ) : (L.cell a i = 3) = False := by
  have := L.four_le_cell a i; simp only [eq_iff_iff, iff_false]; omega

theorem cell_inj (L : Lay) {a a' i i' : ℕ} (ha : a < L.na) (ha' : a' < L.na)
    (h : L.cell a i = L.cell a' i') : a = a' ∧ i = i' := by
  unfold cell at h
  have h1 : a + L.na * i = a' + L.na * i' := by omega
  have hm : (a + L.na * i) % L.na = (a' + L.na * i') % L.na := by rw [h1]
  rw [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha,
    Nat.mod_eq_of_lt ha'] at hm
  subst hm
  refine ⟨rfl, ?_⟩
  have : L.na * i = L.na * i' := by omega
  exact Nat.eq_of_mul_eq_mul_left (by omega) this

theorem cell_add (L : Lay) (a o v : ℕ) : L.cell a o + L.na * v = L.cell a (o + v) := by
  unfold cell; ring

theorem cell_add' (L : Lay) (a o v : ℕ) : L.cell a o + L.na * v = L.cell a (v + o) := by
  unfold cell; ring

theorem rel_hi {L : Lay} {st : St} {σ σ' : Memory} (h : L.Rel st σ)
    (h' : ∀ p, 4 ≤ p → σ' p = σ p) : L.Rel st σ' :=
  ⟨fun x hx => by rw [h' _ (by omega)]; exact h.1 x hx,
   fun a ha i => by rw [h' _ (L.four_le_cell a i)]; exact h.2 a ha i⟩

theorem rel_setSc {L : Lay} {st : St} {σ : Memory} (h : L.Rel st σ) {x : ℕ} (hx : x < L.nv)
    (v : ℕ) : L.Rel (st.setSc x v) (σ.set (4 + x) v) := by
  refine ⟨fun y hy => ?_, fun a ha i => ?_⟩
  · simp only [memory_set_apply, St.setSc_sc, Function.update_apply]
    by_cases hxy : y = x
    · subst hxy; simp
    · rw [if_neg (by omega), if_neg hxy]; exact h.1 y hy
  · rw [memory_set_apply, if_neg (by have := L.sreg_lt_cell hx a i; omega)]
    exact h.2 a ha i

theorem rel_setAr {L : Lay} {st : St} {σ : Memory} (h : L.Rel st σ) {a : ℕ} (ha : a < L.na)
    (i v : ℕ) : L.Rel (st.setAr a i v) (σ.set (L.cell a i) v) := by
  refine ⟨fun y hy => ?_, fun b hb j => ?_⟩
  · rw [memory_set_apply, if_neg (by have := L.sreg_lt_cell hy a i; omega)]
    exact h.1 y hy
  · simp only [memory_set_apply, St.setAr_ar, Function.update_apply]
    by_cases hc : L.cell b j = L.cell a i
    · obtain ⟨rfl, rfl⟩ := L.cell_inj hb ha hc
      simp
    · rw [if_neg hc]
      by_cases hab : b = a
      · subst hab
        have hji : j ≠ i := fun e => hc (by rw [e])
        simp only [if_true, Function.update_apply, if_neg hji]
        exact h.2 b hb j
      · rw [if_neg hab]; exact h.2 b hb j

/-! ### Array `a` as a whole machine memory -/

/-- Array `a` holds `μ`. -/
def RelA (L : Lay) (a : ℕ) (μ : Memory) (σ : Memory) : Prop := ∀ r, σ (L.cell a r) = μ r

/-- `σ'` agrees with `σ` above the scratch registers, off array `a`. -/
def FrA (L : Lay) (a : ℕ) (σ σ' : Memory) : Prop :=
  ∀ p, 4 ≤ p → (∀ r, p ≠ L.cell a r) → σ' p = σ p

theorem frA_refl (L : Lay) (a : ℕ) (σ : Memory) : L.FrA a σ σ := fun _ _ _ => rfl

theorem frA_trans {L : Lay} {a : ℕ} {σ₁ σ₂ σ₃ : Memory} (h₁ : L.FrA a σ₁ σ₂)
    (h₂ : L.FrA a σ₂ σ₃) : L.FrA a σ₁ σ₃ :=
  fun p hp hr => by rw [h₂ p hp hr, h₁ p hp hr]

theorem frA_low {L : Lay} {a : ℕ} (σ : Memory) {q : ℕ} (hq : q < 4) (v : ℕ) :
    L.FrA a σ (σ.set q v) := fun p hp _ => by rw [memory_set_apply, if_neg (by omega)]

theorem frA_cell {L : Lay} {a : ℕ} (σ : Memory) (d v : ℕ) :
    L.FrA a σ (σ.set (L.cell a d) v) := fun p _ hr => by rw [memory_set_apply, if_neg (hr d)]

theorem relA_low {L : Lay} {a : ℕ} {μ σ : Memory} (h : L.RelA a μ σ) {q : ℕ} (hq : q < 4)
    (v : ℕ) : L.RelA a μ (σ.set q v) := fun r => by
  rw [memory_set_apply, if_neg (by have := L.four_le_cell a r; omega)]; exact h r

theorem relA_cell {L : Lay} {a : ℕ} (ha : a < L.na) {μ σ : Memory} (h : L.RelA a μ σ)
    (d v : ℕ) : L.RelA a (μ.set d v) (σ.set (L.cell a d) v) := fun r => by
  rw [memory_set_apply, memory_set_apply]
  by_cases hr : r = d
  · subst hr; simp
  · rw [if_neg (fun e => hr (L.cell_inj ha ha e).2), if_neg hr]; exact h r

theorem relA_frA {L : Lay} {a : ℕ} {μ σ σ' : Memory} (h : L.RelA a μ σ)
    (hf : ∀ p, 4 ≤ p → σ' p = σ p) : L.RelA a μ σ' ∧ L.FrA a σ σ' :=
  ⟨fun r => by rw [hf _ (L.four_le_cell a r)]; exact h r, fun p hp _ => hf p hp⟩

theorem rel_putAr {L : Lay} {st : St} {σ σ' : Memory} (h : L.Rel st σ) {a : ℕ} (ha : a < L.na)
    {μ : Memory} (hA : L.RelA a μ σ') (hF : L.FrA a σ σ') : L.Rel (st.putAr a μ) σ' := by
  refine ⟨fun x hx => ?_, fun b hb i => ?_⟩
  · rw [hF _ (by omega) (fun r => by have := L.sreg_lt_cell hx a r; omega)]
    exact h.1 x hx
  · simp only [St.putAr_ar, Function.update_apply]
    by_cases hab : b = a
    · subst hab; rw [if_pos rfl]; exact hA i
    · rw [if_neg hab, hF _ (L.four_le_cell b i) (fun r e => hab (L.cell_inj hb ha e).1)]
      exact h.2 b hb i

end Lay

/-! ### The compiler -/

/-- `M` with its register `r` living at cell `r` of array `a`.  Registers
`0 … 3` are scratch. -/
def relocA (L : Lay) (a : ℕ) : Program → Program
  | .skip => .skip
  | .seq s t => .seq (relocA L a s) (relocA L a t)
  | .zero d => seqs [.zero 1, .store (L.cell a d) 1 1]
  | .incr d => seqs [.zero 1, .load 2 (L.cell a d) 1, .incr 2, .store (L.cell a d) 1 2]
  | .decr d => seqs [.zero 1, .load 2 (L.cell a d) 1, .decr 2, .store (L.cell a d) 1 2]
  | .copy d s => seqs [.zero 1, .load 2 (L.cell a s) 1, .store (L.cell a d) 1 2]
  | .load d b i => seqs [.zero 1, .load 2 (L.cell a i) 1, mulTo L.na 2,
      .load 2 (L.cell a b) 1, .zero 1, .store (L.cell a d) 1 2]
  | .store b i s => seqs [.zero 1, .load 2 (L.cell a i) 1, mulTo L.na 2,
      .zero 0, .load 2 (L.cell a s) 0, .store (L.cell a b) 1 2]
  | .ifLt x y t e => seqs [.zero 1, .load 2 (L.cell a x) 1, .load 3 (L.cell a y) 1,
      .ifLt 2 3 (relocA L a t) (relocA L a e)]
  | .ifZero x t e => seqs [.zero 1, .load 2 (L.cell a x) 1,
      .ifZero 2 (relocA L a t) (relocA L a e)]
  | .loop b c body => seqs [.zero 1, .load 2 (L.cell a b) 1,
      .loop 2 3 (seqs [.zero 1, .store (L.cell a c) 1 3, relocA L a body])]

/-- The compiler. -/
def compile (L : Lay) : Cmd → Program
  | .skip => .skip
  | .seq s t => .seq (compile L s) (compile L t)
  | .setK x k => Aux.setK (4 + x) k
  | .copy x y => .copy (4 + x) (4 + y)
  | .incr x => .incr (4 + x)
  | .decr x => .decr (4 + x)
  | .rd x a i o => .seq (mulTo L.na (4 + i)) (.load (4 + x) (L.cell a o) 1)
  | .wr a i o y => .seq (mulTo L.na (4 + i)) (.store (L.cell a o) 1 (4 + y))
  | .ifLt x y s t => .ifLt (4 + x) (4 + y) (compile L s) (compile L t)
  | .ifZero x s t => .ifZero (4 + x) (compile L s) (compile L t)
  | .loop b c body => .loop (4 + b) (4 + c) (compile L body)
  | .call M a => relocA L a M

/-- The cost factor: the compiled program costs at most `costK L * (V + S) * S`. -/
def costK (L : Lay) : ℕ := 2 * L.na + 16

/-! ### `relocA` computes what `M` computes -/

namespace Lay

/-- Array `a` holds `μ` in `σ`, and `σ` agrees with `σ₀` off array `a` and the
scratch registers. -/
def OkA (L : Lay) (a : ℕ) (σ₀ μ σ : Memory) : Prop := L.RelA a μ σ ∧ L.FrA a σ₀ σ

theorem okA_low {L : Lay} {a : ℕ} {σ₀ μ σ : Memory} (h : L.OkA a σ₀ μ σ) {q : ℕ} (hq : q < 4)
    (v : ℕ) : L.OkA a σ₀ μ (σ.set q v) :=
  ⟨relA_low h.1 hq v, frA_trans h.2 (frA_low σ hq v)⟩

theorem okA_cell {L : Lay} {a : ℕ} (ha : a < L.na) {σ₀ μ σ : Memory} (h : L.OkA a σ₀ μ σ)
    (d v : ℕ) : L.OkA a σ₀ (μ.set d v) (σ.set (L.cell a d) v) :=
  ⟨relA_cell ha h.1 d v, frA_trans h.2 (frA_cell σ d v)⟩

theorem okA_hi {L : Lay} {a : ℕ} {σ₀ μ σ σ' : Memory} (h : L.OkA a σ₀ μ σ)
    (hf : ∀ p, 4 ≤ p → σ' p = σ p) : L.OkA a σ₀ μ σ' :=
  ⟨(relA_frA h.1 hf).1, frA_trans h.2 (relA_frA h.1 hf).2⟩

end Lay

open Lay

theorem eq12 : ((1:ℕ) = 2) = False := by decide
theorem eq21 : ((2:ℕ) = 1) = False := by decide

theorem mulTo_hi {A src : ℕ} (h1 : src ≠ 1) (σ : Memory) :
    ∀ p, 4 ≤ p → (Program.run (mulTo A src) σ).1 p = σ p :=
  fun _ hp => mulTo_frame h1 σ (by omega) (by omega)

theorem run_relocA (L : Lay) {a : ℕ} (ha : a < L.na) : ∀ (M : Program) (μ σ : Memory),
    L.RelA a μ σ → L.OkA a σ (Program.run M μ).1 (Program.run (relocA L a M) σ).1 := by
  intro M
  induction M with
  | skip => intro μ σ h; exact ⟨h, frA_refl L a σ⟩
  | seq s t ihs iht =>
      intro μ σ h
      have h1 := ihs μ σ h
      have h2 := iht _ _ h1.1
      exact ⟨h2.1, frA_trans h1.2 h2.2⟩
  | zero d =>
      intro μ σ h
      have h0 : L.OkA a σ μ σ := ⟨h, frA_refl L a σ⟩
      simp only [relocA, run_seqs_mem, List.foldl, run_zero_mem, run_store_mem, memory_set_get,
        Nat.add_zero]
      exact okA_cell ha (okA_low h0 (by omega) 0) d 0
  | incr d =>
      intro μ σ h
      have h0 : L.OkA a σ μ σ := ⟨h, frA_refl L a σ⟩
      simp only [relocA, run_seqs_mem, List.foldl, run_zero_mem, run_store_mem, run_load_mem,
        run_incr_mem', memory_set_get, Nat.add_zero, memory_set_apply, cell_ne_one, cell_ne_two,
        if_false, h d, if_true]
      have := okA_low (okA_low (okA_low h0 (by omega : 1 < 4) 0) (by omega : 2 < 4) (μ d))
        (by omega : 2 < 4) (μ d + 1)
      have h2 := okA_cell ha this d (μ d + 1)
      simpa only [memory_set_apply, run_incr_mem', eq12, if_false, Nat.add_zero] using h2
  | decr d =>
      intro μ σ h
      have h0 : L.OkA a σ μ σ := ⟨h, frA_refl L a σ⟩
      simp only [relocA, run_seqs_mem, List.foldl, run_zero_mem, run_store_mem, run_load_mem,
        run_decr_mem, memory_set_get, Nat.add_zero, memory_set_apply, cell_ne_one, cell_ne_two,
        if_false, h d, if_true]
      have := okA_low (okA_low (okA_low h0 (by omega : 1 < 4) 0) (by omega : 2 < 4) (μ d))
        (by omega : 2 < 4) (μ d - 1)
      have h2 := okA_cell ha this d (μ d - 1)
      simpa only [memory_set_apply, run_decr_mem, eq12, if_false, Nat.add_zero] using h2
  | copy d s =>
      intro μ σ h
      have h0 : L.OkA a σ μ σ := ⟨h, frA_refl L a σ⟩
      simp only [relocA, run_seqs_mem, List.foldl, run_zero_mem, run_store_mem, run_load_mem,
        memory_set_get, Nat.add_zero, memory_set_apply, cell_ne_one, cell_ne_two,
        if_false, h s, if_true, run_copy_mem]
      have := okA_low (okA_low h0 (by omega : 1 < 4) 0) (by omega : 2 < 4) (μ s)
      have h2 := okA_cell ha this d (μ s)
      simpa only [memory_set_apply, eq12, if_false, Nat.add_zero] using h2
  | load d b i =>
      intro μ σ h
      have h0 : L.OkA a σ μ σ := ⟨h, frA_refl L a σ⟩
      simp only [relocA, run_seqs_mem, List.foldl, run_zero_mem, run_store_mem, run_load_mem]
      set τ := ((σ.set 1 0).set 2 ((σ.set 1 0) (L.cell a i + (σ.set 1 0) 1))) with hτ
      have hτ2 : τ 2 = μ i := by simp [τ, memory_set_apply, h i]
      have k1 : L.OkA a σ μ τ := okA_low (okA_low h0 (by omega) 0) (by omega) _
      have k2 := okA_hi k1 (mulTo_hi (A := L.na) (by omega : (2:ℕ) ≠ 1) τ)
      set τ' := (Program.run (mulTo L.na 2) τ).1 with hτ'
      have hτ'1 : τ' 1 = L.na * μ i := by rw [hτ', mulTo_one (by omega), hτ2]
      have hval : τ' (L.cell a b + τ' 1) = μ (b + μ i) := by
        rw [hτ'1, cell_add]; exact k2.1 _
      rw [hval]
      have k3 := okA_low (okA_low k2 (by omega : 2 < 4) (μ (b + μ i))) (by omega : 1 < 4) 0
      have k4 := okA_cell ha k3 d (μ (b + μ i))
      simpa only [memory_set_apply, if_true, if_false, run_load_mem, Nat.add_zero,
        eq12, eq21] using k4
  | store b i s =>
      intro μ σ h
      have h0 : L.OkA a σ μ σ := ⟨h, frA_refl L a σ⟩
      simp only [relocA, run_seqs_mem, List.foldl, run_zero_mem, run_store_mem, run_load_mem]
      set τ := ((σ.set 1 0).set 2 ((σ.set 1 0) (L.cell a i + (σ.set 1 0) 1))) with hτ
      have hτ2 : τ 2 = μ i := by simp [τ, memory_set_apply, h i]
      have k1 : L.OkA a σ μ τ := okA_low (okA_low h0 (by omega) 0) (by omega) _
      have k2 := okA_hi k1 (mulTo_hi (A := L.na) (by omega : (2:ℕ) ≠ 1) τ)
      set τ' := (Program.run (mulTo L.na 2) τ).1 with hτ'
      have hτ'1 : τ' 1 = L.na * μ i := by rw [hτ', mulTo_one (by omega), hτ2]
      have hs : (τ'.set 0 0) (L.cell a s + (τ'.set 0 0) 0) = μ s := by
        simp only [memory_set_apply, if_true, Nat.add_zero, cell_ne_zero, if_false]; exact k2.1 s
      rw [hs]
      have k3 := okA_low (okA_low k2 (by omega : 0 < 4) 0) (by omega : 2 < 4) (μ s)
      have h1' : ((τ'.set 0 0).set 2 (μ s)) 1 = L.na * μ i := by
        simp only [memory_set_apply]; simpa using hτ'1
      rw [h1', cell_add]
      have k4 := okA_cell ha k3 (b + μ i) (μ s)
      simpa only [memory_set_apply, if_true, run_store_mem] using k4
  | ifLt x y t e iht ihe =>
      intro μ σ h
      have h0 : L.OkA a σ μ σ := ⟨h, frA_refl L a σ⟩
      simp only [relocA, run_seqs_mem, List.foldl, run_zero_mem, run_load_mem, run_ifLt_mem]
      set τ := (((σ.set 1 0).set 2 ((σ.set 1 0) (L.cell a x + (σ.set 1 0) 1))).set 3
        (((σ.set 1 0).set 2 ((σ.set 1 0) (L.cell a x + (σ.set 1 0) 1)))
          (L.cell a y + ((σ.set 1 0).set 2 ((σ.set 1 0) (L.cell a x + (σ.set 1 0) 1))) 1)))
        with hτ
      have k1 : L.OkA a σ μ τ := okA_low (okA_low (okA_low h0 (by omega) 0) (by omega) _) (by omega) _
      have hx : τ 2 = μ x := by simp [τ, memory_set_apply, h x]
      have hy : τ 3 = μ y := by simp [τ, memory_set_apply, h y]
      rw [hx, hy]
      split_ifs
      · have := iht μ τ k1.1; exact ⟨this.1, frA_trans k1.2 this.2⟩
      · have := ihe μ τ k1.1; exact ⟨this.1, frA_trans k1.2 this.2⟩
  | ifZero x t e iht ihe =>
      intro μ σ h
      have h0 : L.OkA a σ μ σ := ⟨h, frA_refl L a σ⟩
      simp only [relocA, run_seqs_mem, List.foldl, run_zero_mem, run_load_mem, run_ifZero_mem]
      set τ := ((σ.set 1 0).set 2 ((σ.set 1 0) (L.cell a x + (σ.set 1 0) 1))) with hτ
      have k1 : L.OkA a σ μ τ := okA_low (okA_low h0 (by omega) 0) (by omega) _
      have hx : τ 2 = μ x := by simp [τ, memory_set_apply, h x]
      rw [hx]
      split_ifs
      · have := iht μ τ k1.1; exact ⟨this.1, frA_trans k1.2 this.2⟩
      · have := ihe μ τ k1.1; exact ⟨this.1, frA_trans k1.2 this.2⟩
  | loop b c body ih =>
      intro μ σ h
      have h0 : L.OkA a σ μ σ := ⟨h, frA_refl L a σ⟩
      simp only [relocA, run_seqs_mem, List.foldl, run_zero_mem, run_load_mem, run_loop_mem]
      set τ := ((σ.set 1 0).set 2 ((σ.set 1 0) (L.cell a b + (σ.set 1 0) 1))) with hτ
      have k1 : L.OkA a σ μ τ := okA_low (okA_low h0 (by omega) 0) (by omega) _
      have hb : τ 2 = μ b := by simp [τ, memory_set_apply, h b]
      rw [hb]
      have key : ∀ j, L.OkA a σ (loopMem body c j μ)
          (loopMem (seqs [.zero 1, .store (L.cell a c) 1 3, relocA L a body]) 3 j τ) := by
        intro j
        induction j with
        | zero => exact k1
        | succ j ihj =>
            show L.OkA a σ (Program.run body ((loopMem body c j μ).set c j)).1
              (Program.run (seqs [.zero 1, .store (L.cell a c) 1 3, relocA L a body])
                ((loopMem _ 3 j τ).set 3 j)).1
            simp only [run_seqs_mem, List.foldl, run_zero_mem, run_store_mem]
            have e1 : (((loopMem (seqs [.zero 1, .store (L.cell a c) 1 3, relocA L a body]) 3 j τ).set
                3 j).set 1 0) 3 = j := by simp [memory_set_apply]
            have e2 : (((loopMem (seqs [.zero 1, .store (L.cell a c) 1 3, relocA L a body]) 3 j τ).set
                3 j).set 1 0) 1 = 0 := by simp [memory_set_apply]
            rw [e1, e2, Nat.add_zero]
            have m1 := okA_cell ha (okA_low (okA_low ihj (by omega : 3 < 4) j) (by omega : 1 < 4) 0) c j
            have m2 := ih _ _ m1.1
            exact ⟨m2.1, frA_trans m1.2 m2.2⟩
      exact key _

/-! ### What `relocA` costs -/

theorem aux_loopCost_mono (body : Program) (c : ℕ) (μ : Memory) {i j : ℕ} (h : i ≤ j) :
    Aux.loopCost body c i μ ≤ Aux.loopCost body c j μ := by
  induction j with
  | zero => rw [Nat.le_zero.mp h]
  | succ j ih =>
      rcases Nat.lt_or_ge i (j + 1) with h' | h'
      · have := ih (by omega); simp only [Aux.loopCost]; omega
      · rw [show i = j + 1 by omega]

theorem aux_loopMem_val (body : Program) (c : ℕ) (μ : Memory) (V : ℕ) (hV : ∀ r, μ r ≤ V)
    (B : ℕ) (hB : B ≤ V) : ∀ j, j ≤ B → ∀ r, loopMem body c j μ r ≤ V + Aux.loopCost body c j μ := by
  intro j
  induction j with
  | zero => intro _ r; exact le_trans (hV r) (by simp [Aux.loopCost])
  | succ j ih =>
      intro hj r
      have hs : ∀ r, ((loopMem body c j μ).set c j) r ≤ V + Aux.loopCost body c j μ :=
        memory_set_le (ih (by omega)) (by omega)
      have := run_val_le body _ _ hs r
      show (Program.run body ((loopMem body c j μ).set c j)).1 r ≤ V + (Aux.loopCost body c j μ
        + (Program.run body ((loopMem body c j μ).set c j)).2 + 1)
      omega

theorem costK_pos (L : Lay) : 16 ≤ costK L := by unfold costK; omega

theorem prog_one_le_cost (M : Program) (σ : Memory) : 1 ≤ (Program.run M σ).2 := by
  cases M with
  | loop b c body =>
      rw [cost_loop]
      exact le_trans (by simp [Aux.loopCost]) (aux_loopCost_mono body c σ (Nat.zero_le (σ b)))
  | seq s t => rw [cost_seq]; omega
  | ifLt x y s t => rw [cost_ifLt]; omega
  | ifZero x s t => rw [cost_ifZero]; omega
  | _ => simp [Program.run]

theorem sixteen_le_of (L : Lay) {V T X : ℕ} (hX : costK L * (V + T) ≤ X) (hT : 1 ≤ T) :
    16 ≤ X := by
  have := costK_pos L
  have : 16 * 1 ≤ costK L * (V + T) := Nat.mul_le_mul (by omega) (by omega)
  omega

theorem sixteen_le_X (L : Lay) {M : Program} {μ : Memory} {V X : ℕ}
    (hX : costK L * (V + (Program.run M μ).2) ≤ X) : 16 ≤ X := by
  have := costK_pos L; have := prog_one_le_cost M μ
  have : 16 * 1 ≤ costK L * (V + (Program.run M μ).2) := Nat.mul_le_mul (by omega) (by omega)
  omega

/-- The address step: `(2A + 2) v + 15 ≤ costK * (V + 1)` when `v ≤ V`. -/
theorem addr_le (L : Lay) {v V X : ℕ} (hv : v ≤ V) (hX : costK L * (V + 1) ≤ X) :
    v * (2 * L.na + 2) + 15 ≤ X := by
  unfold costK at hX
  have : v * (2 * L.na + 2) ≤ V * (2 * L.na + 2) := Nat.mul_le_mul_right _ hv
  nlinarith

theorem run_loopHead (L : Lay) (a c : ℕ) (P : Program) (ρ : Memory) :
    (Program.run (seqs [.zero 1, .store (L.cell a c) 1 3, P]) ρ).1
      = (Program.run P ((ρ.set 1 0).set (L.cell a c) (ρ 3))).1 ∧
    (Program.run (seqs [.zero 1, .store (L.cell a c) 1 3, P]) ρ).2
      = (Program.run P ((ρ.set 1 0).set (L.cell a c) (ρ 3))).2 + 6 := by
  have e1 : (ρ.set 1 0) 3 = ρ 3 := by simp [memory_set_apply]
  have e2 : (ρ.set 1 0) 1 = 0 := by simp [memory_set_apply]
  constructor
  · simp only [run_seqs_mem, List.foldl, run_zero_mem, run_store_mem, e1, e2, Nat.add_zero]
  · simp only [run_seqs_cost, seqsCost, cost_zero, cost_store, cost_skip, run_zero_mem,
      run_store_mem, e1, e2, Nat.add_zero]
    omega

theorem cost_relocA (L : Lay) {a : ℕ} (ha : a < L.na) : ∀ (M : Program) (μ σ : Memory) (V X : ℕ),
    L.RelA a μ σ → (∀ r, μ r ≤ V) → costK L * (V + (Program.run M μ).2) ≤ X →
    (Program.run (relocA L a M) σ).2 ≤ X * (Program.run M μ).2 := by
  intro M
  induction M with
  | skip =>
      intro μ σ V X _ _ hX
      have := costK_pos L
      simp only [relocA, cost_skip] at hX ⊢; nlinarith
  | seq s t ihs iht =>
      intro μ σ V X h hV hX
      simp only [relocA, cost_seq]
      rw [cost_seq] at hX
      have hX1 : costK L * (V + (Program.run s μ).2) ≤ X :=
        le_trans (Nat.mul_le_mul_left _ (by omega)) hX
      have c1 := ihs μ σ V X h hV hX1
      have hV2 := run_val_le s μ V hV
      have h2 := (run_relocA L ha s μ σ h).1
      have hX2 : costK L * (V + (Program.run s μ).2 + (Program.run t (Program.run s μ).1).2) ≤ X :=
        le_trans (Nat.mul_le_mul_left _ (by omega)) hX
      have c2 := iht _ _ _ X h2 hV2 hX2
      have hX0 : 1 ≤ X := le_trans (by omega) (sixteen_le_of L hX (by omega))
      rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]
      omega
  | zero d =>
      intro μ σ V X _ _ hX
      have := costK_pos L
      simp only [relocA, run_seqs_cost, seqsCost, cost_zero, cost_store, Program.run] at hX ⊢
      nlinarith
  | incr d =>
      intro μ σ V X _ _ hX
      have := costK_pos L
      simp only [relocA, run_seqs_cost, seqsCost, cost_zero, cost_store, cost_load, cost_incr,
        Program.run] at hX ⊢
      nlinarith
  | decr d =>
      intro μ σ V X _ _ hX
      have := costK_pos L
      simp only [relocA, run_seqs_cost, seqsCost, cost_zero, cost_store, cost_load, cost_decr,
        Program.run] at hX ⊢
      nlinarith
  | copy d s =>
      intro μ σ V X _ _ hX
      have := costK_pos L
      simp only [relocA, run_seqs_cost, seqsCost, cost_zero, cost_store, cost_load,
        Program.run] at hX ⊢
      nlinarith
  | load d b i =>
      intro μ σ V X h hV hX
      have hT : (Program.run (Program.load d b i) μ).2 = 1 := rfl
      rw [hT] at hX ⊢
      simp only [relocA, run_seqs_cost, seqsCost, cost_zero, cost_store, cost_load,
        cost_mulTo (by omega : (2:ℕ) ≠ 1), run_zero_mem, run_load_mem]
      have hv : ((σ.set 1 0).set 2 ((σ.set 1 0) (L.cell a i + (σ.set 1 0) 1))) 2 = μ i := by
        simp [memory_set_apply, h i]
      rw [hv]
      have := addr_le L (hV i) hX
      omega
  | store b i s =>
      intro μ σ V X h hV hX
      have hT : (Program.run (Program.store b i s) μ).2 = 1 := rfl
      rw [hT] at hX ⊢
      simp only [relocA, run_seqs_cost, seqsCost, cost_zero, cost_store, cost_load,
        cost_mulTo (by omega : (2:ℕ) ≠ 1), run_zero_mem, run_load_mem]
      have hv : ((σ.set 1 0).set 2 ((σ.set 1 0) (L.cell a i + (σ.set 1 0) 1))) 2 = μ i := by
        simp [memory_set_apply, h i]
      rw [hv]
      have := addr_le L (hV i) hX
      omega
  | ifLt x y t e iht ihe =>
      intro μ σ V X h hV hX
      have hX0 : 16 ≤ X := sixteen_le_X L hX
      simp only [relocA, run_seqs_cost, seqsCost, cost_zero, cost_load, cost_ifLt, cost_skip,
        run_zero_mem, run_load_mem]
      set τ := (((σ.set 1 0).set 2 ((σ.set 1 0) (L.cell a x + (σ.set 1 0) 1))).set 3
        (((σ.set 1 0).set 2 ((σ.set 1 0) (L.cell a x + (σ.set 1 0) 1)))
          (L.cell a y + ((σ.set 1 0).set 2 ((σ.set 1 0) (L.cell a x + (σ.set 1 0) 1))) 1)))
        with hτ
      have k1 : L.RelA a μ τ :=
        (okA_low (okA_low (okA_low (⟨h, frA_refl L a σ⟩ : L.OkA a σ μ σ) (by omega) 0)
          (by omega) _) (by omega) _).1
      have hx : τ 2 = μ x := by simp [τ, memory_set_apply, h x]
      have hy : τ 3 = μ y := by simp [τ, memory_set_apply, h y]
      rw [hx, hy]
      rw [cost_ifLt] at hX
      split_ifs at hX ⊢ with hc
      · have := iht μ τ V X k1 hV (le_trans (Nat.mul_le_mul_left _ (by omega)) hX)
        rw [Nat.mul_add, Nat.mul_one]; omega
      · have := ihe μ τ V X k1 hV (le_trans (Nat.mul_le_mul_left _ (by omega)) hX)
        rw [Nat.mul_add, Nat.mul_one]; omega
  | ifZero x t e iht ihe =>
      intro μ σ V X h hV hX
      have hX0 : 16 ≤ X := sixteen_le_X L hX
      simp only [relocA, run_seqs_cost, seqsCost, cost_zero, cost_load, cost_skip,
        run_zero_mem, run_load_mem]
      set τ := ((σ.set 1 0).set 2 ((σ.set 1 0) (L.cell a x + (σ.set 1 0) 1))) with hτ
      have k1 : L.RelA a μ τ :=
        (okA_low (okA_low (⟨h, frA_refl L a σ⟩ : L.OkA a σ μ σ) (by omega) 0) (by omega) _).1
      have hx : τ 2 = μ x := by simp [τ, memory_set_apply, h x]
      simp only [cost_ifZero] at hX ⊢
      rw [hx]
      split_ifs at hX ⊢ with hc
      · have := iht μ τ V X k1 hV (le_trans (Nat.mul_le_mul_left _ (by omega)) hX)
        rw [Nat.mul_add, Nat.mul_one]; omega
      · have := ihe μ τ V X k1 hV (le_trans (Nat.mul_le_mul_left _ (by omega)) hX)
        rw [Nat.mul_add, Nat.mul_one]; omega
  | loop b c body ih =>
      intro μ σ V X h hV hX
      have hX0 : 16 ≤ X := sixteen_le_X L hX
      simp only [relocA, run_seqs_cost, seqsCost, cost_zero, cost_load, cost_skip,
        run_zero_mem, run_load_mem, cost_loop]
      set τ := ((σ.set 1 0).set 2 ((σ.set 1 0) (L.cell a b + (σ.set 1 0) 1))) with hτ
      have k1 : L.OkA a σ μ τ :=
        okA_low (okA_low (⟨h, frA_refl L a σ⟩ : L.OkA a σ μ σ) (by omega) 0) (by omega) _
      have hb : τ 2 = μ b := by simp [τ, memory_set_apply, h b]
      rw [hb]
      rw [cost_loop] at hX
      set R := seqs [.zero 1, .store (L.cell a c) 1 3, relocA L a body] with hR
      have hval := aux_loopMem_val body c μ V hV (μ b) (hV b)
      have key : ∀ j, j ≤ μ b → L.OkA a σ (loopMem body c j μ) (loopMem R 3 j τ) ∧
          Aux.loopCost R 3 j τ + 6 ≤ X * Aux.loopCost body c j μ := by
        intro j
        induction j with
        | zero => intro _; simp only [Aux.loopCost]; exact ⟨k1, by omega⟩
        | succ j ihj =>
            intro hj
            obtain ⟨ok, cj⟩ := ihj (by omega)
            have m1 := okA_cell ha (okA_low (okA_low ok (by omega : 3 < 4) j) (by omega : 1 < 4) 0) c j
            have hcostR := (run_loopHead L a c (relocA L a body) ((loopMem R 3 j τ).set 3 j)).2
            have hmemR := (run_loopHead L a c (relocA L a body) ((loopMem R 3 j τ).set 3 j)).1
            rw [memory_set_get] at hcostR hmemR
            have m2 := run_relocA L ha body _ _ m1.1
            have hVj : ∀ r, ((loopMem body c j μ).set c j) r ≤ V + Aux.loopCost body c j μ :=
              memory_set_le (hval j (by omega)) (by have := hV b; omega)
            have hmono := aux_loopCost_mono body c μ (show j + 1 ≤ μ b by omega)
            have hXj : costK L * (V + Aux.loopCost body c j μ
                + (Program.run body ((loopMem body c j μ).set c j)).2) ≤ X := by
              refine le_trans (Nat.mul_le_mul_left _ ?_) hX
              simp only [Aux.loopCost] at hmono
              omega
            have c3 := ih _ _ _ X m1.1 hVj hXj
            refine ⟨?_, ?_⟩
            · show L.OkA a σ (Program.run body ((loopMem body c j μ).set c j)).1
                (Program.run R ((loopMem R 3 j τ).set 3 j)).1
              rw [hmemR]; exact ⟨m2.1, frA_trans m1.2 m2.2⟩
            · show Aux.loopCost R 3 j τ + (Program.run R ((loopMem R 3 j τ).set 3 j)).2 + 1 + 6
                ≤ X * (Aux.loopCost body c j μ
                  + (Program.run body ((loopMem body c j μ).set c j)).2 + 1)
              rw [hcostR, Nat.mul_add, Nat.mul_add, Nat.mul_one]
              omega
      have := (key (μ b) le_rfl).2
      omega

/-! ### The compiler is correct, at the promised cost -/

theorem compile_loop_eq (L : Lay) (b c : ℕ) (body : Cmd) :
    compile L (.loop b c body) = .loop (4 + b) (4 + c) (compile L body) := rfl

/-- **The compiler is correct, and costs at most `costK L * (V + S) * S`.**

`V` bounds every value of the starting state and the literals of `s`; `S` is the
source cost.  Stated with a free `X ≥ costK L * (V + S)` so that it composes. -/
theorem comp_ok (L : Lay) : ∀ (s : Cmd) (st : St) (σ : Memory) (V X : ℕ),
    L.Rel st σ → st.Bnd V → s.kmax ≤ V → s.nvars ≤ L.nv → s.narrs ≤ L.na →
    costK L * (V + (Cmd.run s st).2) ≤ X →
    L.Rel (Cmd.run s st).1 (Program.run (compile L s) σ).1 ∧
      (Program.run (compile L s) σ).2 ≤ X * (Cmd.run s st).2 := by
  intro s
  induction s with
  | skip =>
      intro st σ V X h _ _ _ _ hX
      have := sixteen_le_of L hX (Cmd.one_le_cost .skip st)
      exact ⟨h, by simp only [compile, cost_skip, Cmd.run_skip]; omega⟩
  | seq s t ihs iht =>
      intro st σ V X h hb hk hv ha hX
      simp only [Cmd.kmax, Cmd.nvars, Cmd.narrs, max_le_iff] at hk hv ha
      have hT := Cmd.one_le_cost (.seq s t) st
      rw [Cmd.run_seq] at hX hT ⊢
      have hX1 : costK L * (V + (Cmd.run s st).2) ≤ X :=
        le_trans (Nat.mul_le_mul_left _ (by omega)) hX
      obtain ⟨r1, c1⟩ := ihs st σ V X h hb hk.1 hv.1 ha.1 hX1
      have hb2 := Cmd.run_bnd s st V hb hk.1
      have hX2 : costK L * (V + (Cmd.run s st).2 + (Cmd.run t (Cmd.run s st).1).2) ≤ X :=
        le_trans (Nat.mul_le_mul_left _ (by omega)) hX
      obtain ⟨r2, c2⟩ := iht _ _ _ X r1 hb2 (le_trans hk.2 (by omega)) hv.2 ha.2 hX2
      have hX0 : 1 ≤ X := le_trans (by omega) (sixteen_le_of L hX hT)
      refine ⟨r2, ?_⟩
      simp only [compile, cost_seq]
      rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]
      omega
  | setK x k =>
      intro st σ V X h _ hk hv _ hX
      simp only [Cmd.kmax, Cmd.nvars] at hk hv
      simp only [Cmd.run_setK] at hX ⊢
      refine ⟨?_, ?_⟩
      · simp only [compile, run_setK]; exact rel_setSc h (by omega) k
      · simp only [compile, cost_setK]
        have : costK L * (V + 1) ≥ 16 * (V + 1) := Nat.mul_le_mul_right _ (costK_pos L)
        omega
  | copy x y =>
      intro st σ V X h _ _ hv _ hX
      simp only [Cmd.nvars] at hv
      have := sixteen_le_of L hX (Cmd.one_le_cost (.copy x y) st)
      simp only [Cmd.run_copy] at hX ⊢
      refine ⟨?_, by simp only [compile, cost_copy]; omega⟩
      simp only [compile, run_copy_mem]
      rw [h.1 y (by omega)]; exact rel_setSc h (by omega) _
  | incr x =>
      intro st σ V X h _ _ hv _ hX
      simp only [Cmd.nvars] at hv
      have := sixteen_le_of L hX (Cmd.one_le_cost (.incr x) st)
      simp only [Cmd.run_incr] at hX ⊢
      refine ⟨?_, by simp only [compile, cost_incr]; omega⟩
      simp only [compile, run_incr_mem']
      rw [h.1 x (by omega)]; exact rel_setSc h (by omega) _
  | decr x =>
      intro st σ V X h _ _ hv _ hX
      simp only [Cmd.nvars] at hv
      have := sixteen_le_of L hX (Cmd.one_le_cost (.decr x) st)
      simp only [Cmd.run_decr] at hX ⊢
      refine ⟨?_, by simp only [compile, cost_decr]; omega⟩
      simp only [compile, run_decr_mem]
      rw [h.1 x (by omega)]; exact rel_setSc h (by omega) _
  | rd x a i o =>
      intro st σ V X h hb _ hv ha hX
      simp only [Cmd.nvars, Cmd.narrs] at hv ha
      simp only [Cmd.run_rd] at hX ⊢
      have hτ := mulTo_hi (A := L.na) (by omega : 4 + i ≠ 1) σ
      have h1 := mulTo_one (A := L.na) (by omega : 4 + i ≠ 1) σ
      rw [h.1 i (by omega)] at h1
      refine ⟨?_, ?_⟩
      · simp only [compile, run_seq_mem, run_load_mem]
        rw [h1, cell_add', hτ _ (L.four_le_cell _ _), h.2 a (by omega)]
        exact rel_setSc (rel_hi h hτ) (by omega) _
      · simp only [compile, cost_seq, cost_load, cost_mulTo (by omega : 4 + i ≠ 1)]
        rw [h.1 i (by omega)]
        have := addr_le L (hb.1 i) hX
        omega
  | wr a i o y =>
      intro st σ V X h hb _ hv ha hX
      simp only [Cmd.nvars, Cmd.narrs] at hv ha
      simp only [Cmd.run_wr] at hX ⊢
      have hτ := mulTo_hi (A := L.na) (by omega : 4 + i ≠ 1) σ
      have h1 := mulTo_one (A := L.na) (by omega : 4 + i ≠ 1) σ
      rw [h.1 i (by omega)] at h1
      refine ⟨?_, ?_⟩
      · simp only [compile, run_seq_mem, run_store_mem]
        rw [h1, cell_add', hτ _ (by omega), h.1 y (by omega)]
        exact rel_setAr (rel_hi h hτ) (by omega) _ _
      · simp only [compile, cost_seq, cost_store, cost_mulTo (by omega : 4 + i ≠ 1)]
        rw [h.1 i (by omega)]
        have := addr_le L (hb.1 i) hX
        omega
  | ifLt x y s t ihs iht =>
      intro st σ V X h hb hk hv ha hX
      simp only [Cmd.kmax, Cmd.nvars, Cmd.narrs, max_le_iff] at hk hv ha
      have hX0 := sixteen_le_of L hX (Cmd.one_le_cost (.ifLt x y s t) st)
      simp only [Cmd.run_ifLt] at hX ⊢
      simp only [compile, run_ifLt_mem, cost_ifLt]
      rw [h.1 x (by omega), h.1 y (by omega)]
      split_ifs at hX ⊢
      · obtain ⟨r, c⟩ := ihs st σ V X h hb hk.1 hv.2.1 ha.1
          (le_trans (Nat.mul_le_mul_left _ (by omega)) hX)
        exact ⟨r, by rw [Nat.mul_add, Nat.mul_one]; omega⟩
      · obtain ⟨r, c⟩ := iht st σ V X h hb hk.2 hv.2.2 ha.2
          (le_trans (Nat.mul_le_mul_left _ (by omega)) hX)
        exact ⟨r, by rw [Nat.mul_add, Nat.mul_one]; omega⟩
  | ifZero x s t ihs iht =>
      intro st σ V X h hb hk hv ha hX
      simp only [Cmd.kmax, Cmd.nvars, Cmd.narrs, max_le_iff] at hk hv ha
      have hX0 := sixteen_le_of L hX (Cmd.one_le_cost (.ifZero x s t) st)
      simp only [Cmd.run_ifZero] at hX ⊢
      simp only [compile, run_ifZero_mem, cost_ifZero]
      rw [h.1 x (by omega)]
      split_ifs at hX ⊢
      · obtain ⟨r, c⟩ := ihs st σ V X h hb hk.1 hv.2.1 ha.1
          (le_trans (Nat.mul_le_mul_left _ (by omega)) hX)
        exact ⟨r, by rw [Nat.mul_add, Nat.mul_one]; omega⟩
      · obtain ⟨r, c⟩ := iht st σ V X h hb hk.2 hv.2.2 ha.2
          (le_trans (Nat.mul_le_mul_left _ (by omega)) hX)
        exact ⟨r, by rw [Nat.mul_add, Nat.mul_one]; omega⟩
  | loop b c body ih =>
      intro st σ V X h hb hk hv ha hX
      simp only [Cmd.kmax, Cmd.nvars, Cmd.narrs, max_le_iff] at hk hv ha
      have hX0 := sixteen_le_of L hX (Cmd.one_le_cost (.loop b c body) st)
      rw [Cmd.run_loop_eq] at hX ⊢
      rw [compile_loop_eq, run_loop_eq, h.1 b (by omega)]
      simp only
      have key : ∀ j, j ≤ st.sc b →
          L.Rel (Cmd.loopSt body c j st) (loopMem (compile L body) (4 + c) j σ) ∧
          (Cmd.loopSt body c j st).Bnd (V + Cmd.loopCost body c j st) ∧
          Aux.loopCost (compile L body) (4 + c) j σ ≤ X * Cmd.loopCost body c j st := by
        intro j
        induction j with
        | zero =>
            intro _
            exact ⟨h, hb.mono (by simp [Cmd.loopCost]), by simp [Aux.loopCost, Cmd.loopCost]; omega⟩
        | succ j ihj =>
            intro hj
            obtain ⟨r, bd, cst⟩ := ihj (by omega)
            have r1 := rel_setSc r (show c < L.nv by omega) j
            have b1 : ((Cmd.loopSt body c j st).setSc c j).Bnd (V + Cmd.loopCost body c j st) :=
              Cmd.bnd_setSc bd (by have := hb.1 b; omega)
            have hmono := Cmd.loopCost_mono body c st (show j + 1 ≤ st.sc b by omega)
            simp only [Cmd.loopCost] at hmono
            obtain ⟨r2, c2⟩ := ih _ _ _ X r1 b1 (le_trans hk (by omega)) hv.2 ha
              (le_trans (Nat.mul_le_mul_left _ (by omega)) hX)
            have b2 := Cmd.run_bnd body _ _ b1 (le_trans hk (by omega))
            refine ⟨r2, b2.mono (by simp only [Cmd.loopCost]; omega), ?_⟩
            show Aux.loopCost (compile L body) (4 + c) j σ
                + (Program.run (compile L body) ((loopMem (compile L body) (4 + c) j σ).set (4 + c) j)).2
                + 1 ≤ X * (Cmd.loopCost body c j st
                  + (Cmd.run body ((Cmd.loopSt body c j st).setSc c j)).2 + 1)
            rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]
            omega
      obtain ⟨r, -, cst⟩ := key _ le_rfl
      exact ⟨r, cst⟩
  | call M a =>
      intro st σ V X h hb _ _ ha hX
      simp only [Cmd.narrs] at ha
      simp only [Cmd.run_call] at hX ⊢
      have hA : L.RelA a (st.ar a) σ := fun r => h.2 a (by omega) r
      have ok := run_relocA L (show a < L.na by omega) M (st.ar a) σ hA
      refine ⟨rel_putAr h (by omega) ok.1 ok.2, ?_⟩
      have := cost_relocA L (show a < L.na by omega) M (st.ar a) σ V X hA (hb.2 a)
        (le_trans (Nat.mul_le_mul_left _ (by omega)) hX)
      simp only [compile]
      rw [Nat.mul_add, Nat.mul_one]
      omega

end Factoring.Aux.Copied.PLib

#print axioms Factoring.Aux.Copied.PLib.Cmd.run_bnd
#print axioms Factoring.Aux.Copied.PLib.run_relocA
#print axioms Factoring.Aux.Copied.PLib.cost_relocA
#print axioms Factoring.Aux.Copied.PLib.comp_ok
