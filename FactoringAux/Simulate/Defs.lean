/-
FactoringAux/Simulate/Defs.lean — L2′: the translation `Program → SProg`, and its syntactic facts
(stacks used, well-formedness).

Not audited.

`sim p k` simulates `p`; its `loop` nodes get the stacks `k, k+1, …` (two each: the bound and the
counter), so `sim p k` uses the work stacks `0 … 15` and `k … k + 2 nl p - 1` only.
-/
module

public import FactoringAux.Simulate.Instr

@[expose] public section

namespace Factoring.Aux.Sim

open SProg Function Factoring.Aux.Copied

/-- Number of `loop` nodes. -/
def nl : Program → ℕ
  | .seq s t => nl s + nl t
  | .ifLt _ _ t e => nl t + nl e
  | .ifZero _ t e => nl t + nl e
  | .loop _ _ body => nl body + 1
  | _ => 0

/-- The largest register number written in the program text. -/
def lits : Program → ℕ
  | .skip => 0
  | .seq s t => max (lits s) (lits t)
  | .zero d => d
  | .incr d => d
  | .decr d => d
  | .copy d s => max d s
  | .load d b i => max d (max b i)
  | .store b i s => max b (max i s)
  | .ifLt a b t e => max (max a b) (max (lits t) (lits e))
  | .ifZero a t e => max a (max (lits t) (lits e))
  | .loop b c body => max (max b c) (lits body)

/-- Compare `A` with `B` (unary): afterwards `B = B - A`, `F = A - B`. -/
def cmpBody : SProg := read mB skip skip (push mF true)

/-- One turn of a simulated loop with counter register `c`, loop stacks `k` (bound), `k+1`
(counter). -/
def iterP (c : ℕ) (body : SProg) (k : ℕ) : SProg :=
  seqs [copy (k + 1) mV mT1, put c, body, push (k + 1) true]

/-- The simulation. -/
def sim : Program → ℕ → SProg
  | .skip, _ => skip
  | .seq s t, k => seq (sim s k) (sim t (k + 2 * nl s))
  | .zero d, _ => put d
  | .incr d, _ => simIncr d
  | .decr d, _ => simDecr d
  | .copy d s, _ => simCopy d s
  | .load d b i, _ => simLoad d b i
  | .store b i s, _ => simStore b i s
  | .ifLt a b t e, k =>
      seqs [get a mA, get b mB, loop mA cmpBody cmpBody,
        read mB (seq (clear mB) (sim t k)) skip (seq (clear mF) (sim e (k + 2 * nl t)))]
  | .ifZero a t e, k =>
      seqs [get a mA, read mA (seq (clear mA) (sim e (k + 2 * nl t))) skip (sim t k)]
  | .loop b c body, k =>
      seqs [get b mA, move mA k, loop k (iterP c (sim body (k + 2)) k) (iterP c (sim body (k + 2)) k),
        clear (k + 1)]

/-! ### Stacks used -/

/-- The largest stack index used. -/
def maxUse : SProg → ℕ
  | .skip => 0
  | .push k _ => k
  | .read k pt pf pe => max k (max (maxUse pt) (max (maxUse pf) (maxUse pe)))
  | .seq p q => max (maxUse p) (maxUse q)
  | .loop k pt pf => max k (max (maxUse pt) (maxUse pf))

theorem uses_le {j : ℕ} : ∀ p : SProg, p.uses j = true → j ≤ maxUse p
  | .skip, h => by simp [uses] at h
  | .push k _, h => by simp [uses] at h; simp [maxUse, h]
  | .read k pt pf pe, h => by
      simp only [uses, Bool.or_eq_true, beq_iff_eq] at h
      simp only [maxUse]
      rcases h with ((h | h) | h) | h
      · omega
      · have := uses_le pt h; omega
      · have := uses_le pf h; omega
      · have := uses_le pe h; omega
  | .seq p q, h => by
      simp only [uses, Bool.or_eq_true] at h
      simp only [maxUse]
      rcases h with h | h
      · have := uses_le p h; omega
      · have := uses_le q h; omega
  | .loop k pt pf, h => by
      simp only [uses, Bool.or_eq_true, beq_iff_eq] at h
      simp only [maxUse]
      rcases h with (h | h) | h
      · omega
      · have := uses_le pt h; omega
      · have := uses_le pf h; omega

theorem stacksBelow_of {n : ℕ} : ∀ p : SProg, maxUse p < n → p.StacksBelow n = true
  | .skip, _ => rfl
  | .push k _, h => by simpa [StacksBelow, maxUse] using h
  | .read k pt pf pe, h => by
      simp only [maxUse] at h
      simp only [StacksBelow, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨⟨by omega, stacksBelow_of pt (by omega)⟩, stacksBelow_of pf (by omega)⟩,
        stacksBelow_of pe (by omega)⟩
  | .seq p q, h => by
      simp only [maxUse] at h
      simp only [StacksBelow, Bool.and_eq_true]
      exact ⟨stacksBelow_of p (by omega), stacksBelow_of q (by omega)⟩
  | .loop k pt pf, h => by
      simp only [maxUse] at h
      simp only [StacksBelow, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨by omega, stacksBelow_of pt (by omega)⟩, stacksBelow_of pf (by omega)⟩

theorem maxUse_seqs : ∀ l : List SProg, maxUse (seqs l) = (l.map maxUse).foldr max 0
  | [] => rfl
  | p :: l => by simp [seqs, maxUse, maxUse_seqs l]

theorem maxUse_pushN (k : ℕ) : ∀ n, maxUse (pushN k n) ≤ k
  | 0 => by simp [pushN, seqs, maxUse]
  | n + 1 => by
      have := maxUse_pushN k n
      simp only [pushN, List.replicate_succ, seqs, maxUse] at this ⊢
      omega

theorem wf_seqs : ∀ l : List SProg, (∀ p ∈ l, p.WF = true) → (seqs l).WF = true
  | [], _ => rfl
  | p :: l, h => by
      simp only [seqs, WF, Bool.and_eq_true]
      exact ⟨h p (by simp), wf_seqs l (fun q hq => h q (by simp [hq]))⟩

theorem wf_pushN (k : ℕ) : ∀ n, (pushN k n).WF = true
  | 0 => rfl
  | n + 1 => by
      have := wf_pushN k n
      simpa [pushN, List.replicate_succ, SProg.seqs, WF] using this

theorem wf_swap : swap.WF = true := by decide

theorem low_get (d X : ℕ) (hX : X = mA ∨ X = mB) : maxUse (get d X) < 16 ∧ (get d X).WF = true := by
  have h1 := maxUse_pushN mR d
  have h2 : maxUse swap ≤ 15 := by decide
  constructor
  · simp only [get, maxUse_seqs, List.map, List.foldr]
    simp only [copy, move, maxUse]
    rcases hX with rfl | rfl <;> omega
  · apply wf_seqs
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · exact wf_pushN _ _
    · exact wf_swap
    · rcases hX with rfl | rfl <;> decide
    · exact wf_pushN _ _
    · exact wf_swap

theorem low_put (d : ℕ) : maxUse (put d) < 16 ∧ (put d).WF = true := by
  have h1 := maxUse_pushN mR d
  have h2 : maxUse swap ≤ 15 := by decide
  constructor
  · simp only [put, maxUse_seqs, List.map, List.foldr]
    simp only [clear, maxUse]
    omega
  · apply wf_seqs
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact wf_pushN _ _
    · exact wf_swap
    · rfl

theorem low_getI : maxUse (getI mB) < 16 ∧ (getI mB).WF = true := by decide

end Factoring.Aux.Sim
