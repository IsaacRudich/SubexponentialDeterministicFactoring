/-
Adapted from the authors' related work (the whole file).

Not an audit surface.
-/
/-
PLIB, part 2: from a source program to a `Program` on the real input.

`PlibCore` compiles a source command to a `Program` that works on the memory
layout `Lay`.  This file supplies the two ends:

* the **prologue** `pro L`: from `startingMemory xs` to a memory holding the
  source state `St.init xs` -- array `0` is `startingMemory xs` itself (cell `0`
  the length, cell `1 + i` bit `i`), scalar `0` is the length, everything else
  zero.  The input overlaps every fixed register, so the prologue first branches
  on bits `0 … 3` (16 leaves, each knowing those bits as literals), uses the
  freed registers to move bits `4 …` up into array `0` from the top down, then
  writes the four literals and clears the stale cells;
* the **epilogues**: `copy 0 4` for a decision (register `0` gets scalar `0`),
  and `epiFn L out` for a function: array `out`, read in the input format
  (cell `0` the length, cell `1 + i` bit `i`), is copied down to registers
  `0 …` in the input format (`outOf`).

Main results: `wrapDec`, `run_wrapDec`, `steps_wrapDec_le`,
`runsInPolyTime_wrapDec`, `acceptedStrings_wrapDec`; `wrapFn`, `run_wrapFn`,
`outOf_wrapFn`, `runsInPolyTime_wrapFn`.

Not an audit surface.
-/
module

public import FactoringAux.Copied.PlibCore

@[expose] public section

namespace Factoring.Aux.Copied.PLib

open Factoring.Aux.Copied Factoring.Aux.Copied.Aux Lay

theorem cost_rep_decr (r k : ℕ) (σ : Memory) : (Program.run (rep k (.decr r)) σ).2 = 2 * k + 1 := by
  rw [run_rep_decr]

theorem cost_rep_incr (r k : ℕ) (σ : Memory) : (Program.run (rep k (.incr r)) σ).2 = 2 * k + 1 := by
  rw [run_rep_incr]

/-! ### Loops with a body of constant cost -/

theorem loopCost_const {body : Program} {c : ℕ} (hc : ∀ ρ, (Program.run body ρ).2 = c)
    (ctr : ℕ) (σ : Memory) : ∀ j, Aux.loopCost body ctr j σ = j * (c + 1) + 1
  | 0 => by simp [Aux.loopCost]
  | j + 1 => by
      show Aux.loopCost body ctr j σ + (Program.run body _).2 + 1 = _
      rw [loopCost_const hc ctr σ j, hc]; ring

theorem loopCost_le_const {body : Program} {c : ℕ} (hc : ∀ ρ, (Program.run body ρ).2 ≤ c)
    (ctr : ℕ) (σ : Memory) : ∀ j, Aux.loopCost body ctr j σ ≤ j * (c + 1) + 1
  | 0 => by simp [Aux.loopCost]
  | j + 1 => by
      show Aux.loopCost body ctr j σ + (Program.run body _).2 + 1 ≤ _
      have := loopCost_le_const hc ctr σ j
      have := hc ((loopMem body ctr j σ).set ctr j)
      rw [Nat.add_mul, Nat.one_mul]; omega

/-! ### Stage A: move bits `4 …` of the input into array `0` -/

section StageA

variable (L : Lay)

/-- One turn: read the bit at `4 + reg 0`, store it at `cell 0 0 + reg 1`, step
both down. -/
def stABody : Program :=
  seqs [.load 2 4 0, .store (L.cell 0 0) 1 2, .decr 0, rep L.na (.decr 1)]

/-- Stage A: `reg 4 := n`, `reg 1 := A n`, `reg 0 := n - 4`, then `n - 4` turns. -/
def stA : Program :=
  seqs [.copy 4 0, mulTo L.na 4, rep 4 (.decr 0), .loop 0 3 (stABody L)]

theorem cell_zero_ge (k : ℕ) (hnv : 1 ≤ L.nv) (hna : 1 ≤ L.na) : 5 + k ≤ L.cell 0 k := by
  unfold cell B
  have : k ≤ L.na * k := Nat.le_mul_of_pos_left k (by omega)
  omega

theorem cell_ge (a k : ℕ) (hnv : 1 ≤ L.nv) (hna : 1 ≤ L.na) : 5 + a + k ≤ L.cell a k := by
  unfold cell B
  have : k ≤ L.na * k := Nat.le_mul_of_pos_left k (by omega)
  omega

theorem run_stABody (ρ : Memory) :
    (Program.run (stABody L) ρ).1
      = (((ρ.set 2 (ρ (4 + ρ 0))).set (L.cell 0 0 + ρ 1) (ρ (4 + ρ 0))).set 0
          (ρ 0 - 1)).set 1 (ρ 1 - L.na) := by
  have h4 := L.four_le_cell 0 0
  simp only [stABody, run_seqs_mem, List.foldl, run_load_mem, run_store_mem, run_decr_mem,
    run_rep_decr, memory_set_apply]
  simp only [show (0 = L.cell 0 0 + ρ 1) = False by simp only [eq_iff_iff, iff_false]; omega,
    show (1 = L.cell 0 0 + ρ 1) = False by simp only [eq_iff_iff, iff_false]; omega,
    if_false, show ((1:ℕ) = 2) = False by decide, show ((0:ℕ) = 2) = False by decide]
  rfl

theorem cost_stABody (ρ : Memory) : (Program.run (stABody L) ρ).2 = 2 * L.na + 9 := by
  simp only [stABody, run_seqs_cost, seqsCost, cost_load, cost_store, cost_decr, run_rep_decr]
  omega

theorem stA_loop (hnv : 1 ≤ L.nv) (hna : 1 ≤ L.na) (τ : Memory)
    (hτ1 : τ 1 = L.na * (τ 0 + 4)) : ∀ j, j ≤ τ 0 →
    (loopMem (stABody L) 3 j τ) 0 = τ 0 - j ∧
    (loopMem (stABody L) 3 j τ) 1 = L.na * (τ 0 + 4 - j) ∧
    (∀ k, τ 0 + 4 - j < k → k ≤ τ 0 + 4 → (loopMem (stABody L) 3 j τ) (L.cell 0 k) = τ k) ∧
    (∀ p, 4 ≤ p → (∀ k, τ 0 + 4 - j < k → k ≤ τ 0 + 4 → p ≠ L.cell 0 k) →
      (loopMem (stABody L) 3 j τ) p = τ p) := by
  intro j
  induction j with
  | zero =>
      intro _
      refine ⟨rfl, by show τ 1 = _; rw [hτ1]; rfl, fun k h1 h2 => by omega, fun p _ _ => rfl⟩
  | succ j ih =>
      intro hj
      obtain ⟨e0, e1, eW, eF⟩ := ih (by omega)
      set Lj := loopMem (stABody L) 3 j τ with hLj
      have hstep : loopMem (stABody L) 3 (j + 1) τ = (Program.run (stABody L) (Lj.set 3 j)).1 := rfl
      rw [hstep, run_stABody]
      have r0 : (Lj.set 3 j) 0 = τ 0 - j := by rw [memory_set_apply, if_neg (by omega), e0]
      have r1 : (Lj.set 3 j) 1 = L.na * (τ 0 + 4 - j) := by
        rw [memory_set_apply, if_neg (by omega), e1]
      have hk : 4 + (τ 0 - j) = τ 0 + 4 - j := by omega
      have rv : (Lj.set 3 j) (4 + (τ 0 - j)) = τ (τ 0 + 4 - j) := by
        rw [hk, memory_set_apply, if_neg (by omega)]
        refine eF _ (by omega) (fun k hk1 _ e => ?_)
        have := cell_zero_ge L k hnv hna
        omega
      rw [r0, r1, rv, cell_add]
      simp only [Nat.zero_add]
      have hc4 := L.four_le_cell 0 (τ 0 + 4 - j)
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp [memory_set_apply]; omega
      · simp only [memory_set_apply, if_true]
        rw [show τ 0 + 4 - (j + 1) = τ 0 + 4 - j - 1 by omega, Nat.mul_sub_one]
      · intro k hk1 hk2
        have hc := L.four_le_cell 0 k
        simp only [memory_set_apply]
        rw [if_neg (by omega), if_neg (by omega)]
        by_cases hkk : k = τ 0 + 4 - j
        · subst hkk; rw [if_pos rfl]
        · rw [if_neg (fun e => hkk (L.cell_inj (by omega) (by omega) e).2), if_neg (by omega)]
          rw [if_neg (by omega)]
          exact eW k (by omega) hk2
      · intro p hp hpk
        simp only [memory_set_apply]
        rw [if_neg (by omega), if_neg (by omega),
          if_neg (hpk (τ 0 + 4 - j) (by omega) (by omega)), if_neg (by omega),
          if_neg (by omega)]
        exact eF p hp (fun k h1 h2 => hpk k (by omega) h2)

/-- **Stage A.**  From any `σ` with `σ 0 = n`: register `4` holds `n`, cells
`5 … n` of array `0` hold `σ 5 … σ n`, and every register from `5` on that is
not one of those cells is untouched. -/
theorem run_stA (hnv : 1 ≤ L.nv) (hna : 1 ≤ L.na) (σ : Memory) :
    (Program.run (stA L) σ).1 4 = σ 0 ∧
    (∀ k, 5 ≤ k → k ≤ σ 0 → (Program.run (stA L) σ).1 (L.cell 0 k) = σ k) ∧
    (∀ p, 5 ≤ p → (∀ k, 5 ≤ k → k ≤ σ 0 → p ≠ L.cell 0 k) → (Program.run (stA L) σ).1 p = σ p) ∧
    (Program.run (stA L) σ).2 ≤ σ 0 * (4 * L.na + 12) + 20 := by
  set n := σ 0 with hn
  set σ1 := σ.set 4 n with hσ1
  set σ2 := (Program.run (mulTo L.na 4) σ1).1 with hσ2
  have h21 : σ2 1 = L.na * n := by
    rw [hσ2, mulTo_one (by omega)]; simp [σ1, memory_set_apply]
  have h2p : ∀ p, p ≠ 1 → p ≠ 3 → σ2 p = σ1 p := fun p h1 h3 => mulTo_frame (by omega) σ1 h1 h3
  have h20 : σ2 0 = n := by rw [h2p 0 (by omega) (by omega)]; simp [σ1, memory_set_apply, n]
  set τ := σ2.set 0 (n - 4) with hτ
  have hmem : (Program.run (stA L) σ).1 = loopMem (stABody L) 3 (n - 4) τ := by
    simp only [stA, run_seqs_mem, List.foldl, run_copy_mem, run_rep_decr, run_loop_mem]
    rw [← hσ1, ← hσ2, h20]
    simp [τ, memory_set_apply]
  have hcost : (Program.run (stA L) σ).2
      = 1 + (σ2 0 * (2 * L.na + 2) + 3) + 9 + Aux.loopCost (stABody L) 3 (n - 4) τ + 5 := by
    simp only [stA, run_seqs_cost, seqsCost, cost_copy, run_copy_mem, run_rep_decr, cost_loop,
      cost_skip]
    rw [← hσ1, cost_mulTo (by omega), ← hσ2, h20]
    simp only [memory_set_apply, if_true]
    rw [show σ1 4 = n by simp [σ1, memory_set_apply]]
    simp [τ, memory_set_apply]
    omega
  have hτk : ∀ k, 5 ≤ k → τ k = σ k := by
    intro k hk
    rw [hτ, memory_set_apply, if_neg (by omega), h2p k (by omega) (by omega)]
    simp [σ1, memory_set_apply]; omega
  have hτ4 : τ 4 = n := by
    rw [hτ, memory_set_apply, if_neg (by omega), h2p 4 (by omega) (by omega)]
    simp [σ1, memory_set_apply]
  rw [hcost, loopCost_const (cost_stABody L), h20, hmem]
  by_cases h4 : 4 ≤ n
  · have hτ0 : τ 0 = n - 4 := by simp [τ, memory_set_apply]
    have hτ1 : τ 1 = L.na * (τ 0 + 4) := by
      rw [hτ0, show n - 4 + 4 = n by omega, hτ, memory_set_apply, if_neg (by omega), h21]
    obtain ⟨-, -, eW, eF⟩ := stA_loop L hnv hna τ hτ1 (n - 4) (by omega)
    rw [hτ0, show n - 4 + 4 - (n - 4) = 4 by omega, show n - 4 + 4 = n by omega] at eW eF
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [eF 4 (le_refl _) (fun k _ _ e => by have := cell_zero_ge L k hnv hna; omega), hτ4]
    · intro k hk hkn; rw [eW k (by omega) hkn, hτk k hk]
    · intro p hp hpk
      rw [eF p (by omega) (fun k hk1 hk2 => hpk k (by omega) hk2), hτk p hp]
    · have : (n - 4) * (2 * L.na + 9 + 1) ≤ n * (2 * L.na + 10) := Nat.mul_le_mul_right _ (by omega)
      nlinarith
  · have hn4 : n - 4 = 0 := by omega
    rw [hn4]
    refine ⟨hτ4, fun k hk hkn => by omega, fun p hp _ => hτk p hp, ?_⟩
    nlinarith

end StageA

/-! ### Stage B: the four literal bits -/

section StageB

variable (L : Lay)

/-- Write `ls[q]` to cell `1 + q` of array `0`, for `q < k`. -/
def stB (ls : List ℕ) : ℕ → Program
  | 0 => .skip
  | q + 1 => .seq (stB ls q) (seqs [.zero 1, Aux.setK 2 (ls.getD q 0), .store (L.cell 0 (1 + q)) 1 2])

theorem run_stB (hna : 1 ≤ L.na) (ls : List ℕ) (hls : ∀ q, ls.getD q 0 ≤ 1) (σ : Memory) :
    ∀ k, (∀ q, q < k → (Program.run (stB L ls k) σ).1 (L.cell 0 (1 + q)) = ls.getD q 0) ∧
      (∀ p, 4 ≤ p → (∀ q, q < k → p ≠ L.cell 0 (1 + q)) → (Program.run (stB L ls k) σ).1 p = σ p) ∧
      (Program.run (stB L ls k) σ).2 ≤ 12 * k + 1 := by
  intro k
  induction k with
  | zero => exact ⟨fun q hq => by omega, fun p _ _ => rfl, by simp [stB, cost_skip]⟩
  | succ k ih =>
      obtain ⟨iW, iF, iC⟩ := ih
      set μ := (Program.run (stB L ls k) σ).1
      have hmem : (Program.run (stB L ls (k + 1)) σ).1
          = ((μ.set 1 0).set 2 (ls.getD k 0)).set (L.cell 0 (1 + k)) (ls.getD k 0) := by
        simp only [stB, run_seq_mem, run_seqs_mem, List.foldl, run_zero_mem, run_setK_mem,
          run_store_mem, memory_set_apply]
        simp [μ]
      have hcost : (Program.run (stB L ls (k + 1)) σ).2
          = (Program.run (stB L ls k) σ).2 + (2 * ls.getD k 0 + 3) + 7 := by
        simp only [stB, cost_seq, run_seqs_cost, seqsCost, cost_zero, cost_setK, cost_store,
          cost_skip]
        omega
      rw [hmem, hcost]
      refine ⟨fun q hq => ?_, fun p hp hpq => ?_, by have := hls k; omega⟩
      · simp only [memory_set_apply, cell_ne_one, cell_ne_two, if_false]
        by_cases hqk : q = k
        · subst hqk; simp
        · rw [if_neg (fun e => hqk (by have := (L.cell_inj (by omega) (by omega) e).2; omega))]
          exact iW q (by omega)
      · simp only [memory_set_apply]
        rw [if_neg (hpq k (by omega)), if_neg (by omega), if_neg (by omega)]
        exact iF p hp (fun q hq => hpq q (by omega))

end StageB

/-! ### Stage C: cell `0` of array `0`, and the other scalars -/

section StageC

variable (L : Lay)

/-- `reg (5 + x) := 0` for `x < k`. -/
def zeroRegs : ℕ → Program
  | 0 => .skip
  | k + 1 => .seq (zeroRegs k) (.zero (5 + k))

theorem run_zeroRegs (σ : Memory) : ∀ k,
    (∀ p, (Program.run (zeroRegs k) σ).1 p = if 5 ≤ p ∧ p < 5 + k then 0 else σ p) ∧
    (Program.run (zeroRegs k) σ).2 = 2 * k + 1
  | 0 => ⟨fun p => by simp [zeroRegs, run_skip_mem], rfl⟩
  | k + 1 => by
      obtain ⟨h1, h2⟩ := run_zeroRegs σ k
      refine ⟨fun p => ?_, ?_⟩
      · simp only [zeroRegs, run_seq_mem, run_zero_mem, memory_set_apply, h1]
        split_ifs <;> omega
      · simp only [zeroRegs, cost_seq, cost_zero, h2]; ring

/-- Stage C: cell `0` of array `0` gets register `4`; scalars `1 …` are zeroed. -/
def stC : Program := seqs [.zero 1, .store (L.cell 0 0) 1 4, zeroRegs (L.nv - 1)]

theorem run_stC (hnv : 1 ≤ L.nv) (σ : Memory) :
    (Program.run (stC L) σ).1 (L.cell 0 0) = σ 4 ∧
    (∀ x, 1 ≤ x → x < L.nv → (Program.run (stC L) σ).1 (4 + x) = 0) ∧
    (∀ p, 4 ≤ p → p ≠ L.cell 0 0 → (p < 5 ∨ 4 + L.nv ≤ p) → (Program.run (stC L) σ).1 p = σ p) ∧
    (Program.run (stC L) σ).2 = 2 * L.nv + 5 := by
  have hc := L.sreg_lt_cell (show L.nv - 1 < L.nv by omega) 0 0
  have hmem : ∀ p, (Program.run (stC L) σ).1 p
      = if 5 ≤ p ∧ p < 5 + (L.nv - 1) then 0 else ((σ.set 1 0).set (L.cell 0 0) (σ 4)) p := by
    intro p
    simp only [stC, run_seqs_mem, List.foldl, run_zero_mem, run_store_mem]
    rw [(run_zeroRegs _ _).1]
    simp [memory_set_apply]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hmem, if_neg (by omega)]; simp [memory_set_apply]
  · intro x h1 h2; rw [hmem, if_pos (by omega)]
  · intro p hp hpc hr
    rw [hmem, if_neg (by omega)]
    simp only [memory_set_apply]; rw [if_neg hpc, if_neg (by omega)]
  · simp only [stC, run_seqs_cost, seqsCost, cost_zero, cost_store, (run_zeroRegs _ _).2]
    omega

end StageC

/-! ### Stage D: clear the stale cells of arrays `1 …` -/

section StageD

variable (L : Lay)

/-- `cell a 0 + reg 1 := reg 2` for `a = 1 … k`. -/
def clrStores : ℕ → Program
  | 0 => .skip
  | k + 1 => .seq (clrStores k) (.store (L.cell (k + 1) 0) 1 2)

theorem run_clrStores (ρ : Memory) : ∀ k,
    (∀ a, 1 ≤ a → a ≤ k → (Program.run (clrStores L k) ρ).1 (L.cell a 0 + ρ 1) = ρ 2) ∧
    (∀ p, (∀ a, 1 ≤ a → a ≤ k → p ≠ L.cell a 0 + ρ 1) → (Program.run (clrStores L k) ρ).1 p = ρ p) ∧
    (Program.run (clrStores L k) ρ).2 = 2 * k + 1
  | 0 => ⟨fun a h1 h2 => by omega, fun p _ => rfl, rfl⟩
  | k + 1 => by
      obtain ⟨iW, iF, iC⟩ := run_clrStores ρ k
      set μ := (Program.run (clrStores L k) ρ).1
      have h1 : μ 1 = ρ 1 := iF 1 (fun a _ _ => by have := L.four_le_cell a 0; omega)
      have h2 : μ 2 = ρ 2 := iF 2 (fun a _ _ => by have := L.four_le_cell a 0; omega)
      have hmem : (Program.run (clrStores L (k + 1)) ρ).1 = μ.set (L.cell (k + 1) 0 + ρ 1) (ρ 2) := by
        change μ.set (L.cell (k + 1) 0 + μ 1) (μ 2) = _
        rw [h1, h2]
      rw [hmem]
      refine ⟨fun a ha1 ha2 => ?_, fun p hp => ?_, ?_⟩
      · rw [memory_set_apply]
        by_cases hak : a = k + 1
        · subst hak; rw [if_pos rfl]
        · rw [if_neg (by unfold cell; omega)]; exact iW a ha1 (by omega)
      · rw [memory_set_apply, if_neg (hp (k + 1) (by omega) le_rfl)]
        exact iF p (fun a h1 h2 => hp a h1 (by omega))
      · simp only [clrStores, cost_seq, cost_store, iC]; ring

/-- One turn of the clearing loop. -/
def clrBody : Program := .seq (clrStores L (L.na - 1)) (rep L.na (.incr 1))

/-- Stage D: for `i < reg 4`, zero cell `i` of every array `1 … A-1`. -/
def stD : Program := seqs [.zero 1, .zero 2, .loop 4 3 (clrBody L)]

theorem cost_clrBody (hna : 1 ≤ L.na) (ρ : Memory) : (Program.run (clrBody L) ρ).2 = 4 * L.na + 1 := by
  simp only [clrBody, cost_seq, (run_clrStores L ρ _).2.2, run_rep_incr]
  omega

theorem run_stD (hna : 1 ≤ L.na) (σ : Memory) :
    (∀ a i, 1 ≤ a → a < L.na → i < σ 4 → (Program.run (stD L) σ).1 (L.cell a i) = 0) ∧
    (∀ p, 4 ≤ p → (∀ a i, 1 ≤ a → a < L.na → i < σ 4 → p ≠ L.cell a i) →
      (Program.run (stD L) σ).1 p = σ p) ∧
    (Program.run (stD L) σ).2 = σ 4 * (4 * L.na + 2) + 7 := by
  set τ := (σ.set 1 0).set 2 0 with hτ
  have hτ4 : τ 4 = σ 4 := by simp [τ, memory_set_apply]
  have key : ∀ j, (loopMem (clrBody L) 3 j τ) 1 = L.na * j ∧ (loopMem (clrBody L) 3 j τ) 2 = 0 ∧
      (∀ a i, 1 ≤ a → a < L.na → i < j → (loopMem (clrBody L) 3 j τ) (L.cell a i) = 0) ∧
      (∀ p, 4 ≤ p → (∀ a i, 1 ≤ a → a < L.na → i < j → p ≠ L.cell a i) →
        (loopMem (clrBody L) 3 j τ) p = τ p) := by
    intro j
    induction j with
    | zero => exact ⟨by show τ 1 = 0; simp [τ, memory_set_apply],
        by show τ 2 = 0; simp [τ, memory_set_apply],
        fun a i _ _ hi => by omega, fun p _ _ => rfl⟩
    | succ j ih =>
        obtain ⟨e1, e2, eW, eF⟩ := ih
        set Lj := loopMem (clrBody L) 3 j τ
        set ρ := Lj.set 3 j
        have r1 : ρ 1 = L.na * j := by simp [ρ, memory_set_apply, e1]
        have r2 : ρ 2 = 0 := by simp [ρ, memory_set_apply, e2]
        obtain ⟨cW, cF, -⟩ := run_clrStores L ρ (L.na - 1)
        set μ := (Program.run (clrStores L (L.na - 1)) ρ).1
        have hstep : loopMem (clrBody L) 3 (j + 1) τ = μ.set 1 (μ 1 + L.na) := by
          show (Program.run (clrBody L) ρ).1 = _
          simp only [clrBody, run_seq_mem, run_rep_incr]
          rfl
        have m1 : μ 1 = ρ 1 := cF 1 (fun a _ _ => by have := L.four_le_cell a 0; omega)
        have m2 : μ 2 = ρ 2 := cF 2 (fun a _ _ => by have := L.four_le_cell a 0; omega)
        rw [hstep]
        refine ⟨by rw [memory_set_get, m1, r1]; ring, by rw [memory_set_apply, if_neg (by omega), m2, r2],
          fun a i ha1 ha2 hi => ?_, fun p hp hpa => ?_⟩
        · rw [memory_set_apply, if_neg (by have := L.four_le_cell a i; omega)]
          by_cases hij : i = j
          · subst hij
            have := cW a ha1 (by omega)
            rw [r1, cell_add, Nat.zero_add, r2] at this
            exact this
          · rw [cF _ (fun a' _ _ e => by
                rw [r1, cell_add, Nat.zero_add] at e
                exact hij (L.cell_inj (by omega) (by omega) e).2)]
            rw [show ρ (L.cell a i) = Lj (L.cell a i) by
              simp [ρ, memory_set_apply]]
            exact eW a i ha1 ha2 (by omega)
        · rw [memory_set_apply, if_neg (by omega)]
          rw [cF _ (fun a' h1 h2 e => by
              rw [r1, cell_add, Nat.zero_add] at e
              exact hpa a' j h1 (by omega) (by omega) e)]
          rw [show ρ p = Lj p by simp [ρ, memory_set_apply]; omega]
          exact eF p hp (fun a i h1 h2 h3 => hpa a i h1 h2 (by omega))
  have hmem : (Program.run (stD L) σ).1 = loopMem (clrBody L) 3 (σ 4) τ := by
    simp only [stD, run_seqs_mem, List.foldl, run_zero_mem, run_loop_mem]
    rw [← hτ, hτ4]
  obtain ⟨-, -, kW, kF⟩ := key (σ 4)
  refine ⟨fun a i h1 h2 h3 => by rw [hmem]; exact kW a i h1 h2 h3, fun p hp hpa => ?_, ?_⟩
  · rw [hmem, kF p hp hpa]; simp only [τ, memory_set_apply]; rw [if_neg (by omega), if_neg (by omega)]
  · simp only [stD, run_seqs_cost, seqsCost, cost_zero, cost_loop, run_zero_mem]
    rw [← hτ, hτ4, loopCost_const (cost_clrBody L hna)]
    ring

end StageD

/-! ### The prologue -/

/-- The source state a run starts from: array `0` is the input's own starting
memory (cell `0` the length, cell `1 + i` bit `i` as `0`/`1`), scalar `0` is the
length, everything else is zero. -/
def St.init (xs : List Bool) : St :=
  ⟨fun x => if x = 0 then xs.length else 0, fun a => if a = 0 then startingMemory xs else fun _ => 0⟩

@[simp] theorem St.init_sc_zero (xs : List Bool) : (St.init xs).sc 0 = xs.length := rfl
@[simp] theorem St.init_ar_zero (xs : List Bool) : (St.init xs).ar 0 = startingMemory xs := rfl

theorem startingMemory_zero_eq (xs : List Bool) : startingMemory xs 0 = xs.length := rfl

theorem startingMemory_gt (xs : List Bool) {p : ℕ} (hp : xs.length < p) : startingMemory xs p = 0 := by
  simp only [startingMemory, if_neg (show p ≠ 0 by omega)]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
  rfl

theorem startingMemory_le_one (xs : List Bool) {p : ℕ} (hp : p ≠ 0) : startingMemory xs p ≤ 1 := by
  simp only [startingMemory, if_neg hp]; split <;> omega

theorem startingMemory_le (xs : List Bool) (p : ℕ) : startingMemory xs p ≤ xs.length ∨ p ≠ 0 ∧
    startingMemory xs p ≤ 1 := by
  by_cases hp : p = 0
  · left; subst hp; exact le_refl _
  · right; exact ⟨hp, startingMemory_le_one xs hp⟩

section Prologue

variable (L : Lay)

/-- A leaf of the prologue, knowing bits `0 … 3` as the literals `ls`. -/
def proLeaf (ls : List ℕ) : Program := seqs [stA L, stB L ls 4, stC L, stD L]

/-- The prologue's constant. -/
def preK : ℕ := 8 * L.na + 2 * L.nv + 100

theorem run_proLeaf (hnv : 1 ≤ L.nv) (hna : 1 ≤ L.na) (xs : List Bool) (ls : List ℕ)
    (hls : ∀ q, q < 4 → ls.getD q 0 = startingMemory xs (1 + q)) (hls1 : ∀ q, ls.getD q 0 ≤ 1) :
    L.Rel (St.init xs) (Program.run (proLeaf L ls) (startingMemory xs)).1 ∧
    (Program.run (proLeaf L ls) (startingMemory xs)).2 ≤ preK L * (xs.length + 1) := by
  set σ := startingMemory xs with hσ
  set n := xs.length with hn
  have hσ0 : σ 0 = n := rfl
  have hmem : (Program.run (proLeaf L ls) σ).1 = (Program.run (stD L) (Program.run (stC L)
      (Program.run (stB L ls 4) (Program.run (stA L) σ).1).1).1).1 := by
    simp only [proLeaf, run_seqs_mem, List.foldl]
  have hcost : (Program.run (proLeaf L ls) σ).2
      = (Program.run (stA L) σ).2 + (Program.run (stB L ls 4) (Program.run (stA L) σ).1).2
        + (Program.run (stC L) (Program.run (stB L ls 4) (Program.run (stA L) σ).1).1).2
        + (Program.run (stD L) (Program.run (stC L) (Program.run (stB L ls 4)
            (Program.run (stA L) σ).1).1).1).2 + 5 := by
    simp only [proLeaf, run_seqs_cost, seqsCost, cost_skip]; omega
  obtain ⟨a4, aW, aF, aC⟩ := run_stA L hnv hna σ
  set MA := (Program.run (stA L) σ).1
  obtain ⟨bW, bF, bC⟩ := run_stB L hna ls hls1 MA 4
  set MB := (Program.run (stB L ls 4) MA).1
  obtain ⟨c0, cX, cF, cC⟩ := run_stC L hnv MB
  set MC := (Program.run (stC L) MB).1
  obtain ⟨dW, dF, dC⟩ := run_stD L hna MC
  set MD := (Program.run (stD L) MC).1
  -- cells are at least 5, so registers 4 and the scalars are never cells
  have cge : ∀ a i, 4 + L.nv ≤ L.cell a i := fun a i => by unfold cell B; omega
  have hB4 : MB 4 = n := by
    rw [bF 4 le_rfl (fun q _ e => by have := cge 0 (1 + q); omega), a4, hσ0]
  have hC4 : MC 4 = n := by
    rw [cF 4 le_rfl (fun e => by have := cge 0 0; omega) (Or.inl (by omega)), hB4]
  rw [hmem]
  refine ⟨⟨fun x hx => ?_, fun a ha i => ?_⟩, ?_⟩
  · -- scalars
    have hnc : ∀ a i, 1 ≤ a → a < L.na → i < MC 4 → 4 + x ≠ L.cell a i :=
      fun a i _ _ _ e => by have := cge a i; omega
    rw [dF _ (by omega) hnc]
    by_cases hx0 : x = 0
    · subst hx0; simp only [St.init, if_true, Nat.add_zero]; exact hC4
    · simp only [St.init, if_neg hx0]; exact cX x (by omega) hx
  · by_cases ha0 : a = 0
    · subst ha0
      simp only [St.init_ar_zero]
      have hD : MD (L.cell 0 i) = MC (L.cell 0 i) :=
        dF _ (L.four_le_cell 0 i) (fun a' i' h1 _ _ e => by
          have := (L.cell_inj (by omega) (by omega) e).1; omega)
      rw [hD]
      rcases Nat.lt_or_ge i 5 with hi | hi
      · by_cases hi0 : i = 0
        · subst hi0; rw [c0, hB4]; exact (startingMemory_zero_eq xs).symm
        · rw [cF _ (L.four_le_cell 0 i) (fun e => hi0 (L.cell_inj (by omega) (by omega) e).2)
            (Or.inr (cge 0 i))]
          have := bW (i - 1) (by omega)
          rw [show 1 + (i - 1) = i by omega] at this
          rw [this, hls (i - 1) (by omega), show 1 + (i - 1) = i by omega]
      · rw [cF _ (L.four_le_cell 0 i) (fun e => by have := (L.cell_inj (by omega) (by omega) e).2; omega)
            (Or.inr (cge 0 i)),
          bF _ (L.four_le_cell 0 i) (fun q hq e => by
            have := (L.cell_inj (by omega) (by omega) e).2; omega)]
        by_cases hin : i ≤ n
        · exact aW i hi hin
        · rw [aF _ (by have := cell_zero_ge L i hnv hna; omega) (fun k _ hk e => by
              have := (L.cell_inj (by omega) (by omega) e).2; omega)]
          exact (startingMemory_gt xs (by have := cell_zero_ge L i hnv hna; omega)).trans
            (startingMemory_gt xs (by omega)).symm
    · simp only [St.init, if_neg ha0]
      by_cases hin : i < n
      · exact dW a i (by omega) ha (by rw [hC4]; exact hin)
      · have hbig : n < L.cell a i := by have := cell_ge L a i hnv hna; omega
        rw [dF _ (L.four_le_cell a i) (fun a' i' _ _ hi' e => by
              have := L.cell_inj ha (by omega) e; rw [hC4] at hi'; omega),
          cF _ (L.four_le_cell a i) (fun e => ha0 (L.cell_inj ha (by omega) e).1)
            (Or.inr (cge a i)),
          bF _ (L.four_le_cell a i) (fun q _ e => ha0 (L.cell_inj ha (by omega) e).1),
          aF _ (by have := cell_ge L a i hnv hna; omega) (fun k _ _ e =>
            ha0 (L.cell_inj ha (by omega) e).1)]
        exact startingMemory_gt xs hbig
  · rw [hcost, cC, dC, hC4]
    rw [hσ0] at aC
    unfold preK
    nlinarith

/-- The decision tree on bits `0 … k-1`; each leaf knows them as literals. -/
def proTree : ℕ → List ℕ → Program
  | 0, ls => proLeaf L ls
  | k + 1, ls => .ifZero (k + 1) (proTree k (0 :: ls)) (proTree k (1 :: ls))

/-- **The prologue.** -/
def pro : Program := proTree L 4 []

theorem run_proTree (σ : Memory) : ∀ k (ls : List ℕ), (∀ q, q < k → σ (1 + q) ≤ 1) →
    (Program.run (proTree L k ls) σ).1
      = (Program.run (proLeaf L (((List.range k).map (fun q => σ (1 + q))) ++ ls)) σ).1 ∧
    (Program.run (proTree L k ls) σ).2
      = (Program.run (proLeaf L (((List.range k).map (fun q => σ (1 + q))) ++ ls)) σ).2 + k
  | 0, ls, _ => by simp [proTree]
  | k + 1, ls, h => by
      have hk := h k (by omega)
      have e : (List.range (k + 1)).map (fun q => σ (1 + q)) ++ ls
          = (List.range k).map (fun q => σ (1 + q)) ++ (σ (k + 1) :: ls) := by
        rw [List.range_succ, List.map_append, List.append_assoc]
        simp [Nat.add_comm]
      rw [e]
      simp only [proTree, run_ifZero_mem, cost_ifZero]
      by_cases h0 : σ (k + 1) = 0
      · rw [if_pos h0, if_pos h0, h0]
        obtain ⟨r1, r2⟩ := run_proTree σ k (0 :: ls) (fun q hq => h q (by omega))
        exact ⟨r1, by rw [r2]; ring⟩
      · rw [if_neg h0, if_neg h0, show σ (k + 1) = 1 by rw [Nat.add_comm] at hk; omega]
        obtain ⟨r1, r2⟩ := run_proTree σ k (1 :: ls) (fun q hq => h q (by omega))
        exact ⟨r1, by rw [r2]; ring⟩

/-- **The prologue is correct**: from `startingMemory xs` it reaches a memory
holding `St.init xs`, in at most `preK L * (n + 1) + 4` steps. -/
theorem run_pro (hnv : 1 ≤ L.nv) (hna : 1 ≤ L.na) (xs : List Bool) :
    L.Rel (St.init xs) (Program.run (pro L) (startingMemory xs)).1 ∧
    (Program.run (pro L) (startingMemory xs)).2 ≤ preK L * (xs.length + 1) + 4 := by
  have hb : ∀ q, q < 4 → startingMemory xs (1 + q) ≤ 1 :=
    fun q _ => startingMemory_le_one xs (by omega)
  obtain ⟨r1, r2⟩ := run_proTree L (startingMemory xs) 4 [] hb
  set ls := (List.range 4).map (fun q => startingMemory xs (1 + q)) ++ []
  have hls : ∀ q, q < 4 → ls.getD q 0 = startingMemory xs (1 + q) := by
    intro q hq
    simp only [ls, List.append_nil, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range hq]
    rfl
  have hls1 : ∀ q, ls.getD q 0 ≤ 1 := by
    intro q
    by_cases hq : q < 4
    · rw [hls q hq]; exact hb q hq
    · simp only [ls, List.append_nil, List.getD_eq_getElem?_getD, List.getElem?_map]
      rw [List.getElem?_eq_none (by simp; omega)]; simp
  obtain ⟨h1, h2⟩ := run_proLeaf L hnv hna xs ls hls hls1
  exact ⟨by rw [pro, r1]; exact h1, by rw [pro, r2]; omega⟩

end Prologue

/-! ### The function epilogue -/

section Epilogue

variable (L : Lay) (out : ℕ)

/-- Save cell `q` of array `out` at cell `len + 1 + q`, for `q = k-1` down to `0`
(`reg 1 = A * len`). -/
def saveLow : ℕ → Program
  | 0 => .skip
  | k + 1 => .seq (seqs [.zero 0, .load 2 (L.cell out k) 0, .store (L.cell out (1 + k)) 1 2])
      (saveLow k)

/-- One turn of the copy-down loop. -/
def epiBody : Program := seqs [.load 3 (L.cell out 0) 1, .store 0 0 3, .incr 0, rep L.na (.incr 1)]

/-- **The function epilogue**: array `out` copied down to registers `0 … len`. -/
def epiFn : Program :=
  seqs [.zero 1, .load 4 (L.cell out 0) 1, mulTo L.na 4, saveLow L out 5, .copy 3 4, rep 4 (.decr 3),
    Aux.setK 0 5, Aux.setK 1 (5 * L.na), .loop 3 2 (epiBody L out), mulTo L.na 4,
    .load 0 (L.cell out 1) 1, .load 2 (L.cell out 3) 1, .load 3 (L.cell out 4) 1,
    .load 4 (L.cell out 5) 1, .load 1 (L.cell out 2) 1]

theorem run_saveLow (hout : out < L.na) (ρ : Memory) (len : ℕ) (h1 : ρ 1 = L.na * len) : ∀ k,
    (∀ q, q < k → (Program.run (saveLow L out k) ρ).1 (L.cell out (len + 1 + q)) = ρ (L.cell out q)) ∧
    (∀ p, 4 ≤ p → (∀ q, q < k → p ≠ L.cell out (len + 1 + q)) →
      (Program.run (saveLow L out k) ρ).1 p = ρ p) ∧
    (Program.run (saveLow L out k) ρ).1 1 = ρ 1 ∧
    (Program.run (saveLow L out k) ρ).2 = 8 * k + 1
  | 0 => ⟨fun q hq => by omega, fun p _ _ => rfl, rfl, rfl⟩
  | k + 1 => by
      set ρ' := ((ρ.set 0 0).set 2 (ρ (L.cell out k))).set (L.cell out (len + 1 + k)) (ρ (L.cell out k))
        with hρ'
      have hblk : (Program.run (seqs [.zero 0, .load 2 (L.cell out k) 0,
          .store (L.cell out (1 + k)) 1 2]) ρ).1 = ρ' := by
        simp only [run_seqs_mem, List.foldl, run_zero_mem, run_load_mem,
          run_store_mem, memory_set_apply]
        simp only [if_true, cell_ne_zero, if_false, show ((1:ℕ) = 2) = False by decide,
          show ((1:ℕ) = 0) = False by decide, Nat.add_zero, h1]
        rw [cell_add, show 1 + k + len = len + 1 + k by ring]
      have hstep : (Program.run (saveLow L out (k + 1)) ρ).1 = (Program.run (saveLow L out k) ρ').1 := by
        simp only [saveLow, run_seq_mem]; rw [hblk]
      have hρ'1 : ρ' 1 = L.na * len := by
        simp only [ρ', memory_set_apply]
        rw [if_neg (by have := L.four_le_cell out (len + 1 + k); omega), if_neg (by omega),
          if_neg (by omega), h1]
      obtain ⟨iW, iF, i1, iC⟩ := run_saveLow hout ρ' len hρ'1 k
      rw [hstep]
      refine ⟨fun q hq => ?_, fun p hp hpq => ?_, by rw [i1, hρ'1, h1], ?_⟩
      · by_cases hqk : q = k
        · subst hqk
          rw [iF _ (L.four_le_cell _ _) (fun q' hq' e => by
            have := (L.cell_inj hout hout e).2; omega)]
          simp [ρ', memory_set_apply]
        · rw [iW q (by omega)]
          simp only [ρ', memory_set_apply, cell_ne_zero, cell_ne_two, if_false]
          rw [if_neg (fun e => by have := (L.cell_inj hout hout e).2; omega)]
      · rw [iF p hp (fun q hq => hpq q (by omega))]
        simp only [ρ', memory_set_apply]
        rw [if_neg (hpq k (by omega)), if_neg (by omega), if_neg (by omega)]
      · simp only [saveLow, cost_seq]
        rw [hblk, iC]
        simp only [run_seqs_cost, seqsCost, cost_zero, cost_load, cost_store, cost_skip]
        ring

theorem run_epiBody (ρ : Memory) (h0 : 5 ≤ ρ 0) :
    (Program.run (epiBody L out) ρ).1
      = ((((ρ.set 3 (ρ (L.cell out 0 + ρ 1))).set (ρ 0) (ρ (L.cell out 0 + ρ 1))).set 0 (ρ 0 + 1)).set 1
          (ρ 1 + L.na)) := by
  simp only [epiBody, run_seqs_mem, List.foldl, run_load_mem, run_store_mem, run_incr_mem',
    run_rep_incr, memory_set_apply]
  simp only [show ((0:ℕ) = 3) = False by decide, if_false, Nat.zero_add,
    show (0 = ρ 0) = False by simp only [eq_iff_iff, iff_false]; omega,
    show (1 = ρ 0) = False by simp only [eq_iff_iff, iff_false]; omega,
    show ((1:ℕ) = 0) = False by decide, show ((1:ℕ) = 3) = False by decide, if_true]

theorem cost_epiBody (ρ : Memory) : (Program.run (epiBody L out) ρ).2 = 2 * L.na + 9 := by
  simp only [epiBody, run_seqs_cost, seqsCost, cost_load, cost_store, cost_incr, run_rep_incr]
  omega

theorem epi_loop (hnv : 1 ≤ L.nv) (hna : 1 ≤ L.na) (τ : Memory) (h0 : τ 0 = 5) (h1 : τ 1 = L.na * 5) : ∀ t,
    (loopMem (epiBody L out) 2 t τ) 0 = 5 + t ∧ (loopMem (epiBody L out) 2 t τ) 1 = L.na * (5 + t) ∧
    (∀ j, 5 ≤ j → j < 5 + t → (loopMem (epiBody L out) 2 t τ) j = τ (L.cell out j)) ∧
    (∀ p, 4 ≤ p → (p < 5 ∨ 5 + t ≤ p) → (loopMem (epiBody L out) 2 t τ) p = τ p) := by
  intro t
  induction t with
  | zero => exact ⟨h0, by show τ 1 = _; rw [h1], fun j h1 h2 => by omega, fun p _ _ => rfl⟩
  | succ t ih =>
      obtain ⟨e0, e1, eW, eF⟩ := ih
      set Lt := loopMem (epiBody L out) 2 t τ
      have hstep : loopMem (epiBody L out) 2 (t + 1) τ = (Program.run (epiBody L out) (Lt.set 2 t)).1 :=
        rfl
      have r0 : (Lt.set 2 t) 0 = 5 + t := by rw [memory_set_apply, if_neg (by omega), e0]
      have r1 : (Lt.set 2 t) 1 = L.na * (5 + t) := by rw [memory_set_apply, if_neg (by omega), e1]
      have hcg : 5 + (5 + t) ≤ L.cell out (5 + t) := by
        have := Nat.le_mul_of_pos_left (5 + t) hna; unfold cell B; omega
      have rv : (Lt.set 2 t) (L.cell out 0 + L.na * (5 + t)) = τ (L.cell out (5 + t)) := by
        rw [cell_add, Nat.zero_add, memory_set_apply, if_neg (by omega)]
        exact eF _ (by omega) (Or.inr (by omega))
      rw [hstep, run_epiBody L out _ (by omega), r0, r1, rv]
      refine ⟨by simp [memory_set_apply]; omega, by simp [memory_set_apply]; ring, fun j hj1 hj2 => ?_,
        fun p hp hpr => ?_⟩
      · simp only [memory_set_apply]
        rw [if_neg (by omega), if_neg (by omega)]
        by_cases hjt : j = 5 + t
        · rw [if_pos hjt, hjt]
        · rw [if_neg hjt, if_neg (by omega), if_neg (by omega)]; exact eW j hj1 (by omega)
      · simp only [memory_set_apply]
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
          if_neg (by omega)]
        exact eF p hp (by omega)

/-- The epilogue's constant. -/
def epiK : ℕ := 16 * L.na + 140

/-- **The function epilogue is correct**: if array `out` holds `f`, registers
`0 … f 0` end holding `f 0 … f (f 0)`. -/
theorem run_epiFn (hnv : 1 ≤ L.nv) (hout : out < L.na) (σ : Memory) (f : Memory)
    (hf : ∀ j, σ (L.cell out j) = f j) :
    (∀ j, j ≤ f 0 → (Program.run (epiFn L out) σ).1 j = f j) ∧
    (Program.run (epiFn L out) σ).2 ≤ epiK L * (f 0 + 1) := by
  set len := f 0 with hlen
  have hna : 1 ≤ L.na := by omega
  have cge : ∀ i, 5 + i ≤ L.cell out i := fun i => by
    have := Nat.le_mul_of_pos_left i hna; unfold cell B; omega
  set σ1 := (σ.set 1 0).set 4 len with hσ1
  have e1 : (Program.run (.load 4 (L.cell out 0) 1) (Program.run (.zero 1) σ).1).1 = σ1 := by
    simp only [run_zero_mem, run_load_mem, memory_set_get, Nat.add_zero]
    rw [memory_set_apply, if_neg (by have := cge 0; omega), hf 0]
  set σ2 := (Program.run (mulTo L.na 4) σ1).1 with hσ2
  have σ21 : σ2 1 = L.na * len := by
    rw [hσ2, mulTo_one (by omega)]; simp [σ1, memory_set_apply]
  have σ2p : ∀ p, 4 ≤ p → σ2 p = σ1 p := mulTo_hi (by omega) σ1
  obtain ⟨sW, sF, s1, sC⟩ := run_saveLow L out hout σ2 len σ21 5
  set σ3 := (Program.run (saveLow L out 5) σ2).1 with hσ3
  have σ3c : ∀ j, j ≤ len → σ3 (L.cell out j) = f j := by
    intro j hj
    rw [sF _ (L.four_le_cell _ _) (fun q _ e => by have := (L.cell_inj hout hout e).2; omega),
      σ2p _ (L.four_le_cell _ _)]
    simp only [σ1, memory_set_apply]
    rw [if_neg (by have := cge j; omega), if_neg (by have := cge j; omega), hf]
  have σ3s : ∀ q, q < 5 → σ3 (L.cell out (len + 1 + q)) = f q := by
    intro q hq
    rw [sW q hq, σ2p _ (L.four_le_cell _ _)]
    simp only [σ1, memory_set_apply]
    rw [if_neg (by have := cge q; omega), if_neg (by have := cge q; omega), hf]
  have σ34 : σ3 4 = len := by
    rw [sF 4 le_rfl (fun q _ e => by have := cge (len + 1 + q); omega), σ2p 4 le_rfl]
    simp [σ1, memory_set_apply]
  set σ5 := ((σ3.set 3 (len - 4)).set 0 5).set 1 (L.na * 5) with hσ5
  have e5 : (Program.run (Aux.setK 1 (5 * L.na)) (Program.run (Aux.setK 0 5)
      (Program.run (rep 4 (.decr 3)) (Program.run (.copy 3 4) σ3).1).1).1).1 = σ5 := by
    simp only [run_copy_mem, run_rep_decr, run_setK_mem, memory_set_get, memory_set_set, σ34]
    rw [hσ5, Nat.mul_comm]
  have h50 : σ5 0 = 5 := by simp [σ5, memory_set_apply]
  have h51 : σ5 1 = L.na * 5 := by simp [σ5, memory_set_apply]
  have h53 : σ5 3 = len - 4 := by simp [σ5, memory_set_apply]
  have h5p : ∀ p, 4 ≤ p → σ5 p = σ3 p := fun p hp => by
    simp only [σ5, memory_set_apply]; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  obtain ⟨-, -, lW, lF⟩ := epi_loop L out hnv hna σ5 h50 h51 (len - 4)
  set σ6 := loopMem (epiBody L out) 2 (len - 4) σ5 with hσ6
  set σ7 := (Program.run (mulTo L.na 4) σ6).1 with hσ7
  have σ64 : σ6 4 = len := by rw [lF 4 le_rfl (Or.inl (by omega)), h5p 4 le_rfl, σ34]
  have σ71 : σ7 1 = L.na * len := by rw [hσ7, mulTo_one (by omega), σ64]
  have σ7p : ∀ p, 4 ≤ p → σ7 p = σ6 p := mulTo_hi (by omega) σ6
  have σ7s : ∀ q, q < 5 → σ7 (L.cell out (q + 1) + σ7 1) = f q := by
    intro q hq
    rw [σ71, cell_add, σ7p _ (L.four_le_cell _ _),
      lF _ (L.four_le_cell _ _) (Or.inr (by have := cge (q + 1 + len); omega)),
      h5p _ (L.four_le_cell _ _), show q + 1 + len = len + 1 + q by ring, σ3s q hq]
  -- the whole run, as the composition of the stages
  have hmem : (Program.run (epiFn L out) σ).1
      = ((((σ7.set 0 (f 0)).set 2 (f 2)).set 3 (f 3)).set 4 (f 4)).set 1 (f 1) := by
    simp only [epiFn, run_seqs_mem, List.foldl]
    rw [e1, ← hσ2, ← hσ3, e5, run_loop_mem, h53, ← hσ6, ← hσ7]
    simp only [run_load_mem]
    have hc1 := cge 1; have hc2 := cge 2; have hc3 := cge 3; have hc4 := cge 4; have hc5 := cge 5
    simp (disch := omega) only [memory_set_get_ne, memory_set_get]
    rw [σ7s 0 (by omega), σ7s 1 (by omega), σ7s 2 (by omega), σ7s 3 (by omega), σ7s 4 (by omega)]
  have hσ14 : σ1 4 = len := by simp [σ1, memory_set_apply]
  refine ⟨fun j hj => ?_, ?_⟩
  · rw [hmem]
    rcases Nat.lt_or_ge j 5 with h5 | h5
    · rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl | rfl <;>
        simp [memory_set_apply]
    · simp only [memory_set_apply]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega), σ7p j (by omega), lW j h5 (by omega), h5p _ (L.four_le_cell _ _),
        σ3c j hj]
  · simp only [epiFn, run_seqs_cost, seqsCost, cost_zero, cost_load, cost_copy, cost_setK,
      cost_loop, cost_rep_decr]
    rw [e1, ← hσ2, ← hσ3, e5, h53]
    rw [cost_mulTo (by omega), cost_mulTo (by omega)]
    rw [hσ14, run_loop_mem, h53, ← hσ6, σ64]
    rw [sC, loopCost_const (cost_epiBody L out)]
    unfold epiK
    have : (len - 4) * (2 * L.na + 9 + 1) ≤ len * (2 * L.na + 10) := Nat.mul_le_mul_right _ (by omega)
    nlinarith

end Epilogue

/-! ### Reading a memory as a string -/

/-- A memory read in the input format: register `0` the length, bit `i` is
"register `i + 1` is non-zero". -/
def outOf (μ : Memory) : List Bool := List.ofFn (fun i : Fin (μ 0) => decide (μ (i + 1) ≠ 0))

theorem outOf_congr {μ ν : Memory} (h : ∀ j, j ≤ ν 0 → μ j = ν j) : outOf μ = outOf ν := by
  have h0 : μ 0 = ν 0 := h 0 (Nat.zero_le _)
  unfold outOf
  rw [List.ofFn_congr h0]
  congr 1
  funext i
  have : (i : ℕ) + 1 ≤ ν 0 := i.2
  simp only [Fin.val_cast, h _ this]

theorem outOf_startingMemory (ys : List Bool) : outOf (startingMemory ys) = ys := by
  apply List.ext_getElem
  · simp [outOf, startingMemory_zero_eq]
  · intro i h1 h2
    simp only [outOf, List.getElem_ofFn]
    simp only [startingMemory, Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false,
      Nat.add_sub_cancel]
    rw [List.getD_eq_getElem _ _ h2]
    cases ys[i] <;> simp

/-! ### Values of the starting state -/

theorem startingMemory_le_length (xs : List Bool) (p : ℕ) : startingMemory xs p ≤ xs.length := by
  by_cases hp : p = 0
  · subst hp; exact le_refl _
  · simp only [startingMemory, if_neg hp]
    split
    · rename_i h
      have : p - 1 < xs.length := by
        by_contra hc
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at h
        simp at h
      omega
    · omega

theorem bnd_init (xs : List Bool) : (St.init xs).Bnd xs.length := by
  refine ⟨fun x => ?_, fun a i => ?_⟩
  · simp only [St.init]; split <;> omega
  · by_cases ha : a = 0
    · subst ha; exact startingMemory_le_length xs i
    · simp [St.init, ha]

/-! ### The wrappers -/

/-- The layout a command runs in: its scalars, its arrays, and room for array `k`. -/
def layOf (s : Cmd) (k : ℕ) : Lay := ⟨s.nvars + 1, s.narrs + k + 1⟩

theorem layOf_nv (s : Cmd) (k : ℕ) : 1 ≤ (layOf s k).nv := by simp [layOf]
theorem layOf_na (s : Cmd) (k : ℕ) : k < (layOf s k).na := by simp only [layOf]; omega

/-- The source cost of `s` on input `xs`. -/
def srcCost (s : Cmd) (xs : List Bool) : ℕ := (Cmd.run s (St.init xs)).2

/-- The final source state of `s` on input `xs`. -/
def srcOut (s : Cmd) (xs : List Bool) : St := (Cmd.run s (St.init xs)).1

/-- The compiled body runs correctly from the prologue's memory. -/
theorem run_body (s : Cmd) (k : ℕ) (xs : List Bool) :
    (layOf s k).Rel (srcOut s xs)
      (Program.run (compile (layOf s k) s) (Program.run (pro (layOf s k)) (startingMemory xs)).1).1 ∧
    (Program.run (compile (layOf s k) s) (Program.run (pro (layOf s k)) (startingMemory xs)).1).2
      ≤ costK (layOf s k) * (xs.length + s.kmax + srcCost s xs) * srcCost s xs := by
  obtain ⟨r, -⟩ := run_pro (layOf s k) (layOf_nv s k) (by have := layOf_na s k; omega) xs
  have hb := (bnd_init xs).mono (Nat.le_add_right xs.length s.kmax)
  exact comp_ok (layOf s k) s _ _ _ _ r hb (by omega) (by simp [layOf]) (by simp [layOf]; omega)
    le_rfl

/-- **A source program as a decider**: register `0` ends holding scalar `0`. -/
def wrapDec (s : Cmd) : Program :=
  .seq (pro (layOf s 0)) (.seq (compile (layOf s 0) s) (.copy 0 4))

theorem run_wrapDec (s : Cmd) (xs : List Bool) :
    (Program.run (wrapDec s) (startingMemory xs)).1 0 = (srcOut s xs).sc 0 := by
  obtain ⟨r, -⟩ := run_body s 0 xs
  simp only [wrapDec, run_seq_mem, run_copy_mem, memory_set_get]
  exact r.1 0 (layOf_nv s 0)

theorem steps_wrapDec_le (s : Cmd) (xs : List Bool) :
    steps (wrapDec s) xs ≤ preK (layOf s 0) * (xs.length + 1) + 4
      + costK (layOf s 0) * (xs.length + s.kmax + srcCost s xs) * srcCost s xs + 3 := by
  obtain ⟨-, c⟩ := run_body s 0 xs
  obtain ⟨-, cp⟩ := run_pro (layOf s 0) (layOf_nv s 0) (by have := layOf_na s 0; omega) xs
  simp only [steps, wrapDec, cost_seq, cost_copy]
  omega

theorem haltsNonZero_wrapDec (s : Cmd) (xs : List Bool) :
    haltsNonZero (wrapDec s) xs ↔ (srcOut s xs).sc 0 ≠ 0 := by
  rw [haltsNonZero, run_wrapDec]

theorem acceptedStrings_wrapDec (s : Cmd) :
    acceptedStrings (wrapDec s) = {xs | (srcOut s xs).sc 0 ≠ 0} := by
  ext xs; exact haltsNonZero_wrapDec s xs

/-- **A source program as a function**: array `out`, in the input format, ends
in registers `0 … len`. -/
def wrapFn (s : Cmd) (out : ℕ) : Program :=
  .seq (pro (layOf s out)) (.seq (compile (layOf s out) s) (epiFn (layOf s out) out))

theorem run_wrapFn (s : Cmd) (out : ℕ) (xs : List Bool) :
    (∀ j, j ≤ (srcOut s xs).ar out 0 →
      (Program.run (wrapFn s out) (startingMemory xs)).1 j = (srcOut s xs).ar out j) ∧
    steps (wrapFn s out) xs ≤ preK (layOf s out) * (xs.length + 1) + 4
      + costK (layOf s out) * (xs.length + s.kmax + srcCost s xs) * srcCost s xs
      + epiK (layOf s out) * ((srcOut s xs).ar out 0 + 1) + 2 := by
  obtain ⟨r, c⟩ := run_body s out xs
  obtain ⟨-, cp⟩ := run_pro (layOf s out) (layOf_nv s out) (by have := layOf_na s out; omega) xs
  obtain ⟨e1, e2⟩ := run_epiFn (layOf s out) out (layOf_nv s out) (layOf_na s out) _
    ((srcOut s xs).ar out) (fun j => r.2 out (layOf_na s out) j)
  refine ⟨fun j hj => ?_, ?_⟩
  · simp only [wrapFn, run_seq_mem]; exact e1 j hj
  · simp only [steps, wrapFn, cost_seq]
    omega

theorem outOf_wrapFn (s : Cmd) (out : ℕ) (xs : List Bool) :
    outOf (Program.run (wrapFn s out) (startingMemory xs)).1 = outOf ((srcOut s xs).ar out) :=
  outOf_congr (run_wrapFn s out xs).1

/-! ### Polynomial time from a polynomial source cost -/

/-- A step bound quadratic in `length + b + S` is polynomial whenever `S` is. -/
theorem runsInPolyTime_of_sq {M : Program} {S : List Bool → ℕ} (Q b : ℕ)
    (hS : ∃ c d, ∀ xs, S xs ≤ c * (xs.length + 1) ^ d)
    (h : ∀ xs, steps M xs ≤ Q * (xs.length + b + S xs + 1) ^ 2) : RunsInPolyTime M := by
  obtain ⟨c, d, hc⟩ := hS
  have hp : Poly (fun n => Q * (n + b + c * (n + 1) ^ d + 1) ^ 2) :=
    Poly.mul (Poly.const Q) (Poly.pow (Poly.add (Poly.add (Poly.add Poly.id (Poly.const b))
      (Poly.mul (Poly.const c) (poly_pow d))) (Poly.const 1)) 2)
  refine runsInPolyTime_of_poly hp (fun xs => le_trans (h xs) ?_)
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by have := hc xs; omega) 2)

theorem sq_bound {n k S a K : ℕ} :
    a * (n + 1) + 4 + K * (n + k + S) * S + 3 ≤ (a + K + 7) * (n + k + S + 1) ^ 2 := by
  have h0 : n + k + S + 1 ≤ (n + k + S + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have h1 : n + 1 ≤ (n + k + S + 1) ^ 2 := by omega
  have h2 : (n + k + S) * S ≤ (n + k + S + 1) ^ 2 := by
    rw [sq]; exact Nat.mul_le_mul (by omega) (by omega)
  have h3 : 1 ≤ (n + k + S + 1) ^ 2 := by omega
  have := Nat.mul_le_mul_left a h1
  have := Nat.mul_le_mul_left K h2
  rw [Nat.mul_assoc K]
  nlinarith

/-- **A source program with polynomially many source steps compiles to a
polynomial-time decider.** -/
theorem runsInPolyTime_wrapDec (s : Cmd) (hS : ∃ c d, ∀ xs, srcCost s xs ≤ c * (xs.length + 1) ^ d) :
    RunsInPolyTime (wrapDec s) :=
  runsInPolyTime_of_sq (preK (layOf s 0) + costK (layOf s 0) + 7) s.kmax hS
    (fun xs => le_trans (steps_wrapDec_le s xs) sq_bound)

/-- **The same for a function**: the output's length is bounded by the source
values, so it costs nothing extra to state. -/
theorem runsInPolyTime_wrapFn (s : Cmd) (out : ℕ)
    (hS : ∃ c d, ∀ xs, srcCost s xs ≤ c * (xs.length + 1) ^ d) : RunsInPolyTime (wrapFn s out) := by
  refine runsInPolyTime_of_sq (preK (layOf s out) + costK (layOf s out) + 7 + epiK (layOf s out) + 2)
    s.kmax hS (fun xs => ?_)
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
  nlinarith

#print axioms Factoring.Aux.Copied.PLib.run_pro
#print axioms Factoring.Aux.Copied.PLib.run_epiFn
#print axioms Factoring.Aux.Copied.PLib.acceptedStrings_wrapDec
#print axioms Factoring.Aux.Copied.PLib.runsInPolyTime_wrapDec
#print axioms Factoring.Aux.Copied.PLib.outOf_wrapFn
#print axioms Factoring.Aux.Copied.PLib.runsInPolyTime_wrapFn

end Factoring.Aux.Copied.PLib
