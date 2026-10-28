/-
FactoringAux/Simulate/Main.lean — **L2′**: every `Program` (the adapted register machine) is simulated by
an `SProg` with the same input/output convention, at cost `O((steps + n + 1)^3)` (the constant
depends on the program); hence a `Program` for `Nat.minFac` gives `FactoringInTime`.

Not audited.
-/
module

public import FactoringAux.Simulate.IO
public import FactoringAux.SProg.Machine
public import FactoringAux.Time

@[expose] public section

namespace Factoring.Aux.Sim

open SProg Function Factoring.Aux.Copied Factoring.Aux.Copied.PLib Computability

/-- The whole simulation: read the input, run `P`, write `outOf` of the final memory. -/
def fullP (P : Program) : SProg := seqs [inP, sim P 16, outP]

/-- Its number of stacks. -/
def nK (P : Program) : ℕ := 16 + 2 * nl P

theorem stacksBelow_of_uses {n : ℕ} : ∀ p : SProg, (∀ j, p.uses j = true → j < n) →
    p.StacksBelow n = true
  | .skip, _ => rfl
  | .push k _, h => by simpa [StacksBelow] using h k (by simp [uses])
  | .read k pt pf pe, h => by
      simp only [StacksBelow, Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨⟨⟨h k (by simp [uses]), stacksBelow_of_uses pt (fun j hj => h j ?_)⟩,
        stacksBelow_of_uses pf (fun j hj => h j ?_)⟩, stacksBelow_of_uses pe (fun j hj => h j ?_)⟩
      all_goals simp [uses, hj]
  | .seq p q, h => by
      simp only [StacksBelow, Bool.and_eq_true]
      exact ⟨stacksBelow_of_uses p (fun j hj => h j (by simp [uses, hj])),
        stacksBelow_of_uses q (fun j hj => h j (by simp [uses, hj]))⟩
  | .loop k pt pf, h => by
      simp only [StacksBelow, Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨⟨h k (by simp [uses]), stacksBelow_of_uses pt (fun j hj => h j ?_)⟩,
        stacksBelow_of_uses pf (fun j hj => h j ?_)⟩
      all_goals simp [uses, hj]

theorem fullP_wf (P : Program) : (fullP P).WF = true := by
  have h1 : inP.WF = true := by decide
  have h2 : outP.WF = true := by decide
  simp [fullP, SProg.seqs, WF, h1, h2, sim_wf P 16 le_rfl]

theorem fullP_stacks (P : Program) : (fullP P).StacksBelow (nK P) = true := by
  apply stacksBelow_of_uses
  intro j hj
  have h1 : maxUse inP ≤ 15 := by decide
  have h2 : maxUse outP ≤ 15 := by decide
  have key : ∀ p q : SProg, (SProg.seq p q).uses j = true → p.uses j = true ∨ q.uses j = true :=
    fun p q h => by simpa only [uses, Bool.or_eq_true] using h
  have hs : (SProg.skip).uses j = false := rfl
  change (SProg.seq inP (SProg.seq (sim P 16) (SProg.seq outP .skip))).uses j = true at hj
  unfold nK
  rcases key _ _ hj with h | h
  · have := uses_le inP h; omega
  rcases key _ _ h with h | h
  · rcases sim_inRange P 16 j h with h' | h' <;> omega
  rcases key _ _ h with h | h
  · have := uses_le outP h; omega
  · rw [hs] at h; exact absurd h (by decide)

theorem startBlocks_le (xs : List Bool) (i : ℕ) : startingMemory xs i ≤ xs.length :=
  startingMemory_le_length xs i

set_option maxHeartbeats 2000000 in
/-- **L2′.**  `fullP P` computes `outOf` of `P`'s final memory, in cubic cost. -/
theorem fullP_spec (P : Program) (xs : List Bool) :
    (fullP P).exec (initStacks xs) = initStacks (outOf (Program.run P (startingMemory xs)).1) ∧
      (fullP P).cost (initStacks xs) ≤
        2000 * (lits P + 1) * (steps P xs + xs.length + 1) ^ 3 := by
  set n := xs.length with hn
  set T := steps P xs with hT
  set L := lits P with hL
  set Λ := L + n + T + 1 with hΛ
  set M := n + T with hM
  have hin := inP_spec xs
  have hpre : Pre (update (fun _ => []) mMEM (enc (startBlocks xs))) (startingMemory xs) Λ n :=
    ⟨startBlocks xs, by simp, startBlocks_good xs Λ (by omega),
      fun j h1 h2 => by simp [show j ≠ 1 by omega], startBlocks_le xs⟩
  obtain ⟨bs, e2, g2, k2⟩ := sim_ok P 16 le_rfl _ (startingMemory xs) Λ M n hpre
    (by simp [hM, hT, steps]) (by omega)
    (fun j h1 h2 => by simp [show j ≠ 1 by omega])
  have hval : ∀ r, (Program.run P (startingMemory xs)).1 r ≤ M := by
    intro r
    have := Copied.Aux.run_val_le P (startingMemory xs) n (startBlocks_le xs) r
    simp only [hM, hT, steps] at this ⊢; omega
  have hout := outP_spec bs _ Λ M g2 hval
  have e2' : (sim P 16).exec (update (fun _ => []) mMEM (enc (startBlocks xs))) =
      update (fun _ => []) mMEM (enc bs) := by rw [e2, update_idem]
  refine ⟨?_, ?_⟩
  · show outP.exec ((sim P 16).exec (inP.exec (initStacks xs))) = _
    rw [hin.1, e2', hout.1]
  · show inP.cost (initStacks xs) + ((sim P 16).cost (inP.exec (initStacks xs)) +
      (outP.cost ((sim P 16).exec (inP.exec (initStacks xs))) + 0)) ≤ _
    rw [hin.1, e2']
    have c1 := hin.2
    have c3 := hout.2
    have hTsteps : (Program.run P (startingMemory xs)).2 = T := rfl
    rw [hTsteps] at k2
    -- bounds in terms of x = n + T + 1
    set x := T + n + 1 with hx
    have hx1 : 1 ≤ x := by omega
    have hΛx : Λ ≤ (L + 1) * x := by nlinarith
    have hMx : M + 1 ≤ x := by omega
    have hW : W Λ M ≤ 4 * (L + 1) * x * x := by
      unfold W
      have : Λ * (M + 1) ≤ (L + 1) * x * x := by
        calc Λ * (M + 1) ≤ ((L + 1) * x) * x := Nat.mul_le_mul hΛx hMx
          _ = (L + 1) * x * x := rfl
      nlinarith
    have hAcc : Acc Λ M ≤ 1000 * (L + 1) * x * x := by
      unfold Acc; nlinarith
    have hTx : T ≤ x := by omega
    have hsim : T * Acc Λ M ≤ 1000 * ((L + 1) * x * x * x) := by
      calc T * Acc Λ M ≤ x * (1000 * (L + 1) * x * x) := Nat.mul_le_mul hTx hAcc
        _ = 1000 * ((L + 1) * x * x * x) := by ring
    have hout' : 6 * Λ * (M + 1) + 4 * M + 6 ≤ 20 * ((L + 1) * x * x * x) := by
      have : Λ * (M + 1) ≤ (L + 1) * x * x := by
        calc Λ * (M + 1) ≤ ((L + 1) * x) * x := Nat.mul_le_mul hΛx hMx
          _ = (L + 1) * x * x := rfl
      have : (L + 1) * x * x ≤ (L + 1) * x * x * x := Nat.le_mul_of_pos_right _ (by omega)
      have : x ≤ (L + 1) * x * x * x := by
        have : 1 ≤ (L + 1) * x * x := Nat.one_le_iff_ne_zero.mpr (by positivity)
        nlinarith
      have e6 : 6 * Λ * (M + 1) = 6 * (Λ * (M + 1)) := by ring
      omega
    have hin' : 8 * n + 5 ≤ 13 * ((L + 1) * x * x * x) := by
      have : 1 ≤ (L + 1) * x * x := Nat.one_le_iff_ne_zero.mpr (by positivity)
      nlinarith
    have hpow : x ^ 3 = x * x * x := by ring
    rw [hpow, show 2000 * (L + 1) * (x * x * x) = 2000 * ((L + 1) * x * x * x) by ring]
    omega

/-- **L2′ for factoring.**  A `Program` that outputs `encodeNat (minFac N)` on input `encodeNat N`
within `T` steps gives `FactoringInTime` at cost `c · (T n + n + 1)^3`. -/
theorem factoringInTime_of_program (P : Program) (T : ℕ → ℕ)
    (hout : ∀ N, outOf (Program.run P (startingMemory (encodeNat N))).1 = encodeNat (Nat.minFac N))
    (hT : ∀ N, steps P (encodeNat N) ≤ T (encodeNat N).length) :
    FactoringInTime (fun n => (2000 * (lits P + 1) + 1) * (T n + n + 1) ^ 3) := by
  refine factoringInTime_of_sprog (fullP P) (nK P) (by unfold nK; omega) (fullP_wf P)
    (fullP_stacks P) _ (fun N => by rw [(fullP_spec P _).1, hout N]) (fun N => ?_)
  have h := (fullP_spec P (encodeNat N)).2
  have h1 : (steps P (encodeNat N) + (encodeNat N).length + 1) ^ 3 ≤
      (T (encodeNat N).length + (encodeNat N).length + 1) ^ 3 :=
    Nat.pow_le_pow_left (by have := hT N; omega) 3
  have h2 : 1 ≤ (T (encodeNat N).length + (encodeNat N).length + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  nlinarith

/-- The same from interface `TimeComp` (`FactoringAux/Time.lean`). -/
theorem factoringInTime_of_timeComp (P : Program) (g : List Bool → List Bool) (S : List Bool → ℕ)
    (hP : TimeComp P g S) (hg : ∀ N, g (encodeNat N) = encodeNat (Nat.minFac N))
    (T : ℕ → ℕ) (hT : ∀ N, S (encodeNat N) ≤ T (encodeNat N).length) :
    ∃ c : ℕ, FactoringInTime (fun n => c * (T n + n + 1) ^ 3) :=
  ⟨_, factoringInTime_of_program P T (fun N => by rw [(hP _).1, hg])
    (fun N => le_trans (hP _).2 (hT N))⟩

end Factoring.Aux.Sim
