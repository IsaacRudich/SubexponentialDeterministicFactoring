/-
Adapted from the authors' related work (the whole file).

Not an audit surface.
-/
/-
PLIB, part 3: reasoning about source programs.

What a consumer needs to verify a `Cmd` without unfolding `Cmd.run` by hand:

* `Cmd.seqs`, a block of commands, and its unfolding;
* `Cmd.loop_inv`: a loop invariant, indexed by the turn count, proves a property
  of the loop's final state; `Cmd.loop_cost_le` bounds its cost by a per-turn bound
  under the same invariant;
* frames: `Cmd.wsc` / `Cmd.war` list the scalars and arrays a command may write,
  and `Cmd.run_sc_frame` / `Cmd.run_ar_frame` say everything else is unchanged;
* a worked example, `anyOne`, carried all the way to `acceptedStrings` and
  `RunsInPolyTime`.

Not an audit surface.
-/
module

public import FactoringAux.Copied.PlibTop

@[expose] public section

namespace Factoring.Aux.Copied.PLib

open Factoring.Aux.Copied Factoring.Aux.Copied.Aux

namespace Cmd

/-! ### Blocks -/

/-- A block of commands, run in order. -/
def seqs : List Cmd → Cmd
  | [] => .skip
  | s :: ss => .seq s (seqs ss)

theorem run_seqs_nil (st : St) : Cmd.run (seqs []) st = (st, 1) := rfl

theorem run_seqs_cons (s : Cmd) (ss : List Cmd) (st : St) :
    Cmd.run (seqs (s :: ss)) st = ((Cmd.run (seqs ss) (Cmd.run s st).1).1,
      (Cmd.run s st).2 + (Cmd.run (seqs ss) (Cmd.run s st).1).2 + 1) := rfl

theorem kmax_seqs (ss : List Cmd) : (seqs ss).kmax = (ss.map kmax).foldr max 0 := by
  induction ss with
  | nil => rfl
  | cons s ss ih => simp [seqs, kmax, ih]

/-! ### Loops -/

/-- **Loop invariant.**  `P j st'` holds of the state after `j` turns. -/
theorem loop_inv {b c : ℕ} {body : Cmd} {st : St} (P : ℕ → St → Prop) (h0 : P 0 st)
    (hstep : ∀ j st', j < st.sc b → P j st' → P (j + 1) (Cmd.run body (st'.setSc c j)).1) :
    P (st.sc b) (Cmd.run (.loop b c body) st).1 := by
  rw [run_loop_eq]
  have : ∀ j, j ≤ st.sc b → P j (loopSt body c j st) := by
    intro j
    induction j with
    | zero => intro _; exact h0
    | succ j ih => intro hj; exact hstep j _ (by omega) (ih (by omega))
  exact this _ le_rfl

/-- **Loop cost.**  Under an invariant, a per-turn bound `K` gives `b * (K + 1) + 1`. -/
theorem loop_cost_le {b c : ℕ} {body : Cmd} {st : St} (P : ℕ → St → Prop) (K : ℕ) (h0 : P 0 st)
    (hstep : ∀ j st', j < st.sc b → P j st' → P (j + 1) (Cmd.run body (st'.setSc c j)).1)
    (hcost : ∀ j st', j < st.sc b → P j st' → (Cmd.run body (st'.setSc c j)).2 ≤ K) :
    (Cmd.run (.loop b c body) st).2 ≤ st.sc b * (K + 1) + 1 := by
  rw [run_loop_eq]
  have : ∀ j, j ≤ st.sc b → P j (loopSt body c j st) ∧ loopCost body c j st ≤ j * (K + 1) + 1 := by
    intro j
    induction j with
    | zero => intro _; exact ⟨h0, by simp [loopCost]⟩
    | succ j ih =>
        intro hj
        obtain ⟨p, q⟩ := ih (by omega)
        refine ⟨hstep j _ (by omega) p, ?_⟩
        show loopCost body c j st + (Cmd.run body ((loopSt body c j st).setSc c j)).2 + 1 ≤ _
        have := hcost j _ (by omega) p
        rw [Nat.add_mul, Nat.one_mul]; omega
  exact (this _ le_rfl).2

/-- A loop whose body costs at most `K` from every state. -/
theorem loop_cost_le' {b c : ℕ} {body : Cmd} {st : St} (K : ℕ)
    (hcost : ∀ st', (Cmd.run body st').2 ≤ K) :
    (Cmd.run (.loop b c body) st).2 ≤ st.sc b * (K + 1) + 1 :=
  loop_cost_le (fun _ _ => True) K trivial (fun _ _ _ _ => trivial) (fun _ _ _ _ => hcost _)

/-! ### Frames -/

/-- The scalars a command may write. -/
def wsc : Cmd → List ℕ
  | .skip => []
  | .seq s t => wsc s ++ wsc t
  | .setK x _ => [x]
  | .copy x _ => [x]
  | .incr x => [x]
  | .decr x => [x]
  | .rd x _ _ _ => [x]
  | .wr _ _ _ _ => []
  | .ifLt _ _ s t => wsc s ++ wsc t
  | .ifZero _ s t => wsc s ++ wsc t
  | .loop _ c body => c :: wsc body
  | .call _ _ => []

/-- The arrays a command may write. -/
def war : Cmd → List ℕ
  | .seq s t => war s ++ war t
  | .wr a _ _ _ => [a]
  | .ifLt _ _ s t => war s ++ war t
  | .ifZero _ s t => war s ++ war t
  | .loop _ _ body => war body
  | .call _ a => [a]
  | _ => []

/-- **Scalar frame**: a scalar a command does not write is unchanged. -/
theorem run_sc_frame : ∀ (s : Cmd) (st : St) (x : ℕ), x ∉ s.wsc → (Cmd.run s st).1.sc x = st.sc x
  | .skip, _, _, _ => rfl
  | .seq s t, st, x, h => by
      simp only [wsc, List.mem_append, not_or] at h
      rw [run_seq]; simp only
      rw [run_sc_frame t _ x h.2, run_sc_frame s _ x h.1]
  | .setK y _, st, x, h => by
      simp only [wsc, List.mem_singleton] at h
      simp [run_setK, Function.update_apply, h]
  | .copy y _, st, x, h => by
      simp only [wsc, List.mem_singleton] at h
      simp [run_copy, Function.update_apply, h]
  | .incr y, st, x, h => by
      simp only [wsc, List.mem_singleton] at h
      simp [run_incr, Function.update_apply, h]
  | .decr y, st, x, h => by
      simp only [wsc, List.mem_singleton] at h
      simp [run_decr, Function.update_apply, h]
  | .rd y _ _ _, st, x, h => by
      simp only [wsc, List.mem_singleton] at h
      simp [run_rd, Function.update_apply, h]
  | .wr _ _ _ _, st, x, _ => rfl
  | .ifLt _ _ s t, st, x, h => by
      simp only [wsc, List.mem_append, not_or] at h
      rw [run_ifLt]; split_ifs
      · exact run_sc_frame s st x h.1
      · exact run_sc_frame t st x h.2
  | .ifZero _ s t, st, x, h => by
      simp only [wsc, List.mem_append, not_or] at h
      rw [run_ifZero]; split_ifs
      · exact run_sc_frame s st x h.1
      · exact run_sc_frame t st x h.2
  | .loop b c body, st, x, h => by
      simp only [wsc, List.mem_cons, not_or] at h
      exact loop_inv (fun _ st' => st'.sc x = st.sc x) rfl (fun j st' _ hp => by
        rw [run_sc_frame body _ x h.2]
        simp only [St.setSc_sc, Function.update_apply, if_neg h.1]; exact hp)
  | .call _ _, st, x, _ => rfl

/-- **Array frame**: an array a command does not write is unchanged. -/
theorem run_ar_frame : ∀ (s : Cmd) (st : St) (a : ℕ), a ∉ s.war → (Cmd.run s st).1.ar a = st.ar a
  | .skip, _, _, _ => rfl
  | .seq s t, st, a, h => by
      simp only [war, List.mem_append, not_or] at h
      rw [run_seq]; simp only
      rw [run_ar_frame t _ a h.2, run_ar_frame s _ a h.1]
  | .setK _ _, _, _, _ => rfl
  | .copy _ _, _, _, _ => rfl
  | .incr _, _, _, _ => rfl
  | .decr _, _, _, _ => rfl
  | .rd _ _ _ _, _, _, _ => rfl
  | .wr b _ _ _, st, a, h => by
      simp only [war, List.mem_singleton] at h
      simp [run_wr, Function.update_apply, h]
  | .ifLt _ _ s t, st, a, h => by
      simp only [war, List.mem_append, not_or] at h
      rw [run_ifLt]; split_ifs
      · exact run_ar_frame s st a h.1
      · exact run_ar_frame t st a h.2
  | .ifZero _ s t, st, a, h => by
      simp only [war, List.mem_append, not_or] at h
      rw [run_ifZero]; split_ifs
      · exact run_ar_frame s st a h.1
      · exact run_ar_frame t st a h.2
  | .loop b c body, st, a, h => by
      simp only [war] at h
      exact loop_inv (fun _ st' => st'.ar a = st.ar a) rfl (fun j st' _ hp => by
        rw [run_ar_frame body _ a h]; simpa using hp)
  | .call _ b, st, a, h => by
      simp only [war, List.mem_singleton] at h
      simp [run_call, Function.update_apply, h]

end Cmd

/-! ### The worked example: "the input contains a `1`" -/

section AnyOne

/-- Scalars: `0` the answer, `1` the counter, `2` the bit read, `3` the length. -/
def anyOne : Cmd :=
  .seq (.copy 3 0) (.seq (.setK 0 0)
    (.loop 3 1 (.seq (.rd 2 0 1 1) (.ifZero 2 .skip (.setK 0 1)))))

theorem startingMemory_succ (xs : List Bool) (i : ℕ) :
    startingMemory xs (i + 1) = if xs.getD i false then 1 else 0 := by
  simp [startingMemory]

theorem anyOne_spec (xs : List Bool) :
    ((srcOut anyOne xs).sc 0 ≠ 0 ↔ ∃ i, i < xs.length ∧ xs.getD i false = true) ∧
    srcCost anyOne xs ≤ 6 * xs.length + 10 := by
  simp only [srcOut, srcCost, anyOne, Cmd.run_seq, Cmd.run_copy, Cmd.run_setK]
  set st0 := ((St.init xs).setSc 3 ((St.init xs).sc 0)).setSc 0 0 with hst0
  have hb : st0.sc 3 = xs.length := by simp [st0, Function.update_apply]
  -- the invariant: after `j` turns, the answer is non-zero iff a `1` was seen
  let P : ℕ → St → Prop := fun j st' =>
    st'.ar 0 = startingMemory xs ∧ (st'.sc 0 ≠ 0 ↔ ∃ i, i < j ∧ xs.getD i false = true)
  have h0 : P 0 st0 := ⟨by simp [st0], by simp [st0]⟩
  have hstep : ∀ j st', j < st0.sc 3 → P j st' →
      P (j + 1) (Cmd.run (.seq (.rd 2 0 1 1) (.ifZero 2 .skip (.setK 0 1))) (st'.setSc 1 j)).1 := by
    intro j st' _ ⟨ha, hs⟩
    simp only [Cmd.run_seq, Cmd.run_rd, Cmd.run_ifZero, Cmd.run_skip, Cmd.run_setK]
    simp only [St.setSc_sc, St.setSc_ar, Function.update_apply, ha, startingMemory_succ]
    simp only [if_true, show ((1:ℕ) = 2) = False by decide, if_false]
    by_cases hx : xs.getD j false = true
    · simp only [hx, if_true, show ((1:ℕ) = 0) = False by decide, if_false]
      refine ⟨by simp [ha], by simp; exact ⟨j, by omega, hx⟩⟩
    · simp only [hx, Bool.false_eq_true, if_false, if_true, show ((2:ℕ) = 0) = False by decide]
      refine ⟨ha, ?_⟩
      rw [show ((st'.setSc 1 j).setSc 2 0).sc 0 = st'.sc 0 by simp [St.setSc], hs]
      constructor
      · rintro ⟨i, hi, h⟩; exact ⟨i, by omega, h⟩
      · rintro ⟨i, hi, h⟩
        refine ⟨i, ?_, h⟩
        rcases Nat.lt_or_ge i j with hij | hij
        · exact hij
        · exact absurd (show i = j by omega ▸ h) hx
  have hfin := Cmd.loop_inv P h0 hstep
  have hc := Cmd.loop_cost_le P 4 h0 hstep (fun j st' _ _ => by
    simp only [Cmd.run_seq, Cmd.run_rd, Cmd.run_ifZero]; split_ifs <;> simp [Cmd.run_skip, Cmd.run_setK])
  rw [hb] at hfin hc
  refine ⟨hfin.2, ?_⟩
  omega

theorem acceptedStrings_anyOne :
    acceptedStrings (wrapDec anyOne) = {xs | ∃ i, i < xs.length ∧ xs.getD i false = true} := by
  rw [acceptedStrings_wrapDec]
  ext xs
  exact (anyOne_spec xs).1

theorem runsInPolyTime_anyOne : RunsInPolyTime (wrapDec anyOne) :=
  runsInPolyTime_wrapDec anyOne ⟨16, 1, fun xs => by
    have := (anyOne_spec xs).2; rw [pow_one]; nlinarith⟩

end AnyOne

#print axioms Factoring.Aux.Copied.PLib.Cmd.loop_inv
#print axioms Factoring.Aux.Copied.PLib.Cmd.run_sc_frame
#print axioms Factoring.Aux.Copied.PLib.Cmd.run_ar_frame
#print axioms Factoring.Aux.Copied.PLib.acceptedStrings_anyOne
#print axioms Factoring.Aux.Copied.PLib.runsInPolyTime_anyOne

end Factoring.Aux.Copied.PLib
