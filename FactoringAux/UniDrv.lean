/-
The driver for a counting `Cmd`: `drv` (`Driver.lean`) with the counting expression replaced by
a counting command `c` that may write memo tables.

* `CSpec c B`: the counting command's contract (output bit in scalar `3`; scalars `0, 2, 4` and arrays `0, 1, 2`
  kept; cost at most `B n` when `D` holds bits).
* `bodyC`, `drvC`: `body`, `drv` with `Ex.comp e 3 10` replaced by `c` (the rest verbatim).
* `LInvC`, `loop_bodyC`, `search_loopC`, `search_resultC`: the search loop, as in `DriverSpec.lean`, with an
  invariant that lets arrays `≥ 3` (and array `2`) and the scalars the counting command writes change.

Not an audit surface.
-/
module

public import FactoringAux.DriverOut

@[expose] public section

namespace Factoring.Aux

open Factoring.Aux.Copied Factoring.Aux.Copied.PLib Finset Computability Factoring.Aux.Trial

/-- The counting command's contract: output bit in scalar `3`. -/
structure CSpec (c : Cmd) (B : ℕ → ℕ) : Prop where
  keep : ∀ st, (Cmd.run c st).1.sc 0 = st.sc 0 ∧ (Cmd.run c st).1.sc 2 = st.sc 2 ∧
    (Cmd.run c st).1.sc 4 = st.sc 4 ∧ ∀ a, a < 3 → (Cmd.run c st).1.ar a = st.ar a
  le_one : ∀ st, (Cmd.run c st).1.sc 3 ≤ 1
  val : ∀ st, st.sc 2 < st.sc 0 → 2 ≤ numCells (st.ar 0) 1 (st.sc 0) → st.ar 1 (st.sc 2) = 0 →
    (∀ j, st.ar 1 j ≤ 1) →
    (Cmd.run c st).1.sc 3 = if 0 < cntPre (numCells (st.ar 0) 1 (st.sc 0)) (st.sc 2)
      (numCells (st.ar 1) (st.sc 2) (st.sc 0 - st.sc 2)) then 0 else 1
  cost : ∀ st, st.sc 2 < st.sc 0 → (∀ j, st.ar 1 j ≤ 1) → (Cmd.run c st).2 ≤ B (st.sc 0)

/-- The search body, turn `i`, with a counting command. -/
def bodyC (c : Cmd) : Cmd :=
  .seq (Ex.comp kEx 2 10) (.seq (.wr 1 2 0 4) (.seq c (.wr 1 2 0 3)))

/-- The driver with a counting command. -/
def drvC (c : Cmd) : Cmd :=
  .seq (.setK 4 0) (.seq (.setK 5 2) (.ifLt 0 5
    (.ifZero 0 (.seq (.setK 6 2) (.seq (.wr 2 4 0 6) (.seq (.setK 6 1) (.wr 2 4 2 6))))
      (.seq (.setK 6 1) (.seq (.wr 2 4 0 6) (.wr 2 4 1 6))))
    (.seq (.loop 0 1 (bodyC c)) (.seq (.loop 0 1 (.seq (.rd 5 1 1 0) (.wr 2 1 1 5)))
      (.seq (Ex.comp lenEx 6 10) (.wr 2 4 0 6))))))

/-- The loop invariant after `i` turns, from a start state `st` (only `n`, scalar `4`, the input and `D` are
tracked). -/
def LInvC (st : St) (i : ℕ) (s : St) : Prop :=
  s.sc 0 = st.sc 0 ∧ s.sc 4 = 0 ∧ s.ar 0 = st.ar 0 ∧ (∀ j, s.ar 1 j ≤ 1) ∧
    (∀ j, j + i < st.sc 0 → s.ar 1 j = 0) ∧
    (2 ≤ numCells (st.ar 0) 1 (st.sc 0) →
      numCells (s.ar 1) (st.sc 0 - i) i = xs (cntPre (numCells (st.ar 0) 1 (st.sc 0))) (st.sc 0) i)

theorem loop_bodyC (c : Cmd) (B : ℕ → ℕ) (hc : CSpec c B) (st : St) (i : ℕ) (hi : i < st.sc 0) (s : St)
    (hs : LInvC st i s) :
    LInvC st (i + 1) (Cmd.run (bodyC c) (s.setSc 1 i)).1 ∧
      (Cmd.run (bodyC c) (s.setSc 1 i)).2 ≤ B (st.sc 0) + 2 * i + 40 := by
  obtain ⟨h0, h4, ha0, h1, hz, hv⟩ := hs
  set n := st.sc 0
  have wk := Ex.comp_spec kEx 2 10 (s.setSc 1 i) (by simp [kEx, Ex.VB]) (by norm_num)
  simp only [Ex.Wr] at wk
  obtain ⟨k1, k2, k3, k4⟩ := wk
  have hk : (Cmd.run (Ex.comp kEx 2 10) (s.setSc 1 i)).1.sc 2 = n - 1 - i := by
    rw [k1]; simp [kEx, Ex.eval, h0]
  have hkc : Ex.cost (s.setSc 1 i).sc (s.setSc 1 i).ar kEx ≤ 2 * i + 30 := by
    simp [kEx, Ex.cost, Ex.eval]; omega
  simp only [bodyC, Cmd.run_seq, Cmd.run_wr]
  generalize Cmd.run (Ex.comp kEx 2 10) (s.setSc 1 i) = r1 at *
  have r10 : r1.1.sc 0 = n := by rw [k2 0 (by norm_num) (by norm_num)]; simp [h0]
  have r14 : r1.1.sc 4 = 0 := by rw [k2 4 (by norm_num) (by norm_num)]; simp [h4]
  have r1a : r1.1.ar = s.ar := by rw [k3]; rfl
  rw [hk, r14]
  simp only [Nat.add_zero]
  set k := n - 1 - i with hkdef
  -- D[k] := 0
  set s2 := r1.1.setAr 1 k 0 with hs2
  have s2a1 : s2.ar 1 = Function.update (s.ar 1) k 0 := by simp [s2, r1a]
  have s2a0 : s2.ar 0 = st.ar 0 := by simp [s2, Function.update_apply, r1a, ha0]
  have s20 : s2.sc 0 = n := by simp [s2, r10]
  have s22 : s2.sc 2 = k := by simp [s2, hk]
  have s24 : s2.sc 4 = 0 := by simp [s2, r14]
  have hkn : k < n := by omega
  have hcells : ∀ j, s2.ar 1 j ≤ 1 := fun j => by
    rw [s2a1]; by_cases hj : j = k
    · subst hj; simp
    · simp [Function.update_apply, hj, h1 j]
  obtain ⟨e0, e2, e4, ea⟩ := hc.keep s2
  have e1le := hc.le_one s2
  have hcost : (Cmd.run c s2).2 ≤ B n := by
    have := hc.cost s2 (by rw [s22, s20]; exact hkn) hcells
    rwa [s20] at this
  have hvalc := fun hN' => hc.val s2 (by rw [s22, s20]; exact hkn) hN' (by rw [s22, s2a1]; simp) hcells
  generalize Cmd.run c s2 = r3 at *
  have r32 : r3.1.sc 2 = k := by rw [e2, s22]
  have r3a1 : r3.1.ar 1 = s2.ar 1 := ea 1 (by norm_num)
  rw [r32]
  refine ⟨⟨?_, ?_, ?_, fun j => ?_, fun j hj => ?_, fun hN => ?_⟩, ?_⟩
  · simp [e0, s20]; rfl
  · simp [e4, s24]
  · simp [Function.update_apply, ea 0 (by norm_num), s2a0]
  · simp only [St.setAr_ar, Function.update_self]
    rw [Function.update_apply]
    split_ifs with hj
    · exact e1le
    · rw [r3a1]; exact hcells j
  · simp only [St.setAr_ar, Function.update_self]
    rw [Function.update_apply, if_neg (show j ≠ k by omega), r3a1, s2a1]
    simp [Function.update_apply, show j ≠ k by omega, hz j (by omega)]
  · -- the new state of the search
    have hv' := hv hN
    have hN' : 2 ≤ numCells (s2.ar 0) 1 (s2.sc 0) := by rw [s2a0, s20]; exact hN
    have hval := hvalc hN'
    rw [s22, s20, s2a0] at hval
    have hpat : numCells (s2.ar 1) k (n - k) = 2 * xs (cntPre (numCells (st.ar 0) 1 n)) n i := by
      rw [show n - k = i + 1 by omega, numCells_succ, s2a1]
      simp only [Function.update_apply, if_pos rfl, if_true, zero_add]
      rw [← hv', show k + 1 = n - i by omega]
      congr 1
      exact numCells_congr fun j hj _ => by simp [Function.update_apply, show j ≠ k by omega]
    rw [hpat] at hval
    rw [show n - (i + 1) = k by omega, show i + 1 = i + 1 from rfl, numCells_succ]
    simp only [St.setAr_ar, Function.update_self, hval]
    have hrest : numCells (Function.update (r3.1.ar 1) k (if 0 < cntPre (numCells (st.ar 0) 1 n) k
        (2 * xs (cntPre (numCells (st.ar 0) 1 n)) n i) then 0 else 1)) (k + 1) i =
        xs (cntPre (numCells (st.ar 0) 1 n)) n i := by
      rw [← hv', show n - i = k + 1 by omega]
      exact numCells_congr fun j hj _ => by
        simp [Function.update_apply, show j ≠ k by omega, r3a1, s2a1]
    rw [hrest, xs, searchStep, ← hkdef]
    rw [show st.sc 0 = n from rfl]
    split_ifs <;> first | omega | contradiction
  · omega

/-- **The search loop** with a counting command: after `n` turns the invariant holds with `i = n`, within
`n (B n + 2n + 41) + 1`. -/
theorem search_loopC (c : Cmd) (B : ℕ → ℕ) (hc : CSpec c B) (st : St) (h4 : st.sc 4 = 0)
    (hD : ∀ j, st.ar 1 j = 0) :
    LInvC st (st.sc 0) (Cmd.run (.loop 0 1 (bodyC c)) st).1 ∧
      (Cmd.run (.loop 0 1 (bodyC c)) st).2 ≤ st.sc 0 * (B (st.sc 0) + 2 * st.sc 0 + 41) + 1 := by
  have h0 : LInvC st 0 st := ⟨rfl, h4, rfl, fun j => by rw [hD j]; omega, fun j _ => hD j,
    fun _ => by simp [numCells, xs]⟩
  refine ⟨Cmd.loop_inv (LInvC st) h0 (fun j s' hj hs => (loop_bodyC c B hc st j hj s' hs).1), ?_⟩
  exact Cmd.loop_cost_le (LInvC st) (B (st.sc 0) + 2 * st.sc 0 + 40) h0
    (fun j s' hj hs => (loop_bodyC c B hc st j hj s' hs).1)
    (fun j s' hj hs => le_trans (loop_bodyC c B hc st j hj s' hs).2 (by omega))

/-- After the search, for `N ≥ 2` the answer bits are those of `minFac N`. -/
theorem search_resultC (c : Cmd) (B : ℕ → ℕ) (hc : CSpec c B) (st : St) (h4 : st.sc 4 = 0)
    (hD : ∀ j, st.ar 1 j = 0) (hN : 2 ≤ numCells (st.ar 0) 1 (st.sc 0))
    (hlt : numCells (st.ar 0) 1 (st.sc 0) < 2 ^ st.sc 0) :
    numCells ((Cmd.run (.loop 0 1 (bodyC c)) st).1.ar 1) 0 (st.sc 0) =
      (numCells (st.ar 0) 1 (st.sc 0)).minFac := by
  have h := ((search_loopC c B hc st h4 hD).1).2.2.2.2.2 hN
  rw [Nat.sub_self] at h
  rw [h, ← search_eq_minFac hN hlt, xs_spec _ _ (st.sc 0) le_rfl, Nat.sub_self]
  rfl

end Factoring.Aux
