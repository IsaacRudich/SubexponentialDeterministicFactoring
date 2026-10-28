/-
The driver's specification: the search loop (`loop_body`, `search_loop`).

Not an audit surface.
-/
module

public import FactoringAux.Driver

@[expose] public section

namespace Factoring.Aux

open Factoring.Aux.Copied Factoring.Aux.Copied.PLib Finset Computability Factoring.Aux.Trial

/-- The loop invariant after `i` turns, from a start state `st`. -/
def LInv (st : St) (i : ℕ) (s : St) : Prop :=
  s.sc 0 = st.sc 0 ∧ s.sc 4 = 0 ∧ (∀ a, a ≠ 1 → s.ar a = st.ar a) ∧ (∀ j, s.ar 1 j ≤ 1) ∧
    (∀ j, j + i < st.sc 0 → s.ar 1 j = 0) ∧
    (2 ≤ numCells (st.ar 0) 1 (st.sc 0) →
      numCells (s.ar 1) (st.sc 0 - i) i = xs (cntPre (numCells (st.ar 0) 1 (st.sc 0))) (st.sc 0) i)

theorem loop_body (e : Ex) (B : ℕ → ℕ) (he : BitSpec e B) (st : St) (i : ℕ) (hi : i < st.sc 0) (s : St)
    (hs : LInv st i s) :
    LInv st (i + 1) (Cmd.run (body e) (s.setSc 1 i)).1 ∧
      (Cmd.run (body e) (s.setSc 1 i)).2 ≤ B (st.sc 0) + 2 * i + 40 := by
  obtain ⟨h0, h4, ha, h1, hz, hv⟩ := hs
  set n := st.sc 0
  have wk := Ex.comp_spec kEx 2 10 (s.setSc 1 i) (by simp [kEx, Ex.VB]) (by norm_num)
  simp only [Ex.Wr] at wk
  obtain ⟨k1, k2, k3, k4⟩ := wk
  have hk : (Cmd.run (Ex.comp kEx 2 10) (s.setSc 1 i)).1.sc 2 = n - 1 - i := by
    rw [k1]; simp [kEx, Ex.eval, h0]
  have hkc : Ex.cost (s.setSc 1 i).sc (s.setSc 1 i).ar kEx ≤ 2 * i + 30 := by
    simp [kEx, Ex.cost, Ex.eval]; omega
  simp only [body, Cmd.run_seq, Cmd.run_wr]
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
  have s2a : ∀ a, a ≠ 1 → s2.ar a = st.ar a := fun a h => by simp [s2, Function.update_apply, h, r1a, ha a h]
  have s20 : s2.sc 0 = n := by simp [s2, r10]
  have s22 : s2.sc 2 = k := by simp [s2, hk]
  have s24 : s2.sc 4 = 0 := by simp [s2, r14]
  have hkn : k < n := by omega
  have we := Ex.comp_spec e 3 10 s2 he.vb (by norm_num)
  simp only [Ex.Wr] at we
  obtain ⟨e1, e2, e3, e4⟩ := we
  have hcells : ∀ j, s2.ar 1 j ≤ 1 := fun j => by
    rw [s2a1]; by_cases hj : j = k
    · subst hj; simp
    · simp [Function.update_apply, hj, h1 j]
  have hcost : Ex.cost s2.sc s2.ar e ≤ B n := by
    have := he.cost s2.sc s2.ar (by rw [s22, s20]; exact hkn) hcells
    rwa [s20] at this
  generalize Cmd.run (Ex.comp e 3 10) s2 = r3 at *
  have r32 : r3.1.sc 2 = k := by rw [e2 2 (by norm_num) (by norm_num), s22]
  rw [r32]
  refine ⟨⟨?_, ?_, fun a h => ?_, fun j => ?_, fun j hj => ?_, fun hN => ?_⟩, ?_⟩
  · simp [e2 0 (by norm_num) (by norm_num), s20]; rfl
  · simp [e2 4 (by norm_num) (by norm_num), s24]
  · simp [Function.update_apply, h, e3, s2a a h]
  · simp only [St.setAr_ar, Function.update_self]
    rw [Function.update_apply]
    split_ifs with hj
    · rw [e1]; exact he.le_one _ _
    · rw [e3]; exact hcells j
  · simp only [St.setAr_ar, Function.update_self]
    rw [Function.update_apply, if_neg (show j ≠ k by omega), e3, s2a1]
    simp [Function.update_apply, show j ≠ k by omega, hz j (by omega)]
  · -- the new state of the search
    have hv' := hv hN
    have hN' : 2 ≤ numCells (s2.ar 0) 1 (s2.sc 0) := by rw [s2a 0 (by norm_num), s20]; exact hN
    have hval := he.val s2.sc s2.ar (by rw [s22, s20]; exact hkn) hN' (by rw [s22, s2a1]; simp)
    rw [s22, s20, s2a 0 (by norm_num)] at hval
    have hpat : numCells (s2.ar 1) k (n - k) = 2 * xs (cntPre (numCells (st.ar 0) 1 n)) n i := by
      rw [show n - k = i + 1 by omega, numCells_succ, s2a1]
      simp only [Function.update_apply, if_pos rfl, if_true, zero_add]
      rw [← hv', show k + 1 = n - i by omega]
      congr 1
      exact numCells_congr fun j hj _ => by simp [Function.update_apply, show j ≠ k by omega]
    rw [hpat] at hval
    rw [show n - (i + 1) = k by omega, show i + 1 = i + 1 from rfl, numCells_succ]
    simp only [St.setAr_ar, Function.update_self, e1, hval]
    have hrest : numCells (Function.update (r3.1.ar 1) k (if 0 < cntPre (numCells (st.ar 0) 1 n) k
        (2 * xs (cntPre (numCells (st.ar 0) 1 n)) n i) then 0 else 1)) (k + 1) i =
        xs (cntPre (numCells (st.ar 0) 1 n)) n i := by
      rw [← hv', show n - i = k + 1 by omega]
      exact numCells_congr fun j hj _ => by
        simp [Function.update_apply, show j ≠ k by omega, e3, s2a1]
    rw [hrest, xs, searchStep, ← hkdef]
    rw [show st.sc 0 = n from rfl]
    split_ifs <;> first | omega | contradiction
  · omega

/-- **The search loop**: after `n` turns the invariant holds with `i = n`, within `n (B n + 2n + 41) + 1`. -/
theorem search_loop (e : Ex) (B : ℕ → ℕ) (he : BitSpec e B) (st : St) (h4 : st.sc 4 = 0)
    (hD : ∀ j, st.ar 1 j = 0) :
    LInv st (st.sc 0) (Cmd.run (.loop 0 1 (body e)) st).1 ∧
      (Cmd.run (.loop 0 1 (body e)) st).2 ≤ st.sc 0 * (B (st.sc 0) + 2 * st.sc 0 + 41) + 1 := by
  have h0 : LInv st 0 st := ⟨rfl, h4, fun _ _ => rfl, fun j => by rw [hD j]; omega, fun j _ => hD j,
    fun _ => by simp [numCells, xs]⟩
  refine ⟨Cmd.loop_inv (LInv st) h0 (fun j s' hj hs => (loop_body e B he st j hj s' hs).1), ?_⟩
  exact Cmd.loop_cost_le (LInv st) (B (st.sc 0) + 2 * st.sc 0 + 40) h0
    (fun j s' hj hs => (loop_body e B he st j hj s' hs).1)
    (fun j s' hj hs => le_trans (loop_body e B he st j hj s' hs).2 (by omega))

/-- After the search, for `N ≥ 2` the answer bits are those of `minFac N`. -/
theorem search_result (e : Ex) (B : ℕ → ℕ) (he : BitSpec e B) (st : St) (h4 : st.sc 4 = 0)
    (hD : ∀ j, st.ar 1 j = 0) (hN : 2 ≤ numCells (st.ar 0) 1 (st.sc 0))
    (hlt : numCells (st.ar 0) 1 (st.sc 0) < 2 ^ st.sc 0) :
    numCells ((Cmd.run (.loop 0 1 (body e)) st).1.ar 1) 0 (st.sc 0) =
      (numCells (st.ar 0) 1 (st.sc 0)).minFac := by
  have h := ((search_loop e B he st h4 hD).1).2.2.2.2.2 hN
  rw [Nat.sub_self] at h
  rw [h, ← search_eq_minFac hN hlt, xs_spec _ _ (st.sc 0) le_rfl, Nat.sub_self]
  rfl

end Factoring.Aux
