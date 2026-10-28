/-
The specification of the driver for a counting `Cmd`: as `drv_run`, `drv_out`, `drv_cost`,
`drv_spec` (`DriverOut.lean`), for `drvC c` under `CSpec c B`.

* **`drvC_spec`**: on `encodeNat N` the output array holds `encodeNat (minFac N)`, within
  `200 (n + 1)^3 (B n + 1)` source steps on every input.

Not an audit surface.
-/
module

public import FactoringAux.UniDrv

@[expose] public section

namespace Factoring.Aux

open Factoring.Aux.Copied Factoring.Aux.Copied.PLib Finset Computability Factoring.Aux.Trial

/-- **The driver's run for `n ≥ 2`**: the answer bits `D`, the output cells, and the cost. -/
theorem drvC_run (c : Cmd) (B : ℕ → ℕ) (hc : CSpec c B) (xs : List Bool) (hn : 2 ≤ xs.length) :
    ∃ D : ℕ → ℕ, (∀ j, D j ≤ 1) ∧
      (2 ≤ valL xs → numCells D 0 xs.length = (valL xs).minFac) ∧
      (srcOut (drvC c) xs).ar 2 0 =
        ((range xs.length).filter (fun j => ∃ j' < xs.length, j ≤ j' ∧ D j' ≠ 0)).card ∧
      (∀ i < xs.length, (srcOut (drvC c) xs).ar 2 (i + 1) = D i) ∧
      srcCost (drvC c) xs ≤ xs.length * (B xs.length + 2 * xs.length + 41) + 4 * xs.length +
        100 * (xs.length + 1) ^ 3 + 20 := by
  set n := xs.length with hndef
  set stA := ((St.init xs).setSc 4 0).setSc 5 2 with hstA
  have hA0 : stA.sc 0 = n := by simp [stA, n]
  have hA4 : stA.sc 4 = 0 := by simp [stA]
  have hA5 : stA.sc 5 = 2 := by simp [stA]
  have hAD : ∀ j, stA.ar 1 j = 0 := fun j => by simp [stA, init_ar_ne_zero]
  have hAN : numCells (stA.ar 0) 1 (stA.sc 0) = valL xs := by
    rw [hA0]; simp [stA, numCells_startingMemory, n]
  have hrun : Cmd.run (drvC c) (St.init xs) =
      let r := Cmd.run (.seq (.loop 0 1 (bodyC c)) (.seq (.loop 0 1 cpBody)
        (.seq (Ex.comp lenEx 6 10) (.wr 2 4 0 6)))) stA
      (r.1, 1 + (1 + (r.2 + 1) + 1) + 1) := by
    simp only [drvC, Cmd.run_seq, Cmd.run_setK, Cmd.run_ifLt]
    rw [← hstA, hA0, hA5, if_neg (by omega)]
    rfl
  obtain ⟨⟨l0, l4, -, lb, -, -⟩, lc⟩ := search_loopC c B hc stA hA4 hAD
  rw [hA0] at lc
  have lres := search_resultC c B hc stA hA4 hAD
  generalize hr1 : Cmd.run (.loop 0 1 (bodyC c)) stA = r1 at l0 l4 lb lc lres
  obtain ⟨c1, c2, c3, c4⟩ := copy_loop r1.1
  generalize hr2 : Cmd.run (.loop 0 1 cpBody) r1.1 = r2 at c1 c2 c3 c4
  have w := Ex.comp_spec lenEx 6 10 r2.1 (by simp [lenEx, Ex.VB]) (by norm_num)
  simp only [Ex.Wr] at w
  obtain ⟨w1, w2, w3, w4⟩ := w
  have r20 : r2.1.sc 0 = n := by rw [c1 0 (by norm_num) (by norm_num), l0, hA0]
  have r24 : r2.1.sc 4 = 0 := by rw [c1 4 (by norm_num) (by norm_num), l4]
  have r21 : r2.1.ar 1 = r1.1.ar 1 := c2 1 (by norm_num)
  have hlen := eval_lenEx r2.1.sc r2.1.ar
  have hlc := cost_lenEx r2.1.sc r2.1.ar (fun j => by rw [r21]; exact lb j)
  rw [r20, r21] at hlen
  rw [r20] at hlc
  rw [l0, hA0] at c4
  refine ⟨r1.1.ar 1, lb, fun hN => ?_, ?_, fun i hi => ?_, ?_⟩
  · have h := lres (by rw [hAN]; exact hN) (by rw [hAN, hA0]; exact valL_lt xs)
    rw [← hAN, hA0]; exact h
  · simp only [srcOut, hrun, Cmd.run_seq, hr1, hr2, Cmd.run_wr]
    simp [w2 4 (by norm_num) (by norm_num), r24, w1, hlen]
  · simp only [srcOut, hrun, Cmd.run_seq, hr1, hr2, Cmd.run_wr]
    simp only [St.setAr_ar, Function.update_self, w2 4 (by norm_num) (by norm_num), r24, add_zero]
    rw [Function.update_of_ne (by omega), w3]
    exact c3 i (by rw [l0, hA0]; exact hi)
  · simp only [srcCost, hrun, Cmd.run_seq, hr1, hr2, Cmd.run_wr]
    omega

theorem drvC_out (c : Cmd) (B : ℕ → ℕ) (hc : CSpec c B) (N : ℕ) :
    outOf ((srcOut (drvC c) (encodeNat N)).ar 2) = encodeNat N.minFac := by
  rcases Nat.lt_or_ge N 2 with hN | hN
  · obtain rfl | rfl : N = 0 ∨ N = 1 := by omega
    · have e0 : encodeNat 0 = [] := rfl
      have e2 : encodeNat 2 = [false, true] := rfl
      rw [e0, Nat.minFac_zero, e2]
      simp [srcOut, drvC, Cmd.run_seq, Cmd.run_setK, Cmd.run_ifLt, Cmd.run_ifZero, Cmd.run_wr, outOf,
        Function.update_apply, St.init]
      exact ⟨fun h => Nat.zero_ne_one h, rfl⟩
    · have e1 : encodeNat 1 = [true] := rfl
      rw [e1, Nat.minFac_one, e1]
      simp [srcOut, drvC, Cmd.run_seq, Cmd.run_setK, Cmd.run_ifLt, Cmd.run_ifZero, Cmd.run_wr, outOf,
        Function.update_apply, St.init]
      rfl
  · obtain ⟨D, -, hD, h0, hc', -⟩ := drvC_run c B hc (encodeNat N) (two_le_length_encodeNat N hN)
    rw [valL_encodeNat] at hD
    have hD' := hD hN
    rw [← hD']
    exact outOf_bits _ D _ (by rw [hD']; exact Nat.minFac_pos N) h0 hc'

theorem drvC_cost (c : Cmd) (B : ℕ → ℕ) (hc : CSpec c B) (xs : List Bool) :
    srcCost (drvC c) xs ≤ 200 * (xs.length + 1) ^ 3 * (B xs.length + 1) := by
  set n := xs.length with hndef
  have hP : 1 ≤ (n + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  rcases Nat.lt_or_ge n 2 with hn | hn
  · have : srcCost (drvC c) xs ≤ 20 := by
      have hlt : (((St.init xs).setSc 4 0).setSc 5 2).sc 0 < (((St.init xs).setSc 4 0).setSc 5 2).sc 5 := by
        simp [St.init]; omega
      simp only [srcCost, drvC, Cmd.run_seq, Cmd.run_setK, Cmd.run_ifLt]
      rw [if_pos hlt]
      simp only [Cmd.run_ifZero, Cmd.run_seq, Cmd.run_setK, Cmd.run_wr]
      split_ifs <;> simp
    nlinarith
  · obtain ⟨-, -, -, -, -, hcst⟩ := drvC_run c B hc xs hn
    rw [← hndef] at hcst
    have hx : (n + 1) ^ 3 = n ^ 3 + 3 * n ^ 2 + 3 * n + 1 := by ring
    have h1 : n * B n ≤ (n + 1) ^ 3 * B n := Nat.mul_le_mul_right _ (by rw [hx]; omega)
    have h2 : n * (2 * n + 41) + 4 * n + 20 ≤ 100 * (n + 1) ^ 3 := by
      rw [hx]; have : n * (2 * n + 41) = 2 * n ^ 2 + 41 * n := by ring
      omega
    nlinarith

/-- **The driver's specification** for a counting command: on `encodeNat N` the output array holds
`encodeNat (minFac N)`, within `200 (n + 1)^3 (B n + 1)` source steps on every input. -/
theorem drvC_spec (c : Cmd) (B : ℕ → ℕ) (hc : CSpec c B) :
    (∀ N, outOf ((srcOut (drvC c) (encodeNat N)).ar 2) = encodeNat N.minFac) ∧
      ∀ xs, srcCost (drvC c) xs ≤ 200 * (xs.length + 1) ^ 3 * (B xs.length + 1) :=
  ⟨drvC_out c B hc, drvC_cost c B hc⟩

end Factoring.Aux
