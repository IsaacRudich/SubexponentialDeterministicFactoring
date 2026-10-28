/-
The driver's output: the value and cost of `lenEx`, the output copy loop, and the input as a number.

* `numCells_startingMemory`: the input cells hold `valL xs` (so `N` on `encodeNat N`).
* `eval_lenEx`, `cost_lenEx`: `lenEx` counts the positions `j < n` with a nonzero cell at or above `j`, within
  `100 (n + 1)^3` when the cells are bits.
* `copy_loop`: the second loop writes `D[i]` into output cell `i + 1`.

Not an audit surface.
-/
module

public import FactoringAux.DriverSpec

@[expose] public section

namespace Factoring.Aux

open Factoring.Aux.Copied Factoring.Aux.Copied.PLib Finset Computability Factoring.Aux.Trial

/-! ### The input -/

theorem numCells_of_getD : ∀ (l : List Bool) (f : ℕ → ℕ) (o : ℕ),
    (∀ j, f (o + j) = if l.getD j false then 1 else 0) → numCells f o l.length = valL l
  | [], _, _, _ => by simp [numCells]
  | b :: l, f, o, h => by
      rw [List.length_cons, numCells_succ, numCells_of_getD l f (o + 1) (fun j => by
        rw [show o + 1 + j = o + (j + 1) by ring, h]; rfl)]
      have h0 := h 0
      simp only [add_zero, List.getD_cons_zero] at h0
      rw [h0, valL_cons]
      cases b <;> simp

theorem numCells_startingMemory (xs : List Bool) : numCells (startingMemory xs) 1 xs.length = valL xs :=
  numCells_of_getD xs _ 1 fun j => by simp [startingMemory]

/-! ### `lenEx` -/

theorem eval_lenEx (σ : ℕ → ℕ) (A : ℕ → ℕ → ℕ) :
    Ex.eval σ A lenEx = ((range (σ 0)).filter (fun j => ∃ j' < σ 0, j ≤ j' ∧ A 1 j' ≠ 0)).card := by
  simp only [lenEx, Ex.eval, foldSum_eq, Nat.mod_zero]
  rw [card_filter]
  refine sum_congr rfl fun j _ => ?_
  simp only [Function.update_apply, show (0 : ℕ) ≠ 8 by norm_num,
    show (8 : ℕ) ≠ 9 by norm_num, if_false, if_true]
  congr 1
  apply propext
  rw [Nat.pos_iff_ne_zero, Ne, sum_eq_zero_iff]
  push Not
  constructor
  · rintro ⟨j', hj', hne⟩
    simp only [mem_range] at hj'
    refine ⟨j', hj', ?_, ?_⟩
    · by_contra h; exact hne (if_pos (by omega))
    · intro h0; exact hne (by simp [h0])
  · rintro ⟨j', h2, h1, h3⟩
    exact ⟨j', mem_range.mpr h2, by rw [if_neg (by omega)]; exact h3⟩

theorem cost_ifLt_le (σ : ℕ → ℕ) (A : ℕ → ℕ → ℕ) (e f u v : Ex) (K : ℕ) (hu : Ex.cost σ A u ≤ K)
    (hv : Ex.cost σ A v ≤ K) : Ex.cost σ A (.ifLt e f u v) ≤ Ex.cost σ A e + Ex.cost σ A f + K + 6 := by
  simp only [Ex.cost]; split <;> omega

theorem eval_ifLt_le (σ : ℕ → ℕ) (A : ℕ → ℕ → ℕ) (e f u v : Ex) (V : ℕ) (hu : Ex.eval σ A u ≤ V)
    (hv : Ex.eval σ A v ≤ V) : Ex.eval σ A (.ifLt e f u v) ≤ V := by
  simp only [Ex.eval]; split <;> omega

/-- A sum modulo `0` (a plain sum) whose turns cost at most `K` and have values at most `V`. -/
theorem cost_sum0_le (σ : ℕ → ℕ) (A : ℕ → ℕ → ℕ) (x : ℕ) (nE b : Ex) (K V : ℕ)
    (hK : ∀ j < Ex.eval σ A nE, Ex.cost (Function.update σ x j) A b ≤ K)
    (hV : ∀ j < Ex.eval σ A nE, Ex.eval (Function.update σ x j) A b ≤ V) :
    Ex.cost σ A (.sum x nE (.lit 0) b) ≤
      Ex.cost σ A nE + 15 + Ex.eval σ A nE * (K + 9 * V + 7 * (Ex.eval σ A nE * V) + 30) := by
  simp only [Ex.cost, Ex.eval]
  set N := Ex.eval σ A nE
  have hterm : ∀ j ∈ range N, Ex.cost (Function.update σ x j) A b + 9 * Ex.eval (Function.update σ x j) A b +
      7 * foldSum (fun i => Ex.eval (Function.update σ x i) A b) 0 j + 30 ≤
      K + 9 * V + 7 * (N * V) + 30 := by
    intro j hj
    rw [mem_range] at hj
    have h1 := hK j hj
    have h2 := hV j hj
    have h3 : foldSum (fun i => Ex.eval (Function.update σ x i) A b) 0 j ≤ N * V := by
      rw [foldSum_eq, Nat.mod_zero]
      calc ∑ i ∈ range j, Ex.eval (Function.update σ x i) A b ≤ ∑ i ∈ range j, V :=
            sum_le_sum fun i hi => hV i (by rw [mem_range] at hi; omega)
        _ = j * V := by simp
        _ ≤ N * V := Nat.mul_le_mul_right _ hj.le
    omega
  have h1 := sum_le_sum hterm
  rw [sum_const_nat (fun _ _ => rfl), card_range] at h1
  omega

theorem cost_lenEx (σ : ℕ → ℕ) (A : ℕ → ℕ → ℕ) (hA : ∀ j, A 1 j ≤ 1) :
    Ex.cost σ A lenEx ≤ 100 * (σ 0 + 1) ^ 3 := by
  set n := σ 0
  have hin : ∀ j, Ex.cost (Function.update σ 8 j) A (.sum 9 (.var 0) (.lit 0)
      (.ifLt (.var 9) (.var 8) (.lit 0) (.rd 1 (.var 9)))) ≤ 16 + n * (7 * n + 50) := by
    intro j
    have h := cost_sum0_le (Function.update σ 8 j) A 9 (.var 0)
      (.ifLt (.var 9) (.var 8) (.lit 0) (.rd 1 (.var 9))) 11 1
      (fun j' _ => cost_ifLt_le _ _ _ _ _ _ 3 (by simp [Ex.cost]) (by simp [Ex.cost]))
      (fun j' _ => eval_ifLt_le _ _ _ _ _ _ 1 (by simp [Ex.eval]) (hA _))
    have e0 : Ex.eval (Function.update σ 8 j) A (.var 0) = n := by simp [Ex.eval, n]
    have c0 : Ex.cost (Function.update σ 8 j) A (.var 0) = 1 := rfl
    rw [e0, c0] at h
    nlinarith
  have h := cost_sum0_le σ A 8 (.var 0) (.ifLt (.lit 0) (.sum 9 (.var 0) (.lit 0)
      (.ifLt (.var 9) (.var 8) (.lit 0) (.rd 1 (.var 9)))) (.lit 1) (.lit 0)) (24 + n * (7 * n + 50)) 1
    (fun j _ => le_trans (cost_ifLt_le _ _ _ _ _ _ 1 (by simp [Ex.cost]) (by simp [Ex.cost]))
      (by have := hin j; simp only [Ex.cost] at this ⊢; omega))
    (fun j _ => eval_ifLt_le _ _ _ _ _ _ 1 (by simp [Ex.eval]) (by simp [Ex.eval]))
  have e0 : Ex.eval σ A (.var 0) = n := rfl
  have c0 : Ex.cost σ A (.var 0) = 1 := rfl
  rw [e0, c0] at h
  show Ex.cost σ A lenEx ≤ _
  refine le_trans h ?_
  nlinarith

/-! ### The output copy loop -/

/-- The copy body: output cell `i + 1` := `D[i]`. -/
def cpBody : Cmd := .seq (.rd 5 1 1 0) (.wr 2 1 1 5)

theorem copy_loop (st : St) :
    (∀ y, y ≠ 1 → y ≠ 5 → (Cmd.run (.loop 0 1 cpBody) st).1.sc y = st.sc y) ∧
    (∀ a, a ≠ 2 → (Cmd.run (.loop 0 1 cpBody) st).1.ar a = st.ar a) ∧
    (∀ i < st.sc 0, (Cmd.run (.loop 0 1 cpBody) st).1.ar 2 (i + 1) = st.ar 1 i) ∧
    (Cmd.run (.loop 0 1 cpBody) st).2 ≤ 4 * st.sc 0 + 1 := by
  let P : ℕ → St → Prop := fun j s => (∀ y, y ≠ 1 → y ≠ 5 → s.sc y = st.sc y) ∧
    (∀ a, a ≠ 2 → s.ar a = st.ar a) ∧ (∀ i < j, s.ar 2 (i + 1) = st.ar 1 i)
  have h0 : P 0 st := ⟨fun _ _ _ => rfl, fun _ _ => rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  have hstep : ∀ j s, j < st.sc 0 → P j s → P (j + 1) (Cmd.run cpBody (s.setSc 1 j)).1 := by
    intro j s _ ⟨p1, p2, p3⟩
    have r1 : (s.setSc 1 j).ar 1 j = st.ar 1 j := by simp [p2 1 (by norm_num)]
    simp only [cpBody, Cmd.run_seq, Cmd.run_rd, Cmd.run_wr]
    refine ⟨fun y h1 h5 => ?_, fun a ha => ?_, fun i hi => ?_⟩
    · simp [h1, h5, p1 y h1 h5]
    · simp [ha, p2 a ha]
    · simp only [St.setAr_ar, Function.update_self, St.setSc_sc, Function.update_apply, St.setSc_ar,
        add_zero]
      simp only [show (1 : ℕ) ≠ 5 by norm_num, if_false] at *
      by_cases hij : i = j
      · subst hij; simp [p2 1 (by norm_num)]
      · rw [if_neg (by omega)]; exact p3 i (by omega)
  obtain ⟨q1, q2, q3⟩ := Cmd.loop_inv P h0 hstep
  refine ⟨q1, q2, q3, ?_⟩
  have := Cmd.loop_cost_le P 3 h0 hstep (fun j s _ _ => by simp [cpBody, Cmd.run_seq, Cmd.run_rd, Cmd.run_wr])
  omega

/-! ### The driver for `n ≥ 2` -/

theorem init_ar_ne_zero (xs : List Bool) (a : ℕ) (ha : a ≠ 0) (i : ℕ) : (St.init xs).ar a i = 0 := by
  simp [St.init, ha]

/-- **The driver's run for `n ≥ 2`**: the answer bits `D`, the output cells, and the cost. -/
theorem drv_run (e : Ex) (B : ℕ → ℕ) (he : BitSpec e B) (xs : List Bool) (hn : 2 ≤ xs.length) :
    ∃ D : ℕ → ℕ, (∀ j, D j ≤ 1) ∧
      (2 ≤ valL xs → numCells D 0 xs.length = (valL xs).minFac) ∧
      (srcOut (drv e) xs).ar 2 0 =
        ((range xs.length).filter (fun j => ∃ j' < xs.length, j ≤ j' ∧ D j' ≠ 0)).card ∧
      (∀ i < xs.length, (srcOut (drv e) xs).ar 2 (i + 1) = D i) ∧
      srcCost (drv e) xs ≤ xs.length * (B xs.length + 2 * xs.length + 41) + 4 * xs.length +
        100 * (xs.length + 1) ^ 3 + 20 := by
  set n := xs.length with hndef
  set stA := ((St.init xs).setSc 4 0).setSc 5 2 with hstA
  have hA0 : stA.sc 0 = n := by simp [stA, n]
  have hA4 : stA.sc 4 = 0 := by simp [stA]
  have hA5 : stA.sc 5 = 2 := by simp [stA]
  have hAD : ∀ j, stA.ar 1 j = 0 := fun j => by simp [stA, init_ar_ne_zero]
  have hAN : numCells (stA.ar 0) 1 (stA.sc 0) = valL xs := by
    rw [hA0]; simp [stA, numCells_startingMemory, n]
  have hrun : Cmd.run (drv e) (St.init xs) =
      let r := Cmd.run (.seq (.loop 0 1 (body e)) (.seq (.loop 0 1 cpBody)
        (.seq (Ex.comp lenEx 6 10) (.wr 2 4 0 6)))) stA
      (r.1, 1 + (1 + (r.2 + 1) + 1) + 1) := by
    simp only [drv, Cmd.run_seq, Cmd.run_setK, Cmd.run_ifLt]
    rw [← hstA, hA0, hA5, if_neg (by omega)]
    rfl
  obtain ⟨⟨l0, l4, la, lb, -, lv⟩, lc⟩ := search_loop e B he stA hA4 hAD
  rw [hA0] at lc
  have lres := search_result e B he stA hA4 hAD
  generalize hr1 : Cmd.run (.loop 0 1 (body e)) stA = r1 at l0 l4 la lb lv lc lres
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

/-! ### The driver's specification -/

theorem two_le_length_encodeNat (N : ℕ) (hN : 2 ≤ N) : 2 ≤ (encodeNat N).length := by
  have h := lt_two_pow_length N
  by_contra hc
  have : 2 ^ (encodeNat N).length ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-- The output for `n ≥ 2`: the cells hold the bits of `p = numCells D 0 n`, and cell `0` the length of
`encodeNat p`. -/
theorem outOf_bits (μ D : ℕ → ℕ) (n : ℕ) (hp : 0 < numCells D 0 n)
    (h0 : μ 0 = ((range n).filter (fun j => ∃ j' < n, j ≤ j' ∧ D j' ≠ 0)).card)
    (hc : ∀ i < n, μ (i + 1) = D i) :
    outOf μ = encodeNat (numCells D 0 n) := by
  set p := numCells D 0 n
  have hpn : p < 2 ^ n := numCells_lt D 0 n
  have hlen : (encodeNat p).length = μ 0 := by
    rw [length_encodeNat_eq p n hp hpn, h0]
    congr 1
    refine filter_congr fun j _ => ?_
    rw [two_pow_le_iff p n j hpn]
    constructor
    · rintro ⟨j', h1, h2, h3⟩
      refine ⟨j', h2, h1, ?_⟩
      rw [testBit_numCells D n 0 j' h2] at h3
      simpa using h3
    · rintro ⟨j', h2, h1, h3⟩
      refine ⟨j', h1, h2, ?_⟩
      rw [testBit_numCells D n 0 j' h2]
      simpa using h3
  have hle : μ 0 ≤ n := by rw [h0]; exact le_trans (card_filter_le _ _) (by simp)
  rw [encodeNat_eq_bitsW p, bitsW_eq_ofFn, hlen]
  unfold outOf
  congr 1
  funext i
  rw [hc i (by omega), testBit_numCells D n 0 i (by omega), zero_add]

theorem drv_out (e : Ex) (B : ℕ → ℕ) (he : BitSpec e B) (N : ℕ) :
    outOf ((srcOut (drv e) (encodeNat N)).ar 2) = encodeNat N.minFac := by
  rcases Nat.lt_or_ge N 2 with hN | hN
  · obtain rfl | rfl : N = 0 ∨ N = 1 := by omega
    · have e0 : encodeNat 0 = [] := rfl
      have e2 : encodeNat 2 = [false, true] := rfl
      rw [e0, Nat.minFac_zero, e2]
      simp [srcOut, drv, Cmd.run_seq, Cmd.run_setK, Cmd.run_ifLt, Cmd.run_ifZero, Cmd.run_wr, outOf,
        Function.update_apply, St.init]
      exact ⟨fun h => Nat.zero_ne_one h, rfl⟩
    · have e1 : encodeNat 1 = [true] := rfl
      rw [e1, Nat.minFac_one, e1]
      simp [srcOut, drv, Cmd.run_seq, Cmd.run_setK, Cmd.run_ifLt, Cmd.run_ifZero, Cmd.run_wr, outOf,
        Function.update_apply, St.init]
      rfl
  · obtain ⟨D, -, hD, h0, hc, -⟩ := drv_run e B he (encodeNat N) (two_le_length_encodeNat N hN)
    rw [valL_encodeNat] at hD
    have hD' := hD hN
    rw [← hD']
    exact outOf_bits _ D _ (by rw [hD']; exact Nat.minFac_pos N) h0 hc

theorem drv_cost (e : Ex) (B : ℕ → ℕ) (he : BitSpec e B) (xs : List Bool) :
    srcCost (drv e) xs ≤ 200 * (xs.length + 1) ^ 3 * (B xs.length + 1) := by
  set n := xs.length with hndef
  have hP : 1 ≤ (n + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  rcases Nat.lt_or_ge n 2 with hn | hn
  · have : srcCost (drv e) xs ≤ 20 := by
      have hlt : (((St.init xs).setSc 4 0).setSc 5 2).sc 0 < (((St.init xs).setSc 4 0).setSc 5 2).sc 5 := by
        simp [St.init]; omega
      simp only [srcCost, drv, Cmd.run_seq, Cmd.run_setK, Cmd.run_ifLt]
      rw [if_pos hlt]
      simp only [Cmd.run_ifZero, Cmd.run_seq, Cmd.run_setK, Cmd.run_wr]
      split_ifs <;> simp
    nlinarith
  · obtain ⟨-, -, -, -, -, hc⟩ := drv_run e B he xs hn
    rw [← hndef] at hc
    have hx : (n + 1) ^ 3 = n ^ 3 + 3 * n ^ 2 + 3 * n + 1 := by ring
    have h1 : n * B n ≤ (n + 1) ^ 3 * B n := Nat.mul_le_mul_right _ (by rw [hx]; omega)
    have h2 : n * (2 * n + 41) + 4 * n + 20 ≤ 100 * (n + 1) ^ 3 := by
      rw [hx]; have : n * (2 * n + 41) = 2 * n ^ 2 + 41 * n := by ring
      omega
    nlinarith

/-- **The driver's specification**: on `encodeNat N` the output array holds `encodeNat (minFac N)`, within
`200 (n + 1)^3 (B n + 1)` source steps on every input. -/
theorem drv_spec (e : Ex) (B : ℕ → ℕ) (he : BitSpec e B) :
    (∀ N, outOf ((srcOut (drv e) (encodeNat N)).ar 2) = encodeNat N.minFac) ∧
      ∀ xs, srcCost (drv e) xs ≤ 200 * (xs.length + 1) ^ 3 * (B xs.length + 1) :=
  ⟨drv_out e B he, drv_cost e B he⟩

end Factoring.Aux
