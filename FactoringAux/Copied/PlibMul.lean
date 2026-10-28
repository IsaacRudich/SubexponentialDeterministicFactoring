/-
Adapted from the authors' related work (the whole file).

Not an audit surface.
-/
/-
PLIB, part 6: multiplication and division of numbers held in arrays.

A number `N` is **held** by an array at width `L` (`Holds f L N`) when `N < 2^L`
and cells `0 … L-1` are its bits, little-endian (`bitOf N j = N / 2^j % 2`).
The bit-serial scans of `PrimeBits` (add, subtract, compare,
shift, all in place on cells `0 … L-1`) are the primitives.

* `mulSeg`: `C := A * B` at width `2L`, by shift-and-add (`run_mulSeg`).

Not an audit surface.
-/
module

public import FactoringAux.Copied.PrimeBits
public import FactoringAux.Copied.PlibFn

@[expose] public section

namespace Factoring.Aux.Copied.PLib

open Factoring.Aux.Copied Factoring.Aux.Copied.Aux Cmd

/-! ### Numbers held by arrays -/

/-- Array `f` holds `N` at width `L`. -/
def Holds (f : ℕ → ℕ) (L N : ℕ) : Prop := N < 2 ^ L ∧ ∀ j < L, f j = bitOf N j

theorem Holds.segBits {f : ℕ → ℕ} {L N : ℕ} (h : Holds f L N) : SegBits f 0 L :=
  fun j hj => by rw [zero_add, h.2 j hj]; exact bitOf_le_one _ _

theorem Holds.segVal_eq {f : ℕ → ℕ} {L N : ℕ} (h : Holds f L N) : segVal f 0 L = N := by
  have e : segVal f 0 L = segVal (segPut f 0 L (bitOf N)) 0 L :=
    segVal_congr (fun j hj => by simp [segPut, h.2 j hj])
  rw [e, segVal_segPut_bits, Nat.mod_eq_of_lt h.1]

theorem holds_segPut (f : ℕ → ℕ) {L N : ℕ} (hN : N < 2 ^ L) : Holds (segPut f 0 L (bitOf N)) L N :=
  ⟨hN, fun j hj => by simp [segPut, hj]⟩

theorem Holds.segPut_eq {f : ℕ → ℕ} {L N : ℕ} (h : Holds f L N) : segPut f 0 L (bitOf N) = f := by
  funext i; simp only [segPut]; split_ifs with hi
  · rw [h.2 i (by omega)]; simp
  · rfl

theorem segPut_segPut (f : ℕ → ℕ) (L : ℕ) (g g' : ℕ → ℕ) :
    segPut (segPut f 0 L g) 0 L g' = segPut f 0 L g' := by
  funext i; simp only [segPut]; split_ifs <;> rfl

theorem bitOf_eq_zero_of_lt {N j : ℕ} (h : N < 2 ^ j) : bitOf N j = 0 := by
  unfold bitOf; rw [Nat.div_eq_of_lt h]

/-- Bit `j` of `y` and the residues `y mod 2^j`. -/
theorem mod_two_pow_succ (y j : ℕ) : y % 2 ^ (j + 1) = y % 2 ^ j + bitOf y j * 2 ^ j := by
  unfold bitOf
  rw [pow_succ, Nat.mod_mul, Nat.mul_comm (y / 2 ^ j % 2)]

/-! ### One turn of shift-and-add -/

/-- One turn: if bit `i` of `B` is set, `C := C + T`; then `T := 2 T`.  Width `L2`. -/
def mulBody (C T B L2 i u c cnt x y w : ℕ) : Cmd :=
  seqs [.rd u B i 0, .ifZero u .skip (scanSeg C T L2 c cnt x y w (addStep x y c w)), .setK c 0,
    scanSeg T C L2 c cnt x y w (shlStep x c w), .setK c 0, .setK u 0]

theorem run_mulBody {C T B L2 i u c cnt x y w : ℕ} (hCT : C ≠ T) (hBC : B ≠ C) (hBT : B ≠ T)
    (h : [L2, i, u, c, cnt, x, y, w].Nodup) (σ : St) {n XC XT : ℕ}
    (hn : σ.sc L2 = n) (hC : Holds (σ.ar C) n XC) (hT : Holds (σ.ar T) n XT) (hc : σ.sc c = 0)
    (hb : σ.ar B (σ.sc i) ≤ 1) (hsum : XC + σ.ar B (σ.sc i) * XT < 2 ^ n) (h2 : 2 * XT < 2 ^ n) :
    (Cmd.run (mulBody C T B L2 i u c cnt x y w) σ).1
      = (((σ.putAr C (segPut (σ.ar C) 0 n (bitOf (XC + σ.ar B (σ.sc i) * XT)))).putAr T
          (segPut (σ.ar T) 0 n (bitOf (2 * XT))))).zeros [u, c, cnt, x, y, w] ∧
    (Cmd.run (mulBody C T B L2 i u c cnt x y w) σ).2 ≤ 80 * (n + 1) + 40 := by
  have hn' := h
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hn'
  obtain ⟨⟨a1, a2, a3, a4, a5, a6, a7⟩, ⟨b1, b2, b3, b4, b5, b6⟩, ⟨c1, c2, c3, c4, c5⟩,
    ⟨d1, d2, d3, d4⟩, ⟨e1, e2, e3⟩, ⟨f1, f2⟩, g1, -⟩ := hn'
  symm_ne
  have hsc : [L2, c, cnt, x, y, w].Nodup := by nodup_tac
  have hCb := hC.segBits
  have hTb := hT.segBits
  have hCv := hC.segVal_eq
  have hTv := hT.segVal_eq
  -- the add, from any state agreeing with `σ` on what it reads
  have hadd := fun τ (hτC : τ.ar C = σ.ar C) (hτT : τ.ar T = σ.ar T) (hτn : τ.sc L2 = n)
      (hτc : τ.sc c = 0) => run_addSeg (a := C) (b := T) (L := L2) (c := c) (cnt := cnt) (x := x)
      (y := y) (w := w) hCT hsc τ (by rw [hτC, hτn]; exact hCb) (by rw [hτT, hτn]; exact hTb)
      (by rw [hτc]; omega)
  have hshl := fun τ (hτT : SegBits (τ.ar T) 0 (τ.sc L2)) (hτc : τ.sc c = 0) =>
      run_shlSeg (a := T) (b := C) (L := L2) (c := c) (cnt := cnt) (x := x)
      (y := y) (w := w) (Ne.symm hCT) hsc τ hτT (by rw [hτc]; omega)
  simp only [mulBody, Cmd.run_seqs_cons, Cmd.run_seqs_nil, Cmd.run_rd, Cmd.run_setK, Cmd.run_ifZero,
    Cmd.run_skip, Nat.add_zero]
  by_cases hb0 : σ.ar B (σ.sc i) = 0
  · simp only [St.setSc_sc_self, hb0, if_true]
    set τ := (σ.setSc u 0).setSc c 0 with hτ
    have hτT : τ.ar T = σ.ar T := rfl
    have hτn : τ.sc L2 = n := by simp [τ, *]
    obtain ⟨e1, c1⟩ := hshl τ (by rw [hτT, hτn]; exact hTb) (by simp [τ])
    rw [e1]
    have hτc : τ.sc c = 0 := by simp [τ]
    constructor
    · rw [hτT, hτn, hτc, hTv, Nat.add_zero, Nat.div_eq_of_lt h2, zero_mul, add_zero, hC.segPut_eq]
      simp only [τ]; clear hadd hshl e1 c1; st_eq [St.zeros]
    · rw [hτn] at c1; omega
  · have hb1 : σ.ar B (σ.sc i) = 1 := by omega
    simp only [St.setSc_sc_self, hb1, if_false, one_ne_zero]
    set τ := σ.setSc u 1 with hτ
    obtain ⟨e1, c1⟩ := hadd τ rfl rfl (by simp [τ, *]) (by simp [τ, *])
    rw [e1]
    have hS : XC + XT < 2 ^ n := by rw [hb1, one_mul] at hsum; exact hsum
    have hτn : τ.sc L2 = n := by simp [τ, *]
    have hτc : τ.sc c = 0 := by simp [τ, *]
    rw [show τ.ar C = σ.ar C from rfl, show τ.ar T = σ.ar T from rfl, hτn, hτc, hCv, hTv, add_zero,
      Nat.div_eq_of_lt hS]
    set τ2 := ((((((τ.putAr C (segPut (σ.ar C) 0 n (bitOf (XC + XT)))).setSc c 0).setSc x 0).setSc y
      0).setSc w 0).setSc cnt 0).setSc c 0 with hτ2
    have hτ2T : τ2.ar T = σ.ar T := by simp [τ2, τ, Ne.symm hCT]
    have hτ2n : τ2.sc L2 = n := by simp [τ2, τ, *]
    have hτ2c : τ2.sc c = 0 := by simp [τ2]
    obtain ⟨e2, c2⟩ := hshl τ2 (by rw [hτ2T, hτ2n]; exact hTb) hτ2c
    rw [e2, hτ2T, hτ2n, hτ2c, hTv, add_zero, Nat.div_eq_of_lt h2]
    constructor
    · rw [one_mul]; simp only [τ2, τ]; clear hadd hshl e1 e2 c1 c2 hCb hTb hCv hTv hC hT hsum h2 hS hb hb1 hb0 hc hn hτ2T hτ2n hτ2c
      ext z
      · simp only [St.setSc_sc, St.setSc_ar, St.putAr_sc,
          St.putAr_ar, St.zeros_cons, St.zeros_nil]
        sc_split z [u, c, cnt, x, y, w]
      · simp only [St.setSc_sc, St.setSc_ar, St.putAr_sc,
          St.putAr_ar, St.zeros_cons, St.zeros_nil]
    · rw [hτn] at c1; rw [hτ2n] at c2; omega

/-! ### Multiplication -/

/-- `C := A * B` at width `2L` (`A`, `B` at width `L`); `T` is a scratch array.
Scalars: `L` the width (kept), sixteen scratch. -/
def mulSeg (C T A B L L2 i u c cnt x y w z z' p q v t : ℕ) : Cmd :=
  .seq (seqs [.setK z 0, .setK z' 0, .copy L2 L, addTo L2 L t,
    fillSeg C z L2 z' cnt p, fillSeg T z L2 z' cnt p, copySeg T z A z' L cnt p q v,
    .setK c 0, .setK u 0, .setK x 0, .setK y 0, .setK w 0])
  (seqs [.loop L i (mulBody C T B L2 i u c cnt x y w), .setK i 0, .setK L2 0])

theorem segFill_zero (f : ℕ → ℕ) (n : ℕ) : segFill f 0 n 0 = segPut f 0 n (bitOf 0) := by
  funext r; simp [segFill, segPut, bitOf]

theorem segCopy_fill (f g : ℕ → ℕ) (L X : ℕ) (hg : Holds g L X) :
    segCopy (segFill f 0 (L + L) 0) g 0 0 L = segPut f 0 (L + L) (bitOf X) := by
  funext r
  simp only [segCopy, segFill, segPut, zero_add, Nat.sub_zero]
  by_cases h1 : r < L
  · rw [if_pos ⟨by omega, h1⟩, if_pos ⟨by omega, by omega⟩, hg.2 r h1]
  · rw [if_neg (by omega)]
    by_cases h2 : r < L + L
    · rw [if_pos ⟨by omega, h2⟩, if_pos ⟨by omega, h2⟩,
        bitOf_eq_zero_of_lt (lt_of_lt_of_le hg.1 (Nat.pow_le_pow_right (by norm_num) (by omega)))]
    · rw [if_neg (by omega), if_neg (by omega)]

theorem mul_mod_lt {X Y L j : ℕ} (hX : X < 2 ^ L) (hj : j ≤ L) : X * (Y % 2 ^ j) < 2 ^ (L + L) := by
  rw [pow_add]
  have h1 : Y % 2 ^ j < 2 ^ L := lt_of_lt_of_le (Nat.mod_lt _ (by positivity))
    (Nat.pow_le_pow_right (by norm_num) hj)
  calc X * (Y % 2 ^ j) ≤ X * 2 ^ L := Nat.mul_le_mul_left _ h1.le
    _ < 2 ^ L * 2 ^ L := Nat.mul_lt_mul_of_pos_right hX (by positivity)

theorem mul_pow_lt {X L j : ℕ} (hX : X < 2 ^ L) (hj : j ≤ L) : X * 2 ^ j < 2 ^ (L + L) := by
  rw [pow_add]
  calc X * 2 ^ j ≤ X * 2 ^ L := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hj)
    _ < 2 ^ L * 2 ^ L := Nat.mul_lt_mul_of_pos_right hX (by positivity)

/-- **Multiplication.** -/
theorem run_mulSeg {C T A B L L2 i u c cnt x y w z z' p q v t : ℕ} (hCT : C ≠ T) (hAC : A ≠ C)
    (hAT : A ≠ T) (hBC : B ≠ C) (hBT : B ≠ T)
    (h : [L, L2, i, u, c, cnt, x, y, w, z, z', p, q, v, t].Nodup) (st : St) {X Y : ℕ}
    (hA : Holds (st.ar A) (st.sc L) X) (hB : Holds (st.ar B) (st.sc L) Y) :
    (Cmd.run (mulSeg C T A B L L2 i u c cnt x y w z z' p q v t) st).1
      = ((st.putAr C (segPut (st.ar C) 0 (st.sc L + st.sc L) (bitOf (X * Y)))).putAr T
          (segPut (st.ar T) 0 (st.sc L + st.sc L) (bitOf (X * 2 ^ st.sc L)))).zeros
          [L2, i, u, c, cnt, x, y, w, z, z', p, q, v, t] ∧
    (Cmd.run (mulSeg C T A B L L2 i u c cnt x y w z z' p q v t) st).2
      ≤ 200 * (st.sc L + 1) * (st.sc L + 1) := by
  have hn' := h
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hn'
  obtain ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14⟩,
    ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13⟩,
    ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12⟩, ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11⟩,
    ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩, ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9⟩,
    ⟨g1, g2, g3, g4, g5, g6, g7, g8⟩, ⟨i1, i2, i3, i4, i5, i6, i7⟩, ⟨j1, j2, j3, j4, j5, j6⟩,
    ⟨k1, k2, k3, k4, k5⟩, ⟨l1, l2, l3, l4⟩, ⟨m1, m2, m3⟩, ⟨n1, n2⟩, o1, -⟩ := hn'
  symm_ne
  set nL := st.sc L with hnL
  have hf1 := fun σ => (run_fillSeg (b := C) (ob := z) (n := L2) (val := z') (c := cnt) (q := p)
    (by nodup_tac) σ).1
  have hf2 := fun σ => (run_fillSeg (b := T) (ob := z) (n := L2) (val := z') (c := cnt) (q := p)
    (by nodup_tac) σ).1
  have hcp := fun σ => (run_copySeg (b := T) (ob := z) (a := A) (oa := z') (n := L) (c := cnt) (p := p)
    (q := q) (v := v) hAT (by nodup_tac) σ).1
  have had := fun σ => (run_addTo (x := L2) (y := L) (t := t) (by nodup_tac) σ).1
  have hf1c := fun σ => (run_fillSeg (b := C) (ob := z) (n := L2) (val := z') (c := cnt) (q := p)
    (by nodup_tac) σ).2
  have hf2c := fun σ => (run_fillSeg (b := T) (ob := z) (n := L2) (val := z') (c := cnt) (q := p)
    (by nodup_tac) σ).2
  have hcpc := fun σ => (run_copySeg (b := T) (ob := z) (a := A) (oa := z') (n := L) (c := cnt) (p := p)
    (q := q) (v := v) hAT (by nodup_tac) σ).2
  have hadc := fun σ => (run_addTo (x := L2) (y := L) (t := t) (by nodup_tac) σ).2
  set st1 := (((st.zeros [z, z', t, cnt, p, q, v, c, u, x, y, w]).setSc L2 (nL + nL)).putAr C
    (segPut (st.ar C) 0 (nL + nL) (bitOf 0))).putAr T (segPut (st.ar T) 0 (nL + nL) (bitOf X))
    with hst1
  have hpre : (Cmd.run (seqs [.setK z 0, .setK z' 0, .copy L2 L, addTo L2 L t,
      fillSeg C z L2 z' cnt p, fillSeg T z L2 z' cnt p, copySeg T z A z' L cnt p q v,
      .setK c 0, .setK u 0, .setK x 0, .setK y 0, .setK w 0]) st).1 = st1 := by
    simp only [Cmd.run_seqs_cons, Cmd.run_seqs_nil, Cmd.run_setK, Cmd.run_copy, had, hf1, hf2, hcp]
    clear hf1 hf2 hcp had
    ext r
    · simp only [St.setSc_sc, St.setSc_ar, St.putAr_sc, St.putAr_ar, St.zeros_cons, St.zeros_nil, st1]
      sc_split r [z, z', t, cnt, p, q, v, c, u, x, y, w, L2]
    · simp only [St.setSc_sc, St.setSc_ar, St.putAr_sc, St.putAr_ar, St.zeros_cons, St.zeros_nil, st1,
        Function.update_apply]
      by_cases hrT : r = T
      · subst hrT
        simp only [if_true, if_neg hCT.symm, if_neg hAT, Ne.symm hCT]
        simp [Function.update_apply, *]
        rw [segCopy_fill _ _ _ _ hA]
      · by_cases hrC : r = C
        · subst hrC; simp [Function.update_apply, *]
          rw [segFill_zero]
        · simp [*]
  have hprec : (Cmd.run (seqs [.setK z 0, .setK z' 0, .copy L2 L, addTo L2 L t,
      fillSeg C z L2 z' cnt p, fillSeg T z L2 z' cnt p, copySeg T z A z' L cnt p q v,
      .setK c 0, .setK u 0, .setK x 0, .setK y 0, .setK w 0]) st).2 ≤ 40 * nL + 120 := by
    simp only [Cmd.run_seqs_cons, Cmd.run_seqs_nil, Cmd.run_setK, Cmd.run_copy, had, hf1, hf2, hcp,
      hadc, hf1c, hf2c, hcpc]
    clear hf1 hf2 hcp had hadc hf1c hf2c hcpc
    simp [Function.update_apply, *]
    clear_ne
    omega
  clear hf1 hf2 hcp had hadc hf1c hf2c hcpc
  let E : ℕ → St := fun j => (((st1.setSc i 0).putAr C (segPut (st.ar C) 0 (nL + nL)
    (bitOf (X * (Y % 2 ^ j))))).putAr T (segPut (st.ar T) 0 (nL + nL) (bitOf (X * 2 ^ j))))
  have hE0 : st1.setSc i 0 = E 0 := by
    simp only [E, pow_zero, Nat.mod_one, mul_zero, mul_one, st1]
    st_eq
  have hst1L : st1.sc L = nL := by simp [st1, *]
  have hbody := fun σ {n XC XT : ℕ} (hn : σ.sc L2 = n) (hC : Holds (σ.ar C) n XC)
      (hT : Holds (σ.ar T) n XT) (hc : σ.sc c = 0) (hb : σ.ar B (σ.sc i) ≤ 1)
      (hsum : XC + σ.ar B (σ.sc i) * XT < 2 ^ n) (h2 : 2 * XT < 2 ^ n) =>
    run_mulBody (C := C) (T := T) (B := B) (L2 := L2) (i := i) (u := u) (c := c) (cnt := cnt) (x := x)
      (y := y) (w := w) hCT hBC hBT (by nodup_tac) σ hn hC hT hc hb hsum h2
  have hboth : ∀ j, j < st1.sc L → (Cmd.run (mulBody C T B L2 i u c cnt x y w)
      ((E j).setSc i j)).1.setSc i 0 = E (j + 1) ∧
      (Cmd.run (mulBody C T B L2 i u c cnt x y w) ((E j).setSc i j)).2 ≤ 80 * (nL + nL + 1) + 40 := by
    intro j hj
    rw [hst1L] at hj
    have hbj : st.ar B j = bitOf Y j := hB.2 j hj
    have hσB : ((E j).setSc i j).ar B (((E j).setSc i j).sc i) = bitOf Y j := by
      simp [E, st1, *]
    have hsumeq : X * (Y % 2 ^ j) + bitOf Y j * (X * 2 ^ j) = X * (Y % 2 ^ (j + 1)) := by
      rw [mod_two_pow_succ]; ring
    have h2eq : 2 * (X * 2 ^ j) = X * 2 ^ (j + 1) := by ring
    obtain ⟨e, ec⟩ := hbody ((E j).setSc i j) (n := nL + nL) (XC := X * (Y % 2 ^ j)) (XT := X * 2 ^ j)
      (by simp [E, st1, *])
      (by simp only [E, St.setSc_ar, St.putAr_ar_ne _ _ hCT, St.putAr_ar_self]
          exact holds_segPut _ (mul_mod_lt hA.1 hj.le))
      (by simp only [E, St.setSc_ar, St.putAr_ar_self]
          exact holds_segPut _ (mul_pow_lt hA.1 hj.le))
      (by simp [E, st1, *])
      (by rw [hσB]; exact bitOf_le_one _ _)
      (by rw [hσB, hsumeq]; exact mul_mod_lt hA.1 (by omega))
      (by rw [h2eq]; exact mul_pow_lt hA.1 (by omega))
    refine ⟨?_, ec⟩
    rw [e, hσB, hsumeq, h2eq]
    simp only [E, St.setSc_ar, St.putAr_ar_ne _ _ hCT, St.putAr_ar_self, segPut_segPut]
    clear e hbody ec
    ext r
    · simp only [St.setSc_sc, St.setSc_ar, St.putAr_sc, St.putAr_ar, St.zeros_cons, St.zeros_nil]
      sc_split r [i, u, c, cnt, x, y, w]
    · simp only [St.setSc_sc, St.setSc_ar, St.putAr_sc, St.putAr_ar, St.zeros_cons, St.zeros_nil,
        Function.update_apply]
      split_ifs <;> simp_all
  have e := loop_exact (st := st1) E hE0 (fun j hj => (hboth j hj).1)
  rw [hst1L] at e
  have ec := loop_exact_cost (st := st1) E _ hE0 (fun j hj => (hboth j hj).1) (fun j hj => (hboth j hj).2)
  rw [hst1L] at ec
  refine ⟨?_, ?_⟩
  swap
  · simp only [mulSeg, Cmd.run_seq]
    rw [hpre]
    generalize (Cmd.run (seqs [.setK z 0, .setK z' 0, .copy L2 L, addTo L2 L t,
      fillSeg C z L2 z' cnt p, fillSeg T z L2 z' cnt p, copySeg T z A z' L cnt p q v,
      .setK c 0, .setK u 0, .setK x 0, .setK y 0, .setK w 0]) st).2 = P at hprec ⊢
    simp only [Cmd.run_seqs_cons, Cmd.run_seqs_nil, Cmd.run_setK]
    have h3 : nL * (80 * (nL + nL + 1) + 40 + 1) = 160 * (nL * nL) + 121 * nL := by ring
    have h4 : 200 * (nL + 1) * (nL + 1) = 200 * (nL * nL) + 400 * nL + 200 := by ring
    rw [h4]
    rw [h3] at ec
    omega
  simp only [mulSeg, Cmd.run_seq]
  rw [hpre]
  simp only [Cmd.run_seqs_cons, Cmd.run_seqs_nil, Cmd.run_setK]
  rw [e]
  simp only [E, Nat.mod_eq_of_lt hB.1, st1]
  clear e hboth hE0 hpre hprec ec
  ext r
  · simp only [St.setSc_sc, St.setSc_ar, St.putAr_sc, St.putAr_ar, St.zeros_cons, St.zeros_nil]
    sc_split r [L2, i, u, c, cnt, x, y, w, z, z', p, q, v, t]
  · simp only [St.setSc_sc, St.setSc_ar, St.putAr_sc, St.putAr_ar, St.zeros_cons, St.zeros_nil,
      Function.update_apply]
    split_ifs <;> rfl

/-! ### Division with remainder -/

theorem div_two_pow_step (X m : ℕ) : X / 2 ^ m = 2 * (X / 2 ^ (m + 1)) + bitOf X m := by
  unfold bitOf
  rw [pow_succ, ← Nat.div_div_eq_div_mul]
  omega

theorem divmod_step {a b D : ℕ} (hD : 0 < D) (hb : b ≤ 1) :
    (2 * a + b) / D = 2 * (a / D) + (if D ≤ 2 * (a % D) + b then 1 else 0) ∧
    (2 * a + b) % D = if D ≤ 2 * (a % D) + b then 2 * (a % D) + b - D else 2 * (a % D) + b := by
  have hr := Nat.mod_lt a hD
  have hqr := Nat.div_add_mod a D
  set q := a / D
  set r := a % D
  split_ifs with h
  · have e2 : 2 * a + b = D * (2 * q + 1) + (2 * r + b - D) := by
      have : D * (2 * q + 1) = 2 * (D * q) + D := by ring
      omega
    have hlt : 2 * r + b - D < D := by omega
    constructor
    · rw [e2, Nat.mul_add_div hD, Nat.div_eq_of_lt hlt, Nat.add_zero]
    · rw [e2, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]
  · have e : 2 * a + b = D * (2 * q) + (2 * r + b) := by
      have : D * (2 * q) = 2 * (D * q) := by ring
      omega
    have hlt : 2 * r + b < D := by omega
    constructor
    · rw [e, Nat.mul_add_div hD, Nat.div_eq_of_lt hlt]
    · rw [e, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]

/-- One turn of long division: bring down bit `A[kk-1]` into `R`, subtract `Dx` if
it fits, and shift the quotient bit into `Q`. -/
def divBody (A R Dx Q L L1 kk c qb cnt x y w : ℕ) : Cmd :=
  seqs [.decr kk, .rd c A kk 0,
    scanSeg R Dx L1 c cnt x y w (shlStep x c w), .setK c 0,
    scanSeg R Dx L1 c cnt x y w (ltStep x y c w),
    .ifZero c (seqs [scanSeg R Dx L1 c cnt x y w (subStep x y c w), .setK qb 1]) (.setK qb 0),
    .copy c qb,
    scanSeg Q R L c cnt x y w (shlStep x c w), .setK c 0, .setK qb 0]

theorem run_divBody {A R Dx Q L L1 kk c qb cnt x y w : ℕ} (hRD : R ≠ Dx) (hQR : Q ≠ R)
    (hAR : A ≠ R) (hAQ : A ≠ Q) (hQD : Q ≠ Dx)
    (h : [L, L1, kk, c, qb, cnt, x, y, w].Nodup) (σ : St) {n n1 r Dv qv k : ℕ}
    (hn : σ.sc L = n) (hn1 : σ.sc L1 = n1) (hk : σ.sc kk = k + 1)
    (hR : Holds (σ.ar R) n1 r) (hD : Holds (σ.ar Dx) n1 Dv) (hQ : Holds (σ.ar Q) n qv)
    (hc : σ.sc c = 0) (hbit : σ.ar A k ≤ 1)
    (hs : 2 * r + σ.ar A k < 2 ^ n1) (hq : 2 * qv + 1 < 2 ^ n) :
    (Cmd.run (divBody A R Dx Q L L1 kk c qb cnt x y w) σ).1
      = (((σ.putAr R (segPut (σ.ar R) 0 n1 (bitOf (if Dv ≤ 2 * r + σ.ar A k
            then 2 * r + σ.ar A k - Dv else 2 * r + σ.ar A k)))).putAr Q
          (segPut (σ.ar Q) 0 n (bitOf (2 * qv + if Dv ≤ 2 * r + σ.ar A k then 1 else 0)))).setSc kk
          k).zeros [c, qb, cnt, x, y, w] ∧
    (Cmd.run (divBody A R Dx Q L L1 kk c qb cnt x y w) σ).2 ≤ 200 * (n1 + n + 1) + 100 := by
  have hn' := h
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hn'
  obtain ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8⟩, ⟨b1, b2, b3, b4, b5, b6, b7⟩, ⟨c1, c2, c3, c4, c5, c6⟩,
    ⟨d1, d2, d3, d4, d5⟩, ⟨e1, e2, e3, e4⟩, ⟨f1, f2, f3⟩, ⟨g1, g2⟩, i1, -⟩ := hn'
  symm_ne
  have hsc1 : [L1, c, cnt, x, y, w].Nodup := by nodup_tac
  have hsc0 : [L, c, cnt, x, y, w].Nodup := by nodup_tac
  have hRb := hR.segBits
  have hDb := hD.segBits
  have hQb := hQ.segBits
  have hRv := hR.segVal_eq
  have hDv := hD.segVal_eq
  have hQv := hQ.segVal_eq
  -- after `decr kk` and `rd c A kk 0`
  set σ2 := (σ.setSc kk k).setSc c (σ.ar A k) with hσ2
  have p1 : Cmd.run (.decr kk) σ = (σ.setSc kk k, 1) := by
    rw [Cmd.run_decr, hk]; rfl
  have p2 : Cmd.run (.rd c A kk 0) (σ.setSc kk k) = (σ2, 1) := by
    rw [Cmd.run_rd]; simp [σ2]
  have σ2R : σ2.ar R = σ.ar R := rfl
  have σ2L1 : σ2.sc L1 = n1 := by simp [σ2, *]
  have σ2c : σ2.sc c = σ.ar A k := by simp [σ2]
  -- the shift of `R`
  obtain ⟨e3, c3⟩ := run_shlSeg (a := R) (b := Dx) (L := L1) (c := c) (cnt := cnt) (x := x) (y := y)
    (w := w) hRD hsc1 σ2 (by rw [σ2R, σ2L1]; exact hRb) (by rw [σ2c]; exact hbit)
  rw [σ2R, σ2L1, σ2c, hRv, Nat.div_eq_of_lt hs] at e3
  rw [σ2L1] at c3
  set σ4 := ((((((σ2.putAr R (segPut (σ.ar R) 0 n1 (bitOf (2 * r + σ.ar A k)))).setSc c 0).setSc x
    0).setSc y 0).setSc w 0).setSc cnt 0).setSc c 0 with hσ4
  have σ4R : σ4.ar R = segPut (σ.ar R) 0 n1 (bitOf (2 * r + σ.ar A k)) := by simp [σ4]
  have σ4D : σ4.ar Dx = σ.ar Dx := by simp [σ4, σ2, Ne.symm hRD]
  have σ4L1 : σ4.sc L1 = n1 := by simp [σ4, σ2, *]
  have σ4c : σ4.sc c = 0 := by simp [σ4]
  obtain ⟨e5, c5⟩ := run_ltSeg (a := R) (b := Dx) (L := L1) (c := c) (cnt := cnt) (x := x) (y := y)
    (w := w) hRD hsc1 σ4 (by rw [σ4R, σ4L1]; exact segBits_segPut _ _ _ _)
    (by rw [σ4D, σ4L1]; exact hDb) σ4c
  rw [σ4R, σ4D, σ4L1, segVal_segPut_bits, Nat.mod_eq_of_lt hs, hDv] at e5
  rw [σ4L1] at c5
  set σ5 := ((((σ4.setSc c (if 2 * r + σ.ar A k < Dv then 1 else 0)).setSc x 0).setSc y 0).setSc w 0).setSc
    cnt 0 with hσ5
  simp only [divBody, Cmd.run_seqs_cons, Cmd.run_seqs_nil, p1, p2, e3, Cmd.run_setK, ← hσ4, e5,
    ← hσ5, Cmd.run_ifZero, Cmd.run_copy]
  have σ5R : σ5.ar R = segPut (σ.ar R) 0 n1 (bitOf (2 * r + σ.ar A k)) := by simp [σ5, σ4R]
  have σ5D : σ5.ar Dx = σ.ar Dx := by simp [σ5, σ4D]
  have σ5Q : σ5.ar Q = σ.ar Q := by simp [σ5, σ4, σ2, hQR, hQD]
  have σ5L1 : σ5.sc L1 = n1 := by simp [σ5, σ4, σ2, *]
  have σ5L : σ5.sc L = n := by simp [σ5, σ4, σ2, *]
  have hshlQ := fun τ (hτQ : τ.ar Q = σ.ar Q) (hτL : τ.sc L = n) (hτc : τ.sc c ≤ 1) =>
    run_shlSeg (a := Q) (b := R) (L := L) (c := c) (cnt := cnt) (x := x) (y := y) (w := w) hQR hsc0 τ
      (by rw [hτQ, hτL]; exact hQb) hτc
  have hc5' : σ5.sc c = (if 2 * r + σ.ar A k < Dv then 1 else 0) := by
    rw [hσ5, St.setSc_sc_ne _ _ ‹c ≠ cnt›, St.setSc_sc_ne _ _ ‹c ≠ w›, St.setSc_sc_ne _ _ ‹c ≠ y›,
      St.setSc_sc_ne _ _ ‹c ≠ x›, St.setSc_sc_self]
  by_cases hfit : Dv ≤ 2 * r + σ.ar A k
  · have hc5 : σ5.sc c = 0 := by rw [hc5', if_neg (by omega)]
    obtain ⟨e6, c6⟩ := run_subSeg (a := R) (b := Dx) (L := L1) (c := c) (cnt := cnt) (x := x) (y := y)
      (w := w) hRD hsc1 σ5 (by rw [σ5R, σ5L1]; exact segBits_segPut _ _ _ _)
      (by rw [σ5D, σ5L1]; exact hDb) (by rw [hc5]; omega)
      (by rw [σ5R, σ5D, σ5L1, segVal_segPut_bits, Nat.mod_eq_of_lt hs, hDv, hc5]; omega)
    rw [σ5R, σ5D, σ5L1, segVal_segPut_bits, Nat.mod_eq_of_lt hs, hDv, hc5, Nat.sub_zero,
      segPut_segPut] at e6
    rw [σ5L1] at c6
    simp only [hc5, if_true, e6]
    set σ8 := (((((((σ5.putAr R (segPut (σ.ar R) 0 n1 (bitOf (2 * r + σ.ar A k - Dv)))).setSc c 0).setSc
      x 0).setSc y 0).setSc w 0).setSc cnt 0).setSc qb 1) with hσ8
    have σ8qb : σ8.sc qb = 1 := by simp [σ8]
    rw [σ8qb]
    obtain ⟨e9, c9⟩ := hshlQ (σ8.setSc c 1) (by simp [σ8, σ5Q, hQR]) (by simp [σ8, σ5L, *])
      (by simp)
    rw [show (σ8.setSc c 1).ar Q = σ.ar Q by simp [σ8, σ5Q, hQR],
      show (σ8.setSc c 1).sc L = n by simp [σ8, σ5L, *], show (σ8.setSc c 1).sc c = 1 by simp,
      hQv, Nat.div_eq_of_lt hq] at e9
    rw [show (σ8.setSc c 1).sc L = n by simp [σ8, σ5L, *]] at c9
    rw [e9, if_pos hfit, if_pos hfit]
    constructor
    · simp only [σ8, σ5, σ4, σ2]
      clear e3 e5 e6 e9 c3 c5 c6 c9 hshlQ p1 p2
      ext z
      · simp only [St.setSc_sc, St.setSc_ar, St.putAr_sc, St.putAr_ar, St.zeros_cons, St.zeros_nil]
        sc_split z [c, qb, cnt, x, y, w, kk]
      · simp only [St.setSc_sc, St.setSc_ar, St.putAr_sc, St.putAr_ar, St.zeros_cons, St.zeros_nil,
          Function.update_apply]
        all_goals (split_ifs <;> simp_all [segPut_segPut])
    · clear_ne; omega
  · have hc5 : σ5.sc c = 1 := by rw [hc5', if_pos (by omega)]
    simp only [hc5, one_ne_zero, if_false]
    have hq0 : (σ5.setSc qb 0).sc qb = 0 := by simp
    rw [hq0]
    obtain ⟨e9, c9⟩ := hshlQ ((σ5.setSc qb 0).setSc c 0) (by simp [σ5Q]) (by simp [σ5L, *]) (by simp)
    rw [show ((σ5.setSc qb 0).setSc c 0).ar Q = σ.ar Q by simp [σ5Q],
      show ((σ5.setSc qb 0).setSc c 0).sc L = n by simp [σ5L, *],
      show ((σ5.setSc qb 0).setSc c 0).sc c = 0 by simp,
      hQv, Nat.add_zero, Nat.div_eq_of_lt (by omega)] at e9
    rw [show ((σ5.setSc qb 0).setSc c 0).sc L = n by simp [σ5L, *]] at c9
    rw [e9, if_neg hfit, if_neg hfit, Nat.add_zero]
    constructor
    · simp only [σ5, σ4, σ2]
      clear e3 e5 e9 c3 c5 c9 hshlQ p1 p2
      ext z
      · simp only [St.setSc_sc, St.setSc_ar, St.putAr_sc, St.putAr_ar, St.zeros_cons, St.zeros_nil]
        sc_split z [c, qb, cnt, x, y, w, kk]
      · simp only [St.setSc_sc, St.setSc_ar, St.putAr_sc, St.putAr_ar, St.zeros_cons, St.zeros_nil,
          Function.update_apply]
        all_goals (split_ifs <;> simp_all [segPut_segPut])
    · clear_ne; omega

/-- **Division with remainder**: `Q := A / D` (width `L`), `R := A % D` (width `L+1`);
`Dx` is a scratch copy of `D` at width `L+1`. -/
def divmodSeg (A D Q R Dx L L1 kk j c qb cnt x y w z z' p q v : ℕ) : Cmd :=
  .seq (seqs [.setK z 0, .setK z' 0, .copy L1 L, .incr L1,
    fillSeg R z L1 z' cnt p, fillSeg Dx z L1 z' cnt p, copySeg Dx z D z' L cnt p q v,
    fillSeg Q z L z' cnt p, .copy kk L,
    .setK c 0, .setK qb 0, .setK x 0, .setK y 0, .setK w 0])
  (seqs [.loop L j (divBody A R Dx Q L L1 kk c qb cnt x y w), .setK j 0, .setK L1 0])

theorem segFill_zero' (f : ℕ → ℕ) (n : ℕ) : segFill f 0 n 0 = segPut f 0 n (bitOf 0) := segFill_zero f n

theorem segCopy_fill' (f g : ℕ → ℕ) (L X : ℕ) (hg : Holds g L X) :
    segCopy (segFill f 0 (L + 1) 0) g 0 0 L = segPut f 0 (L + 1) (bitOf X) := by
  funext r
  simp only [segCopy, segFill, segPut, zero_add, Nat.sub_zero]
  by_cases h1 : r < L
  · rw [if_pos ⟨by omega, h1⟩, if_pos ⟨by omega, by omega⟩, hg.2 r h1]
  · rw [if_neg (by omega)]
    by_cases h2 : r < L + 1
    · rw [if_pos ⟨by omega, h2⟩, if_pos ⟨by omega, h2⟩,
        bitOf_eq_zero_of_lt (lt_of_lt_of_le hg.1 (Nat.pow_le_pow_right (by norm_num) (by omega)))]
    · rw [if_neg (by omega), if_neg (by omega)]

theorem div_pow_lt {X L j : ℕ} (hX : X < 2 ^ L) (hj : j ≤ L) : X / 2 ^ (L - j) < 2 ^ j := by
  rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, show j + (L - j) = L by omega]
  exact hX

set_option maxHeartbeats 1000000 in
theorem run_divmodSeg {A D Q R Dx L L1 kk j c qb cnt x y w z z' p q v : ℕ}
    (hAR : A ≠ R) (hAQ : A ≠ Q) (hADx : A ≠ Dx) (hDQ : D ≠ Q) (hDR : D ≠ R) (hDDx : D ≠ Dx)
    (hQR : Q ≠ R) (hQDx : Q ≠ Dx) (hRDx : R ≠ Dx)
    (h : [L, L1, kk, j, c, qb, cnt, x, y, w, z, z', p, q, v].Nodup) (st : St) {X Dv : ℕ}
    (hA : Holds (st.ar A) (st.sc L) X) (hD : Holds (st.ar D) (st.sc L) Dv) (hpos : 0 < Dv) :
    (Cmd.run (divmodSeg A D Q R Dx L L1 kk j c qb cnt x y w z z' p q v) st).1
      = (((st.putAr Q (segPut (st.ar Q) 0 (st.sc L) (bitOf (X / Dv)))).putAr R
          (segPut (st.ar R) 0 (st.sc L + 1) (bitOf (X % Dv)))).putAr Dx
          (segPut (st.ar Dx) 0 (st.sc L + 1) (bitOf Dv))).zeros
          [L1, kk, j, c, qb, cnt, x, y, w, z, z', p, q, v] ∧
    (Cmd.run (divmodSeg A D Q R Dx L L1 kk j c qb cnt x y w z z' p q v) st).2
      ≤ 500 * (st.sc L + 1) * (st.sc L + 1) := by
  have hn' := h
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hn'
  obtain ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14⟩,
    ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13⟩,
    ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12⟩, ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11⟩,
    ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩, ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9⟩,
    ⟨g1, g2, g3, g4, g5, g6, g7, g8⟩, ⟨i1, i2, i3, i4, i5, i6, i7⟩, ⟨j1, j2, j3, j4, j5, j6⟩,
    ⟨k1, k2, k3, k4, k5⟩, ⟨l1, l2, l3, l4⟩, ⟨m1, m2, m3⟩, ⟨n1, n2⟩, o1, -⟩ := hn'
  symm_ne
  set nL := st.sc L with hnL
  have hfR := fun σ => run_fillSeg (b := R) (ob := z) (n := L1) (val := z') (c := cnt) (q := p)
    (by nodup_tac) σ
  have hfD := fun σ => run_fillSeg (b := Dx) (ob := z) (n := L1) (val := z') (c := cnt) (q := p)
    (by nodup_tac) σ
  have hfQ := fun σ => run_fillSeg (b := Q) (ob := z) (n := L) (val := z') (c := cnt) (q := p)
    (by nodup_tac) σ
  have hcp := fun σ => run_copySeg (b := Dx) (ob := z) (a := D) (oa := z') (n := L) (c := cnt) (p := p)
    (q := q) (v := v) hDDx (by nodup_tac) σ
  set st1 := (((((st.zeros [z, z', cnt, p, q, v, c, qb, x, y, w]).setSc L1 (nL + 1)).setSc kk nL).putAr R
    (segPut (st.ar R) 0 (nL + 1) (bitOf 0))).putAr Dx (segPut (st.ar Dx) 0 (nL + 1) (bitOf Dv))).putAr Q
    (segPut (st.ar Q) 0 nL (bitOf 0)) with hst1
  have hpre : (Cmd.run (seqs [.setK z 0, .setK z' 0, .copy L1 L, .incr L1,
      fillSeg R z L1 z' cnt p, fillSeg Dx z L1 z' cnt p, copySeg Dx z D z' L cnt p q v,
      fillSeg Q z L z' cnt p, .copy kk L,
      .setK c 0, .setK qb 0, .setK x 0, .setK y 0, .setK w 0]) st).1 = st1 := by
    simp only [Cmd.run_seqs_cons, Cmd.run_seqs_nil, Cmd.run_setK, Cmd.run_copy, Cmd.run_incr,
      (hfR _).1, (hfD _).1, (hfQ _).1, (hcp _).1]
    clear hfR hfD hfQ hcp
    ext r
    · simp only [St.setSc_sc, St.setSc_ar, St.putAr_sc, St.putAr_ar, St.zeros_cons, St.zeros_nil, st1]
      sc_split r [z, z', cnt, p, q, v, c, qb, x, y, w, L1, kk]
    · simp only [St.setSc_sc, St.setSc_ar, St.putAr_sc, St.putAr_ar, St.zeros_cons, St.zeros_nil, st1,
        Function.update_apply]
      by_cases hrQ : r = Q
      · rcases hrQ with rfl; simp [Function.update_apply, *]; rw [segFill_zero']
      · by_cases hrD : r = Dx
        · rcases hrD with rfl
          rw [if_neg (Ne.symm hRDx)]
          simp [Function.update_apply, *]; rw [segCopy_fill' _ _ _ _ hD]
        · by_cases hrR : r = R
          · rcases hrR with rfl; simp [Function.update_apply, *]; rw [segFill_zero]
          · simp [*]
  have hprec : (Cmd.run (seqs [.setK z 0, .setK z' 0, .copy L1 L, .incr L1,
      fillSeg R z L1 z' cnt p, fillSeg Dx z L1 z' cnt p, copySeg Dx z D z' L cnt p q v,
      fillSeg Q z L z' cnt p, .copy kk L,
      .setK c 0, .setK qb 0, .setK x 0, .setK y 0, .setK w 0]) st).2 ≤ 40 * nL + 120 := by
    simp only [Cmd.run_seqs_cons, Cmd.run_seqs_nil, Cmd.run_setK, Cmd.run_copy, Cmd.run_incr,
      (hfR _).1, (hfD _).1, (hfQ _).1, (hcp _).1, (hfR _).2, (hfD _).2, (hfQ _).2, (hcp _).2]
    clear hfR hfD hfQ hcp
    simp [Function.update_apply, *]
    clear_ne
    omega
  clear hfR hfD hfQ hcp
  let P : ℕ → ℕ := fun i => X / 2 ^ (nL - i)
  let E : ℕ → St := fun i => ((((st1.setSc j 0).setSc kk (nL - i)).putAr R (segPut (st.ar R) 0 (nL + 1)
    (bitOf (P i % Dv)))).putAr Q (segPut (st.ar Q) 0 nL (bitOf (P i / Dv))))
  have hP0 : P 0 = 0 := by simp only [P, Nat.sub_zero]; exact Nat.div_eq_of_lt hA.1
  have hE0 : st1.setSc j 0 = E 0 := by
    simp only [E, hP0, Nat.zero_mod, Nat.zero_div, Nat.sub_zero, st1]
    st_eq
  have hst1L : st1.sc L = nL := by simp [st1, *]
  have hDlt : Dv < 2 ^ (nL + 1) := lt_trans hD.1 (Nat.pow_lt_pow_right (by norm_num) (by omega))
  have hbody := fun σ {n n1 r qv k : ℕ} (hn : σ.sc L = n) (hn1 : σ.sc L1 = n1) (hk : σ.sc kk = k + 1)
      (hR : Holds (σ.ar R) n1 r) (hDx : Holds (σ.ar Dx) n1 Dv) (hQ : Holds (σ.ar Q) n qv)
      (hc : σ.sc c = 0) (hbit : σ.ar A k ≤ 1)
      (hs : 2 * r + σ.ar A k < 2 ^ n1) (hq : 2 * qv + 1 < 2 ^ n) =>
    run_divBody (A := A) (R := R) (Dx := Dx) (Q := Q) (L := L) (L1 := L1) (kk := kk) (c := c) (qb := qb)
      (cnt := cnt) (x := x) (y := y) (w := w) hRDx hQR hAR hAQ hQDx (by nodup_tac) σ hn hn1 hk hR hDx hQ
      hc hbit hs hq
  have hboth : ∀ i, i < st1.sc L → (Cmd.run (divBody A R Dx Q L L1 kk c qb cnt x y w)
      ((E i).setSc j i)).1.setSc j 0 = E (i + 1) ∧
      (Cmd.run (divBody A R Dx Q L L1 kk c qb cnt x y w) ((E i).setSc j i)).2
        ≤ 200 * (nL + 1 + nL + 1) + 100 := by
    intro i hi
    rw [hst1L] at hi
    set k := nL - i - 1 with hk
    have hbk : st.ar A k = bitOf X k := by rw [hk]; exact hA.2 _ (by omega)
    have hPi : P i < 2 ^ i := div_pow_lt hA.1 hi.le
    have hrlt : P i % Dv < Dv := Nat.mod_lt _ hpos
    have hqle : P i / Dv ≤ P i := Nat.div_le_self _ _
    have hσA' : ((E i).setSc j i).ar A = st.ar A := by simp [E, st1, hAR, hAQ, hADx]
    have hσA : ((E i).setSc j i).ar A k = bitOf X k := by rw [hσA', hbk]
    have hpi : 2 ^ (i + 1) ≤ 2 ^ nL := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hb1 := bitOf_le_one X k
    have hp1 : 2 ^ (nL + 1) = 2 * 2 ^ nL := by ring
    have hp2 : 2 ^ (i + 1) = 2 * 2 ^ i := by ring
    have hDl := hD.1
    obtain ⟨e, ec⟩ := hbody ((E i).setSc j i) (n := nL) (n1 := nL + 1) (r := P i % Dv) (qv := P i / Dv)
      (k := k) (by simp [E, st1, *]) (by simp [E, st1, *]) (by simp [E, st1, *]; omega)
      (by rw [show ((E i).setSc j i).ar R = segPut (st.ar R) 0 (nL + 1) (bitOf (P i % Dv)) by
            simp [E, Ne.symm hQR]]
          exact holds_segPut _ (by omega))
      (by rw [show ((E i).setSc j i).ar Dx = segPut (st.ar Dx) 0 (nL + 1) (bitOf Dv) by
            simp [E, st1, Ne.symm hQDx, Ne.symm hRDx]]
          exact holds_segPut _ hDlt)
      (by simp only [E, St.setSc_ar, St.putAr_ar_self]
          exact holds_segPut _ (by omega))
      (by simp [E, st1, *])
      (by rw [hσA]; exact hb1)
      (by rw [hσA]; clear_ne; omega)
      (by clear_ne; omega)
    refine ⟨?_, by clear_ne; omega⟩
    have hPs : P (i + 1) = 2 * P i + bitOf X k := by
      simp only [P]
      rw [show nL - (i + 1) = k by omega, div_two_pow_step X k, show k + 1 = nL - i by omega]
    obtain ⟨dq, dr⟩ := divmod_step (a := P i) (b := bitOf X k) hpos hb1
    rw [e, hσA, ← dr, ← dq, ← hPs]
    simp only [E, St.setSc_ar, St.putAr_ar_ne _ _ (Ne.symm hQR), St.putAr_ar_self, segPut_segPut]
    clear e ec hbody hσA hσA' hbk hPi hrlt hqle hpi hb1 hp1 hp2 hDl hPs dq dr hprec hpre hE0 hDlt
    simp only [hk, Nat.sub_sub]
    ext r
    · simp only [St.setSc_sc, St.setSc_ar, St.putAr_sc, St.putAr_ar, St.zeros_cons, St.zeros_nil]
      sc_split r [j, kk, c, qb, cnt, x, y, w]
    · simp only [St.setSc_sc, St.setSc_ar, St.putAr_sc, St.putAr_ar, St.zeros_cons, St.zeros_nil,
        Function.update_apply]
      all_goals (split_ifs <;> first | rfl | simp_all)
  have e := loop_exact (st := st1) E hE0 (fun i hi => (hboth i hi).1)
  have ec := loop_exact_cost (st := st1) E _ hE0 (fun i hi => (hboth i hi).1) (fun i hi => (hboth i hi).2)
  rw [hst1L] at e ec
  refine ⟨?_, ?_⟩
  swap
  · simp only [divmodSeg, Cmd.run_seq]
    rw [hpre]
    generalize (Cmd.run (seqs [.setK z 0, .setK z' 0, .copy L1 L, .incr L1,
      fillSeg R z L1 z' cnt p, fillSeg Dx z L1 z' cnt p, copySeg Dx z D z' L cnt p q v,
      fillSeg Q z L z' cnt p, .copy kk L,
      .setK c 0, .setK qb 0, .setK x 0, .setK y 0, .setK w 0]) st).2 = P0 at hprec ⊢
    simp only [Cmd.run_seqs_cons, Cmd.run_seqs_nil, Cmd.run_setK]
    have h3 : nL * (200 * (nL + 1 + nL + 1) + 100 + 1) = 400 * (nL * nL) + 501 * nL := by ring
    have h4 : 500 * (nL + 1) * (nL + 1) = 500 * (nL * nL) + 1000 * nL + 500 := by ring
    rw [h4]
    rw [h3] at ec
    clear_ne
    omega
  simp only [divmodSeg, Cmd.run_seq]
  rw [hpre]
  simp only [Cmd.run_seqs_cons, Cmd.run_seqs_nil, Cmd.run_setK]
  rw [e]
  have hPn : P nL = X := by simp [P]
  simp only [E, hPn, Nat.sub_self, st1]
  clear e ec hboth hE0 hpre hprec hbody
  ext r
  · simp only [St.setSc_sc, St.setSc_ar, St.putAr_sc, St.putAr_ar, St.zeros_cons, St.zeros_nil]
    sc_split r [L1, kk, j, c, qb, cnt, x, y, w, z, z', p, q, v]
  · simp only [St.setSc_sc, St.setSc_ar, St.putAr_sc, St.putAr_ar, St.zeros_cons, St.zeros_nil,
      Function.update_apply]
    all_goals (split_ifs <;> first | rfl | simp_all)

end Factoring.Aux.Copied.PLib


#print axioms Factoring.Aux.Copied.PLib.run_mulSeg
#print axioms Factoring.Aux.Copied.PLib.run_divmodSeg
