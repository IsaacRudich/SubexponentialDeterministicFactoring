/-
Adapted from the authors' related work (the whole file).

Not an audit surface.
-/
/-
PLIB, part 5: polynomial-time functions on strings, and their closure.

`PolyFun g`: some polynomial-time `Program` `M` computes `g`, its output read as
`outOf (Program.run M (startingMemory xs)).1`.

Closure: `polyFun_comp` (`h ∘ g`), `polyFun_append` (`g xs ++ h xs`),
`polyFun_id`, `polyFun_const`.  Each is a source program built from `call` and
the routines of `PlibArr`, compiled by `wrapFn`.

Not an audit surface.
-/
module

public import FactoringAux.Copied.PlibArr

@[expose] public section

namespace Factoring.Aux.Copied.PLib

open Factoring.Aux.Copied Factoring.Aux.Copied.Aux Cmd

/-- `M` computes `g` in polynomial time, output read in the input format. -/
def PolyComp (M : Program) (g : List Bool → List Bool) : Prop :=
  RunsInPolyTime M ∧ ∀ xs, outOf (Program.run M (startingMemory xs)).1 = g xs

/-- Some polynomial-time program computes `g`. -/
def PolyFun (g : List Bool → List Bool) : Prop := ∃ M, PolyComp M g

/-! ### Polynomial bounds -/

theorem polyBound_of_le {S : List Bool → ℕ} {B : ℕ → ℕ} (hB : Poly B) (h : ∀ xs, S xs ≤ B xs.length) :
    ∃ c d, ∀ xs, S xs ≤ c * (xs.length + 1) ^ d := by
  obtain ⟨c, d, hc⟩ := hB
  exact ⟨c, d, fun xs => le_trans (h xs) (hc _)⟩

theorem length_outOf (μ : Memory) : (outOf μ).length = μ 0 := by simp [outOf]

/-- The output's length is at most the input's length plus the steps. -/
theorem outLen_le (M : Program) (xs : List Bool) :
    (Program.run M (startingMemory xs)).1 0 ≤ xs.length + steps M xs :=
  run_val_le M _ _ (startingMemory_le_length xs) 0

/-! ### Composition -/

/-- `h ∘ g`: run `Mg` on array `0` (the input), clean its output into array `1`,
run `Mh` there.  Scalars `1 … 4` are `cleanStr`'s scratch. -/
def compCmd (Mg Mh : Program) : Cmd := seqs [.call Mg 0, cleanStr 1 0 1 2 3 4, .call Mh 1]

@[simp] theorem St.init_ar_succ (xs : List Bool) (a : ℕ) : (St.init xs).ar (a + 1) = fun _ => 0 := by
  simp [St.init]

theorem compCmd_spec (Mg Mh : Program) (xs : List Bool) :
    (srcOut (compCmd Mg Mh) xs).ar 1
      = (Program.run Mh (startingMemory (outOf (Program.run Mg (startingMemory xs)).1))).1 ∧
    srcCost (compCmd Mg Mh) xs ≤ steps Mg xs + 11 * (xs.length + steps Mg xs)
      + steps Mh (outOf (Program.run Mg (startingMemory xs)).1) + 30 := by
  have hc := run_cleanStr (b := 1) (a := 0) (l := 1) (c := 2) (v := 3) (z := 4) (by omega)
    (by decide) ((St.init xs).putAr 0 (Program.run Mg (startingMemory xs)).1)
  have hcl : cleanArr (((St.init xs).putAr 0 (Program.run Mg (startingMemory xs)).1).ar 0)
      (((St.init xs).putAr 0 (Program.run Mg (startingMemory xs)).1).ar 1)
      = startingMemory (outOf (Program.run Mg (startingMemory xs)).1) := by
    rw [St.putAr_ar_self, St.putAr_ar_ne _ _ (by omega), show (1:ℕ) = 0 + 1 from rfl,
      St.init_ar_succ, cleanArr_zero]
  rw [hcl, St.putAr_ar_self] at hc
  simp only [srcOut, srcCost, compCmd, Cmd.run_seqs_cons, Cmd.run_seqs_nil, Cmd.run_call,
    St.init_ar_zero, hc.1]
  simp only [St.putAr_ar_self, St.setSc_ar]
  refine ⟨trivial, ?_⟩
  have := outLen_le Mg xs
  simp only [steps] at this ⊢
  have := hc.2
  omega

/-- The time bound of a polynomial-time program, as a function of the length. -/
theorem steps_bound {M : Program} (h : RunsInPolyTime M) :
    ∃ c d, ∀ xs, steps M xs ≤ c * (xs.length + 1) ^ d := h

theorem polyComp_wrapFn {s : Cmd} {out : ℕ} {g : List Bool → List Bool}
    (hS : ∃ c d, ∀ xs, srcCost s xs ≤ c * (xs.length + 1) ^ d)
    (hg : ∀ xs, outOf ((srcOut s xs).ar out) = g xs) : PolyComp (wrapFn s out) g :=
  ⟨runsInPolyTime_wrapFn s out hS, fun xs => by rw [outOf_wrapFn, hg]⟩

/-- **Composition.** -/
theorem polyFun_comp {g h : List Bool → List Bool} (hg : PolyFun g) (hh : PolyFun h) :
    PolyFun (h ∘ g) := by
  obtain ⟨Mg, ⟨cg, dg, hcg⟩, eg⟩ := hg
  obtain ⟨Mh, ⟨ch, dh, hch⟩, eh⟩ := hh
  refine ⟨_, polyComp_wrapFn (s := compCmd Mg Mh) (out := 1) ?_ (fun xs => ?_)⟩
  · refine polyBound_of_le (B := fun n => cg * (n + 1) ^ dg + 11 * (n + cg * (n + 1) ^ dg)
      + ch * (n + cg * (n + 1) ^ dg + 1) ^ dh + 30)
      (Poly.add (Poly.add (Poly.add (Poly.mul (Poly.const _) (poly_pow dg))
        (Poly.mul (Poly.const 11) (Poly.add Poly.id (Poly.mul (Poly.const _) (poly_pow dg)))))
        (Poly.mul (Poly.const _) (Poly.pow (Poly.add (Poly.add Poly.id
          (Poly.mul (Poly.const _) (poly_pow dg))) (Poly.const 1)) dh))) (Poly.const 30))
      (fun xs => ?_)
    have h1 := (compCmd_spec Mg Mh xs).2
    have h2 := hcg xs
    have h3 := hch (outOf (Program.run Mg (startingMemory xs)).1)
    have h4 := outLen_le Mg xs
    rw [length_outOf] at h3
    have h5 : ch * ((Program.run Mg (startingMemory xs)).1 0 + 1) ^ dh
        ≤ ch * (xs.length + cg * (xs.length + 1) ^ dg + 1) ^ dh :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    omega
  · rw [(compCmd_spec Mg Mh xs).1, eg, eh]; rfl

/-! ### Concatenation -/

/-- Strings `fa` and `fb` (input format) concatenated; cells past the total from `fc`. -/
def catArr (fa fb fc : ℕ → ℕ) : ℕ → ℕ :=
  fun r => if r = 0 then fa 0 + fb 0 else if r ≤ fa 0 then fa r
    else if r ≤ fa 0 + fb 0 then fb (r - fa 0) else fc r

theorem catArr_startingMemory (ys zs : List Bool) :
    catArr (startingMemory ys) (startingMemory zs) (fun _ => 0) = startingMemory (ys ++ zs) := by
  funext r
  rcases r with _ | k
  · simp [catArr, startingMemory_zero_eq]
  · have e1 : startingMemory ys 0 = ys.length := rfl
    have e2 : startingMemory zs 0 = zs.length := rfl
    simp only [catArr, Nat.add_one_ne_zero, if_false, startingMemory_succ, e1, e2]
    by_cases h1 : k + 1 ≤ ys.length
    · rw [if_pos h1, List.getD_append _ _ _ _ (by omega)]
    · rw [if_neg h1]
      by_cases h2 : k + 1 ≤ ys.length + zs.length
      · rw [if_pos h2, show k + 1 - ys.length = (k - ys.length) + 1 by omega, startingMemory_succ,
          List.getD_append_right _ _ _ _ (by omega)]
      · rw [if_neg h2, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
        rfl

/-- Zero a list of scalars. -/
def St.zeros (st : St) : List ℕ → St
  | [] => st
  | x :: xs => (st.setSc x 0).zeros xs

@[simp] theorem St.zeros_nil (st : St) : st.zeros [] = st := rfl
@[simp] theorem St.zeros_cons (st : St) (x : ℕ) (xs : List ℕ) :
    st.zeros (x :: xs) = (st.setSc x 0).zeros xs := rfl

/-- `c := ` the concatenation of the strings in arrays `a` and `b` (input format);
cells of `c` past the total length untouched.  Scratch: twelve scalars. -/
def catStr (c a b L1 L2 z one one' o2 t s cc p q v : ℕ) : Cmd :=
  seqs [.setK z 0, .setK one 1, .setK one' 1, .rd L1 a z 0, .rd L2 b z 0,
    copySeg c one a one' L1 cc p q v,
    .copy o2 L1, .incr o2,
    copySeg c o2 b one' L2 cc p q v,
    .copy t L1, addTo t L2 s,
    .wr c z 0 t,
    .setK one 0, .setK one' 0, .setK L1 0, .setK L2 0, .setK o2 0, .setK t 0]

theorem cost_catStr {c a b L1 L2 z one one' o2 t s cc p q v : ℕ} (hca : a ≠ c) (hcb : b ≠ c)
    (h : [L1, L2, z, one, one', o2, t, s, cc, p, q, v].Nodup) (st : St) :
    (Cmd.run (catStr c a b L1 L2 z one one' o2 t s cc p q v) st).2
      = 12 * st.ar a 0 + 14 * st.ar b 0 + 69 := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  obtain ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩, ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩,
    ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9⟩, ⟨d1, d2, d3, d4, d5, d6, d7, d8⟩,
    ⟨e1, e2, e3, e4, e5, e6, e7⟩, ⟨f1, f2, f3, f4, f5, f6⟩, ⟨g1, g2, g3, g4, g5⟩,
    ⟨i1, i2, i3, i4⟩, ⟨j1, j2, j3⟩, ⟨k1, k2⟩, l1, -⟩ := h
  symm_ne
  have r1 := fun σ => run_copySeg (b := c) (ob := one) (a := a) (oa := one') (n := L1) (c := cc)
    (p := p) (q := q) (v := v) hca (by nodup_tac) σ
  have r2 := fun σ => run_copySeg (b := c) (ob := o2) (a := b) (oa := one') (n := L2) (c := cc)
    (p := p) (q := q) (v := v) hcb (by nodup_tac) σ
  have r3 := fun σ => run_addTo (x := t) (y := L2) (t := s) (by nodup_tac) σ
  have c1 := fun σ => (r1 σ).2
  have c2 := fun σ => (r2 σ).2
  have c3 := fun σ => (r3 σ).2
  have m1 := fun σ => (r1 σ).1
  have m2 := fun σ => (r2 σ).1
  have m3 := fun σ => (r3 σ).1
  simp only [catStr, Cmd.run_seqs_cons, Cmd.run_seqs_nil, Cmd.run_setK, Cmd.run_rd, Cmd.run_copy,
    Cmd.run_incr, Cmd.run_wr, m1, m2, m3, c1, c2, c3]
  simp [Function.update_apply, *]
  clear_ne
  omega

theorem run_catStr {c a b L1 L2 z one one' o2 t s cc p q v : ℕ} (hca : a ≠ c) (hcb : b ≠ c)
    (h : [L1, L2, z, one, one', o2, t, s, cc, p, q, v].Nodup) (st : St) :
    (Cmd.run (catStr c a b L1 L2 z one one' o2 t s cc p q v) st).1
      = (st.putAr c (catArr (st.ar a) (st.ar b) (st.ar c))).zeros
          [L1, L2, z, one, one', o2, t, s, cc, p, q, v] := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  obtain ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩, ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩,
    ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9⟩, ⟨d1, d2, d3, d4, d5, d6, d7, d8⟩,
    ⟨e1, e2, e3, e4, e5, e6, e7⟩, ⟨f1, f2, f3, f4, f5, f6⟩, ⟨g1, g2, g3, g4, g5⟩,
    ⟨i1, i2, i3, i4⟩, ⟨j1, j2, j3⟩, ⟨k1, k2⟩, l1, -⟩ := h
  symm_ne
  have r1 := fun σ => (run_copySeg (b := c) (ob := one) (a := a) (oa := one') (n := L1) (c := cc)
    (p := p) (q := q) (v := v) hca (by nodup_tac) σ).1
  have r2 := fun σ => (run_copySeg (b := c) (ob := o2) (a := b) (oa := one') (n := L2) (c := cc)
    (p := p) (q := q) (v := v) hcb (by nodup_tac) σ).1
  have r3 := fun σ => (run_addTo (x := t) (y := L2) (t := s) (by nodup_tac) σ).1
  simp only [catStr, Cmd.run_seqs_cons, Cmd.run_seqs_nil, Cmd.run_setK, Cmd.run_rd, Cmd.run_copy,
    Cmd.run_incr, Cmd.run_wr, r1, r2, r3]
  ext x
  · simp only [St.setSc_sc, St.setSc_ar, St.putAr_sc,
      St.putAr_ar, St.setAr_sc, St.setAr_ar, St.zeros_cons, St.zeros_nil]
    by_cases hx : x ∈ [L1, L2, z, one, one', o2, t, s, cc, p, q, v]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [Function.update_apply, *]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
      simp [Function.update_apply, *]
  · simp only [St.setSc_sc, St.setSc_ar, St.putAr_sc,
      St.putAr_ar, St.setAr_sc, St.setAr_ar, St.zeros_cons, St.zeros_nil, Function.update_apply]
    by_cases hx : x = c
    · subst hx
      simp only [if_true, if_neg hca, if_neg hcb]
      simp [*, Function.update_apply]
      simp only [segCopy, catArr]
      split_ifs <;> clear_ne <;> first | rfl | omega | (congr 1; omega)
    · simp only [if_neg hx]

/-! ### Appending two computed strings -/

/-- `g xs ++ h xs`: copy the input to array `2`, run `Mg` on array `0` and clean
into array `1`, run `Mh` on array `2` and clean into array `4`, concatenate into
array `3`. -/
def appendCmd (Mg Mh : Program) : Cmd :=
  seqs [cleanStr 2 0 1 2 3 4, .call Mg 0, cleanStr 1 0 1 2 3 4, .call Mh 2, cleanStr 4 2 1 2 3 4,
    catStr 3 1 4 5 6 7 8 9 10 11 12 13 14 15 16]

theorem appendCmd_spec (Mg Mh : Program) (xs : List Bool) :
    (srcOut (appendCmd Mg Mh) xs).ar 3
      = startingMemory (outOf (Program.run Mg (startingMemory xs)).1
          ++ outOf (Program.run Mh (startingMemory xs)).1) ∧
    srcCost (appendCmd Mg Mh) xs ≤ steps Mg xs + steps Mh xs + 60 * (xs.length + steps Mg xs
      + steps Mh xs) + 300 := by
  have k1 := fun σ => run_cleanStr (b := 2) (a := 0) (l := 1) (c := 2) (v := 3) (z := 4) (by omega)
    (by decide) σ
  have k2 := fun σ => run_cleanStr (b := 1) (a := 0) (l := 1) (c := 2) (v := 3) (z := 4) (by omega)
    (by decide) σ
  have k3 := fun σ => run_cleanStr (b := 4) (a := 2) (l := 1) (c := 2) (v := 3) (z := 4) (by omega)
    (by decide) σ
  have k4 := fun σ => run_catStr (c := 3) (a := 1) (b := 4) (L1 := 5) (L2 := 6) (z := 7) (one := 8)
    (one' := 9) (o2 := 10) (t := 11) (s := 12) (cc := 13) (p := 14) (q := 15) (v := 16)
    (by omega) (by omega) (by decide) σ
  have k5 := fun σ => cost_catStr (c := 3) (a := 1) (b := 4) (L1 := 5) (L2 := 6) (z := 7) (one := 8)
    (one' := 9) (o2 := 10) (t := 11) (s := 12) (cc := 13) (p := 14) (q := 15) (v := 16)
    (by omega) (by omega) (by decide) σ
  have e0 : cleanArr (startingMemory xs) (fun _ => 0) = startingMemory xs := by
    rw [cleanArr_zero, outOf_startingMemory]
  simp only [srcOut, srcCost, appendCmd, Cmd.run_seqs_cons, Cmd.run_seqs_nil, Cmd.run_call,
    (k1 _).1, (k2 _).1, (k3 _).1, k4, (k1 _).2, (k2 _).2, (k3 _).2, k5]
  constructor
  · simp [St.zeros, St.init, cleanArr_zero, outOf_startingMemory, catArr_startingMemory]
  · simp [St.zeros, St.init, cleanArr_zero, outOf_startingMemory, catArr_startingMemory,
      startingMemory_zero_eq, length_outOf]
    have h1 := outLen_le Mg xs
    have h2 := outLen_le Mh xs
    simp only [steps] at h1 h2 ⊢
    omega

/-- **Appending two computed strings.** -/
theorem polyFun_append {g h : List Bool → List Bool} (hg : PolyFun g) (hh : PolyFun h) :
    PolyFun (fun xs => g xs ++ h xs) := by
  obtain ⟨Mg, ⟨cg, dg, hcg⟩, eg⟩ := hg
  obtain ⟨Mh, ⟨ch, dh, hch⟩, eh⟩ := hh
  refine ⟨_, polyComp_wrapFn (s := appendCmd Mg Mh) (out := 3) ?_ (fun xs => ?_)⟩
  · refine polyBound_of_le (B := fun n => cg * (n + 1) ^ dg + ch * (n + 1) ^ dh
      + 60 * (n + cg * (n + 1) ^ dg + ch * (n + 1) ^ dh) + 300)
      (Poly.add (Poly.add (Poly.add (Poly.mul (Poly.const _) (poly_pow dg))
        (Poly.mul (Poly.const _) (poly_pow dh)))
        (Poly.mul (Poly.const 60) (Poly.add (Poly.add Poly.id
          (Poly.mul (Poly.const _) (poly_pow dg))) (Poly.mul (Poly.const _) (poly_pow dh)))))
        (Poly.const 300)) (fun xs => ?_)
    have h1 := (appendCmd_spec Mg Mh xs).2
    have h2 := hcg xs
    have h3 := hch xs
    have : 60 * (xs.length + steps Mg xs + steps Mh xs)
        ≤ 60 * (xs.length + cg * (xs.length + 1) ^ dg + ch * (xs.length + 1) ^ dh) :=
      Nat.mul_le_mul_left _ (by omega)
    omega
  · rw [(appendCmd_spec Mg Mh xs).1, outOf_startingMemory, eg, eh]

/-- **The identity.** -/
theorem polyFun_id : PolyFun (fun xs => xs) :=
  ⟨_, polyComp_wrapFn (s := .skip) (out := 0) ⟨1, 0, fun xs => by simp [srcCost, Cmd.run_skip]⟩
    (fun xs => by simp [srcOut, Cmd.run_skip, outOf_startingMemory])⟩

/-! ### Constant strings -/

/-- Write the bits of `ws` to cells `i+1, i+2, …` of array `b` (`z` holds `0`,
`v` is scratch). -/
def constBits (b z v : ℕ) : ℕ → List Bool → Cmd
  | _, [] => .skip
  | i, w :: ws => .seq (seqs [.setK v (if w then 1 else 0), .wr b z (i + 1) v]) (constBits b z v (i + 1) ws)

theorem run_constBits {b z v : ℕ} (hzv : z ≠ v) : ∀ (ws : List Bool) (i : ℕ) (st : St), st.sc z = 0 →
    (Cmd.run (constBits b z v i ws) st).1.ar b
      = (fun r => if i < r ∧ r ≤ i + ws.length then (if ws.getD (r - i - 1) false then 1 else 0)
          else st.ar b r) ∧
    (Cmd.run (constBits b z v i ws) st).2 = 6 * ws.length + 1
  | [], i, st, _ => ⟨by funext r; simp [constBits, Cmd.run_skip]; try omega,
      by simp [constBits, Cmd.run_skip]⟩
  | w :: ws, i, st, hz => by
      set st' := (Cmd.run (seqs [.setK v (if w then 1 else 0), .wr b z (i + 1) v]) st).1 with hst'
      have hz' : st'.sc z = 0 := by
        simp [st', Cmd.run_seqs_cons, Cmd.run_seqs_nil, Cmd.run_setK, Cmd.run_wr, hz,
          Function.update_apply, hzv]
      have hb' : st'.ar b = Function.update (st.ar b) (i + 1) (if w then 1 else 0) := by
        simp [st', Cmd.run_seqs_cons, Cmd.run_seqs_nil, Cmd.run_setK, Cmd.run_wr, hz,
          Function.update_apply, Ne.symm hzv, hzv]
      obtain ⟨ih1, ih2⟩ := run_constBits hzv ws (i + 1) st' hz'
      simp only [constBits, Cmd.run_seq]
      rw [← hst', ih1, ih2, hb']
      refine ⟨?_, by simp [Cmd.run_seqs_cons, Cmd.run_seqs_nil, Cmd.run_setK, Cmd.run_wr]; ring⟩
      funext r
      simp only [Function.update_apply, List.length_cons]
      by_cases h1 : r = i + 1
      · subst h1; simp
      · rw [if_neg h1]
        by_cases h2 : i + 1 < r ∧ r ≤ i + 1 + ws.length
        · have h3 : i < r ∧ r ≤ i + (ws.length + 1) := by omega
          rw [if_pos h2, if_pos h3, show r - i - 1 = (r - (i + 1) - 1) + 1 by omega]
          simp
        · have h3 : ¬ (i < r ∧ r ≤ i + (ws.length + 1)) := by omega
          rw [if_neg h2, if_neg h3]

/-- Array `1 := startingMemory ys`; scalars `1`, `2` scratch. -/
def constCmd (ys : List Bool) : Cmd :=
  .seq (seqs [.setK 1 0, .setK 2 ys.length, .wr 1 1 0 2]) (constBits 1 1 2 0 ys)

theorem constCmd_spec (ys xs : List Bool) :
    (srcOut (constCmd ys) xs).ar 1 = startingMemory ys ∧ srcCost (constCmd ys) xs = 6 * ys.length + 9 := by
  set st := (Cmd.run (seqs [.setK 1 0, .setK 2 ys.length, .wr 1 1 0 2]) (St.init xs)).1 with hst
  have hz : st.sc 1 = 0 := by simp [st, Cmd.run_seqs_cons, Cmd.run_seqs_nil, Cmd.run_setK, Cmd.run_wr]
  have hb : st.ar 1 = Function.update (fun _ => 0) 0 ys.length := by
    simp [st, Cmd.run_seqs_cons, Cmd.run_seqs_nil, Cmd.run_setK, Cmd.run_wr, St.init]
  obtain ⟨k1, k2⟩ := run_constBits (b := 1) (z := 1) (v := 2) (by omega) ys 0 st hz
  simp only [srcOut, srcCost, constCmd, Cmd.run_seq]
  rw [← hst, k1, k2]
  refine ⟨?_, by simp [Cmd.run_seqs_cons, Cmd.run_seqs_nil, Cmd.run_setK, Cmd.run_wr]; ring⟩
  funext r
  rw [hb]
  rcases r with _ | k
  · simp [startingMemory_zero_eq]
  · simp only [Function.update_apply, Nat.add_one_ne_zero, if_false, startingMemory_succ]
    by_cases hk : k < ys.length
    · rw [if_pos (by omega), show k + 1 - 0 - 1 = k by omega]
    · rw [if_neg (by omega), List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      rfl

/-- **Constant strings.** -/
theorem polyFun_const (ys : List Bool) : PolyFun (fun _ => ys) :=
  ⟨_, polyComp_wrapFn (s := constCmd ys) (out := 1)
    ⟨6 * ys.length + 9, 0, fun xs => by rw [(constCmd_spec ys xs).2]; simp⟩
    (fun xs => by rw [(constCmd_spec ys xs).1, outOf_startingMemory])⟩

end Factoring.Aux.Copied.PLib

#print axioms Factoring.Aux.Copied.PLib.polyFun_comp
#print axioms Factoring.Aux.Copied.PLib.polyFun_append
#print axioms Factoring.Aux.Copied.PLib.polyFun_id
#print axioms Factoring.Aux.Copied.PLib.polyFun_const
