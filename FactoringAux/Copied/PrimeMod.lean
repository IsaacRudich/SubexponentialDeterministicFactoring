/-
Adapted from the authors' related work (the whole file).

Not an audit surface.
-/
/-
Number registers and modular arithmetic on PLIB arrays.

A *register* is an array holding a number in cells `0 … L-1` (`Reg`), with the
width `L` in scalar `2`.  The scans of `PrimeBits` are instantiated with fixed
scratch scalars `3` (carry) and `4 5 6 7` (counter and cells); a routine's spec says
what its output registers hold and that it touches nothing else (`Frame`).

* `addR`, `subR`, `ltR`, `shlR`: `a := a + b`, `a := a - b`, `c := [a < b]`, `a := 2a`.
* `addModR`: `a := a + b mod n`; `dblModR`: `a := 2a mod n` (for `a, b < n`,
  `2n ≤ 2^L`).
* `mulModR`: `z := a b mod n` by the bits of `b`, high bit first (`AKS.mulModV`, whose
  value is `AKS.mulModV_eq` in `PrimeCyc`).

Scalars used: `2` width (read only), `3 … 7` scan scratch, `8 … 11` `mulModR`.

Result: `Reg`, `Frame`, `addR_spec`, `subR_spec`, `ltR_spec`, `shlR_spec`,
        `addModR_spec`, `dblModR_spec`, `zeroR_spec`, `mulModR_spec`.

Not an audit surface.
-/
module

public import FactoringAux.Copied.PrimeBits
public import FactoringAux.Copied.PrimeCyc

@[expose] public section

namespace Factoring.Aux.Copied.NTP

open Factoring.Aux.Copied Factoring.Aux.Copied.Aux Factoring.Aux.Copied.PLib Cmd

/-! ### Registers and frames -/

/-- Register `a` holds `v` in `L` bits (`Reg`). -/
def Reg (st : St) (a L v : ℕ) : Prop := SegBits (st.ar a) 0 L ∧ segVal (st.ar a) 0 L = v

/-- `st'` differs from `st` at most on the arrays `As` and the scalars `Ss`. -/
def Frame (st st' : St) (As Ss : List ℕ) : Prop :=
  (∀ a, a ∉ As → st'.ar a = st.ar a) ∧ (∀ z, z ∉ Ss → st'.sc z = st.sc z)

theorem Frame.refl (st : St) (As Ss : List ℕ) : Frame st st As Ss := ⟨fun _ _ => rfl, fun _ _ => rfl⟩

theorem Frame.trans {st st' st'' : St} {As Ss As' Ss' : List ℕ} (h : Frame st st' As Ss)
    (h' : Frame st' st'' As' Ss') : Frame st st'' (As ++ As') (Ss ++ Ss') :=
  ⟨fun a ha => by
      simp only [List.mem_append, not_or] at ha
      rw [h'.1 a ha.2, h.1 a ha.1],
    fun z hz => by
      simp only [List.mem_append, not_or] at hz
      rw [h'.2 z hz.2, h.2 z hz.1]⟩

theorem Frame.mono {st st' : St} {As Ss As' Ss' : List ℕ} (h : Frame st st' As Ss)
    (hA : As ⊆ As') (hS : Ss ⊆ Ss') : Frame st st' As' Ss' :=
  ⟨fun a ha => h.1 a (fun h' => ha (hA h')), fun z hz => h.2 z (fun h' => hz (hS h'))⟩

theorem Reg.frame {st st' : St} {a L v : ℕ} {As Ss : List ℕ} (h : Reg st a L v)
    (hf : Frame st st' As Ss) (ha : a ∉ As) : Reg st' a L v := by
  unfold Reg; rw [hf.1 a ha]; exact h

@[simp] theorem reg_setSc (st : St) (z v a L w : ℕ) : Reg (st.setSc z v) a L w ↔ Reg st a L w :=
  Iff.rfl

theorem Reg.lt {st : St} {a L v : ℕ} (h : Reg st a L v) : v < 2 ^ L := h.2 ▸ segVal_lt h.1

theorem reg_segPut (st : St) (a L S v : ℕ) (hv : v = S) (hS : S < 2 ^ L) :
    Reg (st.putAr a (segPut (st.ar a) 0 L (bitOf S))) a L v := by
  subst hv
  refine ⟨?_, ?_⟩
  · simp only [St.putAr_ar_self]; exact segBits_segPut _ _ _ _
  · simp only [St.putAr_ar_self]; rw [segVal_segPut_bits, Nat.mod_eq_of_lt hS]

/-- The scan scratch. -/
abbrev scr : List ℕ := [3, 4, 5, 6, 7]

theorem nodup_scan : [2, 3, 4, 5, 6, 7].Nodup := by decide

/-! ### The four scans as register operations -/

/-- `a := a + b` (carry in scalar `3`). -/
def addR (a b : ℕ) : Cmd := scanSeg a b 2 3 4 5 6 7 (addStep 5 6 3 7)

/-- `a := a - b`. -/
def subR (a b : ℕ) : Cmd := scanSeg a b 2 3 4 5 6 7 (subStep 5 6 3 7)

/-- `c := [a < b]`. -/
def ltR (a b : ℕ) : Cmd := scanSeg a b 2 3 4 5 6 7 (ltStep 5 6 3 7)

/-- `a := 2 a` (`b` is not read for its value, but must differ from `a`). -/
def shlR (a b : ℕ) : Cmd := scanSeg a b 2 3 4 5 6 7 (shlStep 5 3 7)

theorem frame_scanSc (st : St) (v : ℕ) :
    Frame st ((((((st.setSc 3 v).setSc 5 0).setSc 6 0).setSc 7 0).setSc 4 0)) [] scr :=
  ⟨fun _ _ => rfl, fun z hz => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
    simp [Function.update_apply, hz.1, hz.2.1, hz.2.2.1, hz.2.2.2.1, hz.2.2.2.2]⟩

theorem frame_scan (st : St) (a : ℕ) (P : ℕ → ℕ) (v : ℕ) :
    Frame st ((((((st.putAr a P).setSc 3 v).setSc 5 0).setSc 6 0).setSc 7 0).setSc 4 0) [a] scr :=
  ⟨fun a' ha' => by
    simp only [List.mem_singleton] at ha'
    simp [St.putAr_ar_ne _ _ ha'], (frame_scanSc (st.putAr a P) v).2⟩

theorem addR_spec {a b : ℕ} (hab : a ≠ b) {st : St} {L x y : ℕ} (hL : st.sc 2 = L) (hc : st.sc 3 = 0)
    (ha : Reg st a L x) (hb : Reg st b L y) (hxy : x + y < 2 ^ L) :
    Reg (Cmd.run (addR a b) st).1 a L (x + y) ∧ (Cmd.run (addR a b) st).1.sc 3 = 0 ∧
    Frame st (Cmd.run (addR a b) st).1 [a] scr ∧ (Cmd.run (addR a b) st).2 ≤ 50 * (L + 1) + 10 := by
  obtain ⟨e, hcost⟩ := run_addSeg hab nodup_scan st (hL ▸ ha.1) (hL ▸ hb.1) (by omega)
  simp only [hL, ha.2, hb.2, hc, add_zero] at e hcost
  unfold addR
  rw [e]
  refine ⟨?_, ?_, frame_scan _ _ _ _, hcost⟩
  · simp only [reg_setSc]; exact reg_segPut st a L (x + y) (x + y) rfl hxy
  · simp [Nat.div_eq_of_lt hxy]

theorem subR_spec {a b : ℕ} (hab : a ≠ b) {st : St} {L x y : ℕ} (hL : st.sc 2 = L) (hc : st.sc 3 = 0)
    (ha : Reg st a L x) (hb : Reg st b L y) (hxy : y ≤ x) :
    Reg (Cmd.run (subR a b) st).1 a L (x - y) ∧ (Cmd.run (subR a b) st).1.sc 3 = 0 ∧
    Frame st (Cmd.run (subR a b) st).1 [a] scr ∧ (Cmd.run (subR a b) st).2 ≤ 60 * (L + 1) + 10 := by
  obtain ⟨e, hcost⟩ := run_subSeg hab nodup_scan st (hL ▸ ha.1) (hL ▸ hb.1) (by omega)
    (by rw [hL, ha.2, hb.2, hc]; omega)
  simp only [hL, ha.2, hb.2, hc, Nat.sub_zero] at e hcost
  unfold subR
  rw [e]
  refine ⟨?_, ?_, frame_scan _ _ _ _, hcost⟩
  · simp only [reg_setSc]; exact reg_segPut st a L (x - y) (x - y) rfl (by have := ha.lt; omega)
  · simp

theorem ltR_spec {a b : ℕ} (hab : a ≠ b) {st : St} {L x y : ℕ} (hL : st.sc 2 = L) (hc : st.sc 3 = 0)
    (ha : Reg st a L x) (hb : Reg st b L y) :
    (Cmd.run (ltR a b) st).1.sc 3 = (if x < y then 1 else 0) ∧
    Frame st (Cmd.run (ltR a b) st).1 [] scr ∧ (Cmd.run (ltR a b) st).2 ≤ 30 * (L + 1) + 10 := by
  obtain ⟨e, hcost⟩ := run_ltSeg hab nodup_scan st (hL ▸ ha.1) (hL ▸ hb.1) hc
  simp only [hL, ha.2, hb.2] at e hcost
  unfold ltR
  rw [e]
  exact ⟨by simp, frame_scanSc _ _, hcost⟩

theorem shlR_spec {a b : ℕ} (hab : a ≠ b) {st : St} {L x : ℕ} (hL : st.sc 2 = L) (hc : st.sc 3 = 0)
    (ha : Reg st a L x) (hx : 2 * x < 2 ^ L) :
    Reg (Cmd.run (shlR a b) st).1 a L (2 * x) ∧ (Cmd.run (shlR a b) st).1.sc 3 = 0 ∧
    Frame st (Cmd.run (shlR a b) st).1 [a] scr ∧ (Cmd.run (shlR a b) st).2 ≤ 25 * (L + 1) + 10 := by
  obtain ⟨e, hcost⟩ := run_shlSeg (b := b) hab nodup_scan st (hL ▸ ha.1) (by omega)
  simp only [hL, ha.2, hc, add_zero] at e hcost
  unfold shlR
  rw [e]
  refine ⟨?_, ?_, frame_scan _ _ _ _, hcost⟩
  · simp only [reg_setSc]; exact reg_segPut st a L (2 * x) (2 * x) rfl hx
  · simp [Nat.div_eq_of_lt hx]

/-! ### Modular addition and doubling -/

/-- `a := a + b mod n` (register `m` holds `n`). -/
def addModR (a b m : ℕ) : Cmd := seqs [addR a b, ltR a m, .ifZero 3 (subR a m) .skip, .setK 3 0]

/-- `a := 2 a mod n`. -/
def dblModR (a m : ℕ) : Cmd := seqs [shlR a m, ltR a m, .ifZero 3 (subR a m) .skip, .setK 3 0]

theorem Frame.setSc (st : St) (z v : ℕ) : Frame st (st.setSc z v) [] [z] :=
  ⟨fun _ _ => rfl, fun y hy => by
    simp only [List.mem_singleton] at hy
    simp [Function.update_apply, hy]⟩

/-- After `a` holds `s < 2n`: reduce once. -/
theorem reduce_spec {a m : ℕ} (ham : a ≠ m) {st : St} {L s n : ℕ} (hL : st.sc 2 = L) (hc : st.sc 3 = 0)
    (ha : Reg st a L s) (hm : Reg st m L n) (hs : s < 2 * n) :
    Reg (Cmd.run (seqs [ltR a m, .ifZero 3 (subR a m) .skip, .setK 3 0]) st).1 a L (s % n) ∧
    (Cmd.run (seqs [ltR a m, .ifZero 3 (subR a m) .skip, .setK 3 0]) st).1.sc 3 = 0 ∧
    Frame st (Cmd.run (seqs [ltR a m, .ifZero 3 (subR a m) .skip, .setK 3 0]) st).1 [a] scr ∧
    (Cmd.run (seqs [ltR a m, .ifZero 3 (subR a m) .skip, .setK 3 0]) st).2 ≤ 90 * (L + 1) + 30 := by
  obtain ⟨l1, l2, l3⟩ := ltR_spec ham hL hc ha hm
  have hL1 : (Cmd.run (ltR a m) st).1.sc 2 = L := by rw [l2.2 2 (by decide), hL]
  have ha1 : Reg (Cmd.run (ltR a m) st).1 a L s := ha.frame l2 (by simp)
  have hm1 : Reg (Cmd.run (ltR a m) st).1 m L n := hm.frame l2 (by simp)
  rw [Cmd.run_seqs_cons, Cmd.run_seqs_cons, Cmd.run_seqs_cons, Cmd.run_seqs_nil, Cmd.run_ifZero]
  by_cases hsn : s < n
  · have h3 : (Cmd.run (ltR a m) st).1.sc 3 ≠ 0 := by rw [l1, if_pos hsn]; norm_num
    rw [if_neg h3, Cmd.run_skip, Cmd.run_setK]
    simp only [reg_setSc]
    refine ⟨by rw [Nat.mod_eq_of_lt hsn]; exact ha1, by simp, ?_, by simp; omega⟩
    exact (l2.trans (Frame.setSc _ 3 0)).mono (by simp) (by simp [scr])
  · have h3 : (Cmd.run (ltR a m) st).1.sc 3 = 0 := by rw [l1, if_neg hsn]
    obtain ⟨s1, s2, s3, s4⟩ := subR_spec ham hL1 h3 ha1 hm1 (by omega)
    rw [if_pos h3, Cmd.run_setK]
    simp only [reg_setSc]
    have hmod : s % n = s - n := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    refine ⟨by rw [hmod]; exact s1, by simp, ?_, by simp; omega⟩
    exact ((l2.trans s3).trans (Frame.setSc _ 3 0)).mono (by simp) (by simp [scr])

theorem addModR_spec {a b m : ℕ} (hab : a ≠ b) (ham : a ≠ m) {st : St} {L x y n : ℕ} (hL : st.sc 2 = L)
    (hc : st.sc 3 = 0) (ha : Reg st a L x) (hb : Reg st b L y) (hm : Reg st m L n)
    (hx : x < n) (hy : y < n) (hn : 2 * n ≤ 2 ^ L) :
    Reg (Cmd.run (addModR a b m) st).1 a L ((x + y) % n) ∧ (Cmd.run (addModR a b m) st).1.sc 3 = 0 ∧
    Frame st (Cmd.run (addModR a b m) st).1 [a] scr ∧ (Cmd.run (addModR a b m) st).2 ≤ 150 * (L + 1) + 50 := by
  obtain ⟨s1, s2, s3, s4⟩ := addR_spec hab hL hc ha hb (by omega)
  have hL1 : (Cmd.run (addR a b) st).1.sc 2 = L := by rw [s3.2 2 (by decide), hL]
  have hm1 := hm.frame s3 (by simp [Ne.symm ham])
  obtain ⟨r1, r2, r3, r4⟩ := reduce_spec ham hL1 s2 s1 hm1 (by omega)
  unfold addModR
  rw [Cmd.run_seqs_cons]
  refine ⟨r1, r2, (s3.trans r3).mono (by simp) (by simp), by omega⟩

theorem dblModR_spec {a m : ℕ} (ham : a ≠ m) {st : St} {L x n : ℕ} (hL : st.sc 2 = L)
    (hc : st.sc 3 = 0) (ha : Reg st a L x) (hm : Reg st m L n) (hx : x < n) (hn : 2 * n ≤ 2 ^ L) :
    Reg (Cmd.run (dblModR a m) st).1 a L (2 * x % n) ∧ (Cmd.run (dblModR a m) st).1.sc 3 = 0 ∧
    Frame st (Cmd.run (dblModR a m) st).1 [a] scr ∧ (Cmd.run (dblModR a m) st).2 ≤ 150 * (L + 1) + 50 := by
  obtain ⟨s1, s2, s3, s4⟩ := shlR_spec ham hL hc ha (by omega)
  have hL1 : (Cmd.run (shlR a m) st).1.sc 2 = L := by rw [s3.2 2 (by decide), hL]
  have hm1 := hm.frame s3 (by simp [Ne.symm ham])
  obtain ⟨r1, r2, r3, r4⟩ := reduce_spec ham hL1 s2 s1 hm1 (by omega)
  unfold dblModR
  rw [Cmd.run_seqs_cons]
  refine ⟨r1, r2, (s3.trans r3).mono (by simp) (by simp), by omega⟩

/-! ### Zero and the modular product -/

/-- `z := 0` on `L` cells.  Scalars `8`, `11`. -/
def zeroR (z : ℕ) : Cmd := seqs [.setK 11 0, .loop 2 8 (.wr z 8 0 11), .setK 8 0]

theorem segVal_eq_zero {f : ℕ → ℕ} {L : ℕ} (h : ∀ j < L, f j = 0) : segVal f 0 L = 0 := by
  induction L with
  | zero => rfl
  | succ L ih => simp [segVal, ih (fun j hj => h j (by omega)), h L (by omega)]

theorem zeroR_spec (z : ℕ) {st : St} {L : ℕ} (hL : st.sc 2 = L) :
    Reg (Cmd.run (zeroR z) st).1 z L 0 ∧ Frame st (Cmd.run (zeroR z) st).1 [z] [8, 11] ∧
    (Cmd.run (zeroR z) st).1.sc 11 = 0 ∧ (Cmd.run (zeroR z) st).1.sc 8 = 0 ∧
    (Cmd.run (zeroR z) st).2 ≤ 2 * L + 8 := by
  unfold zeroR
  simp only [Cmd.run_seqs_cons, Cmd.run_seqs_nil, Cmd.run_setK]
  set st1 := st.setSc 11 0
  have hb : st1.sc 2 = L := by simp [st1, Function.update_apply, hL]
  have inv := loop_inv (b := 2) (c := 8) (body := .wr z 8 0 11) (st := st1)
    (fun j st' => (∀ i < j, st'.ar z i = 0) ∧ Frame st1 st' [z] [8])
    ⟨fun i hi => absurd hi (by omega), Frame.refl _ _ _⟩ (fun j st' hj ⟨h1, h2⟩ => by
      refine ⟨fun i hi => ?_, ?_⟩
      · simp only [run_wr, St.setAr_ar, St.setSc_sc, St.setSc_ar, Function.update_apply, if_true]
        rw [h2.2 11 (by decide)]
        by_cases hij : i = j
        · simp [hij, st1]
        · rw [if_neg (by simpa using hij)]; exact h1 i (by omega)
      · refine ⟨fun a ha => ?_, fun y hy => ?_⟩
        · simp only [List.mem_singleton] at ha
          simp only [run_wr, St.setAr_ar, St.setSc_ar, Function.update_apply, if_neg ha]
          exact h2.1 a (by simpa using ha)
        · simp only [List.mem_singleton] at hy
          simp only [run_wr, St.setAr_sc, St.setSc_sc, Function.update_apply, if_neg hy]
          exact h2.2 y (by simpa using hy))
  have hc := loop_cost_le' (b := 2) (c := 8) (body := .wr z 8 0 11) (st := st1) 1 (fun _ => le_refl _)
  rw [hb] at inv hc
  obtain ⟨h1, h2⟩ := inv
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro j hj; simp only [St.setSc_ar, zero_add]; rw [h1 j hj]; omega
  · simp only [St.setSc_ar]; exact segVal_eq_zero (fun j hj => h1 j hj)
  · exact ((Frame.setSc st 11 0).trans (h2.trans (Frame.setSc _ 8 0))).mono (by simp) (by simp)
  · simp only [St.setSc_sc, Function.update_apply]; simp
    rw [h2.2 11 (by decide)]; simp [st1]
  · simp
  · omega

theorem testBit_eq_bitOf (y t : ℕ) : y.testBit t = decide (bitOf y t = 1) := by
  rw [Nat.testBit_eq_decide_div_mod_eq]; rfl

/-- The body of `mulModR`'s loop. -/
def mulBody (z a b m : ℕ) : Cmd :=
  seqs [.copy 9 2, .decr 9, subFrom 9 8 10, .rd 11 b 9 0, dblModR z m,
    .ifZero 11 .skip (addModR z a m), .setK 11 0, .setK 9 0]

theorem mulBody_spec {z a b m : ℕ} (hza : z ≠ a) (hzb : z ≠ b) (hzm : z ≠ m) {st : St} {L x y n v j : ℕ}
    (hL : st.sc 2 = L) (hc : st.sc 3 = 0) (h8 : st.sc 8 = j) (hj : j < L)
    (hz : Reg st z L v) (ha : Reg st a L x) (hb : Reg st b L y) (hm : Reg st m L n)
    (hv : v < n) (hx : x < n) (hn : 2 * n ≤ 2 ^ L) :
    Reg (Cmd.run (mulBody z a b m) st).1 z L
      (if y.testBit (L - 1 - j) then (2 * v % n + x) % n else 2 * v % n) ∧
    (Cmd.run (mulBody z a b m) st).1.sc 3 = 0 ∧
    Frame st (Cmd.run (mulBody z a b m) st).1 [z] (scr ++ [9, 10, 11]) ∧
    (Cmd.run (mulBody z a b m) st).2 ≤ 310 * (L + 1) + 150 := by
  unfold mulBody
  simp only [Cmd.run_seqs_cons, Cmd.run_seqs_nil, Cmd.run_copy, Cmd.run_decr]
  -- the index `L - 1 - j`
  have hsub := run_subFrom (x := 9) (y := 8) (t := 10) (by decide)
    ((st.setSc 9 (st.sc 2)).setSc 9 ((st.setSc 9 (st.sc 2)).sc 9 - 1))
  have hs8 : ((st.setSc 9 (st.sc 2)).setSc 9 ((st.setSc 9 (st.sc 2)).sc 9 - 1)).sc 8 = j := by
    simp [Function.update_apply, h8]
  have hsc := hsub.2
  rw [hs8] at hsc
  rw [hsub.1]
  set st2 := (((st.setSc 9 (st.sc 2)).setSc 9 ((st.setSc 9 (st.sc 2)).sc 9 - 1)).setSc 9
      (((st.setSc 9 (st.sc 2)).setSc 9 ((st.setSc 9 (st.sc 2)).sc 9 - 1)).sc 9 -
        ((st.setSc 9 (st.sc 2)).setSc 9 ((st.setSc 9 (st.sc 2)).sc 9 - 1)).sc 8)).setSc 10 0 with hst2
  have f2 : Frame st st2 [] [9, 10] := ⟨fun _ _ => rfl, fun y hy => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    simp [st2, Function.update_apply, hy.1, hy.2]⟩
  have h9 : st2.sc 9 = L - 1 - j := by simp [st2, Function.update_apply, hL, h8]
  rw [run_rd]
  set bit := st2.ar b (st2.sc 9 + 0)
  have hbit : bit = bitOf y (L - 1 - j) := by
    simp only [bit, h9, add_zero, st2, St.setSc_ar]
    rw [← hb.2]
    have := bitOf_segVal hb.1 (L - 1 - j) (by omega)
    simpa using this.symm
  set st3 := st2.setSc 11 bit
  have f3 : Frame st st3 [] [9, 10, 11] := (f2.trans (Frame.setSc st2 11 bit)).mono (by simp) (by simp)
  have hL3 : st3.sc 2 = L := by rw [f3.2 2 (by decide), hL]
  have hc3 : st3.sc 3 = 0 := by rw [f3.2 3 (by decide), hc]
  obtain ⟨d1, d2, d3, d4⟩ := dblModR_spec hzm hL3 hc3 (hz.frame f3 (by simp)) (hm.frame f3 (by simp)) hv hn
  set st4 := (Cmd.run (dblModR z m) st3).1
  have h11 : st4.sc 11 = bit := by rw [d3.2 11 (by decide)]; simp [st3]
  rw [Cmd.run_ifZero, h11]
  have hbit1 : bit ≤ 1 := hbit ▸ bitOf_le_one _ _
  have htb : y.testBit (L - 1 - j) = decide (bit = 1) := by rw [hbit, testBit_eq_bitOf]
  by_cases hb0 : bit = 0
  · rw [if_pos hb0, Cmd.run_skip, Cmd.run_setK, Cmd.run_setK]
    have : y.testBit (L - 1 - j) = false := by rw [htb]; simp [hb0]
    simp only [reg_setSc, this, Bool.false_eq_true, if_false]
    refine ⟨d1, by simp [d2], ?_, by omega⟩
    exact (((f3.trans d3).trans (Frame.setSc _ 11 0)).trans (Frame.setSc _ 9 0)).mono (by simp)
      (by intro w; simp [scr]; omega)
  · have hb1 : bit = 1 := by omega
    rw [if_neg hb0, Cmd.run_setK, Cmd.run_setK]
    have hL4 : st4.sc 2 = L := by rw [d3.2 2 (by decide), hL3]
    obtain ⟨e1, e2, e3, e4⟩ := addModR_spec hza hzm hL4 d2 d1 ((ha.frame f3 (by simp)).frame d3
      (by simp [Ne.symm hza])) ((hm.frame f3 (by simp)).frame d3 (by simp [Ne.symm hzm]))
      (Nat.mod_lt _ (by omega)) hx hn
    have : y.testBit (L - 1 - j) = true := by rw [htb]; simp [hb1]
    simp only [reg_setSc, this, if_true]
    refine ⟨e1, by simp [e2], ?_, by omega⟩
    exact ((((f3.trans d3).trans e3).trans (Frame.setSc _ 11 0)).trans (Frame.setSc _ 9 0)).mono
      (by simp) (by intro w; simp [scr]; omega)

/-- `z := a b mod n` by the bits of `b` (high bit first); register `m` holds `n`.
Scalars `3 … 11`. -/
def mulModR (z a b m : ℕ) : Cmd := seqs [zeroR z, .loop 2 8 (mulBody z a b m), .setK 8 0]

theorem mulModV_lt {n : ℕ} (hn : 0 < n) (x y B : ℕ) : ∀ j, AKS.mulModV n x y B j < n
  | 0 => hn
  | j + 1 => by unfold AKS.mulModV; split_ifs <;> exact Nat.mod_lt _ hn

/-- **The modular product.** -/
theorem mulModR_spec {z a b m : ℕ} (hza : z ≠ a) (hzb : z ≠ b) (hzm : z ≠ m) {st : St} {L x y n : ℕ}
    (hL : st.sc 2 = L) (hc : st.sc 3 = 0) (ha : Reg st a L x) (hb : Reg st b L y)
    (hm : Reg st m L n) (hx : x < n) (hn : 2 * n ≤ 2 ^ L) :
    Reg (Cmd.run (mulModR z a b m) st).1 z L (x * y % n) ∧ (Cmd.run (mulModR z a b m) st).1.sc 3 = 0 ∧
    Frame st (Cmd.run (mulModR z a b m) st).1 [z] (scr ++ [8, 9, 10, 11]) ∧
    (Cmd.run (mulModR z a b m) st).2 ≤ 400 * (L + 1) ^ 2 := by
  have hn0 : 0 < n := by omega
  obtain ⟨z1, z2, z3, z4, z5⟩ := zeroR_spec z hL
  set st1 := (Cmd.run (zeroR z) st).1
  have hL1 : st1.sc 2 = L := by rw [z2.2 2 (by decide), hL]
  have hc1 : st1.sc 3 = 0 := by rw [z2.2 3 (by decide), hc]
  have ha1 := ha.frame z2 (by simp [Ne.symm hza])
  have hb1 := hb.frame z2 (by simp [Ne.symm hzb])
  have hm1 := hm.frame z2 (by simp [Ne.symm hzm])
  let P : ℕ → St → Prop := fun j st' => Reg st' z L (AKS.mulModV n x y L j) ∧ st'.sc 3 = 0 ∧
    Frame st1 st' [z] (scr ++ [8, 9, 10, 11])
  have h0 : P 0 st1 := ⟨by simpa [AKS.mulModV] using z1, hc1, Frame.refl _ _ _⟩
  have hstep : ∀ j st', j < st1.sc 2 → P j st' → P (j + 1) (Cmd.run (mulBody z a b m) (st'.setSc 8 j)).1 := by
    intro j st' hj ⟨p1, p2, p3⟩
    rw [hL1] at hj
    have q := Frame.setSc st' 8 j
    obtain ⟨b1, b2, b3, b4⟩ := mulBody_spec hza hzb hzm (st := st'.setSc 8 j) (L := L) (x := x) (y := y)
      (n := n) (v := AKS.mulModV n x y L j) (j := j)
      (by rw [q.2 2 (by decide), p3.2 2 (by decide), hL1]) (by rw [q.2 3 (by decide), p2])
      (by simp) hj (by simpa using p1)
      (by simp only [reg_setSc]; exact ha1.frame p3 (by simp [Ne.symm hza]))
      (by simp only [reg_setSc]; exact hb1.frame p3 (by simp [Ne.symm hzb]))
      (by simp only [reg_setSc]; exact hm1.frame p3 (by simp [Ne.symm hzm]))
      (mulModV_lt hn0 _ _ _ _) hx hn
    refine ⟨by simpa [AKS.mulModV] using b1, b2, ((p3.trans q).trans b3).mono (by simp)
      (by intro w; simp [scr]; omega)⟩
  have inv := loop_inv (b := 2) (c := 8) (body := mulBody z a b m) (st := st1) P h0 hstep
  have hcost := loop_cost_le (b := 2) (c := 8) (body := mulBody z a b m) (st := st1) P
    (310 * (L + 1) + 150) h0 hstep (fun j st' hj ⟨p1, p2, p3⟩ => by
      rw [hL1] at hj
      have q := Frame.setSc st' 8 j
      exact (mulBody_spec hza hzb hzm (st := st'.setSc 8 j) (L := L) (x := x) (y := y)
        (n := n) (v := AKS.mulModV n x y L j) (j := j)
        (by rw [q.2 2 (by decide), p3.2 2 (by decide), hL1]) (by rw [q.2 3 (by decide), p2])
        (by simp) hj (by simpa using p1)
        (by simp only [reg_setSc]; exact ha1.frame p3 (by simp [Ne.symm hza]))
        (by simp only [reg_setSc]; exact hb1.frame p3 (by simp [Ne.symm hzb]))
        (by simp only [reg_setSc]; exact hm1.frame p3 (by simp [Ne.symm hzm]))
        (mulModV_lt hn0 _ _ _ _) hx hn).2.2.2)
  rw [hL1] at inv hcost
  obtain ⟨i1, i2, i3⟩ := inv
  unfold mulModR
  simp only [Cmd.run_seqs_cons, Cmd.run_seqs_nil, Cmd.run_setK, reg_setSc]
  have hval : AKS.mulModV n x y L L = x * y % n := by
    rw [AKS.mulModV_eq n x y L hb.lt L le_rfl, Nat.sub_self, pow_zero, Nat.div_one]
  refine ⟨hval ▸ i1, by simp only [St.setSc_sc, Function.update_apply]; exact i2, ?_, ?_⟩
  · exact ((z2.trans i3).trans (Frame.setSc _ 8 0)).mono (by simp) (by intro w; simp [scr]; omega)
  · have : (L + 1) ^ 2 = (L + 1) * (L + 1) := by ring
    rw [this]; nlinarith

end Factoring.Aux.Copied.NTP
