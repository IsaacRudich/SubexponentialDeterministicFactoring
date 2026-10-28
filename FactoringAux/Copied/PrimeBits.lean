/-
Adapted from the authors' related work (the whole file).

Not an audit surface.
-/
/-
Bit-serial arithmetic on segments of PLIB arrays: one generic scan, and add,
subtract, compare and shift as its instances.

A number lives in `L` consecutive cells of an array from an offset (a scalar),
little-endian, one bit (`0`/`1`) per cell (`segVal`).  The generic routine
`scanSeg` walks two segments in step, from the low cell up, with a carry scalar:
at cell `j` it replaces `a[oa + j]` by `fw x y c` and the carry `c` by `fc x y c`,
where `x = a[oa + j]`, `y = b[ob + j]`.  Its exact-state spec (`run_scanSeg`) is
proved once; the instances only prove a small step and the arithmetic of the
carries:

* `addStep`: `a := (a + b + c) mod 2^L`, carry out `(a + b + c) / 2^L` (`scanAdd_val`);
* `subStep`: `a := a - b` when `b ≤ a` (`scanSub_val`);
* `ltStep`: carry out `[a < b]`, `a` unchanged (`scanLt_val`);
* `shlStep`: `a := 2 a + c mod 2^L` (`scanShl_val`).

They follow PLIB's conventions (exact-state specs, scratch zeroed, `List.Nodup`
hypotheses) so PLIB can absorb them.

Result: `segVal`, `segPut`, `scanSeg`, `run_scanSeg`, `addStep`, `subStep`, `ltStep`,
        `shlStep` and their value lemmas.

Not an audit surface.
-/
module

public import FactoringAux.Copied.PlibArr
public import Mathlib.Tactic.IntervalCases

@[expose] public section

namespace Factoring.Aux.Copied.PLib

open Factoring.Aux.Copied Factoring.Aux.Copied.Aux Cmd Finset

/-! ### Segments as numbers -/

/-- The number in cells `o … o+L-1` of `f`, little-endian. -/
def segVal (f : ℕ → ℕ) (o : ℕ) : ℕ → ℕ
  | 0 => 0
  | L + 1 => segVal f o L + f (o + L) * 2 ^ L

/-- Every cell of the segment is a bit. -/
def SegBits (f : ℕ → ℕ) (o L : ℕ) : Prop := ∀ j < L, f (o + j) ≤ 1

/-- Replace cells `o … o+L-1` of `f` by `g 0, …, g (L-1)`. -/
def segPut (f : ℕ → ℕ) (o L : ℕ) (g : ℕ → ℕ) : ℕ → ℕ :=
  fun i => if o ≤ i ∧ i < o + L then g (i - o) else f i

/-- Bit `j` of `x`, as a cell. -/
def bitOf (x j : ℕ) : ℕ := x / 2 ^ j % 2

theorem bitOf_le_one (x j : ℕ) : bitOf x j ≤ 1 := by
  unfold bitOf; have := Nat.mod_lt (x / 2 ^ j) (by norm_num : 0 < 2); omega

theorem segVal_lt {f : ℕ → ℕ} {o : ℕ} : ∀ {L}, SegBits f o L → segVal f o L < 2 ^ L
  | 0, _ => by simp [segVal]
  | L + 1, h => by
      have ih := segVal_lt (L := L) (fun j hj => h j (by omega))
      have := h L (by omega)
      simp only [segVal, pow_succ]
      nlinarith

/-- The cells of the segment are the bits of its value. -/
theorem bitOf_segVal {f : ℕ → ℕ} {o : ℕ} : ∀ {L}, SegBits f o L → ∀ j < L,
    bitOf (segVal f o L) j = f (o + j)
  | 0, _, j, hj => absurd hj (by omega)
  | L + 1, h, j, hj => by
      have hL : SegBits f o L := fun j hj => h j (by omega)
      have hv := segVal_lt hL
      unfold bitOf
      simp only [segVal]
      rcases Nat.lt_or_ge j L with hjL | hjL
      · -- the top cell does not reach bit `j`
        have ih := bitOf_segVal hL j hjL
        unfold bitOf at ih
        have e : f (o + L) * 2 ^ L = (f (o + L) * 2 ^ (L - j)) * 2 ^ j := by
          rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hjL.le]
        rw [e, Nat.add_mul_div_right _ _ (by positivity)]
        have e2 : f (o + L) * 2 ^ (L - j) = 2 * (f (o + L) * 2 ^ (L - j - 1)) := by
          have : 2 ^ (L - j) = 2 * 2 ^ (L - j - 1) := by rw [← pow_succ']; congr 1; omega
          rw [this]; ring
        rw [e2, Nat.add_mul_mod_self_left, ih]
      · have hj : j = L := by omega
        subst hj
        rw [Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hv, zero_add]
        exact Nat.mod_eq_of_lt (by have := h j (by omega); omega)

theorem segVal_congr {f g : ℕ → ℕ} {o : ℕ} : ∀ {L}, (∀ j < L, f (o + j) = g (o + j)) →
    segVal f o L = segVal g o L
  | 0, _ => rfl
  | L + 1, h => by
      simp only [segVal]
      rw [segVal_congr (L := L) (fun j hj => h j (by omega)), h L (by omega)]

/-- The value of bits written by `segPut`. -/
theorem segVal_segPut_bits (f : ℕ → ℕ) (o : ℕ) (x : ℕ) : ∀ L,
    segVal (segPut f o L (bitOf x)) o L = x % 2 ^ L := by
  intro L
  have key : ∀ m, m ≤ L → segVal (segPut f o L (bitOf x)) o m = x % 2 ^ m := by
    intro m
    induction m with
    | zero => intro _; simp [segVal, Nat.mod_one]
    | succ m ih =>
        intro hm
        simp only [segVal, ih (by omega), segPut]
        rw [if_pos ⟨by omega, by omega⟩, show o + m - o = m by omega, bitOf]
        rw [pow_succ, Nat.mod_mul, Nat.mul_comm (2 ^ m)]
  exact key L le_rfl

theorem segBits_segPut (f : ℕ → ℕ) (o L x : ℕ) : SegBits (segPut f o L (bitOf x)) o L := by
  intro j hj
  simp only [segPut, if_pos (⟨by omega, by omega⟩ : o ≤ o + j ∧ o + j < o + L)]
  exact bitOf_le_one _ _

/-! ### The generic scan -/

/-- The carries of a scan over the cells `A j`, `B j`. -/
def scanCarry (fc : ℕ → ℕ → ℕ → ℕ) (A B : ℕ → ℕ) (c0 : ℕ) : ℕ → ℕ
  | 0 => c0
  | j + 1 => fc (A j) (B j) (scanCarry fc A B c0 j)

/-- The cells a scan writes. -/
def scanOut (fw fc : ℕ → ℕ → ℕ → ℕ) (A B : ℕ → ℕ) (c0 : ℕ) (j : ℕ) : ℕ :=
  fw (A j) (B j) (scanCarry fc A B c0 j)

/-- `for j < L: (a[j], c) := (fw x y c, fc x y c)` with `x = a[j]`, `y = b[j]`
(both segments from cell `0`; other offsets go through `copySeg`).  `step` reads
scalars `x y c` and writes `w` (the new cell) and `c`.  Scratch `cnt x y w`. -/
def scanSeg (a b L c cnt x y w : ℕ) (step : Cmd) : Cmd :=
  seqs [.setK x 0, .setK y 0, .setK w 0,
    .loop L cnt (seqs [.rd x a cnt 0, .rd y b cnt 0, step, .wr a cnt 0 w,
      .setK x 0, .setK y 0, .setK w 0]),
    .setK cnt 0]

/-- A step computing `(fw, fc)` exactly, at cost at most `K`. -/
def StepOK (step : Cmd) (x y c w : ℕ) (fw fc : ℕ → ℕ → ℕ → ℕ) (K : ℕ) : Prop :=
  ∀ st, (Cmd.run step st).1 = (st.setSc w (fw (st.sc x) (st.sc y) (st.sc c))).setSc c
      (fc (st.sc x) (st.sc y) (st.sc c)) ∧ (Cmd.run step st).2 ≤ K

/-- The state a scan ends in. -/
def scanSt (st : St) (a b L c : ℕ) (fw fc : ℕ → ℕ → ℕ → ℕ) (cnt x y w : ℕ) : St :=
  (((((st.putAr a (segPut (st.ar a) 0 (st.sc L)
      (scanOut fw fc (st.ar a) (st.ar b) (st.sc c)))).setSc c
      (scanCarry fc (st.ar a) (st.ar b) (st.sc c) (st.sc L))).setSc x 0).setSc y 0).setSc w 0).setSc cnt 0

theorem run_scanSeg {a b L c cnt x y w : ℕ} {step : Cmd} {fw fc : ℕ → ℕ → ℕ → ℕ} {K : ℕ}
    (hab : a ≠ b) (h : [L, c, cnt, x, y, w].Nodup)
    (hstep : StepOK step x y c w fw fc K) (st : St) :
    (Cmd.run (scanSeg a b L c cnt x y w step) st).1 = scanSt st a b L c fw fc cnt x y w ∧
    (Cmd.run (scanSeg a b L c cnt x y w step) st).2 ≤ (K + 20) * (st.sc L + 1) + 10 := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  obtain ⟨⟨h1, h2, h3, h4, h5⟩, ⟨h6, h7, h8, h9⟩, ⟨h10, h11, h12⟩, ⟨h13, h14⟩, h15, -⟩ := h
  set A := st.ar a
  set Bf := st.ar b
  set st1 := ((st.setSc x 0).setSc y 0).setSc w 0 with hst1
  have hL : st1.sc L = st.sc L := by
    simp only [st1, St.setSc_sc, Function.update_apply, h3, h4, h5, if_false]
  let E : ℕ → St := fun j => (((((st.setSc x 0).setSc y 0).setSc w 0).setSc cnt 0).setSc c
      (scanCarry fc A Bf (st.sc c) j)).putAr a (segPut A 0 j (scanOut fw fc A Bf (st.sc c)))
  have s1 := Ne.symm h1; have s2 := Ne.symm h2; have s3 := Ne.symm h3; have s4 := Ne.symm h4
  have s5 := Ne.symm h5; have s6 := Ne.symm h6; have s7 := Ne.symm h7; have s8 := Ne.symm h8
  have s9 := Ne.symm h9; have s10 := Ne.symm h10; have s11 := Ne.symm h11; have s12 := Ne.symm h12
  have s13 := Ne.symm h13; have s14 := Ne.symm h14; have s15 := Ne.symm h15
  have hstepE : ∀ j, j < st1.sc L →
      (Cmd.run (seqs [.rd x a cnt 0, .rd y b cnt 0, step, .wr a cnt 0 w,
        .setK x 0, .setK y 0, .setK w 0]) ((E j).setSc cnt j)).1.setSc cnt 0 = E (j + 1) := by
    intro j _
    simp only [Cmd.run_seqs_cons, Cmd.run_seqs_nil, run_rd, run_wr, Cmd.run_setK]
    rw [(hstep _).1]
    have hx : (E j).ar a j = A j := by
      simp only [E, St.putAr_ar_self, segPut]; rw [if_neg (by omega)]
    have hy : (E j).ar b j = Bf j := by
      simp only [E, St.putAr_ar_ne _ _ hab.symm, St.setSc_ar]; rfl
    have hc : (E j).sc c = scanCarry fc A Bf (st.sc c) j := by simp [E]
    apply St.ext
    · funext z
      simp only [St.setSc_sc, St.setSc_ar, St.setAr_sc, St.setAr_ar, Function.update_apply,
        h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
        s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, if_true, if_false, add_zero,
        hx, hy]
      simp only [E, St.putAr_sc, St.setSc_sc, Function.update_apply, scanCarry]
      split_ifs <;> first | rfl | (subst_vars; simp_all) | omega
    · funext z
      simp only [St.setSc_sc, St.setSc_ar, St.setAr_sc, St.setAr_ar, Function.update_apply,
        h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
        s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, if_true, if_false, add_zero,
        hx, hy]
      simp only [E, St.putAr_ar, St.setSc_ar, Function.update_apply]
      split_ifs with hz
      · subst hz
        funext i
        simp only [segPut, scanOut, scanCarry, Function.update_apply, St.putAr_sc, St.setSc_sc,
          h6, h7, h8, h9, s6, s7, s8, s9, if_false, if_true, hc]
        split_ifs <;> first | rfl | omega | (subst_vars; simp_all)
      · rfl
  have e0 : st1.setSc cnt 0 = E 0 := by
    simp only [E, st1]
    have : segPut A 0 0 (scanOut fw fc A Bf (st.sc c)) = A := by
      funext i; simp [segPut]
    rw [this]
    apply St.ext
    · funext z
      simp only [St.setSc_sc, St.putAr_sc, Function.update_apply, scanCarry]
      split_ifs <;> first | rfl | (subst_vars; simp_all)
    · funext z
      simp only [St.setSc_ar, St.putAr_ar, Function.update_apply, A]
      split_ifs with hz
      · subst hz; rfl
      · rfl
  have e := loop_exact (st := st1) E e0 hstepE
  have hbody : ∀ st', (Cmd.run (seqs [.rd x a cnt 0, .rd y b cnt 0, step, .wr a cnt 0 w,
      .setK x 0, .setK y 0, .setK w 0]) st').2 ≤ K + 15 := by
    intro st'
    rw [Cmd.run_seqs_cons, Cmd.run_seqs_cons, Cmd.run_seqs_cons]
    have := (hstep (Cmd.run (.rd y b cnt 0) (Cmd.run (.rd x a cnt 0) st').1).1).2
    simp only [Cmd.run_seqs_cons, Cmd.run_seqs_nil, run_rd, run_wr, Cmd.run_setK] at this ⊢
    omega
  have hc := loop_exact_cost (st := st1) E (K + 15) e0 hstepE (fun j _ => hbody _)
  rw [hL] at e hc
  simp only [scanSeg, Cmd.run_seqs_cons, Cmd.run_seqs_nil, Cmd.run_setK]
  rw [← hst1]
  constructor
  · rw [e]
    simp only [E, scanSt]
    apply St.ext
    · funext z
      simp only [St.setSc_sc, St.putAr_sc, Function.update_apply]
      split_ifs <;> first | rfl | (subst_vars; simp_all)
    · funext z
      simp only [St.setSc_ar, St.putAr_ar, Function.update_apply]
      split_ifs <;> rfl
  · nlinarith

theorem bitOf_mod {S L j : ℕ} (hj : j < L) : bitOf (S % 2 ^ L) j = bitOf S j := by
  unfold bitOf
  have e : S = S % 2 ^ L + 2 ^ j * (2 * (2 ^ (L - j - 1) * (S / 2 ^ L))) := by
    have : 2 ^ j * (2 * (2 ^ (L - j - 1) * (S / 2 ^ L))) = 2 ^ L * (S / 2 ^ L) := by
      rw [← mul_assoc, ← mul_assoc, ← pow_succ, ← pow_add]; congr 2; omega
    rw [this]; exact (Nat.mod_add_div S (2 ^ L)).symm
  conv_rhs => rw [e]
  rw [Nat.add_mul_div_left _ _ (by positivity), Nat.add_mul_mod_self_left]

theorem segPut_congr {f : ℕ → ℕ} {o L : ℕ} {g g' : ℕ → ℕ} (h : ∀ j < L, g j = g' j) :
    segPut f o L g = segPut f o L g' := by
  funext i; simp only [segPut]; split_ifs with hi
  · exact h _ (by omega)
  · rfl

theorem segPut_self (f : ℕ → ℕ) (L : ℕ) : segPut f 0 L f = f := by
  funext i; simp [segPut]

/-- Bits written are the bits of their value. -/
theorem segPut_eq_bits {f g : ℕ → ℕ} {L : ℕ} (hg : ∀ j < L, g j ≤ 1) (S : ℕ)
    (hS : segVal g 0 L = S % 2 ^ L) : segPut f 0 L g = segPut f 0 L (bitOf S) := by
  refine segPut_congr (fun j hj => ?_)
  have hb : SegBits g 0 L := fun j hj => by simpa using hg j hj
  have := bitOf_segVal hb j hj
  simp only [zero_add] at this
  rw [← this, hS]
  exact bitOf_mod hj



/-! ### Addition -/

/-- `s = x + [y ≠ 0] + [c ≠ 0]`. -/
def addS (x y c : ℕ) : ℕ := x + (if y = 0 then 0 else 1) + (if c = 0 then 0 else 1)

/-- The written cell of an addition step. -/
def addW (x y c : ℕ) : ℕ := if addS x y c = 0 then 0 else if addS x y c - 1 = 0 then 1 else addS x y c - 2

/-- The carry of an addition step. -/
def addC (x y c : ℕ) : ℕ := if addS x y c = 0 then 0 else if addS x y c - 1 = 0 then 0 else 1

/-- One addition step on scalars `x y c`, writing `w` and `c`. -/
def addStep (x y c w : ℕ) : Cmd :=
  seqs [.copy w x, .ifZero y .skip (.incr w), .ifZero c .skip (.incr w), .setK c 0,
    .ifZero w .skip (seqs [.decr w, .ifZero w (.setK w 1) (seqs [.decr w, .setK c 1])])]

theorem addStep_ok {x y c w : ℕ} (h : [c, x, y, w].Nodup) : StepOK (addStep x y c w) x y c w addW addC 30 := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  obtain ⟨⟨h1, h2, h3⟩, ⟨h4, h5⟩, h6, -⟩ := h
  intro st
  simp only [addStep, Cmd.run_seqs_cons, Cmd.run_seqs_nil, Cmd.run_copy, Cmd.run_ifZero, Cmd.run_incr,
    Cmd.run_skip, Cmd.run_setK, Cmd.run_decr]
  have s1 := Ne.symm h1; have s2 := Ne.symm h2; have s3 := Ne.symm h3
  have s4 := Ne.symm h4; have s5 := Ne.symm h5; have s6 := Ne.symm h6
  simp only [St.setSc_sc, Function.update_apply, h1, h2, h3, h4, h5, h6, s1, s2, s3, s4, s5, s6,
    if_true, if_false, apply_ite Prod.fst, apply_ite Prod.snd]
  unfold addW addC addS
  refine ⟨?_, ?_⟩
  · split_ifs <;> (apply St.ext <;> funext z <;> simp only [St.setSc_sc, St.setSc_ar,
      Function.update_apply] <;> split_ifs <;> first | rfl | omega | (subst_vars; simp_all) | simp_all)
  · split_ifs <;> simp

theorem addW_addC {x y c : ℕ} (hx : x ≤ 1) (hy : y ≤ 1) (hc : c ≤ 1) :
    addW x y c + 2 * addC x y c = x + y + c ∧ addW x y c ≤ 1 ∧ addC x y c ≤ 1 := by
  interval_cases x <;> interval_cases y <;> interval_cases c <;> decide

/-- The scan's output and carry as numbers, for any step with a linear invariant. -/
theorem segVal_succ_zero (f : ℕ → ℕ) (m : ℕ) : segVal f 0 (m + 1) = segVal f 0 m + f m * 2 ^ m := by
  simp [segVal]

theorem scanAdd_inv (A B : ℕ → ℕ) (c0 L : ℕ) (hA : ∀ j < L, A j ≤ 1) (hB : ∀ j < L, B j ≤ 1)
    (hc0 : c0 ≤ 1) : ∀ m ≤ L, scanCarry addC A B c0 m ≤ 1 ∧
      segVal (scanOut addW addC A B c0) 0 m + scanCarry addC A B c0 m * 2 ^ m
        = segVal A 0 m + segVal B 0 m + c0
  | 0, _ => by simp [scanCarry, segVal, hc0]
  | m + 1, hm => by
      obtain ⟨ih1, ih2⟩ := scanAdd_inv A B c0 L hA hB hc0 m (by omega)
      have hs := addW_addC (hA m (by omega)) (hB m (by omega)) ih1
      refine ⟨by simp only [scanCarry]; exact hs.2.2, ?_⟩
      simp only [segVal_succ_zero, scanCarry, scanOut] at *
      have h3 : _ * 2 ^ m = _ * 2 ^ m := congrArg (· * 2 ^ m) hs.1
      rw [pow_succ]
      nlinarith [h3]

/-- The general "value of a scan" step: from `S = out + carry · 2^L` with `out < 2^L`. -/
theorem out_carry_of_eq {out carry S L : ℕ} (hout : out < 2 ^ L) (h : out + carry * 2 ^ L = S) :
    out = S % 2 ^ L ∧ carry = S / 2 ^ L := by
  subst h
  constructor
  · rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hout]
  · rw [Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hout, zero_add]

/-- **Addition.**  `a := (a + b + c) mod 2^L`, `c := (a + b + c) / 2^L`. -/
theorem run_addSeg {a b L c cnt x y w : ℕ} (hab : a ≠ b) (h : [L, c, cnt, x, y, w].Nodup) (st : St)
    (hA : SegBits (st.ar a) 0 (st.sc L)) (hB : SegBits (st.ar b) 0 (st.sc L)) (hc : st.sc c ≤ 1) :
    let S := segVal (st.ar a) 0 (st.sc L) + segVal (st.ar b) 0 (st.sc L) + st.sc c
    (Cmd.run (scanSeg a b L c cnt x y w (addStep x y c w)) st).1
      = (((((st.putAr a (segPut (st.ar a) 0 (st.sc L) (bitOf S))).setSc c (S / 2 ^ st.sc L)).setSc x
          0).setSc y 0).setSc w 0).setSc cnt 0 ∧
    (Cmd.run (scanSeg a b L c cnt x y w (addStep x y c w)) st).2 ≤ 50 * (st.sc L + 1) + 10 := by
  intro S
  have hn : [c, x, y, w].Nodup :=
    h.sublist (.cons _ (.cons_cons _ (.cons _ (.cons_cons _ (.cons_cons _ (.cons_cons _ .slnil))))))
  obtain ⟨e, hcost⟩ := run_scanSeg hab h (addStep_ok hn) st
  have hA' : ∀ j < st.sc L, st.ar a j ≤ 1 := fun j hj => by simpa using hA j hj
  have hB' : ∀ j < st.sc L, st.ar b j ≤ 1 := fun j hj => by simpa using hB j hj
  obtain ⟨-, hinv⟩ := scanAdd_inv (st.ar a) (st.ar b) (st.sc c) (st.sc L) hA' hB' hc (st.sc L) le_rfl
  have hob : ∀ j < st.sc L, scanOut addW addC (st.ar a) (st.ar b) (st.sc c) j ≤ 1 := by
    intro j hj
    have := scanAdd_inv (st.ar a) (st.ar b) (st.sc c) (st.sc L) hA' hB' hc j hj.le
    exact (addW_addC (hA' j hj) (hB' j hj) this.1).2.1
  have hlt := segVal_lt (f := scanOut addW addC (st.ar a) (st.ar b) (st.sc c)) (o := 0)
    (fun j hj => by simpa using hob j hj)
  obtain ⟨h1, h2⟩ := out_carry_of_eq hlt hinv
  refine ⟨?_, le_trans hcost (by nlinarith)⟩
  rw [e, scanSt, segPut_eq_bits hob S h1, h2]

/-! ### Subtraction -/

/-- `x + 2 - [y ≠ 0] - [c ≠ 0]`. -/
def subS (x y c : ℕ) : ℕ := x + 2 - (if y = 0 then 0 else 1) - (if c = 0 then 0 else 1)

def subW (x y c : ℕ) : ℕ := if subS x y c = 0 then 0 else if subS x y c - 1 = 0 then 1 else subS x y c - 2

def subC (x y c : ℕ) : ℕ := if subS x y c = 0 then 1 else if subS x y c - 1 = 0 then 1 else 0

/-- One subtraction step (borrow in `c`). -/
def subStep (x y c w : ℕ) : Cmd :=
  seqs [.copy w x, .incr w, .incr w, .ifZero y .skip (.decr w), .ifZero c .skip (.decr w), .setK c 1,
    .ifZero w .skip (seqs [.decr w, .ifZero w (.setK w 1) (seqs [.decr w, .setK c 0])])]

set_option maxHeartbeats 2000000 in
theorem subStep_ok {x y c w : ℕ} (h : [c, x, y, w].Nodup) : StepOK (subStep x y c w) x y c w subW subC 40 := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  obtain ⟨⟨h1, h2, h3⟩, ⟨h4, h5⟩, h6, -⟩ := h
  intro st
  simp only [subStep, Cmd.run_seqs_cons, Cmd.run_seqs_nil, Cmd.run_copy, Cmd.run_ifZero, Cmd.run_incr,
    Cmd.run_skip, Cmd.run_setK, Cmd.run_decr]
  have s1 := Ne.symm h1; have s2 := Ne.symm h2; have s3 := Ne.symm h3
  have s4 := Ne.symm h4; have s5 := Ne.symm h5; have s6 := Ne.symm h6
  simp only [St.setSc_sc, Function.update_apply, h1, h2, h3, h4, h5, h6, s1, s2, s3, s4, s5, s6,
    if_true, if_false, apply_ite Prod.fst, apply_ite Prod.snd]
  unfold subW subC subS
  refine ⟨?_, ?_⟩
  · split_ifs <;> (apply St.ext <;> funext z <;> simp only [St.setSc_sc, St.setSc_ar,
      Function.update_apply] <;> split_ifs <;> first | rfl | omega | (subst_vars; simp_all) | simp_all)
  · split_ifs <;> simp

theorem subW_subC {x y c : ℕ} (hx : x ≤ 1) (hy : y ≤ 1) (hc : c ≤ 1) :
    subW x y c + y + c = x + 2 * subC x y c ∧ subW x y c ≤ 1 ∧ subC x y c ≤ 1 := by
  interval_cases x <;> interval_cases y <;> interval_cases c <;> decide

theorem scanSub_inv (A B : ℕ → ℕ) (c0 L : ℕ) (hA : ∀ j < L, A j ≤ 1) (hB : ∀ j < L, B j ≤ 1)
    (hc0 : c0 ≤ 1) : ∀ m ≤ L, scanCarry subC A B c0 m ≤ 1 ∧
      segVal (scanOut subW subC A B c0) 0 m + segVal B 0 m + c0
        = segVal A 0 m + scanCarry subC A B c0 m * 2 ^ m
  | 0, _ => by simp [scanCarry, segVal, hc0]
  | m + 1, hm => by
      obtain ⟨ih1, ih2⟩ := scanSub_inv A B c0 L hA hB hc0 m (by omega)
      have hs := subW_subC (hA m (by omega)) (hB m (by omega)) ih1
      refine ⟨by simp only [scanCarry]; exact hs.2.2, ?_⟩
      simp only [segVal_succ_zero, scanCarry, scanOut] at *
      have h3 : _ * 2 ^ m = _ * 2 ^ m := congrArg (· * 2 ^ m) hs.1
      rw [pow_succ]
      nlinarith [h3]

/-- **Subtraction.**  With `b + c ≤ a`: `a := a - b - c`, `c := 0`. -/
theorem run_subSeg {a b L c cnt x y w : ℕ} (hab : a ≠ b) (h : [L, c, cnt, x, y, w].Nodup) (st : St)
    (hA : SegBits (st.ar a) 0 (st.sc L)) (hB : SegBits (st.ar b) 0 (st.sc L)) (hc : st.sc c ≤ 1)
    (hle : segVal (st.ar b) 0 (st.sc L) + st.sc c ≤ segVal (st.ar a) 0 (st.sc L)) :
    let S := segVal (st.ar a) 0 (st.sc L) - segVal (st.ar b) 0 (st.sc L) - st.sc c
    (Cmd.run (scanSeg a b L c cnt x y w (subStep x y c w)) st).1
      = (((((st.putAr a (segPut (st.ar a) 0 (st.sc L) (bitOf S))).setSc c 0).setSc x
          0).setSc y 0).setSc w 0).setSc cnt 0 ∧
    (Cmd.run (scanSeg a b L c cnt x y w (subStep x y c w)) st).2 ≤ 60 * (st.sc L + 1) + 10 := by
  intro S
  have hn : [c, x, y, w].Nodup :=
    h.sublist (.cons _ (.cons_cons _ (.cons _ (.cons_cons _ (.cons_cons _ (.cons_cons _ .slnil))))))
  obtain ⟨e, hcost⟩ := run_scanSeg hab h (subStep_ok hn) st
  have hA' : ∀ j < st.sc L, st.ar a j ≤ 1 := fun j hj => by simpa using hA j hj
  have hB' : ∀ j < st.sc L, st.ar b j ≤ 1 := fun j hj => by simpa using hB j hj
  obtain ⟨hcar, hinv⟩ := scanSub_inv (st.ar a) (st.ar b) (st.sc c) (st.sc L) hA' hB' hc (st.sc L) le_rfl
  have hob : ∀ j < st.sc L, scanOut subW subC (st.ar a) (st.ar b) (st.sc c) j ≤ 1 := by
    intro j hj
    have := scanSub_inv (st.ar a) (st.ar b) (st.sc c) (st.sc L) hA' hB' hc j hj.le
    exact (subW_subC (hA' j hj) (hB' j hj) this.1).2.1
  have hlt := segVal_lt (f := scanOut subW subC (st.ar a) (st.ar b) (st.sc c)) (o := 0)
    (fun j hj => by simpa using hob j hj)
  have hAlt := segVal_lt hA
  -- the borrow out is `0`
  have hc0 : scanCarry subC (st.ar a) (st.ar b) (st.sc c) (st.sc L) = 0 := by
    rcases Nat.lt_or_ge (scanCarry subC (st.ar a) (st.ar b) (st.sc c) (st.sc L)) 1 with h1 | h1
    · omega
    · have : 2 ^ st.sc L ≤ scanCarry subC (st.ar a) (st.ar b) (st.sc c) (st.sc L) * 2 ^ st.sc L :=
        Nat.le_mul_of_pos_left _ (by omega)
      omega
  rw [hc0, zero_mul, add_zero] at hinv
  have hout : segVal (scanOut subW subC (st.ar a) (st.ar b) (st.sc c)) 0 (st.sc L) = S % 2 ^ st.sc L := by
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  refine ⟨?_, le_trans hcost (by nlinarith)⟩
  rw [e, scanSt, segPut_eq_bits hob S hout, hc0]

/-! ### Comparison -/

def ltW (x _y _c : ℕ) : ℕ := x
def ltC (x y c : ℕ) : ℕ := if x < y then 1 else if y < x then 0 else c

/-- One comparison step: the cell is kept; `c` is the verdict so far. -/
def ltStep (x y c w : ℕ) : Cmd := seqs [.copy w x, .ifLt x y (.setK c 1) (.ifLt y x (.setK c 0) .skip)]

theorem ltStep_ok {x y c w : ℕ} (h : [c, x, y, w].Nodup) : StepOK (ltStep x y c w) x y c w ltW ltC 10 := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  obtain ⟨⟨h1, h2, h3⟩, ⟨h4, h5⟩, h6, -⟩ := h
  intro st
  have ex : (st.setSc w (st.sc x)).sc x = st.sc x := St.setSc_sc_ne _ _ h5
  have ey : (st.setSc w (st.sc x)).sc y = st.sc y := St.setSc_sc_ne _ _ h6
  simp only [ltStep, Cmd.run_seqs_cons, Cmd.run_seqs_nil, Cmd.run_copy, Cmd.run_ifLt,
    Cmd.run_skip, Cmd.run_setK, ex, ey]
  unfold ltW ltC
  by_cases hxy : st.sc x < st.sc y
  · simp only [if_pos hxy]
    exact ⟨by first | trivial | rfl, by omega⟩
  · by_cases hyx : st.sc y < st.sc x
    · simp only [if_neg hxy, if_pos hyx]
      exact ⟨by first | trivial | rfl, by omega⟩
    · simp only [if_neg hxy, if_neg hyx]
      refine ⟨?_, by omega⟩
      apply St.ext <;> funext z <;> simp only [St.setSc_sc, St.setSc_ar, Function.update_apply] <;>
        split_ifs <;> first | rfl | (subst_vars; simp_all)

theorem scanLt_inv (A B : ℕ → ℕ) (c0 L : ℕ) (hA : ∀ j < L, A j ≤ 1) (hB : ∀ j < L, B j ≤ 1) :
    ∀ m ≤ L, scanCarry ltC A B c0 m =
      if segVal A 0 m < segVal B 0 m then 1 else if segVal B 0 m < segVal A 0 m then 0 else c0
  | 0, _ => by simp [scanCarry, segVal]
  | m + 1, hm => by
      have ih := scanLt_inv A B c0 L hA hB m (by omega)
      have hAm : SegBits A 0 m := fun j hj => by simpa using hA j (by omega)
      have hBm : SegBits B 0 m := fun j hj => by simpa using hB j (by omega)
      have h1 := segVal_lt hAm
      have h2 := segVal_lt hBm
      have ha := hA m (by omega)
      have hb := hB m (by omega)
      simp only [scanCarry, segVal_succ_zero, ltC, ih]
      interval_cases hx : A m <;> interval_cases hy : B m <;> simp <;> split_ifs <;> omega

theorem segPut_scanOut_ltW (A B : ℕ → ℕ) (c0 L : ℕ) :
    segPut A 0 L (scanOut ltW ltC A B c0) = A := by
  funext i; simp only [segPut, scanOut, ltW]; split_ifs <;> simp

/-- **Comparison.**  `c := [a < b]` (from `c = 0`); `a` is unchanged. -/
theorem run_ltSeg {a b L c cnt x y w : ℕ} (hab : a ≠ b) (h : [L, c, cnt, x, y, w].Nodup) (st : St)
    (hA : SegBits (st.ar a) 0 (st.sc L)) (hB : SegBits (st.ar b) 0 (st.sc L)) (hc : st.sc c = 0) :
    (Cmd.run (scanSeg a b L c cnt x y w (ltStep x y c w)) st).1
      = ((((st.setSc c (if segVal (st.ar a) 0 (st.sc L) < segVal (st.ar b) 0 (st.sc L) then 1 else 0)).setSc x
          0).setSc y 0).setSc w 0).setSc cnt 0 ∧
    (Cmd.run (scanSeg a b L c cnt x y w (ltStep x y c w)) st).2 ≤ 30 * (st.sc L + 1) + 10 := by
  have hn : [c, x, y, w].Nodup :=
    h.sublist (.cons _ (.cons_cons _ (.cons _ (.cons_cons _ (.cons_cons _ (.cons_cons _ .slnil))))))
  obtain ⟨e, hcost⟩ := run_scanSeg hab h (ltStep_ok hn) st
  have hA' : ∀ j < st.sc L, st.ar a j ≤ 1 := fun j hj => by simpa using hA j hj
  have hB' : ∀ j < st.sc L, st.ar b j ≤ 1 := fun j hj => by simpa using hB j hj
  have hinv := scanLt_inv (st.ar a) (st.ar b) (st.sc c) (st.sc L) hA' hB' (st.sc L) le_rfl
  refine ⟨?_, le_trans hcost (by nlinarith)⟩
  rw [e, scanSt, segPut_scanOut_ltW, hinv, hc]
  have : st.putAr a (st.ar a) = st := by apply St.ext <;> simp [St.putAr]
  rw [this]
  congr 5
  split_ifs <;> omega

/-! ### Shift -/

def shlW (_x _y c : ℕ) : ℕ := c
def shlC (x _y _c : ℕ) : ℕ := x

/-- One shift step: write the incoming bit, carry out the old one. -/
def shlStep (x c w : ℕ) : Cmd := seqs [.copy w c, .copy c x]

theorem shlStep_ok {x y c w : ℕ} (h : [c, x, y, w].Nodup) : StepOK (shlStep x c w) x y c w shlW shlC 5 := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  obtain ⟨⟨h1, h2, h3⟩, ⟨h4, h5⟩, h6, -⟩ := h
  intro st
  simp only [shlStep, Cmd.run_seqs_cons, Cmd.run_seqs_nil, Cmd.run_copy]
  refine ⟨?_, by simp⟩
  unfold shlW shlC
  apply St.ext <;> funext z <;> simp only [St.setSc_sc, St.setSc_ar, Function.update_apply] <;>
    split_ifs <;> first | rfl | omega | (subst_vars; simp_all) | simp_all

theorem scanShl_inv (A B : ℕ → ℕ) (c0 L : ℕ) (hA : ∀ j < L, A j ≤ 1) :
    ∀ m ≤ L, segVal (scanOut shlW shlC A B c0) 0 m + scanCarry shlC A B c0 m * 2 ^ m
        = 2 * segVal A 0 m + c0
  | 0, _ => by simp [scanCarry, segVal]
  | m + 1, hm => by
      have ih := scanShl_inv A B c0 L hA m (by omega)
      simp only [segVal_succ_zero, scanCarry, scanOut, shlW, shlC] at *
      rw [pow_succ]
      nlinarith [ih]

/-- **Shift.**  `a := (2 a + c) mod 2^L`, `c := ` the bit shifted out (`c ≤ 1`). -/
theorem run_shlSeg {a b L c cnt x y w : ℕ} (hab : a ≠ b) (h : [L, c, cnt, x, y, w].Nodup) (st : St)
    (hA : SegBits (st.ar a) 0 (st.sc L)) (hc : st.sc c ≤ 1) :
    let S := 2 * segVal (st.ar a) 0 (st.sc L) + st.sc c
    (Cmd.run (scanSeg a b L c cnt x y w (shlStep x c w)) st).1
      = (((((st.putAr a (segPut (st.ar a) 0 (st.sc L) (bitOf S))).setSc c (S / 2 ^ st.sc L)).setSc x
          0).setSc y 0).setSc w 0).setSc cnt 0 ∧
    (Cmd.run (scanSeg a b L c cnt x y w (shlStep x c w)) st).2 ≤ 25 * (st.sc L + 1) + 10 := by
  intro S
  have hn : [c, x, y, w].Nodup :=
    h.sublist (.cons _ (.cons_cons _ (.cons _ (.cons_cons _ (.cons_cons _ (.cons_cons _ .slnil))))))
  obtain ⟨e, hcost⟩ := run_scanSeg hab h (shlStep_ok hn) st
  have hA' : ∀ j < st.sc L, st.ar a j ≤ 1 := fun j hj => by simpa using hA j hj
  have hinv := scanShl_inv (st.ar a) (st.ar b) (st.sc c) (st.sc L) hA' (st.sc L) le_rfl
  have hob : ∀ j < st.sc L, scanOut shlW shlC (st.ar a) (st.ar b) (st.sc c) j ≤ 1 := by
    intro j hj
    simp only [scanOut, shlW]
    cases j with
    | zero => simpa [scanCarry] using hc
    | succ j => simp only [scanCarry, shlC]; exact hA' j (by omega)
  have hlt := segVal_lt (f := scanOut shlW shlC (st.ar a) (st.ar b) (st.sc c)) (o := 0)
    (fun j hj => by simpa using hob j hj)
  obtain ⟨h1, h2⟩ := out_carry_of_eq hlt hinv
  refine ⟨?_, le_trans hcost (by nlinarith)⟩
  rw [e, scanSt, segPut_eq_bits hob S h1, h2]

end Factoring.Aux.Copied.PLib
