/-
FactoringAux/Simulate/Swap.lean — L2′, the memory: registers as unary blocks on one stack, and `swap`,
the one routine that touches it (exchange register `r` with the unary stack `V`, in one pass).

Not audited.

The memory stack `MEM` holds `enc bs`: register `i` is the block `true^(bs[i]) false` (register 0 on
top); registers past the end hold 0.  `swap` reads the register number `r` in unary from `R`, and
the new value in unary from `V`; afterwards register `r` holds the old `V`, `V` holds the old value,
and `R` is empty.  It is one pass over `MEM` (a fold, `exec_loop_fold`), then a pass back.
-/
module

public import FactoringAux.SProg.Local

@[expose] public section

namespace Factoring.Aux.Sim

open SProg Function

/-! ### Stacks of the simulation -/
/-- input / output -/
scoped notation "mIO" => (0 : ℕ)
/-- the memory -/
scoped notation "mMEM" => (1 : ℕ)
/-- the memory, reversed, during a pass -/
scoped notation "mTM" => (2 : ℕ)
/-- a register number, unary -/
scoped notation "mR" => (3 : ℕ)
/-- a value, unary -/
scoped notation "mV" => (4 : ℕ)
/-- the old value of the register being swapped -/
scoped notation "mOLD" => (5 : ℕ)
/-- flag: the register was passed -/
scoped notation "mDONE" => (6 : ℕ)
/-- work value A -/
scoped notation "mA" => (7 : ℕ)
/-- work value B -/
scoped notation "mB" => (8 : ℕ)
/-- copy temporary -/
scoped notation "mT1" => (9 : ℕ)
/-- comparison flag -/
scoped notation "mF" => (10 : ℕ)
/-- saved register number -/
scoped notation "mR2" => (11 : ℕ)

/-- Unary. -/
def rep (n : ℕ) : List Bool := List.replicate n true

/-- A one-symbol flag stack. -/
def flag (b : Bool) : List Bool := if b then [true] else []

@[simp] theorem flag_true : flag true = [true] := rfl
@[simp] theorem flag_false : flag false = [] := rfl
@[simp] theorem rep_zero : rep 0 = [] := rfl
theorem rep_succ (n : ℕ) : rep (n + 1) = true :: rep n := rfl
@[simp] theorem length_rep (n : ℕ) : (rep n).length = n := List.length_replicate
@[simp] theorem reverse_rep (n : ℕ) : (rep n).reverse = rep n := List.reverse_replicate

/-- One register. -/
def enc1 (v : ℕ) : List Bool := rep v ++ [false]

/-- The memory stack. -/
def enc : List ℕ → List Bool
  | [] => []
  | b :: bs => enc1 b ++ enc bs

@[simp] theorem enc_nil : enc [] = [] := rfl
@[simp] theorem enc_cons (b : ℕ) (bs : List ℕ) : enc (b :: bs) = enc1 b ++ enc bs := rfl

theorem length_enc : ∀ bs : List ℕ, (enc bs).length = bs.sum + bs.length
  | [] => rfl
  | b :: bs => by simp [enc1, length_enc bs]; try ring

/-- Register `r` (0 past the end). -/
def getR : List ℕ → ℕ → ℕ
  | [], _ => 0
  | b :: _, 0 => b
  | _ :: bs, r + 1 => getR bs r

/-- Set register `r` to `v`, extending with zeros if needed. -/
def setL : List ℕ → ℕ → ℕ → List ℕ
  | [], 0, v => [v]
  | [], r + 1, v => 0 :: setL [] r v
  | _ :: bs, 0, v => v :: bs
  | b :: bs, r + 1, v => b :: setL bs r v

theorem getR_setL : ∀ (bs : List ℕ) (r v i : ℕ), getR (setL bs r v) i = if i = r then v else getR bs i
  | [], 0, v, 0 => rfl
  | [], 0, v, i + 1 => by simp [setL, getR]
  | [], r + 1, v, 0 => by simp [setL, getR]
  | [], r + 1, v, i + 1 => by
      simp only [setL, getR, getR_setL [] r v i, Nat.add_right_cancel_iff]
  | b :: bs, 0, v, 0 => rfl
  | b :: bs, 0, v, i + 1 => by simp [setL, getR]
  | b :: bs, r + 1, v, 0 => by simp [setL, getR]
  | b :: bs, r + 1, v, i + 1 => by
      simp only [setL, getR, getR_setL bs r v i, Nat.add_right_cancel_iff]

theorem length_setL : ∀ (bs : List ℕ) (r v : ℕ), (setL bs r v).length = max bs.length (r + 1)
  | [], 0, v => rfl
  | [], r + 1, v => by simp [setL, length_setL [] r v]
  | b :: bs, 0, v => by simp [setL]
  | b :: bs, r + 1, v => by simp [setL, length_setL bs r v]

theorem sum_setL : ∀ (bs : List ℕ) (r v : ℕ), (setL bs r v).sum ≤ bs.sum + v
  | [], 0, v => by simp [setL]
  | [], r + 1, v => by have := sum_setL [] r v; simp [setL] at this ⊢; omega
  | b :: bs, 0, v => by simp [setL]; omega
  | b :: bs, r + 1, v => by have := sum_setL bs r v; simp [setL]; omega

theorem getR_le_sum : ∀ (bs : List ℕ) (r : ℕ), getR bs r ≤ bs.sum
  | [], _ => Nat.zero_le _
  | b :: bs, 0 => by simp [getR]
  | b :: bs, r + 1 => by have := getR_le_sum bs r; simp [getR]; omega

theorem enc_setL_nil : ∀ r v : ℕ, enc (setL [] r v) = List.replicate r false ++ enc1 v
  | 0, v => by simp [setL]
  | r + 1, v => by simp [setL, enc1, enc_setL_nil r v, List.replicate_succ]

/-! ### The pass -/

/-- What the pass carries: register count still to skip, passed flag, the reversed new memory,
the old value, the value to write. -/
structure SP where
  r : ℕ
  d : Bool
  acc : List Bool
  o : ℕ
  v : ℕ

/-- The stacks during the pass. -/
def scanSt (s : Stacks) (P : SP) : Stacks :=
  update (update (update (update (update s mR (rep P.r)) mDONE (flag P.d)) mTM P.acc) mOLD
    (rep P.o)) mV (rep P.v)

/-- One step of the pass, on values. -/
def sstep (P : SP) : Bool → SP
  | true => if P.d then { P with acc := true :: P.acc }
      else if 0 < P.r then { P with acc := true :: P.acc } else { P with o := P.o + 1 }
  | false => if P.d then { P with acc := false :: P.acc }
      else if 0 < P.r then { P with r := P.r - 1, acc := false :: P.acc }
      else { P with d := true, acc := false :: (rep P.v ++ P.acc), v := 0 }

/-- Its cost. -/
def scost (P : SP) : Bool → ℕ
  | true => if P.d then 3 else if 0 < P.r then 4 else 3
  | false => if P.d then 3 else if 0 < P.r then 3 else 2 * P.v + 5

/-- Body of the pass on a `true` symbol. -/
def swapT : SProg :=
  read mDONE (seq (push mDONE true) (push mTM true)) skip
    (read mR (seq (push mR true) (push mTM true)) skip (push mOLD true))

/-- Body of the pass on a `false` symbol (a block end). -/
def swapF : SProg :=
  read mDONE (seq (push mDONE true) (push mTM false)) skip
    (read mR (push mTM false) skip (seqs [move mV mTM, push mTM false, push mDONE true]))

/-- After the pass: if register `r` lies past the end, append empty registers and then it. -/
def swapTail : SProg :=
  read mDONE skip skip
    (seqs [loop mR (push mTM false) (push mTM false), move mV mTM, push mTM false])

/-- Exchange register `R` with `V`. -/
def swap : SProg := seqs [loop mMEM swapT swapF, swapTail, move mTM mMEM, move mOLD mV]

theorem rep_append_cons (u : ℕ) (b : List Bool) : rep u ++ true :: b = true :: (rep u ++ b) := by
  induction u with
  | zero => rfl
  | succ u ih => rw [rep_succ, List.cons_append, ih]; rfl

theorem rep_ne_nil {n : ℕ} (h : 0 < n) : rep n = true :: rep (n - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rfl

theorem scan_step (s : Stacks) (P : SP) (b : Bool) :
    bodyF swapT swapF (scanSt s P) b = scanSt s (sstep P b) ∧
      bodyC swapT swapF (scanSt s P) b = scost P b := by
  obtain ⟨r, d, acc, o, v⟩ := P
  have hD : scanSt s ⟨r, d, acc, o, v⟩ mDONE = flag d := by simp [scanSt]
  have hR : scanSt s ⟨r, d, acc, o, v⟩ mR = rep r := by simp [scanSt]
  cases b <;> cases d
  · -- false, not done
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · have hR0 : scanSt s ⟨0, false, acc, o, v⟩ mR = [] := by simp [scanSt]
      simp only [bodyF, bodyC, cond_false, swapF, sstep, scost, Bool.false_eq_true, if_false,
        lt_self_iff_false]
      rw [exec_read_nil (by simpa using hD), exec_read_nil hR0, cost_read_nil (by simpa using hD),
        cost_read_nil hR0]
      simp only [exec_seqs_cons, exec_seqs_nil, exec_push, exec_move (show mV ≠ mTM by decide),
        cost_seqs_cons, cost_seqs_nil, cost_push, cost_move _ _ (show mV ≠ mTM by decide)]
      refine ⟨?_, by simp [scanSt]; ring⟩
      simp only [scanSt]
      stacks_ext_with [reverse_rep]
    · have hR1 : scanSt s ⟨r, false, acc, o, v⟩ mR = true :: rep (r - 1) := by
        rw [hR, rep_ne_nil hr]
      simp only [bodyF, bodyC, cond_false, swapF, sstep, scost, Bool.false_eq_true, if_false,
        if_pos hr]
      rw [exec_read_nil (by simpa using hD), exec_read_true hR1, cost_read_nil (by simpa using hD),
        cost_read_true hR1]
      refine ⟨?_, by simp⟩
      simp only [exec_push, scanSt]
      stacks_ext_with []
  · -- false, done
    simp only [bodyF, bodyC, cond_false, swapF, sstep, scost, if_true]
    rw [exec_read_true (l := []) (by simpa using hD), cost_read_true (l := []) (by simpa using hD)]
    refine ⟨?_, by simp⟩
    simp only [exec_seq, exec_push, scanSt]
    stacks_ext_with []
  · -- true, not done
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · have hR0 : scanSt s ⟨0, false, acc, o, v⟩ mR = [] := by simp [scanSt]
      simp only [bodyF, bodyC, cond_true, swapT, sstep, scost, Bool.false_eq_true, if_false,
        lt_self_iff_false]
      rw [exec_read_nil (by simpa using hD), exec_read_nil hR0, cost_read_nil (by simpa using hD),
        cost_read_nil hR0]
      refine ⟨?_, by simp⟩
      simp only [exec_push, scanSt, rep_succ]
      stacks_ext_with []
    · have hR1 : scanSt s ⟨r, false, acc, o, v⟩ mR = true :: rep (r - 1) := by
        rw [hR, rep_ne_nil hr]
      simp only [bodyF, bodyC, cond_true, swapT, sstep, scost, Bool.false_eq_true, if_false,
        if_pos hr]
      rw [exec_read_nil (by simpa using hD), exec_read_true hR1, cost_read_nil (by simpa using hD),
        cost_read_true hR1]
      refine ⟨?_, by simp⟩
      simp only [exec_seq, exec_push, scanSt]
      have hrr : true :: rep (r - 1) = rep r := (rep_ne_nil hr).symm
      stacks_ext_with [hrr]
  · -- true, done
    simp only [bodyF, bodyC, cond_true, swapT, sstep, scost, if_true]
    rw [exec_read_true (l := []) (by simpa using hD), cost_read_true (l := []) (by simpa using hD)]
    refine ⟨?_, by simp⟩
    simp only [exec_seq, exec_push, scanSt]
    stacks_ext_with []

/-- The pure cost of folding `sstep`. -/
def scanCost : SP → List Bool → ℕ
  | _, [] => 0
  | P, b :: l => scost P b + scanCost (sstep P b) l

theorem scan_fold (s : Stacks) : ∀ (l : List Bool) (P : SP),
    l.foldl (bodyF swapT swapF) (scanSt s P) = scanSt s (l.foldl sstep P) ∧
      foldCost (bodyF swapT swapF) (bodyC swapT swapF) (scanSt s P) l = scanCost P l
  | [], P => ⟨rfl, rfl⟩
  | b :: l, P => by
      have h := scan_step s P b
      rw [List.foldl_cons, List.foldl_cons, foldCost_cons, h.1, h.2, (scan_fold s l _).1,
        (scan_fold s l _).2]
      exact ⟨rfl, rfl⟩

theorem scanCost_le : ∀ (l : List Bool) (P : SP), scanCost P l ≤ 5 * l.length + 2 * P.v + 2
  | [], P => by simp [scanCost]
  | b :: l, P => by
      have ih := scanCost_le l (sstep P b)
      obtain ⟨r, d, acc, o, v⟩ := P
      simp only [scanCost, List.length_cons]
      cases b <;> cases d <;> rcases Nat.eq_zero_or_pos r with h | h <;>
        simp [scost, sstep, h] at ih ⊢ <;> omega

/-! ### The pass on values -/

theorem scan_done : ∀ (l : List Bool) (P : SP), P.d = true →
    l.foldl sstep P = { P with acc := l.reverse ++ P.acc }
  | [], P, _ => rfl
  | b :: l, P, hd => by
      obtain ⟨r, d, acc, o, v⟩ := P
      simp only at hd; subst hd
      rw [List.foldl_cons]
      cases b <;>
      · simp only [sstep, if_true]
        rw [scan_done l _ rfl]
        simp

theorem scan_trues_before (u : ℕ) : ∀ (P : SP), P.d = false → 0 < P.r →
    (rep u).foldl sstep P = { P with acc := rep u ++ P.acc } := by
  induction u with
  | zero => intro P _ _; rfl
  | succ u ih =>
      intro P hd hr
      rw [rep_succ, List.foldl_cons]
      obtain ⟨r, d, acc, o, v⟩ := P
      simp only at hd hr; subst hd
      simp only [sstep, Bool.false_eq_true, if_false, if_pos hr]
      rw [ih _ rfl hr, rep_append_cons]; rfl

theorem scan_trues_target (u : ℕ) : ∀ (P : SP), P.d = false → P.r = 0 →
    (rep u).foldl sstep P = { P with o := P.o + u } := by
  induction u with
  | zero => intro P _ _; rfl
  | succ u ih =>
      intro P hd hr
      rw [rep_succ, List.foldl_cons]
      obtain ⟨r, d, acc, o, v⟩ := P
      simp only at hd hr; subst hd hr
      simp only [sstep, Bool.false_eq_true, if_false, lt_self_iff_false]
      rw [ih _ rfl rfl]
      simp; omega

/-- The pass over the whole memory, from `r`, not yet passed, nothing collected. -/
theorem scan_enc : ∀ (bs : List ℕ) (r v : ℕ) (acc : List Bool),
    (enc bs).foldl sstep ⟨r, false, acc, 0, v⟩ =
      if r < bs.length then ⟨0, true, (enc (setL bs r v)).reverse ++ acc, getR bs r, 0⟩
      else ⟨r - bs.length, false, (enc bs).reverse ++ acc, 0, v⟩
  | [], r, v, acc => by simp
  | b :: bs, 0, v, acc => by
      rw [enc_cons, List.foldl_append, enc1, List.foldl_append,
        scan_trues_target b _ rfl rfl]
      simp only [List.foldl_cons, List.foldl_nil, sstep, Bool.false_eq_true, if_false,
        lt_self_iff_false]
      rw [scan_done _ _ rfl]
      simp [setL, getR, enc1]
  | b :: bs, r + 1, v, acc => by
      rw [enc_cons, List.foldl_append, enc1, List.foldl_append,
        scan_trues_before b _ rfl (by simp)]
      simp only [List.foldl_cons, List.foldl_nil, sstep, Bool.false_eq_true, if_false,
        Nat.succ_pos, if_true, Nat.add_sub_cancel]
      rw [scan_enc bs r v]
      simp only [List.length_cons, Nat.add_lt_add_iff_right]
      split_ifs <;> simp [setL, getR, enc1]

theorem getR_of_le : ∀ (bs : List ℕ) (r : ℕ), bs.length ≤ r → getR bs r = 0
  | [], _, _ => rfl
  | b :: bs, 0, h => by simp at h
  | b :: bs, r + 1, h => getR_of_le bs r (by simp at h; omega)

theorem enc_setL_of_le : ∀ (bs : List ℕ) (r v : ℕ), bs.length ≤ r →
    enc (setL bs r v) = enc bs ++ List.replicate (r - bs.length) false ++ enc1 v
  | [], r, v, _ => by simp [enc_setL_nil]
  | b :: bs, 0, v, h => by simp at h
  | b :: bs, r + 1, v, h => by
      simp only [setL, enc_cons, enc_setL_of_le bs r v (by simp at h; omega), List.length_cons,
        Nat.add_sub_add_right, List.append_assoc]

theorem swapT_uses : swapT.uses mMEM = false := by decide
theorem swapF_uses : swapF.uses mMEM = false := by decide

set_option maxHeartbeats 1000000 in
/-- **Swap**: register `r` and the unary stack `V` exchange their values. -/
theorem swap_spec (s : Stacks) (bs : List ℕ) (r v : ℕ) (hM : s mMEM = enc bs) (hR : s mR = rep r)
    (hV : s mV = rep v) (hTM : s mTM = []) (hO : s mOLD = []) (hD : s mDONE = []) :
    swap.exec s = update (update (update s mMEM (enc (setL bs r v))) mR []) mV (rep (getR bs r)) ∧
      swap.cost s ≤ 10 * ((enc bs).length + r + v) + 12 := by
  have hs0 : scanSt s ⟨r, false, [], 0, v⟩ = s := by
    simp only [scanSt]; stacks_ext_with [hR, hV, hTM, hO, hD]
  have hloop : (loop mMEM swapT swapF).exec s =
      update (scanSt s ((enc bs).foldl sstep ⟨r, false, [], 0, v⟩)) mMEM [] := by
    rw [exec_loop_fold swapT_uses swapF_uses, hM]
    conv_lhs => rw [← hs0]
    rw [(scan_fold s _ _).1]
  have hloopc : (loop mMEM swapT swapF).cost s ≤ 6 * (enc bs).length + 2 * v + 3 := by
    rw [cost_loop_fold swapT_uses swapF_uses, hM]
    conv_lhs => rw [← hs0]
    rw [(scan_fold s _ _).2]
    have := scanCost_le (enc bs) ⟨r, false, [], 0, v⟩
    simp only at this
    omega
  have hsplit : ∀ t : Stacks, swap.exec t = (move mOLD mV).exec ((move mTM mMEM).exec
      (swapTail.exec ((loop mMEM swapT swapF).exec t))) ∧
      swap.cost t = (loop mMEM swapT swapF).cost t + (swapTail.cost ((loop mMEM swapT swapF).exec t) +
        ((move mTM mMEM).cost (swapTail.exec ((loop mMEM swapT swapF).exec t)) +
        ((move mOLD mV).cost ((move mTM mMEM).exec (swapTail.exec
          ((loop mMEM swapT swapF).exec t))) + 0))) := fun t => ⟨rfl, rfl⟩
  rw [scan_enc bs r v [], List.append_nil] at hloop
  have hE := length_enc bs
  by_cases hr : r < bs.length
  · rw [if_pos hr] at hloop
    have hD1 : (loop mMEM swapT swapF).exec s mDONE = true :: [] := by rw [hloop]; simp [scanSt]
    have htail : swapTail.exec ((loop mMEM swapT swapF).exec s) =
        update ((loop mMEM swapT swapF).exec s) mDONE [] := by
      rw [swapTail, exec_read_true hD1]; rfl
    have htailc : swapTail.cost ((loop mMEM swapT swapF).exec s) = 1 := by
      rw [swapTail, cost_read_true hD1]; rfl
    have hE' := length_enc (setL bs r v)
    have hs := sum_setL bs r v
    have hl := length_setL bs r v
    have hg := getR_le_sum bs r
    refine ⟨?_, ?_⟩
    · rw [(hsplit s).1, htail, exec_move (by decide), exec_move (by decide), hloop]
      simp only [scanSt]
      stacks_ext_with [hR, hV, hTM, hO, hD, List.reverse_reverse]
    · rw [(hsplit s).2, htail, htailc, cost_move _ _ (by decide), exec_move (by decide),
        cost_move _ _ (by decide), hloop]
      simp [scanSt]
      omega
  · rw [if_neg hr] at hloop
    have hle : bs.length ≤ r := by omega
    have hD1 : (loop mMEM swapT swapF).exec s mDONE = [] := by rw [hloop]; simp [scanSt]
    set S1 := (loop mMEM swapT swapF).exec s with hS1
    have htail : swapTail.exec S1 =
        update (update (update S1 mR []) mV []) mTM
          (false :: (rep v ++ (List.replicate (r - bs.length) false ++ (enc bs).reverse))) := by
      rw [swapTail, exec_read_nil hD1]
      simp only [exec_seqs_cons, exec_seqs_nil, exec_push]
      rw [exec_loop_push (by decide), exec_move (by decide)]
      rw [hloop]; simp only [scanSt]
      stacks_ext_with [reverse_rep, rep]
    have htailc : swapTail.cost S1 ≤ 2 * (r - bs.length) + 2 * v + 4 := by
      rw [swapTail, cost_read_nil hD1]
      simp only [cost_seqs_cons, cost_seqs_nil, exec_seqs_cons, cost_push, cost_loop_push,
        cost_move _ _ (show mV ≠ mTM by decide), exec_loop_push (show mR ≠ mTM by decide)]
      rw [hloop]; simp [scanSt]; omega
    have henc := enc_setL_of_le bs r v hle
    refine ⟨?_, ?_⟩
    · rw [(hsplit s).1, ← hS1, htail, exec_move (by decide), exec_move (by decide), hloop,
        getR_of_le bs r hle, henc]
      simp only [scanSt]
      stacks_ext_with [hR, hV, hTM, hO, hD, enc1, rep, List.reverse_replicate]
    · have hO1 : S1 mOLD = [] := by rw [hloop]; simp [scanSt]
      rw [(hsplit s).2, ← hS1, htail, cost_move _ _ (by decide), exec_move (by decide),
        cost_move _ _ (by decide)]
      simp [hO1]
      have := hloopc
      omega

end Factoring.Aux.Sim
