/-
FactoringAux/Trial/Setup.lean — specifications of `setup` and `finish`.

Not audited.
-/
module

public import FactoringAux.Trial.Step

@[expose] public section

namespace Factoring.Aux.Trial

open SProg Function Computability

/-! ### Reading the input -/

/-- The toggle after `m` more input bits. -/
def tf : Bool → ℕ → Bool
  | t, 0 => t
  | t, m + 1 => tf (!t) m

/-- The number of marks pushed on `H` during `m` more input bits. -/
def hc : Bool → ℕ → ℕ
  | _, 0 => 0
  | t, m + 1 => (if t then 0 else 1) + hc (!t) m

theorem hc_eq : ∀ m : ℕ, hc false m = (m + 1) / 2 ∧ hc true m = m / 2
  | 0 => by simp [hc]
  | m + 1 => by
      have := hc_eq m
      simp only [hc, Bool.not_false, Bool.not_true, this]
      constructor <;> simp <;> omega

theorem rep_cons (n : ℕ) (b : Bool) (l : List Bool) :
    List.replicate n b ++ b :: l = b :: (List.replicate n b ++ l) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih]

theorem bodyIn_spec (x t : Bool) (s : Stacks) (h8 : s sT = cstk t) :
    (bodyIn x).exec s = update (update (update (update s sNR (x :: s sNR)) sW (true :: s sW)) sT
      (cstk (!t))) sH (List.replicate (if t then 0 else 1) true ++ s sH) := by
  unfold bodyIn
  simp only [exec_seqs_cons, exec_seqs_nil, exec_push]
  cases t
  · rw [exec_read_nil (by simpa using h8)]
    simp only [exec_seq, exec_push]
    stacks_ext_with [h8]
  · rw [exec_read_true (l := []) (by simpa using h8)]
    simp only [exec_skip]
    stacks_ext_with [h8]

theorem bodyIn_cost (x : Bool) (s : Stacks) : (bodyIn x).cost s ≤ 5 := by
  have h := cost_le_lfBound (bodyIn x) s (by cases x <;> decide)
  have : (bodyIn x).lfBound ≤ 5 := by cases x <;> decide
  omega

theorem inLoop : ∀ (l : List Bool) (t : Bool) (s : Stacks), s sIO = l → s sT = cstk t →
    loopExec sIO (fun x => bif x then (bodyIn true).exec else (bodyIn false).exec) l s =
      update (update (update (update (update s sIO []) sNR (l.reverse ++ s sNR))
        sW (List.replicate l.length true ++ s sW)) sT (cstk (tf t l.length)))
        sH (List.replicate (hc t l.length) true ++ s sH)
  | [], t, s, h0, h8 => by
      simp only [loopExec_nil, List.reverse_nil, List.nil_append, List.length_nil, tf, hc,
        List.replicate_zero]
      stacks_ext
  | x :: l, t, s, h0, h8 => by
      rw [loopExec_cons]
      have e : (bif x then (bodyIn true).exec else (bodyIn false).exec) (update s sIO l) =
          (bodyIn x).exec (update s sIO l) := by cases x <;> rfl
      rw [e, bodyIn_spec x t _ (by simp [h8]), inLoop l (!t) _ (by simp) (by simp)]
      simp only [List.length_cons, tf, hc, List.reverse_cons, List.append_assoc,
        List.singleton_append, List.replicate_succ', List.replicate_add]
      stacks_ext_with [h0, h8, rep_cons]

/-- The doubling loop body: `CTR := 2 CTR` (all marks). -/
theorem dbl_spec (c : ℕ) (s : Stacks) (h6 : s sCTR = List.replicate c true) (h8 : s sT = []) :
    dbl.exec s = update s sCTR (List.replicate (2 * c) true) ∧ dbl.cost s = 7 * c + 2 := by
  have H : ∀ (l : List Bool) (s : Stacks), s sCTR = l →
      loopExec sCTR (fun x => bif x then (seq (push sT true) (push sT true)).exec
        else (seq (push sT true) (push sT true)).exec) l s =
        update (update s sCTR []) sT (List.replicate (2 * l.length) true ++ s sT) ∧
      loopCost sCTR (fun x => bif x then (seq (push sT true) (push sT true)).exec
        else (seq (push sT true) (push sT true)).exec)
        (fun x => bif x then (seq (push sT true) (push sT true)).cost
          else (seq (push sT true) (push sT true)).cost) l s = 3 * l.length + 1 := by
    intro l
    induction l with
    | nil => intro s hs; refine ⟨?_, rfl⟩; rw [loopExec_nil, ← hs]; stacks_ext
    | cons x l ih =>
        intro s hs
        have e : (bif x then (seq (push sT true) (push sT true)).exec
            else (seq (push sT true) (push sT true)).exec) (update s sCTR l) =
            update (update s sCTR l) sT (true :: true :: s sT) := by
          cases x <;> simp
        have ec : (bif x then (seq (push sT true) (push sT true)).cost
            else (seq (push sT true) (push sT true)).cost) (update s sCTR l) = 2 := by
          cases x <;> simp
        rw [loopExec_cons, loopCost_cons, e, ec]
        have ih' := ih (update (update s sCTR l) sT (true :: true :: s sT)) (by simp)
        rw [ih'.1, ih'.2]
        refine ⟨?_, by simp; ring⟩
        simp only [List.length_cons, Nat.mul_succ, List.replicate_add]
        stacks_ext_with [hs]
  have hl := H (s sCTR) s rfl
  rw [h6, List.length_replicate, h8, List.append_nil] at hl
  refine ⟨?_, ?_⟩
  · show (move sT sCTR).exec ((loop sCTR _ _).exec s) = _
    rw [exec_loop, h6, hl.1, exec_move (by decide)]
    stacks_ext_with [h8]
  · show (loop sCTR _ _).cost s + (move sT sCTR).cost ((loop sCTR _ _).exec s) = _
    rw [cost_loop, exec_loop, h6, hl.1, hl.2, cost_move _ _ (by decide)]
    simp; ring

theorem hLoop : ∀ (hl : List Bool) (c : ℕ) (s : Stacks), s sH = hl →
    s sCTR = List.replicate c true → s sT = [] →
    loopExec sH (fun x => bif x then dbl.exec else dbl.exec) hl s =
        update (update s sH []) sCTR (List.replicate (c * 2 ^ hl.length) true) ∧
      loopCost sH (fun x => bif x then dbl.exec else dbl.exec)
        (fun x => bif x then dbl.cost else dbl.cost) hl s + 7 * c ≤
        7 * c * 2 ^ hl.length + 3 * hl.length + 1
  | [], c, s, h7, h6, _ => by
      refine ⟨?_, by simp only [loopCost_nil, List.length_nil, pow_zero]; omega⟩
      simp only [loopExec_nil, List.length_nil, pow_zero, Nat.mul_one]
      rw [← h7, ← h6]; stacks_ext
  | x :: hl, c, s, h7, h6, h8 => by
      have hF : (bif x then dbl.exec else dbl.exec) = dbl.exec := by cases x <;> rfl
      have hC : (bif x then dbl.cost else dbl.cost) = dbl.cost := by cases x <;> rfl
      have hd := dbl_spec c (update s sH hl) (by simp [h6]) (by simp [h8])
      rw [loopExec_cons, loopCost_cons, hF, hC, hd.1, hd.2]
      have ih := hLoop hl (2 * c) (update (update s sH hl) sCTR (List.replicate (2 * c) true))
        (by simp) (by simp) (by simp [h8])
      refine ⟨?_, ?_⟩
      · rw [ih.1]
        simp only [List.length_cons, pow_succ]
        rw [show 2 * c * (2 ^ hl.length) = c * (2 ^ hl.length * 2) by ring]
        stacks_ext
      · have := ih.2
        simp only [List.length_cons, pow_succ]
        nlinarith

theorem bitsW_two (k : ℕ) : bitsW (k + 2) 2 = false :: true :: List.replicate k false := by
  simp [bitsW_succ, bitsW_zero_eq]

/-- The state after reading the input. -/
def stB (w : ℕ) (nr ctr : List Bool) : Stacks :=
  fun j => if j = sW then List.replicate w true else if j = sNR then nr
    else if j = sCTR then ctr else []

set_option maxHeartbeats 1000000 in
theorem setupA_spec (l : List Bool) :
    setupA.exec (initStacks l) = update (stB (l.length + 3) (false :: false :: false :: l.reverse)
        [true]) sH (List.replicate ((l.length + 1) / 2) true) ∧
      setupA.cost (initStacks l) ≤ 6 * l.length + 10 := by
  have hin := inLoop l false (initStacks l) (by simp [initStacks]) (by simp [initStacks])
  have hinc : (loop sIO (bodyIn true) (bodyIn false)).cost (initStacks l) ≤ 6 * l.length + 1 := by
    rw [cost_loop]
    have := loopCost_le (k := sIO) (f := fun b => bif b then (bodyIn true).exec
      else (bodyIn false).exec) (c := fun b => bif b then (bodyIn true).cost
      else (bodyIn false).cost) (B := 5) (fun x s => by cases x <;> exact bodyIn_cost _ s)
      (initStacks l sIO) (initStacks l)
    simpa [initStacks] using this
  have htf : (cstk (tf false l.length)).length ≤ 1 := by
    cases tf false l.length <;> simp
  rw [(hc_eq l.length).1] at hin
  refine ⟨?_, ?_⟩
  · simp only [setupA, exec_seqs_cons, exec_seqs_nil, exec_push]
    rw [exec_loop, show initStacks l sIO = l by simp [initStacks], hin, exec_clear]
    clear hin hinc htf
    simp only [initStacks, Function.update_self, Function.update_of_ne, ne_eq, not_false_eq_true,
      List.append_nil]
    funext j; simp only [update_apply, stB]
    have rep3 : List.replicate (l.length + 3) true =
        true :: true :: true :: List.replicate l.length true := rfl
    split_ifs <;> (try subst j) <;> first | omega | contradiction | simp [rep3]
  · simp only [setupA, cost_seqs_cons, cost_seqs_nil, cost_push, exec_seqs_cons, exec_push]
    rw [cost_clear, exec_loop, show initStacks l sIO = l by simp [initStacks], hin]
    simp
    omega

theorem setupB_spec (w H : ℕ) (nr : List Bool) :
    setupB.exec (update (stB w nr [true]) sH (List.replicate H true)) =
        stB w nr (List.replicate (2 ^ H) true) ∧
      setupB.cost (update (stB w nr [true]) sH (List.replicate H true)) ≤ 7 * 2 ^ H + 3 * H + 1 := by
  have h := hLoop (List.replicate H true) 1 (update (stB w nr [true]) sH (List.replicate H true))
    (by simp) (by simp [stB]) (by simp [stB])
  rw [List.length_replicate, Nat.one_mul] at h
  refine ⟨?_, ?_⟩
  · rw [setupB, exec_loop, update_self, h.1]
    funext j; simp only [update_apply, stB]; split_ifs <;> simp_all
  · rw [setupB, cost_loop, update_self]; have := h.2; omega

theorem setupC_spec (k : ℕ) (nr ctr : List Bool) :
    setupC.exec (stB (k + 2) nr ctr) = mainSt (k + 2) nr 2 none ctr ∧
      setupC.cost (stB (k + 2) nr ctr) ≤ 7 * k + 25 := by
  have e10 : stB (k + 2) nr ctr sCNT = [] := by simp [stB]
  have e18 : stB (k + 2) nr ctr sTMP = [] := by simp [stB]
  have e3 : stB (k + 2) nr ctr sD = [] := by simp [stB]
  have e1 : stB (k + 2) nr ctr sW = List.replicate (k + 2) true := by simp [stB]
  have hcp : (copy sW sCNT sTMP).exec (stB (k + 2) nr ctr) =
      update (stB (k + 2) nr ctr) sCNT (List.replicate (k + 2) true) := by
    rw [exec_copy (by decide) (by decide) (by decide) _ e18, e1, e10, List.append_nil]
  have hcpc : (copy sW sCNT sTMP).cost (stB (k + 2) nr ctr) = 5 * (k + 2) + 2 := by
    rw [cost_copy (by decide) (by decide) (by decide) _ e18, e1, List.length_replicate]
  have hl : (loop sCNT (push sD false) (push sD false)).exec
      (update (stB (k + 2) nr ctr) sCNT (List.replicate (k + 2) true)) =
      update (stB (k + 2) nr ctr) sD (false :: false :: List.replicate k false) := by
    rw [exec_loop_push (by decide)]
    simp only [update_self, List.length_replicate, update_idem]
    rw [update_of_ne (by decide), e3, List.append_nil]
    rw [show List.replicate (k + 2) false = false :: false :: List.replicate k false from rfl]
    funext j; simp only [update_apply]; split_ifs <;> simp_all [e10]
  have hlc : (loop sCNT (push sD false) (push sD false)).cost
      (update (stB (k + 2) nr ctr) sCNT (List.replicate (k + 2) true)) = 2 * (k + 2) + 1 := by
    rw [cost_loop_push]; simp
  have hp1 : (pop sD).exec (update (stB (k + 2) nr ctr) sD (false :: false :: List.replicate k false))
      = update (stB (k + 2) nr ctr) sD (false :: List.replicate k false) := by
    rw [exec_pop_cons (x := false) (l := false :: List.replicate k false) (by simp)]; simp
  have hp2 : (pop sD).exec (update (stB (k + 2) nr ctr) sD (false :: List.replicate k false))
      = update (stB (k + 2) nr ctr) sD (List.replicate k false) := by
    rw [exec_pop_cons (x := false) (l := List.replicate k false) (by simp)]; simp
  have c1 := cost_pop_le sD (update (stB (k + 2) nr ctr) sD (false :: false :: List.replicate k false))
  have c2 := cost_pop_le sD (update (stB (k + 2) nr ctr) sD (false :: List.replicate k false))
  refine ⟨?_, ?_⟩
  · simp only [setupC, exec_seqs_cons, exec_seqs_nil]
    rw [hcp, hl, hp1, hp2]
    simp only [exec_push, update_self, update_idem, bitsW_two]
    funext j; simp only [update_apply, stB, mainSt]; split_ifs <;> simp_all [bitsW_two]
  · simp only [setupC, cost_seqs_cons, cost_seqs_nil, exec_seqs_cons, cost_push]
    rw [hcpc, hcp, hlc, hl, hp1]
    omega

/-! ### Output -/

/-- The seen flag after the output loop. -/
def seenF : Bool → List Bool → Bool
  | f, [] => f
  | _, true :: ms => seenF true ms
  | f, false :: ms => seenF f ms

/-- Output loop bodies. -/
abbrev bOutT : SProg := seqs [clear sZ, push sZ true, push sIO true]
abbrev bOutF : SProg := read sZ (seq (push sZ true) (push sIO false)) skip skip

theorem outLoop : ∀ (ms : List Bool) (seen : Bool) (s : Stacks), s sT = ms → s sZ = cstk seen →
    loopExec sT (fun x => bif x then bOutT.exec else bOutF.exec) ms s =
        update (update (update s sT []) sZ (cstk (seenF seen ms))) sIO (stripAux seen ms (s sIO)) ∧
      loopCost sT (fun x => bif x then bOutT.exec else bOutF.exec)
        (fun x => bif x then bOutT.cost else bOutF.cost) ms s ≤ 5 * ms.length + 1
  | [], seen, s, h8, h17 => by
      refine ⟨?_, by simp⟩
      simp only [loopExec_nil, seenF, stripAux]
      rw [← h8, ← h17]; stacks_ext
  | x :: ms, seen, s, h8, h17 => by
      rw [loopExec_cons, loopCost_cons]
      cases x
      · -- false
        cases seen
        · have hz : update s sT ms sZ = [] := by simp [h17]
          have e : (bif false then bOutT.exec else bOutF.exec) (update s sT ms) = update s sT ms := by
            show bOutF.exec _ = _
            rw [exec_read_nil hz]; rfl
          have ec : (bif false then bOutT.cost else bOutF.cost) (update s sT ms) = 1 := by
            show bOutF.cost _ = _
            rw [cost_read_nil hz]; rfl
          rw [e, ec]
          have ih := outLoop ms false (update s sT ms) (by simp) (by simp [h17])
          rw [ih.1]
          refine ⟨?_, by have := ih.2; simp at this ⊢; omega⟩
          simp only [seenF, stripAux, Bool.false_eq_true, if_false]
          stacks_ext
        · have hz : update s sT ms sZ = true :: [] := by simp [h17]
          have e : (bif false then bOutT.exec else bOutF.exec) (update s sT ms) =
              update (update (update s sT ms) sZ [true]) sIO (false :: s sIO) := by
            show bOutF.exec _ = _
            rw [exec_read_true hz]
            simp only [exec_seq, exec_push]
            stacks_ext
          have ec : (bif false then bOutT.cost else bOutF.cost) (update s sT ms) = 3 := by
            show bOutF.cost _ = _
            rw [cost_read_true hz]; rfl
          rw [e, ec]
          have ih := outLoop ms true (update (update (update s sT ms) sZ [true]) sIO (false :: s sIO))
            (by simp) (by simp)
          rw [ih.1]
          refine ⟨?_, by have := ih.2; simp at this ⊢; omega⟩
          simp only [seenF, stripAux, if_true]
          stacks_ext
      · -- true
        have e : (bif true then bOutT.exec else bOutF.exec) (update s sT ms) =
            update (update (update s sT ms) sZ [true]) sIO (true :: s sIO) := by
          show bOutT.exec _ = _
          simp only [exec_seqs_cons, exec_seqs_nil, exec_push, exec_clear]
          stacks_ext
        have ec : (bif true then bOutT.cost else bOutF.cost) (update s sT ms) ≤ 4 := by
          show bOutT.cost _ ≤ _
          simp only [cost_seqs_cons, cost_seqs_nil, cost_push, cost_clear]
          cases seen <;> simp [h17]
        rw [e]
        have ih := outLoop ms true (update (update (update s sT ms) sZ [true]) sIO (true :: s sIO))
          (by simp) (by simp)
        rw [ih.1]
        refine ⟨?_, by have := ih.2; simp only [List.length_cons]; omega⟩
        simp only [seenF, stripAux]
        stacks_ext

theorem finish_def : finish = seqs [read sFD (clear sNR) skip (move sNR sANS), move sANS sT,
    loop sT bOutT bOutF, clear sZ, clear sW, clear sD] := rfl

theorem cstk_length_le (b : Bool) : (cstk b).length ≤ 1 := by cases b <;> simp

/-- The output from the state where `T` holds the MSB-first answer `ms`. -/
theorem finish_tail (w : ℕ) (ms : List Bool) (s : Stacks) (h8 : s sT = ms) (h17 : s sZ = [])
    (h0 : s sIO = []) (h1 : s sW = List.replicate w true) (hD : (s sD).length ≤ w)
    (hrest : ∀ j, j ≠ sT → j ≠ sW → j ≠ sD → s j = []) :
    (seqs [loop sT bOutT bOutF, clear sZ, clear sW, clear sD]).exec s =
        initStacks (stripAux false ms []) ∧
      (seqs [loop sT bOutT bOutF, clear sZ, clear sW, clear sD]).cost s ≤ 5 * ms.length + 2 * w + 6 := by
  have ho := outLoop ms false s h8 (by simp [h17])
  rw [h0] at ho
  refine ⟨?_, ?_⟩
  · simp only [exec_seqs_cons, exec_seqs_nil, exec_clear]
    rw [exec_loop, h8, ho.1]
    funext j
    simp only [update_apply, initStacks]
    split_ifs <;> (try subst j) <;> first | omega | simp_all
  · simp only [cost_seqs_cons, cost_seqs_nil, exec_seqs_cons, cost_clear, exec_clear]
    rw [cost_loop, exec_loop, h8, ho.1]
    have ho2 := ho.2
    have := cstk_length_le (seenF false ms)
    simp [h1] at ho2 ⊢
    omega

/-- The output: from the final state of the main loop, stack 0 holds `encodeNat ans` and all other
stacks are empty. -/
theorem finish_spec (w d : ℕ) (nr : List Bool) (fa : Option ℕ) (hnr : nr.length = w) :
    finish.exec (mainSt w nr d fa []) =
        initStacks (encodeNat (fa.elim (valFrom 0 nr) (fun a => valL (bitsW w a)))) ∧
      finish.cost (mainSt w nr d fa []) ≤ 12 * w + 12 := by
  have split : ∀ s, finish.exec s = (seqs [loop sT bOutT bOutF, clear sZ, clear sW, clear sD]).exec
      ((move sANS sT).exec ((read sFD (clear sNR) skip (move sNR sANS)).exec s)) ∧
    finish.cost s = (read sFD (clear sNR) skip (move sNR sANS)).cost s +
      ((move sANS sT).cost ((read sFD (clear sNR) skip (move sNR sANS)).exec s) +
      (seqs [loop sT bOutT bOutF, clear sZ, clear sW, clear sD]).cost
        ((move sANS sT).exec ((read sFD (clear sNR) skip (move sNR sANS)).exec s))) :=
    fun s => ⟨rfl, rfl⟩
  cases fa with
  | none =>
      have hFD : mainSt w nr d none [] sFD = [] := by simp [mainSt]
      set sa := (read sFD (clear sNR) skip (move sNR sANS)).exec (mainSt w nr d none []) with hsa
      have hsa' : sa = update (update (mainSt w nr d none []) sNR []) sANS (nr.reverse) := by
        rw [hsa, exec_read_nil hFD, exec_move (by decide)]; simp [mainSt]
      have hca : (read sFD (clear sNR) skip (move sNR sANS)).cost (mainSt w nr d none []) =
          2 * w + 2 := by
        rw [cost_read_nil hFD, cost_move _ _ (by decide)]; simp [mainSt, hnr]; ring
      set sb := (move sANS sT).exec sa with hsb
      have hsb' : sb = update (update sa sANS []) sT nr := by
        rw [hsb, exec_move (by decide), hsa']; simp [mainSt]
      have hcb : (move sANS sT).cost sa = 2 * w + 1 := by
        rw [cost_move _ _ (by decide), hsa']; simp [hnr]
      have ht := finish_tail w nr sb (by rw [hsb']; simp) (by rw [hsb', hsa']; simp [mainSt])
        (by rw [hsb', hsa']; simp [mainSt]) (by rw [hsb', hsa']; simp [mainSt])
        (by rw [hsb', hsa']; simp [mainSt])
        (by intro j h1 h2 h3; rw [hsb', hsa']; simp only [update_apply, mainSt];
            split_ifs <;> simp_all)
      have hstrip : stripAux false nr [] = encodeNat (valFrom 0 nr) := stripAux_encodeNat nr 0
      refine ⟨?_, ?_⟩
      · rw [(split _).1, ← hsa, ← hsb, ht.1, hstrip]; rfl
      · rw [(split _).2, ← hsa, ← hsb, hca, hcb]; have := ht.2; rw [hnr] at this; omega
  | some a =>
      have hFD : mainSt w nr d (some a) [] sFD = true :: [] := by simp [mainSt]
      set sa := (read sFD (clear sNR) skip (move sNR sANS)).exec (mainSt w nr d (some a) [])
        with hsa
      have hsa' : sa = update (update (mainSt w nr d (some a) []) sFD []) sNR [] := by
        rw [hsa, exec_read_true hFD, exec_clear]
      have hca : (read sFD (clear sNR) skip (move sNR sANS)).cost (mainSt w nr d (some a) []) =
          w + 2 := by
        rw [cost_read_true hFD, cost_clear]; simp [mainSt, hnr]; ring
      set sb := (move sANS sT).exec sa with hsb
      have hsb' : sb = update (update sa sANS []) sT (bitsW w a).reverse := by
        rw [hsb, exec_move (by decide), hsa']; simp [mainSt]
      have hcb : (move sANS sT).cost sa = 2 * w + 1 := by
        rw [cost_move _ _ (by decide), hsa']; simp [mainSt]
      have ht := finish_tail w (bitsW w a).reverse sb (by rw [hsb']; simp)
        (by rw [hsb', hsa']; simp [mainSt]) (by rw [hsb', hsa']; simp [mainSt])
        (by rw [hsb', hsa']; simp [mainSt]) (by rw [hsb', hsa']; simp [mainSt])
        (by intro j h1 h2 h3; rw [hsb', hsa']; simp only [update_apply, mainSt];
            split_ifs <;> simp_all)
      have hstrip : stripAux false (bitsW w a).reverse [] =
          encodeNat (valFrom 0 (bitsW w a).reverse) := stripAux_encodeNat _ 0
      rw [valFrom_reverse, Nat.mul_zero, Nat.zero_add] at hstrip
      refine ⟨?_, ?_⟩
      · rw [(split _).1, ← hsa, ← hsb, ht.1, hstrip]; rfl
      · rw [(split _).2, ← hsa, ← hsb]
        have := ht.2; rw [List.length_reverse, length_bitsW] at this
        have := hca; have := hcb
        omega

end Factoring.Aux.Trial
