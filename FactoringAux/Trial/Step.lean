/-
FactoringAux/Trial/Step.lean — the zero test, the increment, one turn of the main loop, and the
main loop.

Not audited.
-/
module

public import FactoringAux.Trial.Div

@[expose] public section

namespace Factoring.Aux.Trial

open SProg Function

/-! ### Zero test -/

theorem count_true_eq_zero_iff : ∀ l : List Bool, l.count true = 0 ↔ valL l = 0
  | [] => by simp
  | b :: l => by
      have := count_true_eq_zero_iff l
      cases b <;> simp [List.count_cons, this] <;> omega

theorem loop_count {k j : ℕ} (hkj : k ≠ j) :
    ∀ (l : List Bool) (s : Stacks), s k = l →
      loopExec k (fun x => bif x then (push j true).exec else skip.exec) l s =
        update (update s k []) j (List.replicate (l.count true) true ++ s j) ∧
      loopCost k (fun x => bif x then (push j true).exec else skip.exec)
        (fun x => bif x then (push j true).cost else skip.cost) l s ≤ 2 * l.length + 1
  | [], s, hs => by
      refine ⟨?_, by simp⟩
      rw [loopExec_nil, ← hs]; stacks_ext
  | x :: l, s, hs => by
      have e : (bif x then (push j true).exec else skip.exec) (update s k l) =
          update (update s k l) j (List.replicate (if x then 1 else 0) true ++ s j) := by
        cases x <;> simp [update_of_ne (Ne.symm hkj)]
      have ih := loop_count hkj l ((bif x then (push j true).exec else skip.exec) (update s k l))
        (by rw [e]; simp [update_of_ne hkj])
      rw [loopExec_cons, loopCost_cons]
      refine ⟨?_, ?_⟩
      · rw [ih.1, e]
        cases x <;> simp [List.count_cons, List.replicate_succ', List.append_assoc] <;> stacks_ext
      · have := ih.2
        have hc : (bif x then (push j true).cost else skip.cost) (update s k l) ≤ 1 := by
          cases x <;> simp
        simp only [List.length_cons]; omega

theorem count_le_length (l : List Bool) : l.count true ≤ l.length := List.count_le_length

theorem testZ_spec (w v d : ℕ) (s : Stacks) (h9 : s sR = bitsW w v) (h17 : s sZ = [])
    (h18 : s sTMP = []) (h4 : s sFD = []) (h5 : s sANS = []) (h3 : s sD = bitsW w d) :
    testZ.exec s = (if v % 2 ^ w = 0 then
        update (update (update s sR []) sFD [true]) sANS (bitsW w d) else update s sR []) ∧
      testZ.cost s ≤ 8 * w + 6 := by
  have hl := loop_count (k := sR) (j := sZ) (by decide) (s sR) s rfl
  rw [h9] at hl
  set c := (bitsW w v).count true with hc
  have hcw : c ≤ w := by have := count_le_length (bitsW w v); simpa using this
  have hiff : c = 0 ↔ v % 2 ^ w = 0 := by
    rw [hc, count_true_eq_zero_iff, valL_bitsW]
  have hexec : testZ.exec s = (read sZ (clear sZ) skip (seq (push sFD true) (copy sD sANS sTMP))).exec
      (update (update s sR []) sZ (List.replicate c true ++ s sZ)) := by
    show (seqs [read sZ (clear sZ) skip (seq (push sFD true) (copy sD sANS sTMP))]).exec
      ((loop sR (push sZ true) skip).exec s) = _
    rw [exec_loop, h9, hl.1]; rfl
  have hcost : testZ.cost s = (loop sR (push sZ true) skip).cost s +
      ((read sZ (clear sZ) skip (seq (push sFD true) (copy sD sANS sTMP))).cost
        (update (update s sR []) sZ (List.replicate c true ++ s sZ)) + 0) := by
    show (loop sR (push sZ true) skip).cost s +
      (seqs [read sZ (clear sZ) skip (seq (push sFD true) (copy sD sANS sTMP))]).cost
      ((loop sR (push sZ true) skip).exec s) = _
    rw [exec_loop, h9, hl.1]; rfl
  have hlc : (loop sR (push sZ true) skip).cost s ≤ 2 * w + 1 := by
    rw [cost_loop, h9]; have := hl.2; simpa using this
  rw [h17, List.append_nil] at hexec hcost
  by_cases h0 : c = 0
  · have hv : v % 2 ^ w = 0 := hiff.1 h0
    have hz : update (update s sR []) sZ (List.replicate c true) sZ = [] := by simp [h0]
    rw [if_pos hv]
    rw [exec_read_nil hz, exec_seq, exec_copy (by decide) (by decide) (by decide) _ (by simp [h18]),
      exec_push] at hexec
    rw [cost_read_nil hz, cost_seq, cost_copy (by decide) (by decide) (by decide) _ (by simp [h18]),
      cost_push] at hcost
    refine ⟨?_, ?_⟩
    · rw [hexec, h0]; stacks_ext_with [h3, h4, h5, h17]
    · rw [hcost]; simp [h3]; omega
  · have hv : ¬ v % 2 ^ w = 0 := fun h => h0 (hiff.2 h)
    obtain ⟨k, hk⟩ : ∃ k, c = k + 1 := ⟨c - 1, by omega⟩
    have hz : update (update s sR []) sZ (List.replicate c true) sZ = true :: List.replicate k true := by
      simp [hk, List.replicate_succ]
    rw [if_neg hv]
    rw [exec_read_true hz, exec_clear] at hexec
    rw [cost_read_true hz, cost_clear] at hcost
    refine ⟨?_, ?_⟩
    · rw [hexec]; stacks_ext_with [h17]
    · rw [hcost]; simp; omega

/-! ### Increment -/

theorem incBody_spec (x c : Bool) (s : Stacks) (h19 : s sCAR = cstk c) :
    (incBody x).exec s = update (update s sCAR (cstk (x && c))) sDT (xor x c :: s sDT) := by
  unfold incBody
  cases c
  · rw [exec_readBit_nil (by simpa using h19)]
    cases x <;> simp <;> stacks_ext_with [h19]
  · rw [exec_readBit (x := true) (l := []) (by simpa using h19)]
    cases x <;> simp <;> stacks_ext_with [h19]

theorem incBody_cost (x : Bool) (s : Stacks) : (incBody x).cost s ≤ 3 := by
  have h := cost_le_lfBound (incBody x) s (by cases x <;> decide)
  have : (incBody x).lfBound ≤ 3 := by cases x <;> decide
  omega

theorem incLoop : ∀ (ds : List Bool) (c : Bool) (s : Stacks), s sD = ds → s sCAR = cstk c →
    loopExec sD (fun x => bif x then (incBody true).exec else (incBody false).exec) ds s =
      update (update (update s sD []) sDT ((incSpec c ds).1.reverse ++ s sDT)) sCAR
        (cstk (incSpec c ds).2)
  | [], c, s, h3, h19 => by
      simp only [loopExec_nil, incSpec, List.reverse_nil, List.nil_append]
      stacks_ext
  | x :: ds, c, s, h3, h19 => by
      rw [loopExec_cons]
      have e : (bif x then (incBody true).exec else (incBody false).exec) (update s sD ds) =
          update (update (update s sD ds) sCAR (cstk (x && c))) sDT (xor x c :: s sDT) := by
        have := incBody_spec x c (update s sD ds) (by simp [h19])
        cases x <;> simpa using this
      rw [e, incLoop ds (x && c) _ (by simp) (by simp)]
      simp only [incSpec, List.reverse_cons, List.append_assoc, List.singleton_append]
      stacks_ext_with [h19]

theorem incSpec_carry (w d : ℕ) (hd : d + 1 < 2 ^ w) : (incSpec true (bitsW w d)).2 = false := by
  have h := incSpec_val true (bitsW w d)
  simp only [length_bitsW, valL_bitsW, Bool.toNat_true] at h
  rw [Nat.mod_eq_of_lt (by omega)] at h
  by_contra hc
  have : (incSpec true (bitsW w d)).2.toNat = 1 := by simpa using hc
  rw [this] at h
  omega

theorem incD_spec (w d : ℕ) (hd : d + 1 < 2 ^ w) (s : Stacks) (h3 : s sD = bitsW w d)
    (h16 : s sDT = []) (h19 : s sCAR = []) :
    incD.exec s = update s sD (bitsW w (d + 1)) ∧ incD.cost s ≤ 6 * w + 4 := by
  have hout := incSpec_bitsW w d hd
  have hcar := incSpec_carry w d hd
  have hlen := (incSpec_val true (bitsW w d)).2
  rw [length_bitsW] at hlen
  set s1 := (push sCAR true).exec s with hs1
  have hs1' : s1 = update s sCAR [true] := by simp [s1, h19]
  have hl : (loop sD (incBody true) (incBody false)).exec s1 =
      update (update (update s1 sD []) sDT ((incSpec true (bitsW w d)).1.reverse ++ s1 sDT)) sCAR
        (cstk (incSpec true (bitsW w d)).2) := by
    rw [exec_loop]
    have a : s1 sD = bitsW w d := by rw [hs1']; simp [h3]
    rw [a]; exact incLoop _ _ _ a (by rw [hs1']; simp)
  have hlc : (loop sD (incBody true) (incBody false)).cost s1 ≤ 4 * w + 1 := by
    rw [cost_loop]
    have := loopCost_le (k := sD) (f := fun b => bif b then (incBody true).exec
      else (incBody false).exec) (c := fun b => bif b then (incBody true).cost
      else (incBody false).cost) (B := 3) (fun x s => by cases x <;> exact incBody_cost _ s)
      (s1 sD) s1
    have a : s1 sD = bitsW w d := by rw [hs1']; simp [h3]
    rw [a] at this ⊢; rw [length_bitsW] at this; omega
  set s2 := (loop sD (incBody true) (incBody false)).exec s1 with hs2
  set s3 := (move sDT sD).exec s2 with hs3
  have hs3' : s3 = update (update s2 sDT []) sD ((s2 sDT).reverse ++ s2 sD) :=
    exec_move (by decide) _
  have hexec : incD.exec s = (clear sCAR).exec s3 := rfl
  have hcost : incD.cost s = 1 + ((loop sD (incBody true) (incBody false)).cost s1 +
      ((move sDT sD).cost s2 + ((clear sCAR).cost s3 + 0))) := rfl
  have hmc : (move sDT sD).cost s2 = 2 * w + 1 := by
    rw [cost_move _ _ (by decide), hl, hs1']; simp [h16, hlen]
  have hcc : (clear sCAR).cost s3 = 1 := by
    rw [cost_clear, hs3', hl, hcar]; simp
  refine ⟨?_, ?_⟩
  · rw [hexec, exec_clear, hs3', hl, hs1', hcar, hout]
    stacks_ext_with [h3, h16, h19, List.reverse_reverse]
  · rw [hcost, hmc, hcc]; omega

/-! ### One turn of the main loop -/

/-- The state between turns of the main loop: `W`, `NR`, `D = d`, the found flag and the recorded
divisor (`fa`), the counter `CTR`; every other stack empty. -/
def mainSt (w : ℕ) (nr : List Bool) (d : ℕ) (fa : Option ℕ) (ctr : List Bool) : Stacks :=
  fun j => if j = sW then List.replicate w true else if j = sNR then nr
    else if j = sD then bitsW w d else if j = sFD then (if fa.isSome then [true] else [])
    else if j = sANS then fa.elim [] (bitsW w) else if j = sCTR then ctr else []

theorem mainSt_update (w : ℕ) (nr : List Bool) (d : ℕ) (fa : Option ℕ) (x : Bool)
    (l : List Bool) : update (mainSt w nr d fa (x :: l)) sCTR l = mainSt w nr d fa l := by
  funext j; simp only [update_apply, mainSt]; split_ifs <;> simp_all

theorem st_found (w : ℕ) (nr : List Bool) (d v : ℕ) (l : List Bool) :
    update (update (update (update (update (mainSt w nr d none l) sR (bitsW w v)) sR []) sFD [true])
      sANS (bitsW w d)) sD (bitsW w (d + 1)) = mainSt w nr (d + 1) (some d) l := by
  funext j; simp only [update_apply, mainSt]; split_ifs <;> simp_all

theorem st_notfound (w : ℕ) (nr : List Bool) (d v : ℕ) (l : List Bool) :
    update (update (update (mainSt w nr d none l) sR (bitsW w v)) sR []) sD (bitsW w (d + 1)) =
      mainSt w nr (d + 1) none l := by
  funext j; simp only [update_apply, mainSt]; split_ifs <;> simp_all

set_option maxHeartbeats 1000000 in
theorem body_none (w d : ℕ) (nr : List Bool) (l : List Bool) (hw : 1 ≤ w) (hd1 : 1 ≤ d)
    (hd : d + 1 ≤ 2 ^ (w - 1)) (hnr : nr.length = w) :
    body.exec (mainSt w nr d none l) =
        mainSt w nr (d + 1) (if valFrom 0 nr % d = 0 then some d else none) l ∧
      body.cost (mainSt w nr d none l) ≤ 14 * w * w + 34 * w + 17 := by
  have hpow : 2 ^ w = 2 * 2 ^ (w - 1) := by rw [← pow_succ']; congr 1; omega
  have hFD : mainSt w nr d none l sFD = [] := by simp [mainSt]
  have hb : body.exec (mainSt w nr d none l) =
      (seqs [modD, testZ, incD]).exec (mainSt w nr d none l) := exec_read_nil hFD
  have hbc : body.cost (mainSt w nr d none l) =
      1 + (seqs [modD, testZ, incD]).cost (mainSt w nr d none l) := cost_read_nil hFD
  have hm := modD_spec w d nr hw hd1 (by omega) hnr (mainSt w nr d none l) (by simp [mainSt])
    (by simp [mainSt]) (by simp [mainSt]) (by simp [mainSt]) (by simp [mainSt]) (by simp [mainSt])
    (by simp [mainSt]) (by simp [mainSt]) (by simp [mainSt]) (by simp [mainSt]) (by simp [mainSt])
    (by simp [mainSt])
  set v := valFrom 0 nr % d with hvdef
  have hvd : v < d := Nat.mod_lt _ (by omega)
  have hvw : v % 2 ^ w = v := Nat.mod_eq_of_lt (by omega)
  set s1 := update (mainSt w nr d none l) sR (bitsW w v) with hs1
  have ht := testZ_spec w v d s1 (by rw [hs1]; simp) (by rw [hs1]; simp [mainSt])
    (by rw [hs1]; simp [mainSt]) (by rw [hs1]; simp [mainSt]) (by rw [hs1]; simp [mainSt])
    (by rw [hs1]; simp [mainSt])
  rw [hvw] at ht
  by_cases h0 : v = 0
  · rw [if_pos h0] at ht
    set s2 := update (update (update s1 sR []) sFD [true]) sANS (bitsW w d) with hs2
    have hi := incD_spec w d (by omega) s2 (by rw [hs2, hs1]; simp [mainSt]) (by rw [hs2, hs1]; simp [mainSt])
      (by rw [hs2, hs1]; simp [mainSt])
    refine ⟨?_, ?_⟩
    · rw [hb, exec_seqs_cons, hm.1, exec_seqs_cons, ht.1, exec_seqs_cons, hi.1, exec_seqs_nil,
        if_pos h0]
      exact st_found w nr d v l
    · rw [hbc, cost_seqs_cons, hm.1, cost_seqs_cons, ht.1, cost_seqs_cons, cost_seqs_nil]
      have := hm.2; have := ht.2; have := hi.2
      nlinarith
  · rw [if_neg h0] at ht
    set s2 := update s1 sR [] with hs2
    have hi := incD_spec w d (by omega) s2 (by rw [hs2, hs1]; simp [mainSt]) (by rw [hs2, hs1]; simp [mainSt])
      (by rw [hs2, hs1]; simp [mainSt])
    refine ⟨?_, ?_⟩
    · rw [hb, exec_seqs_cons, hm.1, exec_seqs_cons, ht.1, exec_seqs_cons, hi.1, exec_seqs_nil,
        if_neg h0]
      exact st_notfound w nr d v l
    · rw [hbc, cost_seqs_cons, hm.1, cost_seqs_cons, ht.1, cost_seqs_cons, cost_seqs_nil]
      have := hm.2; have := ht.2; have := hi.2
      nlinarith

theorem body_some (w d a : ℕ) (nr : List Bool) (l : List Bool) :
    body.exec (mainSt w nr d (some a) l) = mainSt w nr d (some a) l ∧
      body.cost (mainSt w nr d (some a) l) = 2 := by
  have hFD : mainSt w nr d (some a) l sFD = true :: [] := by simp [mainSt]
  refine ⟨?_, ?_⟩
  · rw [body, exec_read_true hFD, exec_push]
    funext j; simp only [update_apply, mainSt]; split_ifs <;> simp_all
  · rw [body, cost_read_true hFD, cost_push]

/-! ### The main loop -/

/-- What the main loop computes: the final `d` and the recorded divisor. -/
def search (N : ℕ) : ℕ → ℕ → Option ℕ → ℕ × Option ℕ
  | d, 0, fa => (d, fa)
  | d, m + 1, some a => search N d m (some a)
  | d, m + 1, none => search N (d + 1) m (if N % d = 0 then some d else none)

theorem mainLoop (w : ℕ) (nr : List Bool) (hw : 1 ≤ w) (hnr : nr.length = w) :
    ∀ (ctr : List Bool) (d : ℕ) (fa : Option ℕ), 1 ≤ d → d + ctr.length ≤ 2 ^ (w - 1) →
      loopExec sCTR (fun x => bif x then body.exec else body.exec) ctr (mainSt w nr d fa ctr) =
        mainSt w nr (search (valFrom 0 nr) d ctr.length fa).1
          (search (valFrom 0 nr) d ctr.length fa).2 [] ∧
      loopCost sCTR (fun x => bif x then body.exec else body.exec)
        (fun x => bif x then body.cost else body.cost) ctr (mainSt w nr d fa ctr) ≤
        (14 * w * w + 34 * w + 18) * ctr.length + 1
  | [], d, fa, _, _ => by simp [search]
  | x :: l, d, fa, hd1, hd => by
      have hF : (bif x then body.exec else body.exec) = body.exec := by cases x <;> rfl
      have hC : (bif x then body.cost else body.cost) = body.cost := by cases x <;> rfl
      rw [loopExec_cons, loopCost_cons, hF, hC, mainSt_update]
      simp only [List.length_cons] at hd ⊢
      cases fa with
      | some a =>
          rw [(body_some w d a nr l).1, (body_some w d a nr l).2]
          have ih := mainLoop w nr hw hnr l d (some a) hd1 (by omega)
          refine ⟨by rw [ih.1]; rfl, ?_⟩
          have := ih.2; rw [Nat.mul_succ]; omega
      | none =>
          have hb := body_none w d nr l hw hd1 (by omega) hnr
          rw [hb.1]
          have ih := mainLoop w nr hw hnr l (d + 1)
            (if valFrom 0 nr % d = 0 then some d else none) (by omega) (by omega)
          refine ⟨by rw [ih.1]; rfl, ?_⟩
          have := ih.2; have := hb.2; rw [Nat.mul_succ]; omega

end Factoring.Aux.Trial
