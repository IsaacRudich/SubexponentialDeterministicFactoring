/-
FactoringAux/Trial/Div.lean — specifications of the division step `divstep` and of `modD`.

Not audited.
-/
module

public import FactoringAux.Trial.Prog

@[expose] public section

namespace Factoring.Aux.Trial

open SProg Function

/-- A one-bit flag stack: `[true]` or empty. -/
def cstk (c : Bool) : List Bool := if c then [true] else []

@[simp] theorem cstk_true : cstk true = [true] := rfl
@[simp] theorem cstk_false : cstk false = [] := rfl

theorem bodyDiv_cost (r : Bool) (s : Stacks) : (bodyDiv r).cost s ≤ 8 := by
  have h := cost_le_lfBound (bodyDiv r) s (by cases r <;> decide)
  have : (bodyDiv r).lfBound ≤ 8 := by cases r <;> decide
  omega

theorem exec_bodyDiv (r prev d c : Bool) (ds : List Bool) (s : Stacks) (h12 : s sPREV = [prev])
    (h3 : s sD = d :: ds) (h13 : s sBOR = cstk c) :
    (bodyDiv r).exec s =
      update (update (update (update (update (update s sPREV [r]) sD ds) sDT (d :: s sDT))
        sBOR (cstk (bbit prev d c))) sS (zbit prev d c :: s sS)) sX (prev :: s sX) := by
  unfold bodyDiv
  rw [exec_readBit h12]
  simp only [exec_seq, exec_push]
  rw [exec_readBit (k := sD) (x := d) (l := ds) (by simp [h3])]
  simp only [exec_seq, exec_push]
  cases c
  · rw [exec_readBit_nil (by simp [h13])]
    cases hb : bbit prev d false <;> simp [hb] <;> stacks_ext
  · rw [exec_readBit (k := sBOR) (x := true) (l := []) (by simp [h13])]
    cases hb : bbit prev d true <;> simp [hb] <;> stacks_ext

theorem bodyDiv_fun : (fun x => bif x then (bodyDiv true).exec else (bodyDiv false).exec) =
    fun x => (bodyDiv x).exec := by
  funext x; cases x <;> rfl

/-- The subtraction pass over `R`. -/
theorem exec_passLoop : ∀ (rs ds : List Bool) (prev c : Bool) (s : Stacks),
    ds.length = rs.length → s sR = rs → s sPREV = [prev] → s sD = ds → s sBOR = cstk c →
    loopExec sR (fun x => (bodyDiv x).exec) rs s =
      update (update (update (update (update (update (update s sR []) sPREV
        [(passSpec prev c rs ds).2.2.1]) sD []) sDT (ds.reverse ++ s sDT))
        sBOR (cstk (passSpec prev c rs ds).2.2.2)) sS ((passSpec prev c rs ds).1.reverse ++ s sS))
        sX ((passSpec prev c rs ds).2.1.reverse ++ s sX)
  | [], ds, prev, c, s, hl, h9, h12, h3, h13 => by
      have : ds = [] := List.eq_nil_of_length_eq_zero hl
      subst this
      simp only [loopExec_nil, passSpec, List.reverse_nil, List.nil_append]
      stacks_ext
  | r :: rs, ds, prev, c, s, hl, h9, h12, h3, h13 => by
      obtain ⟨d, ds, rfl⟩ : ∃ d ds', ds = d :: ds' := by
        cases ds with
        | nil => simp at hl
        | cons d ds' => exact ⟨d, ds', rfl⟩
      rw [loopExec_cons]
      rw [exec_bodyDiv r prev d c ds (update s sR rs) (by simp [h12]) (by simp [h3])
        (by simp [h13])]
      rw [exec_passLoop rs ds r (bbit prev d c) _ (by simpa using hl) (by simp) (by simp)
        (by simp) (by simp)]
      simp only [passSpec, List.headD_cons, List.tail_cons, List.reverse_cons, List.append_assoc,
        List.singleton_append]
      stacks_ext

set_option maxHeartbeats 4000000 in
/-- The division step: `R := (2 R + b) mod d`, all temporaries restored. -/
theorem divstep_spec (w r d : ℕ) (b : Bool) (hw : 1 ≤ w) (hrd : r < d) (hd : d ≤ 2 ^ (w - 1))
    (s : Stacks) (h9 : s sR = bitsW w r) (h3 : s sD = bitsW w d) (h12 : s sPREV = [])
    (h13 : s sBOR = []) (h14 : s sS = []) (h15 : s sX = []) (h16 : s sDT = []) :
    (divstep b).exec s = update s sR (bitsW w ((2 * r + b.toNat) % d)) ∧
      (divstep b).cost s ≤ 14 * w + 8 := by
  obtain ⟨hx, hzl, hT, hF⟩ := passSpec_step w r d b hw hrd hd
  have hxl : (passSpec b false (bitsW w r) (bitsW w d)).2.1.length = w := by rw [hx]; simp
  -- after `push PREV b`
  set s1 := (push sPREV b).exec s with hs1
  have hs1' : s1 = update s sPREV [b] := by simp [s1, h12]
  -- after the pass
  have hl1 : (loop sR (bodyDiv true) (bodyDiv false)).exec s1 =
      update (update (update (update (update (update (update s1 sR []) sPREV
        [(passSpec b false (bitsW w r) (bitsW w d)).2.2.1]) sD []) sDT ((bitsW w d).reverse ++ s1 sDT))
        sBOR (cstk (passSpec b false (bitsW w r) (bitsW w d)).2.2.2))
        sS ((passSpec b false (bitsW w r) (bitsW w d)).1.reverse ++ s1 sS))
        sX ((passSpec b false (bitsW w r) (bitsW w d)).2.1.reverse ++ s1 sX) := by
    rw [exec_loop, bodyDiv_fun]
    have a1 : s1 sR = bitsW w r := by rw [hs1']; simp [h9]
    have a2 : s1 sPREV = [b] := by rw [hs1']; simp
    have a3 : s1 sD = bitsW w d := by rw [hs1']; simp [h3]
    have a4 : s1 sBOR = cstk false := by rw [hs1']; simp [h13]
    rw [a1]
    exact exec_passLoop (bitsW w r) (bitsW w d) b false s1 (by simp) a1 a2 a3 a4
  have hc1 : (loop sR (bodyDiv true) (bodyDiv false)).cost s1 ≤ 9 * w + 1 := by
    rw [cost_loop]
    have := loopCost_le (k := sR) (f := fun b => bif b then (bodyDiv true).exec
      else (bodyDiv false).exec) (c := fun b => bif b then (bodyDiv true).cost
      else (bodyDiv false).cost) (B := 8) (fun x s => by cases x <;> exact bodyDiv_cost _ s)
      (s1 sR) s1
    have h1R : s1 sR = bitsW w r := by rw [hs1']; simp [h9]
    rw [h1R] at this ⊢
    rw [length_bitsW] at this
    omega
  set s2 := (loop sR (bodyDiv true) (bodyDiv false)).exec s1 with hs2
  set s3 := (clear sPREV).exec s2 with hs3
  have hs3' : s3 = update s2 sPREV [] := exec_clear _ _
  set s4 := (move sDT sD).exec s3 with hs4
  have hs4' : s4 = update (update s3 sDT []) sD ((s3 sDT).reverse ++ s3 sD) := exec_move (by decide) _
  have hc2 : (clear sPREV).cost s2 = 2 := by rw [cost_clear, hl1]; simp
  have hc3 : (move sDT sD).cost s3 = 2 * w + 1 := by
    rw [cost_move _ _ (by decide), hs3', hl1]; simp [hs1', h16]
  have hdiv : (divstep b).exec s =
      (read sBOR (seq (move sX sR) (clear sS)) skip (seq (move sS sR) (clear sX))).exec s4 := rfl
  have hdivc : (divstep b).cost s = 1 + ((loop sR (bodyDiv true) (bodyDiv false)).cost s1 +
      ((clear sPREV).cost s2 + ((move sDT sD).cost s3 +
      ((read sBOR (seq (move sX sR) (clear sS)) skip (seq (move sS sR) (clear sX))).cost s4 + 0)))) :=
    rfl
  -- the state before the final choice, in short form
  have hlen := passSpec_length b false (bitsW w r) (bitsW w d)
  rw [length_bitsW] at hlen
  clear_value s1 s2 s3 s4
  generalize passSpec b false (bitsW w r) (bitsW w d) = t at *
  have hs4c : s4 = update (update (update (update s sBOR (cstk t.2.2.2)) sS t.1.reverse) sX
      t.2.1.reverse) sR [] := by
    rw [hs4', hs3', hl1, hs1']
    stacks_ext_with [h9, h3, h12, h13, h14, h15, h16, List.reverse_reverse]
  cases hbor : t.2.2.2
  · -- no borrow: R := difference
    have hz := hF hbor
    have h4 : s4 sBOR = [] := by rw [hs4c]; simp [hbor]
    have e : (read sBOR (seq (move sX sR) (clear sS)) skip (seq (move sS sR) (clear sX))).exec s4
        = update s sR (bitsW w ((2 * r + b.toNat) % d)) := by
      rw [exec_read_nil h4, exec_seq, exec_move (by decide), exec_clear, hs4c, ← hz]
      stacks_ext_with [h13, h14, h15, hbor, List.reverse_reverse]
    have ec : (read sBOR (seq (move sX sR) (clear sS)) skip (seq (move sS sR) (clear sX))).cost s4
        = 3 * w + 3 := by
      rw [cost_read_nil h4, cost_seq, cost_move _ _ (by decide), exec_move (by decide),
        cost_clear, hs4c]
      simp only [update_apply]
      simp [hlen.1, hlen.2]; ring
    refine ⟨by rw [hdiv, e], ?_⟩
    rw [hdivc, ec, hc2, hc3]; omega
  · -- borrow: R := shifted remainder
    have hxx := hT hbor
    have h4 : s4 sBOR = true :: [] := by rw [hs4c]; simp [hbor]
    have e : (read sBOR (seq (move sX sR) (clear sS)) skip (seq (move sS sR) (clear sX))).exec s4
        = update s sR (bitsW w ((2 * r + b.toNat) % d)) := by
      rw [exec_read_true h4, exec_seq, exec_move (by decide), exec_clear, hs4c, ← hxx]
      stacks_ext_with [h13, h14, h15, hbor, List.reverse_reverse]
    have ec : (read sBOR (seq (move sX sR) (clear sS)) skip (seq (move sS sR) (clear sX))).cost s4
        = 3 * w + 3 := by
      rw [cost_read_true h4, cost_seq, cost_move _ _ (by decide), exec_move (by decide),
        cost_clear, hs4c]
      simp only [update_apply]
      simp [hlen.1, hlen.2]; ring
    refine ⟨by rw [hdiv, e], ?_⟩
    rw [hdivc, ec, hc2, hc3]; omega

end Factoring.Aux.Trial

namespace Factoring.Aux.Trial

open SProg Function

theorem valFrom_linear : ∀ (l : List Bool) (v : ℕ), valFrom v l = 2 ^ l.length * v + valFrom 0 l
  | [], v => by simp [valFrom]
  | b :: l, v => by
      simp only [valFrom, List.length_cons]
      rw [valFrom_linear l (2 * v + b.toNat), valFrom_linear l (2 * 0 + b.toNat), pow_succ]
      ring

theorem valFrom_mod (d x : ℕ) (l : List Bool) : valFrom (x % d) l % d = valFrom x l % d := by
  rw [valFrom_linear l x, valFrom_linear l (x % d), Nat.add_mod, Nat.mul_mod, Nat.mod_mod,
    ← Nat.mul_mod, ← Nat.add_mod]

theorem bitsW_zero_eq (w : ℕ) : bitsW w 0 = List.replicate w false := by
  induction w with
  | zero => rfl
  | succ w ih => rw [bitsW_succ, List.replicate_succ, ih]; rfl

/-- The division loop over the bits of `NR`. -/
theorem nrLoop (w d : ℕ) (hw : 1 ≤ w) (hd : d ≤ 2 ^ (w - 1)) :
    ∀ (l : List Bool) (v : ℕ) (s : Stacks), v < d → s sNR = l → s sR = bitsW w v →
      s sD = bitsW w d → s sPREV = [] → s sBOR = [] → s sS = [] → s sX = [] → s sDT = [] →
      loopExec sNR (fun x => bif x then (seq (push sNT true) (divstep true)).exec
          else (seq (push sNT false) (divstep false)).exec) l s =
        update (update (update s sNR []) sNT (l.reverse ++ s sNT)) sR (bitsW w (valFrom v l % d)) ∧
      loopCost sNR (fun x => bif x then (seq (push sNT true) (divstep true)).exec
          else (seq (push sNT false) (divstep false)).exec)
        (fun x => bif x then (seq (push sNT true) (divstep true)).cost
          else (seq (push sNT false) (divstep false)).cost) l s ≤ (14 * w + 10) * l.length + 1
  | [], v, s, hv, h2, h9, _, _, _, _, _, _ => by
      simp only [loopExec_nil, loopCost_nil, List.reverse_nil, List.nil_append, valFrom,
        Nat.mod_eq_of_lt hv]
      refine ⟨?_, by simp⟩
      rw [← h2, ← h9]; stacks_ext
  | x :: l, v, s, hv, h2, h9, h3, h12, h13, h14, h15, h16 => by
      have hF : (bif x then (seq (push sNT true) (divstep true)).exec
          else (seq (push sNT false) (divstep false)).exec) = (seq (push sNT x) (divstep x)).exec := by
        cases x <;> rfl
      have hC : (bif x then (seq (push sNT true) (divstep true)).cost
          else (seq (push sNT false) (divstep false)).cost) = (seq (push sNT x) (divstep x)).cost := by
        cases x <;> rfl
      set s' := update (update s sNR l) sNT (x :: s sNT) with hs'
      have hds := divstep_spec w v d x hw hv hd s' (by simp [s', h9]) (by simp [s', h3])
        (by simp [s', h12]) (by simp [s', h13]) (by simp [s', h14]) (by simp [s', h15])
        (by simp [s', h16])
      have hv' : (2 * v + x.toNat) % d < d := Nat.mod_lt _ (by omega)
      have ih := nrLoop w d hw hd l ((2 * v + x.toNat) % d)
        (update s' sR (bitsW w ((2 * v + x.toNat) % d))) hv' (by simp [s']) (by simp)
        (by simp [s', h3]) (by simp [s', h12]) (by simp [s', h13]) (by simp [s', h14])
        (by simp [s', h15]) (by simp [s', h16])
      have e1 : (seq (push sNT x) (divstep x)).exec (update s sNR l) =
          update s' sR (bitsW w ((2 * v + x.toNat) % d)) := by
        rw [exec_seq, exec_push, ← hds.1]; simp [s']
      have c1 : (seq (push sNT x) (divstep x)).cost (update s sNR l) ≤ 14 * w + 9 := by
        rw [cost_seq, cost_push, exec_push]
        have := hds.2
        simp only [s'] at this
        simp only [update_of_ne (show sNT ≠ sNR by decide)]
        omega
      rw [loopExec_cons, loopCost_cons, hF, hC, e1]
      refine ⟨?_, ?_⟩
      · rw [ih.1, valFrom, valFrom_mod]
        simp only [s', List.reverse_cons, List.append_assoc, List.singleton_append]
        stacks_ext
      · have := ih.2
        simp only [List.length_cons, Nat.mul_succ]
        omega

/-- `R := N mod d`, where `N` is read MSB first from `NR` (restored). -/
theorem modD_spec (w d : ℕ) (nr : List Bool) (hw : 1 ≤ w) (hd1 : 1 ≤ d) (hd : d ≤ 2 ^ (w - 1))
    (hnr : nr.length = w) (s : Stacks) (h1 : s sW = List.replicate w true) (h2 : s sNR = nr)
    (h3 : s sD = bitsW w d) (h9 : s sR = []) (h10 : s sCNT = []) (h11 : s sNT = [])
    (h12 : s sPREV = []) (h13 : s sBOR = []) (h14 : s sS = []) (h15 : s sX = [])
    (h16 : s sDT = []) (h18 : s sTMP = []) :
    modD.exec s = update s sR (bitsW w (valFrom 0 nr % d)) ∧
      modD.cost s ≤ 14 * w * w + 20 * w + 6 := by
  set s1 := (copy sW sCNT sTMP).exec s with hs1
  have hs1' : s1 = update s sCNT (s sW ++ s sCNT) := exec_copy (by decide) (by decide) (by decide) _ h18
  have hc1 : (copy sW sCNT sTMP).cost s = 5 * w + 2 := by
    rw [cost_copy (by decide) (by decide) (by decide) _ h18, h1]; simp
  set s2 := (loop sCNT (push sR false) (push sR false)).exec s1 with hs2
  have hs2' : s2 = update (update s1 sCNT []) sR (List.replicate (s1 sCNT).length false ++ s1 sR) :=
    exec_loop_push (by decide) _ _
  have hc2 : (loop sCNT (push sR false) (push sR false)).cost s1 = 2 * w + 1 := by
    rw [cost_loop_push, hs1']; simp [h1, h10]
  have hnr2 := nrLoop w d hw hd nr 0 s2 (by omega) (by simp [hs2', hs1', h2])
    (by simp [hs2', hs1', h1, h10, h9, bitsW_zero_eq]) (by simp [hs2', hs1', h3])
    (by simp [hs2', hs1', h12]) (by simp [hs2', hs1', h13]) (by simp [hs2', hs1', h14])
    (by simp [hs2', hs1', h15]) (by simp [hs2', hs1', h16])
  set s3 := (loop sNR (seq (push sNT true) (divstep true)) (seq (push sNT false) (divstep false))).exec s2
    with hs3
  have hs3' : s3 = update (update (update s2 sNR []) sNT (nr.reverse ++ s2 sNT)) sR
      (bitsW w (valFrom 0 nr % d)) := by
    rw [hs3, exec_loop]
    have : s2 sNR = nr := by simp [hs2', hs1', h2]
    rw [this]; exact hnr2.1
  have hc3 : (loop sNR (seq (push sNT true) (divstep true))
      (seq (push sNT false) (divstep false))).cost s2 ≤ (14 * w + 10) * w + 1 := by
    rw [cost_loop]
    have : s2 sNR = nr := by simp [hs2', hs1', h2]
    have h := hnr2.2
    rw [hnr] at h
    rw [this]; exact h
  have hc4 : (move sNT sNR).cost s3 = 2 * w + 1 := by
    rw [cost_move _ _ (by decide), hs3']; simp [hs2', hs1', h11, hnr]
  refine ⟨?_, ?_⟩
  · show (move sNT sNR).exec s3 = _
    rw [exec_move (by decide), hs3', hs2', hs1']
    stacks_ext_with [h1, h2, h9, h10, h11, List.reverse_reverse]
  · show (copy sW sCNT sTMP).cost s + ((loop sCNT (push sR false) (push sR false)).cost s1 +
      ((loop sNR (seq (push sNT true) (divstep true))
        (seq (push sNT false) (divstep false))).cost s2 + ((move sNT sNR).cost s3 + 0))) ≤ _
    rw [hc1, hc2, hc4]
    nlinarith [hc3]

end Factoring.Aux.Trial
