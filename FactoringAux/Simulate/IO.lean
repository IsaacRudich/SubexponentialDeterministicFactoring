/-
FactoringAux/Simulate/IO.lean — L2′: input and output.  `inP` turns the input bits on stack 0 into
the memory `startingMemory xs`; `outP` turns the final memory into `outOf σ` on stack 0, emptying
every other stack.

Not audited.
-/
module

public import FactoringAux.Simulate.Correct
public import FactoringAux.Copied.PlibTop

@[expose] public section

namespace Factoring.Aux.Sim

open SProg Function Factoring.Aux.Copied Factoring.Aux.Copied.PLib

/-! ### Input -/

/-- Read the input: `MEM := enc (n :: bits)`. -/
def inP : SProg :=
  seqs [loop mIO (seq (push mTM true) (push mA true)) (seq (push mTM false) (push mA true)),
    loop mTM (seq (push mMEM false) (push mMEM true)) (push mMEM false),
    push mMEM false, move mA mMEM]

/-- The starting blocks. -/
def startBlocks (xs : List Bool) : List ℕ := xs.length :: xs.map Bool.toNat

theorem getR_map_toNat : ∀ (xs : List Bool) (i : ℕ),
    getR (xs.map Bool.toNat) i = if xs.getD i false then 1 else 0
  | [], i => by simp [getR]
  | x :: xs, 0 => by cases x <;> simp [getR]
  | x :: xs, i + 1 => by simp only [List.map_cons, getR, List.getD_cons_succ]; exact getR_map_toNat xs i

theorem startBlocks_good (xs : List Bool) (Λ : ℕ) (hΛ : xs.length + 1 ≤ Λ) :
    Good (startBlocks xs) (startingMemory xs) Λ := by
  refine ⟨fun i => ?_, by simp [startBlocks]; omega⟩
  cases i with
  | zero => simp [startBlocks, getR, startingMemory]
  | succ i =>
      simp only [startBlocks, getR, startingMemory, Nat.add_eq_zero_iff, one_ne_zero, and_false,
        if_false, Nat.add_sub_cancel]
      exact getR_map_toNat xs i

theorem enc_map_toNat : ∀ xs : List Bool,
    enc (xs.map Bool.toNat) = xs.foldr (fun x acc => (if x then [true, false] else [false]) ++ acc) []
  | [] => rfl
  | x :: xs => by cases x <;> simp [enc1, rep, enc_map_toNat xs]

set_option maxHeartbeats 1000000 in
theorem inP_spec (xs : List Bool) :
    inP.exec (initStacks xs) = update (fun _ => []) mMEM (enc (startBlocks xs)) ∧
      inP.cost (initStacks xs) ≤ 8 * xs.length + 5 := by
  have hu1 : (seq (push mTM true) (push mA true)).uses mIO = false := by decide
  have hu2 : (seq (push mTM false) (push mA true)).uses mIO = false := by decide
  have hu3 : (seq (push mMEM false) (push mMEM true)).uses mTM = false := by decide
  have hu4 : (push mMEM false).uses mTM = false := by decide
  -- first loop: reverse the input onto TM, count it on A
  have L1 : ∀ (l : List Bool) (t : Stacks), l.foldl (bodyF (seq (push mTM true) (push mA true))
      (seq (push mTM false) (push mA true))) t =
      update (update t mTM (l.reverse ++ t mTM)) mA (rep l.length ++ t mA) ∧
      foldCost (bodyF (seq (push mTM true) (push mA true)) (seq (push mTM false) (push mA true)))
        (bodyC (seq (push mTM true) (push mA true)) (seq (push mTM false) (push mA true))) t l =
        2 * l.length := by
    intro l
    induction l with
    | nil => intro t; refine ⟨?_, rfl⟩; simp only [List.foldl_nil]; stacks_ext_with []
    | cons x l ih =>
        intro t
        have e : bodyF (seq (push mTM true) (push mA true)) (seq (push mTM false) (push mA true))
            t x = update (update t mTM (x :: t mTM)) mA (true :: t mA) := by
          cases x <;> simp [bodyF]
        have ec : bodyC (seq (push mTM true) (push mA true)) (seq (push mTM false) (push mA true))
            t x = 2 := by cases x <;> simp [bodyC]
        rw [List.foldl_cons, foldCost_cons, e, ec, (ih _).1, (ih _).2]
        refine ⟨?_, by simp; ring⟩
        simp only [List.length_cons, rep_succ, List.reverse_cons, List.append_assoc,
          List.singleton_append]
        stacks_ext_with [rep_append_cons]
  -- second loop: blocks onto MEM
  have L2 : ∀ (l : List Bool) (t : Stacks), l.foldl (bodyF (seq (push mMEM false) (push mMEM true))
      (push mMEM false)) t =
      update t mMEM ((l.reverse.map Bool.toNat).foldr
        (fun v acc => enc1 v ++ acc) [] ++ t mMEM) ∧
      foldCost (bodyF (seq (push mMEM false) (push mMEM true)) (push mMEM false))
        (bodyC (seq (push mMEM false) (push mMEM true)) (push mMEM false)) t l ≤ 2 * l.length := by
    intro l
    induction l with
    | nil => intro t; refine ⟨?_, by simp⟩; simp
    | cons x l ih =>
        intro t
        have e : bodyF (seq (push mMEM false) (push mMEM true)) (push mMEM false) t x =
            update t mMEM (enc1 x.toNat ++ t mMEM) := by
          cases x <;> simp [bodyF, enc1, rep]
        have ec : bodyC (seq (push mMEM false) (push mMEM true)) (push mMEM false) t x ≤ 2 := by
          cases x <;> simp [bodyC]
        rw [List.foldl_cons, foldCost_cons, e, (ih _).1]
        refine ⟨?_, by have := (ih (update t mMEM (enc1 x.toNat ++ t mMEM))).2; simp; omega⟩
        simp [List.foldr_append]
  have hfold : ∀ m : List ℕ, m.foldr (fun v acc => enc1 v ++ acc) [] = enc m := by
    intro m
    induction m with
    | nil => rfl
    | cons v m ih => simp [ih]
  have s0IO : initStacks xs mIO = xs := by simp [initStacks]
  have s0 : ∀ j, j ≠ mIO → initStacks xs j = [] := fun j hj => by simp [initStacks, hj]
  -- after the first loop
  obtain ⟨S1, hS1⟩ : ∃ S : Stacks, S = update (update (update (initStacks xs) mTM xs.reverse) mA
      (rep xs.length)) mIO [] := ⟨_, rfl⟩
  have E1 : (loop mIO (seq (push mTM true) (push mA true)) (seq (push mTM false) (push mA true))).exec
      (initStacks xs) = S1 := by
    rw [exec_loop_fold hu1 hu2, s0IO, (L1 xs _).1, s0 mTM (by decide), s0 mA (by decide), hS1]
    simp only [List.append_nil]
  have C1 : (loop mIO (seq (push mTM true) (push mA true)) (seq (push mTM false) (push mA true))).cost
      (initStacks xs) = xs.length + 1 + 2 * xs.length := by
    rw [cost_loop_fold hu1 hu2, s0IO, (L1 xs _).2]
  have S1TM : S1 mTM = xs.reverse := by simp [hS1]
  have E2 : (loop mTM (seq (push mMEM false) (push mMEM true)) (push mMEM false)).exec S1 =
      update (update S1 mMEM (enc (xs.map Bool.toNat))) mTM [] := by
    rw [exec_loop_fold hu3 hu4, S1TM, (L2 _ _).1, List.reverse_reverse, hfold]
    have : S1 mMEM = [] := by simp [hS1, s0 mMEM (by decide)]
    rw [this, List.append_nil]
  have C2 : (loop mTM (seq (push mMEM false) (push mMEM true)) (push mMEM false)).cost S1 ≤
      xs.length + 1 + 2 * xs.length := by
    rw [cost_loop_fold hu3 hu4, S1TM]
    have := (L2 xs.reverse S1).2
    simp only [List.length_reverse] at this ⊢
    omega
  have hsplit : inP.exec (initStacks xs) = (move mA mMEM).exec ((push mMEM false).exec
      ((loop mTM (seq (push mMEM false) (push mMEM true)) (push mMEM false)).exec
      ((loop mIO (seq (push mTM true) (push mA true)) (seq (push mTM false) (push mA true))).exec
        (initStacks xs)))) ∧
      inP.cost (initStacks xs) =
      (loop mIO (seq (push mTM true) (push mA true)) (seq (push mTM false) (push mA true))).cost
        (initStacks xs) + ((loop mTM (seq (push mMEM false) (push mMEM true)) (push mMEM false)).cost
        ((loop mIO (seq (push mTM true) (push mA true)) (seq (push mTM false) (push mA true))).exec
          (initStacks xs)) + ((push mMEM false).cost ((loop mTM (seq (push mMEM false)
          (push mMEM true)) (push mMEM false)).exec ((loop mIO (seq (push mTM true) (push mA true))
          (seq (push mTM false) (push mA true))).exec (initStacks xs))) +
        ((move mA mMEM).cost ((push mMEM false).exec ((loop mTM (seq (push mMEM false)
          (push mMEM true)) (push mMEM false)).exec ((loop mIO (seq (push mTM true) (push mA true))
          (seq (push mTM false) (push mA true))).exec (initStacks xs)))) + 0))) := ⟨rfl, rfl⟩
  rw [E1] at hsplit
  refine ⟨?_, ?_⟩
  · rw [hsplit.1, E2, exec_push, exec_move (by decide)]
    funext j
    simp only [update_apply, hS1, initStacks]
    split_ifs <;> (try subst j) <;> first | contradiction | omega | simp [startBlocks, enc1]
  · have hc := hsplit.2
    have hA : S1 mA = rep xs.length := by simp [hS1]
    have hm : (move mA mMEM).cost ((push mMEM false).exec
        ((loop mTM (seq (push mMEM false) (push mMEM true)) (push mMEM false)).exec S1)) =
        2 * xs.length + 1 := by
      rw [E2, exec_push, cost_move _ _ (by decide)]; simp [hA]
    rw [C1, hm, cost_push] at hc
    have := C2
    omega

/-! ### Output -/

/-- Output pass, on a `true` symbol. -/
def outT : SProg :=
  read mF (seq (push mF true) (read mB (push mB true) skip (push mB true))) skip (push mA true)

/-- Output pass, on a `false` symbol (a block end). -/
def outF : SProg :=
  read mF (seq (push mF true) (read mA (read mB (push mTM true) skip (push mTM false)) skip
    (clear mB))) skip (push mF true)

/-- Write `outOf σ` on stack 0 and empty everything. -/
def outP : SProg :=
  seqs [loop mMEM outT outF, loop mA (push mTM false) (push mTM false), clear mF, move mTM mIO]

/-- The output pass state: phase passed, count left, current block nonzero, bits so far. -/
structure OP where
  f : Bool
  a : ℕ
  z : Bool
  out : List Bool

def outSt (s : Stacks) (P : OP) : Stacks :=
  update (update (update (update s mF (flag P.f)) mA (rep P.a)) mB (flag P.z)) mTM P.out

def ostep (P : OP) : Bool → OP
  | true => if P.f then { P with z := true } else { P with a := P.a + 1 }
  | false => if P.f then
      (if 0 < P.a then { P with a := P.a - 1, z := false, out := P.z :: P.out }
        else { P with z := false })
      else { P with f := true }

theorem out_step (s : Stacks) (P : OP) (b : Bool) :
    bodyF outT outF (outSt s P) b = outSt s (ostep P b) ∧ bodyC outT outF (outSt s P) b ≤ 5 := by
  obtain ⟨f, a, z, out⟩ := P
  have hF : outSt s ⟨f, a, z, out⟩ mF = flag f := by simp [outSt]
  have hA : outSt s ⟨f, a, z, out⟩ mA = rep a := by simp [outSt]
  have hB : outSt s ⟨f, a, z, out⟩ mB = flag z := by simp [outSt]
  cases b <;> cases f
  · -- false, phase 0
    simp only [bodyF, bodyC, cond_false, outF, ostep, Bool.false_eq_true, if_false]
    rw [exec_read_nil (by simpa using hF), cost_read_nil (by simpa using hF)]
    refine ⟨?_, by simp⟩
    simp only [exec_push, outSt]; stacks_ext_with [hF]
  · -- false, phase 1
    simp only [bodyF, bodyC, cond_false, outF, ostep, if_true]
    rw [exec_read_true (l := []) (by simpa using hF), cost_read_true (l := []) (by simpa using hF)]
    simp only [exec_seq, cost_seq, exec_push, cost_push, update_self, update_idem]
    rcases Nat.eq_zero_or_pos a with ha | ha
    · subst ha
      have hA0 : update (outSt s ⟨true, 0, z, out⟩) mF [true] mA = [] := by
        simp [outSt]
      rw [exec_read_nil hA0, cost_read_nil hA0, exec_clear, cost_clear]
      refine ⟨?_, by cases z <;> simp [outSt]⟩
      simp only [lt_self_iff_false, if_false, outSt]; stacks_ext_with []
    · have hA1 : update (outSt s ⟨true, a, z, out⟩) mF [true] mA =
          true :: rep (a - 1) := by simp [outSt, rep_ne_nil ha]
      rw [exec_read_true hA1, cost_read_true hA1, if_pos ha]
      cases z
      · have hB0 : update (update (outSt s ⟨true, a, false, out⟩) mF [true])
            mA (rep (a - 1)) mB = [] := by simp [outSt]
        rw [exec_read_nil hB0, cost_read_nil hB0]
        refine ⟨?_, by simp⟩
        simp only [exec_push, outSt]; stacks_ext_with []
      · have hB1 : update (update (outSt s ⟨true, a, true, out⟩) mF [true])
            mA (rep (a - 1)) mB = true :: [] := by simp [outSt]
        rw [exec_read_true hB1, cost_read_true hB1]
        refine ⟨?_, by simp⟩
        simp only [exec_push, outSt]; stacks_ext_with []
  · -- true, phase 0
    simp only [bodyF, bodyC, cond_true, outT, ostep, Bool.false_eq_true, if_false]
    rw [exec_read_nil (by simpa using hF), cost_read_nil (by simpa using hF)]
    refine ⟨?_, by simp⟩
    simp only [exec_push, outSt, rep_succ]; stacks_ext_with []
  · -- true, phase 1
    simp only [bodyF, bodyC, cond_true, outT, ostep, if_true]
    rw [exec_read_true (l := []) (by simpa using hF), cost_read_true (l := []) (by simpa using hF)]
    simp only [exec_seq, cost_seq, exec_push, cost_push, update_self, update_idem]
    cases z
    · have hB0 : update (outSt s ⟨true, a, false, out⟩) mF [true] mB = [] := by
        simp [outSt]
      rw [exec_read_nil hB0, cost_read_nil hB0]
      refine ⟨?_, by simp⟩
      simp only [exec_push, outSt]; stacks_ext_with []
    · have hB1 : update (outSt s ⟨true, a, true, out⟩) mF [true] mB =
          true :: [] := by simp [outSt]
      rw [exec_read_true hB1, cost_read_true hB1]
      refine ⟨?_, by simp⟩
      simp only [exec_push, outSt]; stacks_ext_with []

theorem out_fold (s : Stacks) : ∀ (l : List Bool) (P : OP),
    l.foldl (bodyF outT outF) (outSt s P) = outSt s (l.foldl ostep P) ∧
      foldCost (bodyF outT outF) (bodyC outT outF) (outSt s P) l ≤ 5 * l.length
  | [], P => ⟨rfl, by simp⟩
  | b :: l, P => by
      have h := out_step s P b
      rw [List.foldl_cons, List.foldl_cons, foldCost_cons, h.1, (out_fold s l _).1]
      refine ⟨rfl, ?_⟩
      have := (out_fold s l (ostep P b)).2
      have := h.2
      simp only [List.length_cons]; omega

/-- The output bits for count `a` from blocks `bs`. -/
def outBits (a : ℕ) (bs : List ℕ) : List Bool := (List.range a).map (fun i => decide (getR bs i ≠ 0))

theorem ostep_trues (v : ℕ) : ∀ (P : OP), P.f = true →
    (rep v).foldl ostep P = { P with z := P.z || decide (v ≠ 0) } := by
  induction v with
  | zero => intro P _; simp
  | succ v ih =>
      intro P hf
      rw [rep_succ, List.foldl_cons]
      obtain ⟨f, a, z, out⟩ := P
      simp only at hf; subst hf
      simp only [ostep, if_true]
      rw [ih _ rfl]
      simp

theorem ostep_zeros (v : ℕ) : ∀ (P : OP), P.f = false →
    (rep v).foldl ostep P = { P with a := P.a + v } := by
  induction v with
  | zero => intro P _; simp
  | succ v ih =>
      intro P hf
      rw [rep_succ, List.foldl_cons]
      obtain ⟨f, a, z, out⟩ := P
      simp only at hf; subst hf
      simp only [ostep, Bool.false_eq_true, if_false]
      rw [ih _ rfl]
      simp; omega

theorem out_blocks : ∀ (bs : List ℕ) (a : ℕ) (out : List Bool),
    let Q := (enc bs).foldl ostep ⟨true, a, false, out⟩
    Q.f = true ∧ Q.z = false ∧ List.replicate Q.a false ++ Q.out = (outBits a bs).reverse ++ out
  | [], a, out => by
      simp only [enc_nil, List.foldl_nil, true_and]
      simp [outBits, getR]
  | v :: bs, a, out => by
      simp only [enc_cons, enc1, List.foldl_append]
      rw [ostep_trues v _ rfl]
      simp only [List.foldl_cons, List.foldl_nil, ostep, if_true, Bool.false_or]
      rcases Nat.eq_zero_or_pos a with ha | ha
      · subst ha
        simp only [lt_self_iff_false, if_false]
        have := out_blocks bs 0 out
        simpa [outBits] using this
      · rw [if_pos ha]
        have := out_blocks bs (a - 1) (decide (v ≠ 0) :: out)
        obtain ⟨h1, h2, h3⟩ := this
        refine ⟨h1, h2, ?_⟩
        rw [h3]
        obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
        simp only [Nat.add_sub_cancel, outBits, List.range_succ_eq_map, List.map_cons, getR,
          List.map_map, List.reverse_cons, List.append_assoc, List.singleton_append]
        rfl

theorem outOf_eq (σ : Memory) :
    outOf σ = (List.range (σ 0)).map (fun i => decide (σ (i + 1) ≠ 0)) := by
  apply List.ext_getElem
  · simp [outOf]
  · intro i h1 h2
    simp [outOf]

theorem outT_uses : outT.uses mMEM = false := by decide
theorem outF_uses : outF.uses mMEM = false := by decide

set_option maxHeartbeats 2000000 in
/-- **Output.** -/
theorem outP_spec (bs : List ℕ) (σ : Memory) (Λ M : ℕ) (hG : Good bs σ Λ) (hσ : ∀ i, σ i ≤ M) :
    outP.exec (update (fun _ => []) mMEM (enc bs)) = initStacks (outOf σ) ∧
      outP.cost (update (fun _ => []) mMEM (enc bs)) ≤ 6 * Λ * (M + 1) + 4 * M + 6 := by
  set s0 : Stacks := update (fun _ => []) mMEM (enc bs) with hs0
  have hE := enc_length_le hG hσ
  have hP0 : outSt s0 ⟨false, 0, false, []⟩ = s0 := by
    simp only [outSt, hs0]; stacks_ext_with []
  have hsplit : outP.exec s0 = (move mTM mIO).exec ((clear mF).exec
      ((loop mA (push mTM false) (push mTM false)).exec ((loop mMEM outT outF).exec s0))) ∧
      outP.cost s0 = (loop mMEM outT outF).cost s0 + ((loop mA (push mTM false) (push mTM false)).cost
        ((loop mMEM outT outF).exec s0) + ((clear mF).cost ((loop mA (push mTM false)
        (push mTM false)).exec ((loop mMEM outT outF).exec s0)) + ((move mTM mIO).cost
        ((clear mF).exec ((loop mA (push mTM false) (push mTM false)).exec
        ((loop mMEM outT outF).exec s0))) + 0))) := ⟨rfl, rfl⟩
  have hL : (loop mMEM outT outF).exec s0 =
      update (outSt s0 ((enc bs).foldl ostep ⟨false, 0, false, []⟩)) mMEM [] := by
    rw [exec_loop_fold outT_uses outF_uses, show s0 mMEM = enc bs by simp [hs0]]
    conv_lhs => rw [← hP0]
    rw [(out_fold s0 _ _).1]
  have hLc : (loop mMEM outT outF).cost s0 ≤ 6 * (enc bs).length + 1 := by
    rw [cost_loop_fold outT_uses outF_uses, show s0 mMEM = enc bs by simp [hs0]]
    conv_lhs => rw [← hP0]
    have := (out_fold s0 (enc bs) ⟨false, 0, false, []⟩).2
    omega
  -- the result of the pass
  obtain ⟨Q, hQ, hQf, hQz, hQo, hQa⟩ : ∃ Q : OP, (enc bs).foldl ostep ⟨false, 0, false, []⟩ = Q ∧
      Q.f = (decide (bs ≠ [])) ∧ Q.z = false ∧
      List.replicate Q.a false ++ Q.out = (outOf σ).reverse ∧ Q.a ≤ σ 0 := by
    cases bs with
    | nil =>
        refine ⟨_, rfl, by simp, rfl, ?_, by simp⟩
        have h0 : σ 0 = 0 := by rw [← hG.1 0]; rfl
        simp [outOf_eq, h0]
    | cons b0 bs' =>
        have hb0 : σ 0 = b0 := by rw [← hG.1 0]; rfl
        have hbi : ∀ i, σ (i + 1) = getR bs' i := fun i => by rw [← hG.1 (i + 1)]; rfl
        have hfold : (enc (b0 :: bs')).foldl ostep ⟨false, 0, false, []⟩ =
            (enc bs').foldl ostep ⟨true, b0, false, []⟩ := by
          rw [enc_cons, enc1, List.foldl_append, List.foldl_append, ostep_zeros b0 _ rfl]
          simp [ostep]
        have hb := out_blocks bs' b0 []
        refine ⟨_, hfold, by rw [hb.1]; simp, hb.2.1, ?_, ?_⟩
        · rw [hb.2.2, List.append_nil, outOf_eq, hb0]
          simp [outBits, hbi]
        · have := congrArg List.length hb.2.2
          simp [outBits] at this
          omega
  rw [hQ] at hL
  have hA : (update (outSt s0 Q) mMEM []) mA = rep Q.a := by simp [outSt]
  have hlen : (outOf σ).length = σ 0 := by simp [outOf]
  refine ⟨?_, ?_⟩
  · rw [hsplit.1, hL, exec_loop_push (by decide), hA, exec_clear, exec_move (by decide)]
    have hTM : (update (outSt s0 Q) mMEM []) mTM = Q.out := by simp [outSt]
    simp only [length_rep, update_self, update_of_ne (show mTM ≠ mF by decide),
      update_of_ne (show mTM ≠ mA by decide), hTM, hQo]
    simp only [List.reverse_reverse, outSt, hs0, hQz, flag_false]
    funext j
    simp only [update_apply, initStacks]
    split_ifs <;> (try subst j) <;> first | contradiction | omega | simp
  · rw [hsplit.2, hL, exec_loop_push (by decide), hA, cost_loop_push, hA, cost_clear, exec_clear,
      cost_move _ _ (by decide)]
    have hTM : (update (outSt s0 Q) mMEM []) mTM = Q.out := by simp [outSt]
    have hF : (update (update (update (outSt s0 Q) mMEM []) mA [])
        mTM (List.replicate Q.a false ++ Q.out)) mF = flag Q.f := by simp [outSt]
    have hFl := (show (flag Q.f).length ≤ 1 by cases Q.f <;> simp)
    have := congrArg List.length hQo
    simp only [List.length_append, List.length_replicate, List.length_reverse, hlen] at this
    simp only [length_rep, update_self, update_of_ne (show mTM ≠ mF by decide),
      update_of_ne (show mTM ≠ mA by decide), hTM, hF, List.length_append, List.length_replicate]
    have := hσ 0
    have hE' : (enc bs).length ≤ Λ * (M + 1) := hE
    nlinarith

end Factoring.Aux.Sim
