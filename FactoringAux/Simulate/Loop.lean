/-
FactoringAux/Simulate/Loop.lean — L2′: the simulation of a `Program` loop.

Not audited.

The loop node gets stack `k` (the bound, unary, read once on entry) and stack `k+1` (the counter
`j`, unary).  Each turn sets register `c := j`, runs the body, and adds one to the counter.
-/
module

public import FactoringAux.Simulate.Branch

@[expose] public section

namespace Factoring.Aux.Sim

open SProg Function Factoring.Aux.Copied

/-- The body of a simulated `Program` piece satisfies its specification (with base stack `k`). -/
def BodyOK (body : Program) (Pb : SProg) (k Λ M : ℕ) : Prop :=
  ∀ (s : Stacks) (τ : Memory) (V : ℕ), Pre s τ Λ V → V + (Program.run body τ).2 ≤ M →
    (∀ j, k ≤ j → j < k + 2 * nl body → s j = []) →
    Post Pb s (Program.run body τ).1 Λ ((Program.run body τ).2 * Acc Λ M)

theorem rep_append_true (j : ℕ) : rep j ++ [true] = true :: rep j := by
  rw [rep_append_cons, List.append_nil]

theorem loopCost_mono (body : Program) (c : ℕ) (σ : Memory) :
    ∀ {i j : ℕ}, i ≤ j → Copied.Aux.loopCost body c i σ ≤ Copied.Aux.loopCost body c j σ := by
  intro i j hij
  induction j with
  | zero => rw [Nat.le_zero.mp hij]
  | succ j ih =>
      rcases Nat.eq_or_lt_of_le hij with h | h
      · rw [h]
      · have := ih (by omega)
        simp only [Copied.Aux.loopCost]
        omega

theorem iterP_uses (c : ℕ) (Pb : SProg) (k : ℕ) (hk : 16 ≤ k) (hPb : Pb.uses k = false) :
    (iterP c Pb k).uses k = false := by
  have hput := uses_le (j := k) (put c)
  have hlow := (low_put c).1
  have hput' : (put c).uses k = false := by
    by_contra h; simp only [Bool.not_eq_false] at h; have := hput h; omega
  simp only [iterP, SProg.seqs, uses, copy, move, hput', hPb, Bool.or_false, Bool.false_or,
    beq_eq_false_iff_ne]
  simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne]
  omega

set_option maxHeartbeats 4000000 in
/-- The turns of a simulated loop. -/
theorem iters (body : Program) (Pb : SProg) (b c k : ℕ) {s : Stacks} {σ : Memory} {Λ M V : ℕ}
    (hk : 16 ≤ k) (hc : c < Λ) (hC : Clean s) (hσ : ∀ i, σ i ≤ V)
    (hVM : V + Copied.Aux.loopCost body c (σ b) σ ≤ M)
    (hloop : ∀ j, k ≤ j → j < k + 2 * (nl body + 1) → s j = [])
    (hPb : BodyOK body Pb (k + 2) Λ M) (hPbk : Pb.uses k = false) (hPbk1 : Pb.uses (k + 1) = false)
    (b0 : List ℕ) (g0 : Good b0 σ Λ) :
    ∀ j, j ≤ σ b → ∃ bj, Good bj (Copied.Aux.loopMem body c j σ) Λ ∧
      (rep j).foldl (bodyF (iterP c Pb k) (iterP c Pb k))
          (update (update s mMEM (enc b0)) k (rep (σ b))) =
        update (update (update s mMEM (enc bj)) k (rep (σ b))) (k + 1) (rep j) ∧
      foldCost (bodyF (iterP c Pb k) (iterP c Pb k)) (bodyC (iterP c Pb k) (iterP c Pb k))
          (update (update s mMEM (enc b0)) k (rep (σ b))) (rep j) + j + Acc Λ M ≤
        Copied.Aux.loopCost body c j σ * Acc Λ M ∧
      ∀ r, Copied.Aux.loopMem body c j σ r ≤ V + Copied.Aux.loopCost body c j σ := by
  obtain ⟨c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15⟩ := hC.facts
  have hsk : s k = [] := hloop k le_rfl (by omega)
  have hsk1 : s (k + 1) = [] := hloop (k + 1) (by omega) (by omega)
  have hW := W_ge Λ M
  intro j
  induction j with
  | zero =>
      intro _
      refine ⟨b0, g0, ?_, ?_, ?_⟩
      · simp only [rep_zero, List.foldl_nil]
        stacks_ext_with [hsk1]
      · simp [Copied.Aux.loopCost]
      · intro r; simp only [Copied.Aux.loopMem, Copied.Aux.loopCost]; have := hσ r; omega
  | succ j ih =>
      intro hj
      obtain ⟨bj, gj, ej, kj, vj⟩ := ih (by omega)
      have hmono := loopCost_mono body c σ (show j + 1 ≤ σ b from hj)
      have hstep : Copied.Aux.loopCost body c (j + 1) σ = Copied.Aux.loopCost body c j σ +
          (Program.run body ((Copied.Aux.loopMem body c j σ).set c j)).2 + 1 := rfl
      have hjV : j ≤ V := by have := hσ b; omega
      -- the state at the start of turn j
      set X := update (update (update s mMEM (enc bj)) k (rep (σ b))) (k + 1) (rep j) with hX
      have hX9 : X mT1 = [] := by simp (disch := omega) [hX, c9]
      have e1 : (copy (k + 1) mV mT1).exec X = update X mV (rep j) := by
        rw [exec_copy (by omega) (by omega) (by decide) X hX9]; simp (disch := omega) [hX, c4]
      have k1 : (copy (k + 1) mV mT1).cost X = 5 * j + 2 := by
        rw [cost_copy (by omega) (by omega) (by decide) X hX9]; simp (disch := omega) [hX]
      have hτ : ∀ i, (Copied.Aux.loopMem body c j σ).set c j i ≤
          V + Copied.Aux.loopCost body c j σ :=
        Copied.Aux.memory_set_le vj (by omega)
      obtain ⟨b2, g2, e2, k2⟩ := put_spec c j (update X mV (rep j)) (Copied.Aux.loopMem body c j σ)
        bj Λ M (by simp (disch := omega) [hX]) gj (fun i => by have := vj i; omega) hc (by omega) (by simp)
        (by intro j' h1 h2 h3; simp only [hX, update_apply]; split_ifs <;>
              first | omega | rfl | exact hC j' h1 h2)
      set X2 := update (update (update X mV (rep j)) mMEM (enc b2)) mV [] with hX2
      have hX2' : X2 = update (update (update s mMEM (enc b2)) k (rep (σ b))) (k + 1) (rep j) := by
        rw [hX2, hX]; stacks_ext_with [c4]
      obtain ⟨b3, e3, g3, k3⟩ := hPb X2 ((Copied.Aux.loopMem body c j σ).set c j)
        (V + Copied.Aux.loopCost body c j σ)
        ⟨b2, by rw [hX2']; simp (disch := omega), g2, fun j' h1 h2 => by
          rw [hX2']; simp only [update_apply]; split_ifs <;> first | omega | exact hC j' h1 h2,
          hτ⟩
        (by omega)
        (fun j' h1 h2 => by rw [hX2']; simp only [update_apply]; split_ifs <;>
          first | omega | exact hloop j' (by omega) (by omega))
      refine ⟨b3, g3, ?_, ?_, ?_⟩
      · rw [show rep (j + 1) = rep j ++ [true] by simp [rep, List.replicate_succ'],
          List.foldl_append, ej, List.foldl_cons, List.foldl_nil]
        show (iterP c Pb k).exec X = _
        show (push (k + 1) true).exec (Pb.exec ((put c).exec ((copy (k + 1) mV mT1).exec X))) = _
        rw [e1, e2, e3, hX2', exec_push]
        stacks_ext_with [rep_append_true]
      · rw [show rep (j + 1) = rep j ++ [true] by simp [rep, List.replicate_succ'],
          foldCost_append, ej, foldCost_cons, foldCost_nil]
        have hiter : bodyC (iterP c Pb k) (iterP c Pb k) X true =
            (copy (k + 1) mV mT1).cost X + ((put c).cost ((copy (k + 1) mV mT1).exec X) +
            (Pb.cost ((put c).exec ((copy (k + 1) mV mT1).exec X)) + (1 + 0))) := rfl
        rw [hiter, k1, e1, e2]
        have hAcc : 5 * j + 2 + (12 * W Λ M + 14) + 1 + 1 ≤ Acc Λ M := by
          unfold Acc; have : j ≤ W Λ M := by omega
          omega
        rw [hstep]
        have : (Program.run body ((Copied.Aux.loopMem body c j σ).set c j)).2 * Acc Λ M +
          Acc Λ M = ((Program.run body ((Copied.Aux.loopMem body c j σ).set c j)).2 + 1) *
          Acc Λ M := by ring
        nlinarith
      · intro r
        have := Copied.Aux.run_val_le body ((Copied.Aux.loopMem body c j σ).set c j)
          (V + Copied.Aux.loopCost body c j σ) hτ r
        show (Program.run body ((Copied.Aux.loopMem body c j σ).set c j)).1 r ≤ _
        omega

end Factoring.Aux.Sim

namespace Factoring.Aux.Sim

open SProg Function Factoring.Aux.Copied

set_option maxHeartbeats 2000000 in
/-- A simulated loop. -/
theorem loop_post (body : Program) (Pb : SProg) (b c k : ℕ) {s : Stacks} {σ : Memory} {Λ M V : ℕ}
    (hk : 16 ≤ k) (hb : b < Λ) (hc : c < Λ) (h : Pre s σ Λ V)
    (hVM : V + (Program.run (.loop b c body) σ).2 ≤ M)
    (hloop : ∀ j, k ≤ j → j < k + 2 * (nl body + 1) → s j = [])
    (hPb : BodyOK body Pb (k + 2) Λ M) (hPbk : Pb.uses k = false)
    (hPbk1 : Pb.uses (k + 1) = false) :
    Post (seqs [get b mA, move mA k, loop k (iterP c Pb k) (iterP c Pb k), clear (k + 1)]) s
      (Program.run (.loop b c body) σ).1 Λ ((Program.run (.loop b c body) σ).2 * Acc Λ M) := by
  rw [Copied.Aux.run_loop_eq] at hVM ⊢
  simp only at hVM ⊢
  obtain ⟨bs, hM, hG, hC, hσ⟩ := h
  obtain ⟨c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15⟩ := hC.facts
  have hsk : s k = [] := hloop k le_rfl (by omega)
  have hsk1 : s (k + 1) = [] := hloop (k + 1) (by omega) (by omega)
  have hW := W_ge Λ M
  have hσb := hσ b
  have hl1 : 1 ≤ Copied.Aux.loopCost body c (σ b) σ := by
    have := loopCost_mono body c σ (Nat.zero_le (σ b)); simpa [Copied.Aux.loopCost] using this
  have hσM : ∀ i, σ i ≤ M := fun i => by have := hσ i; omega
  obtain ⟨b1, g1, e1, k1⟩ := get_spec b mA (Or.inl rfl) s σ bs Λ M hM hG hσM hb hC
  have e2 : (move mA k).exec (update (update s mMEM (enc b1)) mA (rep (σ b))) =
      update (update s mMEM (enc b1)) k (rep (σ b)) := by
    rw [exec_move (by omega)]
    funext j; simp only [update_apply]
    split_ifs <;> (try subst j) <;> first | omega | simp [c7, hsk]
  have k2 : (move mA k).cost (update (update s mMEM (enc b1)) mA (rep (σ b))) = 2 * σ b + 1 := by
    rw [cost_move _ _ (by omega)]; simp
  obtain ⟨bk, gk, ek, kk, -⟩ := iters body Pb b c k hk hc hC hσ hVM hloop hPb hPbk hPbk1 b1 g1
    (σ b) le_rfl
  have hu := iterP_uses c Pb k hk hPbk
  have e3 : (loop k (iterP c Pb k) (iterP c Pb k)).exec
      (update (update s mMEM (enc b1)) k (rep (σ b))) =
      update (update (update (update s mMEM (enc bk)) k (rep (σ b))) (k + 1) (rep (σ b))) k [] := by
    rw [exec_loop_fold hu hu, update_self, ek]
  have k3 : (loop k (iterP c Pb k) (iterP c Pb k)).cost
      (update (update s mMEM (enc b1)) k (rep (σ b))) = σ b + 1 +
      foldCost (bodyF (iterP c Pb k) (iterP c Pb k)) (bodyC (iterP c Pb k) (iterP c Pb k))
        (update (update s mMEM (enc b1)) k (rep (σ b))) (rep (σ b)) := by
    rw [cost_loop_fold hu hu, update_self, length_rep]
  refine ⟨bk, ?_, gk, ?_⟩
  · show (clear (k + 1)).exec ((loop k (iterP c Pb k) (iterP c Pb k)).exec ((move mA k).exec
      ((get b mA).exec s))) = _
    rw [e1, e2, e3, exec_clear]
    funext j; simp only [update_apply]
    split_ifs <;> (try subst j) <;> first | omega | simp [hsk, hsk1]
  · show (get b mA).cost s + ((move mA k).cost ((get b mA).exec s) +
      ((loop k (iterP c Pb k) (iterP c Pb k)).cost ((move mA k).exec ((get b mA).exec s)) +
      ((clear (k + 1)).cost ((loop k (iterP c Pb k) (iterP c Pb k)).exec ((move mA k).exec
        ((get b mA).exec s))) + 0))) ≤ _
    rw [e1, k2, e2, k3, e3, cost_clear]
    simp only [update_of_ne (show k + 1 ≠ k by omega), update_self, length_rep]
    have hAcc : 30 * W Λ M + 30 + 3 * σ b + 3 ≤ Acc Λ M := by
      unfold Acc; omega
    nlinarith

end Factoring.Aux.Sim
