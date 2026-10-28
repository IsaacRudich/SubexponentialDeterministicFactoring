/-
FactoringAux/Simulate/Instr.lean — L2′: the simulation of the straight-line `Program` instructions.

Not audited.
-/
module

public import FactoringAux.Simulate.Ops

@[expose] public section

namespace Factoring.Aux.Sim

open SProg Function Factoring.Aux.Copied Factoring.Aux.Copied.Aux

/-- The cost allowed per `Program` step. -/
def Acc (Λ M : ℕ) : ℕ := 200 * W Λ M + 200

/-- What a simulated piece achieves from `s`: the memory now represents `σ'`, every other stack is
as before, within cost `c`. -/
def Post (P : SProg) (s : Stacks) (σ' : Memory) (Λ c : ℕ) : Prop :=
  ∃ bs', P.exec s = update s mMEM (enc bs') ∧ Good bs' σ' Λ ∧ P.cost s ≤ c

/-- The starting conditions. -/
def Pre (s : Stacks) (σ : Memory) (Λ M : ℕ) : Prop :=
  ∃ bs, s mMEM = enc bs ∧ Good bs σ Λ ∧ Clean s ∧ ∀ i, σ i ≤ M

theorem W_ge (Λ M : ℕ) : M + Λ + 1 ≤ W Λ M := by unfold W; nlinarith

/-- Indirect read: `X := σ r` for `R = r` (unary); `R` and `V` end empty. -/
def getI (X : ℕ) : SProg := seqs [copy mR mR2 mT1, swap, copy mV X mT1, move mR2 mR, swap]

/-! ### `zero`, `incr`, `decr`, `copy` -/

theorem sim_zero (d : ℕ) {s : Stacks} {σ : Memory} {Λ M : ℕ} (h : Pre s σ Λ M) (hd : d < Λ) :
    Post (put d) s (σ.set d 0) Λ (Acc Λ M) := by
  obtain ⟨bs, hM, hG, hC, hσ⟩ := h
  obtain ⟨c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15⟩ := hC.facts
  obtain ⟨b1, g1, e1, k1⟩ := put_spec d 0 s σ bs Λ M hM hG hσ hd (Nat.zero_le _) c4
    (fun j h1 h2 _ => hC j h1 h2)
  refine ⟨b1, by rw [e1]; stacks_ext_with [c4], g1, ?_⟩
  unfold Acc; omega

/-- `incr d`, simulated. -/
def simIncr (d : ℕ) : SProg := seqs [get d mA, push mA true, move mA mV, put d]
/-- `decr d`, simulated. -/
def simDecr (d : ℕ) : SProg := seqs [get d mA, pop mA, move mA mV, put d]
/-- `copy d s`, simulated. -/
def simCopy (d s : ℕ) : SProg := seqs [get s mA, move mA mV, put d]

set_option maxHeartbeats 1000000 in
theorem sim_incr (d : ℕ) {s : Stacks} {σ : Memory} {Λ M : ℕ} (h : Pre s σ Λ M) (hd : d < Λ)
    (hv : σ d + 1 ≤ M) : Post (simIncr d) s (σ.set d (σ d + 1)) Λ (Acc Λ M) := by
  obtain ⟨bs, hM, hG, hC, hσ⟩ := h
  obtain ⟨c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15⟩ := hC.facts
  obtain ⟨b1, g1, e1, k1⟩ := get_spec d mA (Or.inl rfl) s σ bs Λ M hM hG hσ hd hC
  set s1 := update (update s mMEM (enc b1)) mA (rep (σ d)) with hs1
  set s2 := (move mA mV).exec ((push mA true).exec s1) with hs2
  have hs2' : s2 = update (update s1 mA []) mV (rep (σ d + 1)) := by
    rw [hs2, exec_move (by decide), exec_push]; simp [s1, c4, rep_succ, rep_append_cons]
  obtain ⟨b2, g2, e2, k2⟩ := put_spec d (σ d + 1) s2 σ b1 Λ M (by rw [hs2']; simp [s1]) g1 hσ hd hv
    (by rw [hs2']; simp) (by
      intro j h1 h2 h3; rw [hs2']; simp only [s1, update_apply]
      split_ifs <;> first | omega | rfl | exact hC j h1 h2)
  have hW := W_ge Λ M
  refine ⟨b2, ?_, g2, ?_⟩
  · show (put d).exec ((move mA mV).exec ((push mA true).exec ((get d mA).exec s))) = _
    rw [e1, ← hs2, e2, hs2', hs1]
    stacks_ext_with [c4, c7]
  · show (get d mA).cost s + ((push mA true).cost ((get d mA).exec s) +
      ((move mA mV).cost ((push mA true).exec ((get d mA).exec s)) +
      ((put d).cost ((move mA mV).exec ((push mA true).exec ((get d mA).exec s))) + 0))) ≤ _
    rw [e1, ← hs2, cost_push, cost_move _ _ (by decide)]
    simp only [exec_push, update_self, s1, List.length_cons, length_rep] at *
    unfold Acc; omega

set_option maxHeartbeats 1000000 in
theorem sim_decr (d : ℕ) {s : Stacks} {σ : Memory} {Λ M : ℕ} (h : Pre s σ Λ M) (hd : d < Λ) :
    Post (simDecr d) s (σ.set d (σ d - 1)) Λ (Acc Λ M) := by
  obtain ⟨bs, hM, hG, hC, hσ⟩ := h
  obtain ⟨c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15⟩ := hC.facts
  obtain ⟨b1, g1, e1, k1⟩ := get_spec d mA (Or.inl rfl) s σ bs Λ M hM hG hσ hd hC
  set s1 := update (update s mMEM (enc b1)) mA (rep (σ d)) with hs1
  have hpop : (pop mA).exec s1 = update s1 mA (rep (σ d - 1)) ∧ (pop mA).cost s1 ≤ 1 := by
    refine ⟨?_, cost_pop_le _ _⟩
    rcases Nat.eq_zero_or_pos (σ d) with h0 | hpos
    · rw [pop, exec_read_nil (by simp [s1, h0])]
      simp [s1, h0]
    · rw [exec_pop_cons (x := true) (l := rep (σ d - 1)) (by simp [s1, rep_ne_nil hpos])]
  set s2 := (move mA mV).exec ((pop mA).exec s1) with hs2
  have hs2' : s2 = update (update s1 mA []) mV (rep (σ d - 1)) := by
    rw [hs2, exec_move (by decide), hpop.1]; simp [s1, c4]
  obtain ⟨b2, g2, e2, k2⟩ := put_spec d (σ d - 1) s2 σ b1 Λ M (by rw [hs2']; simp [s1]) g1 hσ hd
    (by have := hσ d; omega) (by rw [hs2']; simp) (by
      intro j h1 h2 h3; rw [hs2']; simp only [s1, update_apply]
      split_ifs <;> first | omega | rfl | exact hC j h1 h2)
  have hW := W_ge Λ M
  have := hσ d
  refine ⟨b2, ?_, g2, ?_⟩
  · show (put d).exec ((move mA mV).exec ((pop mA).exec ((get d mA).exec s))) = _
    rw [e1, ← hs2, e2, hs2', hs1]
    stacks_ext_with [c4, c7]
  · show (get d mA).cost s + ((pop mA).cost ((get d mA).exec s) +
      ((move mA mV).cost ((pop mA).exec ((get d mA).exec s)) +
      ((put d).cost ((move mA mV).exec ((pop mA).exec ((get d mA).exec s))) + 0))) ≤ _
    rw [e1, ← hs2, cost_move _ _ (by decide), hpop.1]
    have := hpop.2
    simp only [update_self, length_rep] at *
    unfold Acc; omega

set_option maxHeartbeats 1000000 in
theorem sim_copy (d src : ℕ) {s : Stacks} {σ : Memory} {Λ M : ℕ} (h : Pre s σ Λ M) (hd : d < Λ)
    (hs : src < Λ) : Post (simCopy d src) s (σ.set d (σ src)) Λ (Acc Λ M) := by
  obtain ⟨bs, hM, hG, hC, hσ⟩ := h
  obtain ⟨c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15⟩ := hC.facts
  obtain ⟨b1, g1, e1, k1⟩ := get_spec src mA (Or.inl rfl) s σ bs Λ M hM hG hσ hs hC
  set s1 := update (update s mMEM (enc b1)) mA (rep (σ src)) with hs1
  set s2 := (move mA mV).exec s1 with hs2
  have hs2' : s2 = update (update s1 mA []) mV (rep (σ src)) := by
    rw [hs2, exec_move (by decide)]; simp [s1, c4]
  obtain ⟨b2, g2, e2, k2⟩ := put_spec d (σ src) s2 σ b1 Λ M (by rw [hs2']; simp [s1]) g1 hσ hd
    (hσ src) (by rw [hs2']; simp) (by
      intro j h1 h2 h3; rw [hs2']; simp only [s1, update_apply]
      split_ifs <;> first | omega | rfl | exact hC j h1 h2)
  have hW := W_ge Λ M
  have := hσ src
  refine ⟨b2, ?_, g2, ?_⟩
  · show (put d).exec ((move mA mV).exec ((get src mA).exec s)) = _
    rw [e1, ← hs2, e2, hs2', hs1]
    stacks_ext_with [c4, c7]
  · show (get src mA).cost s + ((move mA mV).cost ((get src mA).exec s) +
      ((put d).cost ((move mA mV).exec ((get src mA).exec s)) + 0)) ≤ _
    rw [e1, ← hs2, cost_move _ _ (by decide)]
    simp only [s1, update_self, length_rep] at *
    unfold Acc; omega

/-! ### `load`, `store` -/

theorem rep_add (a b : ℕ) : rep a ++ rep b = rep (a + b) := by
  rw [rep, rep, rep, List.replicate_add]

theorem pushN_uses {j k : ℕ} (h : k ≠ j) : ∀ n, (pushN k n).uses j = false
  | 0 => rfl
  | n + 1 => by
      have := pushN_uses h n
      simp only [pushN, List.replicate_succ, SProg.seqs, uses, beq_eq_false_iff_ne.mpr h,
        Bool.false_or] at this ⊢
      exact this

theorem get_uses_A (d : ℕ) : (get d mB).uses mA = false := by
  have h1 : swap.uses mA = false := by decide
  have h2 : (copy mV mB mT1).uses mA = false := by decide
  simp only [get, SProg.seqs, uses, h1, h2, pushN_uses (show mR ≠ mA by decide), Bool.or_false]

set_option maxHeartbeats 2000000 in
/-- Indirect read. -/
theorem getI_spec (r : ℕ) (s : Stacks) (σ : Memory) (bs : List ℕ) (Λ M : ℕ)
    (hM : s mMEM = enc bs) (hG : Good bs σ Λ) (hσ : ∀ i, σ i ≤ M) (hr : r < Λ)
    (hR : s mR = rep r) (hC : ∀ j, 2 ≤ j → j < 16 → j ≠ mR → s j = []) :
    ∃ bs', Good bs' σ Λ ∧
      (getI mB).exec s = update (update (update s mMEM (enc bs')) mR []) mB (rep (σ r)) ∧
      (getI mB).cost s ≤ 40 * W Λ M + 40 := by
  have c2 := hC 2 (by norm_num) (by norm_num) (by decide)
  have c4 := hC 4 (by norm_num) (by norm_num) (by decide)
  have c5 := hC 5 (by norm_num) (by norm_num) (by decide)
  have c6 := hC 6 (by norm_num) (by norm_num) (by decide)
  have c8 := hC 8 (by norm_num) (by norm_num) (by decide)
  have c9 := hC 9 (by norm_num) (by norm_num) (by decide)
  have c11 := hC 11 (by norm_num) (by norm_num) (by decide)
  have hW := W_ge Λ M
  have hσ1 : ∀ i, σ.set r 0 i ≤ M := memory_set_le hσ (Nat.zero_le _)
  have e0 : (copy mR mR2 mT1).exec s = update s mR2 (rep r) := by
    rw [exec_copy (by decide) (by decide) (by decide) s c9, c11, List.append_nil, hR]
  have k0 : (copy mR mR2 mT1).cost s = 5 * r + 2 := by
    rw [cost_copy (by decide) (by decide) (by decide) s c9, hR, length_rep]
  obtain ⟨b1, g1, e1, k1⟩ := swap_good (update s mR2 (rep r)) σ bs Λ M r 0 (by simp [hM]) hG hσ hr
    (Nat.zero_le _) (by simp [hR]) (by simp [c4]) (by simp [c2]) (by simp [c5]) (by simp [c6])
  have e2 : (copy mV mB mT1).exec (update (update (update (update s mR2 (rep r)) mMEM (enc b1)) mR [])
      mV (rep (σ r))) = update (update (update (update (update s mR2 (rep r)) mMEM (enc b1)) mR [])
      mV (rep (σ r))) mB (rep (σ r)) := by
    rw [exec_copy (by decide) (by decide) (by decide) _ (by simp [c9])]; simp [c8]
  have k2 : (copy mV mB mT1).cost (update (update (update (update s mR2 (rep r)) mMEM (enc b1)) mR [])
      mV (rep (σ r))) = 5 * σ r + 2 := by
    rw [cost_copy (by decide) (by decide) (by decide) _ (by simp [c9])]; simp
  have e3 : (move mR2 mR).exec (update (update (update (update (update s mR2 (rep r)) mMEM (enc b1))
      mR []) mV (rep (σ r))) mB (rep (σ r))) = update (update (update (update s mMEM (enc b1))
      mV (rep (σ r))) mB (rep (σ r))) mR (rep r) := by
    rw [exec_move (by decide)]
    stacks_ext_with [c8, c11, hR]
  have k3 : (move mR2 mR).cost (update (update (update (update (update s mR2 (rep r)) mMEM (enc b1))
      mR []) mV (rep (σ r))) mB (rep (σ r))) = 2 * r + 1 := by
    rw [cost_move _ _ (by decide)]; simp
  obtain ⟨b2, g2, e5, k5⟩ := swap_good (update (update (update (update s mMEM (enc b1))
      mV (rep (σ r))) mB (rep (σ r))) mR (rep r)) (σ.set r 0) b1 Λ M r (σ r) (by simp) g1 hσ1 hr
    (hσ r) (by simp) (by simp) (by simp [c2]) (by simp [c5]) (by simp [c6])
  rw [memory_set_set, memory_set_eq_self] at g2
  refine ⟨b2, g2, ?_, ?_⟩
  · show swap.exec ((move mR2 mR).exec ((copy mV mB mT1).exec (swap.exec
      ((copy mR mR2 mT1).exec s)))) = _
    rw [e0, e1, e2, e3, e5]
    simp only [Memory.set, if_true]
    stacks_ext_with [c4]
  · show (copy mR mR2 mT1).cost s + (swap.cost ((copy mR mR2 mT1).exec s) +
      ((copy mV mB mT1).cost (swap.exec ((copy mR mR2 mT1).exec s)) +
      ((move mR2 mR).cost ((copy mV mB mT1).exec (swap.exec ((copy mR mR2 mT1).exec s))) +
      (swap.cost ((move mR2 mR).exec ((copy mV mB mT1).exec (swap.exec
        ((copy mR mR2 mT1).exec s)))) + 0)))) ≤ _
    rw [e0, k0, e1, k2, e2, k3, e3]
    have := hσ r
    have hrW : r ≤ W Λ M := by omega
    omega

/-- `load d b i`, simulated. -/
def simLoad (d b i : ℕ) : SProg :=
  seqs [get i mA, move mA mR, pushN mR b, getI mB, move mB mV, put d]

/-- `store b i src`, simulated. -/
def simStore (b i src : ℕ) : SProg :=
  seqs [get src mA, get i mB, move mB mR, pushN mR b, move mA mV, swap, clear mV]

set_option maxHeartbeats 2000000 in
theorem sim_load (d b i : ℕ) {s : Stacks} {σ : Memory} {Λ M : ℕ} (h : Pre s σ Λ M) (hd : d < Λ)
    (hi : i < Λ) (hb : b + M < Λ) :
    Post (simLoad d b i) s (σ.set d (σ (b + σ i))) Λ (Acc Λ M) := by
  obtain ⟨bs, hM, hG, hC, hσ⟩ := h
  obtain ⟨c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15⟩ := hC.facts
  have hW := W_ge Λ M
  obtain ⟨b1, g1, e1, k1⟩ := get_spec i mA (Or.inl rfl) s σ bs Λ M hM hG hσ hi hC
  have p := pushN_spec mR b ((move mA mR).exec (update (update s mMEM (enc b1)) mA (rep (σ i))))
  have h2 : (pushN mR b).exec ((move mA mR).exec (update (update s mMEM (enc b1)) mA (rep (σ i)))) =
      update (update s mMEM (enc b1)) mR (rep (b + σ i)) := by
    rw [p.1, exec_move (by decide)]
    stacks_ext_with [c3, c7, rep_add]
  have hbi : b + σ i < Λ := by have := hσ i; omega
  obtain ⟨b2, g2, e2, k2⟩ := getI_spec (b + σ i) (update (update s mMEM (enc b1)) mR
      (rep (b + σ i))) σ b1 Λ M (by simp) g1 hσ hbi (by simp) (by
      intro j h1 h2' h3; simp only [update_apply]
      split_ifs <;> first | omega | rfl | exact hC j h1 h2')
  have e4 : (move mB mV).exec (update (update (update (update (update s mMEM (enc b1)) mR
      (rep (b + σ i))) mMEM (enc b2)) mR []) mB (rep (σ (b + σ i)))) =
      update (update s mMEM (enc b2)) mV (rep (σ (b + σ i))) := by
    rw [exec_move (by decide)]
    stacks_ext_with [c3, c4, c8]
  obtain ⟨b3, g3, e5, k5⟩ := put_spec d (σ (b + σ i)) (update (update s mMEM (enc b2)) mV
      (rep (σ (b + σ i)))) σ b2 Λ M (by simp) g2 hσ hd (hσ _) (by simp) (by
      intro j h1 h2' h3; simp only [update_apply]
      split_ifs <;> first | omega | rfl | exact hC j h1 h2')
  refine ⟨b3, ?_, g3, ?_⟩
  · show (put d).exec ((move mB mV).exec ((getI mB).exec ((pushN mR b).exec
      ((move mA mR).exec ((get i mA).exec s))))) = _
    rw [e1, h2, e2, e4, e5]
    stacks_ext_with [c4]
  · show (get i mA).cost s + ((move mA mR).cost ((get i mA).exec s) +
      ((pushN mR b).cost ((move mA mR).exec ((get i mA).exec s)) +
      ((getI mB).cost ((pushN mR b).exec ((move mA mR).exec ((get i mA).exec s))) +
      ((move mB mV).cost ((getI mB).exec ((pushN mR b).exec ((move mA mR).exec
        ((get i mA).exec s)))) +
      ((put d).cost ((move mB mV).exec ((getI mB).exec ((pushN mR b).exec ((move mA mR).exec
        ((get i mA).exec s))))) + 0))))) ≤ _
    rw [e1, cost_move _ _ (by decide), p.2, h2, e2, cost_move _ _ (by decide), e4]
    have := hσ i; have := hσ (b + σ i)
    simp only [update_self, length_rep] at *
    unfold Acc; omega

set_option maxHeartbeats 2000000 in
theorem sim_store (b i src : ℕ) {s : Stacks} {σ : Memory} {Λ M : ℕ} (h : Pre s σ Λ M)
    (hi : i < Λ) (hs : src < Λ) (hb : b + M < Λ) :
    Post (simStore b i src) s (σ.set (b + σ i) (σ src)) Λ (Acc Λ M) := by
  obtain ⟨bs, hM, hG, hC, hσ⟩ := h
  obtain ⟨c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15⟩ := hC.facts
  have hW := W_ge Λ M
  obtain ⟨b1, g1, e1, k1⟩ := get_spec src mA (Or.inl rfl) s σ bs Λ M hM hG hσ hs hC
  have hC1 : Clean (update s mMEM (enc b1)) := fun j h1 h2 => by
    rw [update_of_ne (by omega)]; exact hC j h1 h2
  obtain ⟨b2, g2, e2, k2⟩ := get_spec i mB (Or.inr rfl) (update s mMEM (enc b1)) σ b1 Λ M
    (by simp) g1 hσ hi hC1
  have e2' : (get i mB).exec (update (update s mMEM (enc b1)) mA (rep (σ src))) =
      update (update (update s mMEM (enc b2)) mB (rep (σ i))) mA (rep (σ src)) := by
    rw [exec_update _ _ _ (get_uses_A i), e2]
    stacks_ext_with []
  have k2' : (get i mB).cost (update (update s mMEM (enc b1)) mA (rep (σ src))) =
      (get i mB).cost (update s mMEM (enc b1)) := cost_update _ _ _ (get_uses_A i)
  have p := pushN_spec mR b ((move mB mR).exec
    (update (update (update s mMEM (enc b2)) mB (rep (σ i))) mA (rep (σ src))))
  have h3 : (move mA mV).exec ((pushN mR b).exec ((move mB mR).exec
      (update (update (update s mMEM (enc b2)) mB (rep (σ i))) mA (rep (σ src))))) =
      update (update (update s mMEM (enc b2)) mR (rep (b + σ i))) mV (rep (σ src)) := by
    rw [exec_move (by decide), p.1, exec_move (by decide)]
    stacks_ext_with [c3, c4, c7, c8, rep_add]
  have hbi : b + σ i < Λ := by have := hσ i; omega
  obtain ⟨b3, g3, e4, k4⟩ := swap_good (update (update (update s mMEM (enc b2)) mR
      (rep (b + σ i))) mV (rep (σ src))) σ b2 Λ M (b + σ i) (σ src) (by simp) g2 hσ hbi
    (hσ src) (by simp) (by simp) (by simp [c2]) (by simp [c5]) (by simp [c6])
  refine ⟨b3, ?_, g3, ?_⟩
  · show (clear mV).exec (swap.exec ((move mA mV).exec ((pushN mR b).exec ((move mB mR).exec
      ((get i mB).exec ((get src mA).exec s)))))) = _
    rw [e1, e2', h3, e4, exec_clear]
    stacks_ext_with [c3, c4]
  · show (get src mA).cost s + ((get i mB).cost ((get src mA).exec s) +
      ((move mB mR).cost ((get i mB).exec ((get src mA).exec s)) +
      ((pushN mR b).cost ((move mB mR).exec ((get i mB).exec ((get src mA).exec s))) +
      ((move mA mV).cost ((pushN mR b).exec ((move mB mR).exec ((get i mB).exec
        ((get src mA).exec s)))) +
      (swap.cost ((move mA mV).exec ((pushN mR b).exec ((move mB mR).exec ((get i mB).exec
        ((get src mA).exec s))))) +
      ((clear mV).cost (swap.exec ((move mA mV).exec ((pushN mR b).exec ((move mB mR).exec
        ((get i mB).exec ((get src mA).exec s)))))) + 0)))))) ≤ _
    have hA : ((pushN mR b).exec ((move mB mR).exec
        (update (update (update s mMEM (enc b2)) mB (rep (σ i))) mA (rep (σ src))))) mA =
        rep (σ src) := by
      rw [p.1, exec_move (by decide)]; simp
    have q2 : (get i mB).cost ((get src mA).exec s) ≤ 30 * W Λ M + 30 := by rw [e1, k2']; exact k2
    have q3 : (move mB mR).cost ((get i mB).exec ((get src mA).exec s)) = 2 * σ i + 1 := by
      rw [e1, e2', cost_move _ _ (by decide)]; simp
    have q4 : (pushN mR b).cost ((move mB mR).exec ((get i mB).exec ((get src mA).exec s))) = b := by
      rw [e1, e2']; exact p.2
    have q5 : (move mA mV).cost ((pushN mR b).exec ((move mB mR).exec ((get i mB).exec
        ((get src mA).exec s)))) = 2 * σ src + 1 := by
      rw [e1, e2', cost_move _ _ (by decide), hA]; simp
    have q6 : swap.cost ((move mA mV).exec ((pushN mR b).exec ((move mB mR).exec ((get i mB).exec
        ((get src mA).exec s))))) ≤ 10 * W Λ M + 12 := by
      rw [e1, e2', h3]; exact k4
    have q7 : (clear mV).cost (swap.exec ((move mA mV).exec ((pushN mR b).exec ((move mB mR).exec
        ((get i mB).exec ((get src mA).exec s)))))) = σ (b + σ i) + 1 := by
      rw [e1, e2', h3, e4, cost_clear]; simp
    have := hσ i; have := hσ src; have := hσ (b + σ i)
    unfold Acc; omega

end Factoring.Aux.Sim
