/-
FactoringAux/Simulate/Correct.lean — L2′: `sim p k` simulates `p`, each `Program` step costing at
most `Acc Λ M = O(Λ · M)` `SProg` steps; and `sim p k` is well formed.

Not audited.
-/
module

public import FactoringAux.Simulate.Loop

@[expose] public section

namespace Factoring.Aux.Sim

open SProg Function Factoring.Aux.Copied

/-! ### Stacks used by `sim p k` -/

/-- Every stack used is a work stack or in `[k, n)`. -/
def InRange (k n : ℕ) (p : SProg) : Prop := ∀ j, p.uses j = true → j < 16 ∨ (k ≤ j ∧ j < n)

theorem InRange.low {k n : ℕ} {p : SProg} (h : maxUse p < 16) : InRange k n p :=
  fun j hj => Or.inl (lt_of_le_of_lt (uses_le p hj) h)

theorem InRange.mono {k n k' n' : ℕ} {p : SProg} (h : InRange k' n' p) (hk : k ≤ k')
    (hn : n' ≤ n) : InRange k n p := fun j hj => by
  rcases h j hj with h1 | h1
  · exact Or.inl h1
  · exact Or.inr ⟨by omega, by omega⟩

theorem InRange.seq {k n : ℕ} {p q : SProg} (hp : InRange k n p) (hq : InRange k n q) :
    InRange k n (.seq p q) := fun j hj => by
  simp only [uses, Bool.or_eq_true] at hj
  rcases hj with h | h
  · exact hp j h
  · exact hq j h

theorem InRange.read {k n i : ℕ} {a b c : SProg} (hi : i < 16 ∨ (k ≤ i ∧ i < n))
    (ha : InRange k n a) (hb : InRange k n b) (hc : InRange k n c) :
    InRange k n (.read i a b c) := fun j hj => by
  simp only [uses, Bool.or_eq_true, beq_iff_eq] at hj
  rcases hj with ((h | h) | h) | h
  · subst h; exact hi
  · exact ha j h
  · exact hb j h
  · exact hc j h

theorem InRange.loop {k n i : ℕ} {a b : SProg} (hi : i < 16 ∨ (k ≤ i ∧ i < n))
    (ha : InRange k n a) (hb : InRange k n b) : InRange k n (.loop i a b) := fun j hj => by
  simp only [uses, Bool.or_eq_true, beq_iff_eq] at hj
  rcases hj with (h | h) | h
  · subst h; exact hi
  · exact ha j h
  · exact hb j h

theorem InRange.push {k n i : ℕ} {x : Bool} (hi : i < 16 ∨ (k ≤ i ∧ i < n)) :
    InRange k n (.push i x) := fun j hj => by
  simp only [uses, beq_iff_eq] at hj; subst hj; exact hi

theorem InRange.skip {k n : ℕ} : InRange k n .skip := fun j hj => by simp [uses] at hj

theorem InRange.seqs {k n : ℕ} : ∀ {l : List SProg}, (∀ p ∈ l, InRange k n p) →
    InRange k n (SProg.seqs l)
  | [], _ => InRange.skip
  | p :: l, h => InRange.seq (h p (by simp)) (InRange.seqs (fun q hq => h q (by simp [hq])))

theorem low_simIncr (d : ℕ) : maxUse (simIncr d) < 16 := by
  have := (low_get d mA (Or.inl rfl)).1; have := (low_put d).1
  simp only [simIncr, maxUse_seqs, List.map, List.foldr, move, maxUse]; omega

theorem low_simDecr (d : ℕ) : maxUse (simDecr d) < 16 := by
  have := (low_get d mA (Or.inl rfl)).1; have := (low_put d).1
  simp only [simDecr, maxUse_seqs, List.map, List.foldr, move, pop, maxUse]; omega

theorem low_simCopy (d s : ℕ) : maxUse (simCopy d s) < 16 := by
  have := (low_get s mA (Or.inl rfl)).1; have := (low_put d).1
  simp only [simCopy, maxUse_seqs, List.map, List.foldr, move, maxUse]; omega

theorem low_simLoad (d b i : ℕ) : maxUse (simLoad d b i) < 16 := by
  have := (low_get i mA (Or.inl rfl)).1; have := (low_put d).1; have := low_getI.1
  have := maxUse_pushN mR b
  simp only [simLoad, maxUse_seqs, List.map, List.foldr, move, maxUse]; omega

theorem low_simStore (b i s : ℕ) : maxUse (simStore b i s) < 16 := by
  have := (low_get s mA (Or.inl rfl)).1; have := (low_get i mB (Or.inr rfl)).1
  have := maxUse_pushN mR b
  have h2 : maxUse swap ≤ 15 := by decide
  simp only [simStore, maxUse_seqs, List.map, List.foldr, move, clear, maxUse]; omega

theorem sim_inRange : ∀ (p : Program) (k : ℕ), InRange k (k + 2 * nl p) (sim p k)
  | .skip, _ => InRange.skip
  | .zero d, _ => InRange.low (low_put d).1
  | .incr d, _ => InRange.low (low_simIncr d)
  | .decr d, _ => InRange.low (low_simDecr d)
  | .copy d s, _ => InRange.low (low_simCopy d s)
  | .load d b i, _ => InRange.low (low_simLoad d b i)
  | .store b i s, _ => InRange.low (low_simStore b i s)
  | .seq s t, k => by
      simp only [sim, nl]
      exact InRange.seq ((sim_inRange s k).mono le_rfl (by omega))
        ((sim_inRange t (k + 2 * nl s)).mono (by omega) (by omega))
  | .ifLt a b t e, k => by
      simp only [sim, nl]
      refine InRange.seqs ?_
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl
      · exact InRange.low (low_get a mA (Or.inl rfl)).1
      · exact InRange.low (low_get b mB (Or.inr rfl)).1
      · exact InRange.low (by decide)
      · refine InRange.read (Or.inl (by decide)) ?_ InRange.skip ?_
        · exact InRange.seq (InRange.low (by decide)) ((sim_inRange t k).mono le_rfl (by omega))
        · exact InRange.seq (InRange.low (by decide))
            ((sim_inRange e (k + 2 * nl t)).mono (by omega) (by omega))
  | .ifZero a t e, k => by
      simp only [sim, nl]
      refine InRange.seqs ?_
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact InRange.low (low_get a mA (Or.inl rfl)).1
      · refine InRange.read (Or.inl (by decide)) ?_ InRange.skip ?_
        · exact InRange.seq (InRange.low (by decide))
            ((sim_inRange e (k + 2 * nl t)).mono (by omega) (by omega))
        · exact (sim_inRange t k).mono le_rfl (by omega)
  | .loop b c body, k => by
      simp only [sim, nl]
      have hk : k < 16 ∨ (k ≤ k ∧ k < k + 2 * (nl body + 1)) := Or.inr ⟨le_rfl, by omega⟩
      have hk1 : k + 1 < 16 ∨ (k ≤ k + 1 ∧ k + 1 < k + 2 * (nl body + 1)) :=
        Or.inr ⟨by omega, by omega⟩
      have hiter : InRange k (k + 2 * (nl body + 1)) (iterP c (sim body (k + 2)) k) := by
        refine InRange.seqs ?_
        intro p hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl
        · simp only [copy, move]
          exact InRange.seq (InRange.loop hk1 (InRange.push (Or.inl (by decide)))
              (InRange.push (Or.inl (by decide))))
            (InRange.loop (Or.inl (by decide))
              (InRange.seq (InRange.push hk1) (InRange.push (Or.inl (by decide))))
              (InRange.seq (InRange.push hk1) (InRange.push (Or.inl (by decide)))))
        · exact InRange.low (low_put c).1
        · exact (sim_inRange body (k + 2)).mono (by omega) (by omega)
        · exact InRange.push hk1
      refine InRange.seqs ?_
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl
      · exact InRange.low (low_get b mA (Or.inl rfl)).1
      · exact InRange.loop (Or.inl (by decide)) (InRange.push hk) (InRange.push hk)
      · exact InRange.loop hk hiter hiter
      · exact InRange.loop hk1 InRange.skip InRange.skip

theorem sim_uses_of_lt {p : Program} {k j : ℕ} (hj16 : 16 ≤ j) (hj : j < k) :
    (sim p k).uses j = false := by
  by_contra h
  simp only [Bool.not_eq_false] at h
  rcases sim_inRange p k j h with h1 | h1 <;> omega

/-! ### Well-formedness -/

theorem wf_parts {l : List SProg} (h : ∀ p ∈ l, p.WF = true) : (SProg.seqs l).WF = true :=
  wf_seqs l h

theorem sim_wf : ∀ (p : Program) (k : ℕ), 16 ≤ k → (sim p k).WF = true
  | .skip, _, _ => rfl
  | .zero d, _, _ => (low_put d).2
  | .incr d, _, _ => by
      refine wf_parts ?_; intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl
      · exact (low_get d mA (Or.inl rfl)).2
      · rfl
      · decide
      · exact (low_put d).2
  | .decr d, _, _ => by
      refine wf_parts ?_; intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl
      · exact (low_get d mA (Or.inl rfl)).2
      · rfl
      · decide
      · exact (low_put d).2
  | .copy d s, _, _ => by
      refine wf_parts ?_; intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl
      · exact (low_get s mA (Or.inl rfl)).2
      · decide
      · exact (low_put d).2
  | .load d b i, _, _ => by
      refine wf_parts ?_; intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
      · exact (low_get i mA (Or.inl rfl)).2
      · decide
      · exact wf_pushN _ _
      · exact low_getI.2
      · decide
      · exact (low_put d).2
  | .store b i s, _, _ => by
      refine wf_parts ?_; intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact (low_get s mA (Or.inl rfl)).2
      · exact (low_get i mB (Or.inr rfl)).2
      · decide
      · exact wf_pushN _ _
      · decide
      · exact wf_swap
      · rfl
  | .seq s t, k, hk => by
      simp only [sim, WF, Bool.and_eq_true]
      exact ⟨sim_wf s k hk, sim_wf t _ (by omega)⟩
  | .ifLt a b t e, k, hk => by
      refine wf_parts ?_; intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl
      · exact (low_get a mA (Or.inl rfl)).2
      · exact (low_get b mB (Or.inr rfl)).2
      · decide
      · simp [WF, uses, sim_wf t k hk, sim_wf e (k + 2 * nl t) (by omega), clear]
  | .ifZero a t e, k, hk => by
      refine wf_parts ?_; intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact (low_get a mA (Or.inl rfl)).2
      · simp [WF, uses, sim_wf t k hk, sim_wf e (k + 2 * nl t) (by omega), clear]
  | .loop b c body, k, hk => by
      have hu : (sim body (k + 2)).uses k = false := sim_uses_of_lt hk (by omega)
      have hiu := iterP_uses c (sim body (k + 2)) k hk hu
      have hiw : (iterP c (sim body (k + 2)) k).WF = true := by
        refine wf_parts ?_; intro p hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl
        · have h1 : k + 1 ≠ 9 := by omega
          have h2 : k + 1 ≠ 4 := by omega
          have h3 : k ≠ 8 := by omega
          have h4 : k ≠ 3 := by omega
          simp [copy, move, WF, uses, h1, h2, Ne.symm h1, Ne.symm h2, h3, h4]
        · exact (low_put c).2
        · exact sim_wf body _ (by omega)
        · rfl
      refine wf_parts ?_; intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl
      · exact (low_get b mA (Or.inl rfl)).2
      · have h1 : k ≠ 7 := by omega
        simp [move, WF, uses, h1, Ne.symm h1]
      · simp only [WF, Bool.and_eq_true, Bool.not_eq_true']
        exact ⟨⟨⟨hiu, hiu⟩, hiw⟩, hiw⟩
      · rfl

/-! ### Correctness -/

/-- `sim p k` simulates `p`. -/
def SimOK (p : Program) (k : ℕ) : Prop :=
  ∀ (s : Stacks) (σ : Memory) (Λ M V : ℕ), Pre s σ Λ V → V + (Program.run p σ).2 ≤ M →
    lits p + M + 1 ≤ Λ → (∀ j, k ≤ j → j < k + 2 * nl p → s j = []) →
    Post (sim p k) s (Program.run p σ).1 Λ ((Program.run p σ).2 * Acc Λ M)

theorem Pre.update_mem {s : Stacks} {σ : Memory} {Λ V : ℕ} (h : Pre s σ Λ V) {bs : List ℕ}
    (hg : Good bs σ Λ) : Pre (update s mMEM (enc bs)) σ Λ V := by
  obtain ⟨_, _, _, hC, hσ⟩ := h
  exact ⟨bs, by simp, hg, hC.update_mem _, hσ⟩

theorem acc_one (Λ M : ℕ) : 1 * Acc Λ M = Acc Λ M := Nat.one_mul _

set_option maxHeartbeats 2000000 in
theorem sim_ok : ∀ (p : Program) (k : ℕ), 16 ≤ k → SimOK p k
  | .skip, k, _ => by
      intro s σ Λ M V h _ _ _
      obtain ⟨bs, hM, hG, _, _⟩ := h
      refine ⟨bs, ?_, hG, ?_⟩
      · show s = _; rw [← hM, update_eq_self]
      · show 0 ≤ _; omega
  | .zero d, k, _ => by
      intro s σ Λ M V h hV hL _
      have hV1 : V + 1 ≤ M := hV
      have hL1 : d + M + 1 ≤ Λ := hL
      have := sim_zero d (h.mono (show V ≤ M by omega)) (by omega)
      simpa [Program.run, sim] using this
  | .incr d, k, _ => by
      intro s σ Λ M V h hV hL _
      have hσ := h.choose_spec.2.2.2 d
      have hV1 : V + 1 ≤ M := hV
      have hL1 : d + M + 1 ≤ Λ := hL
      have := sim_incr d (h.mono (show V ≤ M by omega)) (by omega) (by omega)
      simpa [Program.run, sim] using this
  | .decr d, k, _ => by
      intro s σ Λ M V h hV hL _
      have hV1 : V + 1 ≤ M := hV
      have hL1 : d + M + 1 ≤ Λ := hL
      have := sim_decr d (h.mono (show V ≤ M by omega)) (by omega)
      simpa [Program.run, sim] using this
  | .copy d src, k, _ => by
      intro s σ Λ M V h hV hL _
      have hV1 : V + 1 ≤ M := hV
      have hL1 : max d src + M + 1 ≤ Λ := hL
      have := le_max_left d src; have := le_max_right d src
      have := sim_copy d src (h.mono (show V ≤ M by omega)) (by omega) (by omega)
      simpa [Program.run, sim] using this
  | .load d b i, k, _ => by
      intro s σ Λ M V h hV hL _
      have hV1 : V + 1 ≤ M := hV
      have hL1 : max d (max b i) + M + 1 ≤ Λ := hL
      have := le_max_left d (max b i); have := le_max_right d (max b i)
      have := le_max_left b i; have := le_max_right b i
      have := sim_load d b i (h.mono (show V ≤ M by omega)) (by omega) (by omega) (by omega)
      simpa [Program.run, sim] using this
  | .store b i src, k, _ => by
      intro s σ Λ M V h hV hL _
      have hV1 : V + 1 ≤ M := hV
      have hL1 : max b (max i src) + M + 1 ≤ Λ := hL
      have := le_max_left b (max i src); have := le_max_right b (max i src)
      have := le_max_left i src; have := le_max_right i src
      have := sim_store b i src (h.mono (show V ≤ M by omega)) (by omega) (by omega) (by omega)
      simpa [Program.run, sim] using this
  | .seq p q, k, hk => by
      intro s σ Λ M V h hV hL hloop
      have hrun : Program.run (.seq p q) σ = ((Program.run q (Program.run p σ).1).1,
          (Program.run p σ).2 + (Program.run q (Program.run p σ).1).2 + 1) := rfl
      rw [hrun] at hV ⊢
      simp only [lits] at hL
      have := le_max_left (lits p) (lits q); have := le_max_right (lits p) (lits q)
      simp only [nl] at hloop
      have h1 := sim_ok p k hk s σ Λ M V h (by omega) (by omega)
        (fun j h1 h2 => hloop j h1 (by omega))
      have hval : ∀ r, (Program.run p σ).1 r ≤ V + (Program.run p σ).2 :=
        Copied.Aux.run_val_le p σ V h.choose_spec.2.2.2
      have h2 : ∀ bs₁, Good bs₁ (Program.run p σ).1 Λ →
          Post (sim q (k + 2 * nl p)) (update s mMEM (enc bs₁)) (Program.run q (Program.run p σ).1).1
            Λ ((Program.run q (Program.run p σ).1).2 * Acc Λ M) := by
        intro bs₁ g₁
        obtain ⟨_, _, _, hC, _⟩ := h
        exact sim_ok q (k + 2 * nl p) (by omega) _ _ Λ M (V + (Program.run p σ).2)
          ⟨bs₁, by simp, g₁, hC.update_mem _, hval⟩ (by omega) (by omega)
          (fun j h1 h2 => by rw [update_of_ne (by omega)]; exact hloop j (by omega) (by omega))
      refine post_mono (post_seq h1 h2) ?_
      nlinarith
  | .ifZero a t e, k, hk => by
      intro s σ Λ M V h hV hL hloop
      have hrun : Program.run (.ifZero a t e) σ =
          ((if σ a = 0 then Program.run t σ else Program.run e σ).1,
            (if σ a = 0 then Program.run t σ else Program.run e σ).2 + 1) := rfl
      rw [hrun] at hV ⊢
      simp only [lits] at hL
      have := le_max_left a (max (lits t) (lits e)); have := le_max_right a (max (lits t) (lits e))
      have := le_max_left (lits t) (lits e); have := le_max_right (lits t) (lits e)
      simp only [nl] at hloop
      have hW := W_ge Λ M
      show Post _ s (if σ a = 0 then Program.run t σ else Program.run e σ).1 Λ
        (((if σ a = 0 then Program.run t σ else Program.run e σ).2 + 1) * Acc Λ M)
      refine post_mono (ifZero_post a (sim t k) (sim e (k + 2 * nl t))
        (c := (if σ a = 0 then Program.run t σ else Program.run e σ).2 * Acc Λ M)
        (h.mono (show V ≤ M by omega)) (by omega) ?_ ?_) ?_
      · intro h0 bs₁ g₁
        simp only [if_pos h0] at hV ⊢
        exact sim_ok t k hk _ σ Λ M V (h.update_mem g₁) (by omega) (by omega)
          (fun j h1 h2 => by rw [update_of_ne (by omega)]; exact hloop j h1 (by omega))
      · intro h0 bs₁ g₁
        simp only [if_neg h0] at hV ⊢
        exact sim_ok e _ (by omega) _ σ Λ M V (h.update_mem g₁) (by omega) (by omega)
          (fun j h1 h2 => by rw [update_of_ne (by omega)]; exact hloop j (by omega) (by omega))
      · unfold Acc at *; nlinarith
  | .ifLt a b t e, k, hk => by
      intro s σ Λ M V h hV hL hloop
      have hrun : Program.run (.ifLt a b t e) σ =
          ((if σ a < σ b then Program.run t σ else Program.run e σ).1,
            (if σ a < σ b then Program.run t σ else Program.run e σ).2 + 1) := rfl
      rw [hrun] at hV ⊢
      simp only [lits] at hL
      have := le_max_left (max a b) (max (lits t) (lits e))
      have := le_max_right (max a b) (max (lits t) (lits e))
      have := le_max_left (lits t) (lits e); have := le_max_right (lits t) (lits e)
      have := le_max_left a b; have := le_max_right a b
      simp only [nl] at hloop
      have hW := W_ge Λ M
      show Post _ s (if σ a < σ b then Program.run t σ else Program.run e σ).1 Λ
        (((if σ a < σ b then Program.run t σ else Program.run e σ).2 + 1) * Acc Λ M)
      refine post_mono (ifLt_post a b (sim t k) (sim e (k + 2 * nl t))
        (c := (if σ a < σ b then Program.run t σ else Program.run e σ).2 * Acc Λ M)
        (h.mono (show V ≤ M by omega)) (by omega) (by omega) ?_ ?_) ?_
      · intro h0 bs₁ g₁
        simp only [if_pos h0] at hV ⊢
        exact sim_ok t k hk _ σ Λ M V (h.update_mem g₁) (by omega) (by omega)
          (fun j h1 h2 => by rw [update_of_ne (by omega)]; exact hloop j h1 (by omega))
      · intro h0 bs₁ g₁
        simp only [if_neg h0] at hV ⊢
        exact sim_ok e _ (by omega) _ σ Λ M V (h.update_mem g₁) (by omega) (by omega)
          (fun j h1 h2 => by rw [update_of_ne (by omega)]; exact hloop j (by omega) (by omega))
      · unfold Acc at *; nlinarith
  | .loop b c body, k, hk => by
      intro s σ Λ M V h hV hL hloop
      simp only [lits] at hL
      have := le_max_left (max b c) (lits body); have := le_max_right (max b c) (lits body)
      have := le_max_left b c; have := le_max_right b c
      have hPb : BodyOK body (sim body (k + 2)) (k + 2) Λ M := by
        intro s' τ V' h' hV' hloop'
        exact sim_ok body (k + 2) (by omega) s' τ Λ M V' h' hV' (by omega) hloop'
      exact loop_post body (sim body (k + 2)) b c k hk (by omega) (by omega) h hV hloop hPb
        (sim_uses_of_lt hk (by omega)) (sim_uses_of_lt (by omega) (by omega))

end Factoring.Aux.Sim
