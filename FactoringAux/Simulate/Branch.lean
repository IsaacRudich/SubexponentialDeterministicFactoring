/-
FactoringAux/Simulate/Branch.lean — L2′: composition of simulated pieces, and the two branches.

Not audited.
-/
module

public import FactoringAux.Simulate.Defs

@[expose] public section

namespace Factoring.Aux.Sim

open SProg Function Factoring.Aux.Copied

theorem Pre.mono {s : Stacks} {σ : Memory} {Λ V M : ℕ} (h : Pre s σ Λ V) (hVM : V ≤ M) :
    Pre s σ Λ M := by
  obtain ⟨bs, h1, h2, h3, h4⟩ := h
  exact ⟨bs, h1, h2, h3, fun i => le_trans (h4 i) hVM⟩

theorem Clean.update_mem {s : Stacks} (h : Clean s) (x : List Bool) : Clean (update s mMEM x) :=
  fun j h1 h2 => by rw [update_of_ne (by omega)]; exact h j h1 h2

theorem post_seq {P Q : SProg} {s : Stacks} {σ₁ σ₂ : Memory} {Λ c₁ c₂ : ℕ}
    (h1 : Post P s σ₁ Λ c₁)
    (h2 : ∀ bs₁, Good bs₁ σ₁ Λ → Post Q (update s mMEM (enc bs₁)) σ₂ Λ c₂) :
    Post (seq P Q) s σ₂ Λ (c₁ + c₂) := by
  obtain ⟨b1, e1, g1, k1⟩ := h1
  obtain ⟨b2, e2, g2, k2⟩ := h2 b1 g1
  refine ⟨b2, ?_, g2, ?_⟩
  · rw [exec_seq, e1, e2, update_idem]
  · rw [cost_seq, e1]; omega

theorem post_mono {P : SProg} {s : Stacks} {σ : Memory} {Λ c c' : ℕ} (h : Post P s σ Λ c)
    (hc : c ≤ c') : Post P s σ Λ c' := by
  obtain ⟨b, e, g, k⟩ := h
  exact ⟨b, e, g, le_trans k hc⟩

/-! ### `ifZero` -/

set_option maxHeartbeats 1000000 in
theorem ifZero_post (a : ℕ) (Pt Pe : SProg) {s : Stacks} {σ σ' : Memory} {Λ M c : ℕ}
    (h : Pre s σ Λ M) (ha : a < Λ)
    (ht : σ a = 0 → ∀ bs₁, Good bs₁ σ Λ → Post Pt (update s mMEM (enc bs₁)) σ' Λ c)
    (he : σ a ≠ 0 → ∀ bs₁, Good bs₁ σ Λ → Post Pe (update s mMEM (enc bs₁)) σ' Λ c) :
    Post (seqs [get a mA, read mA (seq (clear mA) Pe) skip Pt]) s σ' Λ (31 * W Λ M + 32 + c) := by
  obtain ⟨bs, hM, hG, hC, hσ⟩ := h
  obtain ⟨c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15⟩ := hC.facts
  have hW := W_ge Λ M
  obtain ⟨b1, g1, e1, k1⟩ := get_spec a mA (Or.inl rfl) s σ bs Λ M hM hG hσ ha hC
  have hsplit : (seqs [get a mA, read mA (seq (clear mA) Pe) skip Pt]).exec s =
      (read mA (seq (clear mA) Pe) skip Pt).exec ((get a mA).exec s) ∧
      (seqs [get a mA, read mA (seq (clear mA) Pe) skip Pt]).cost s =
      (get a mA).cost s + ((read mA (seq (clear mA) Pe) skip Pt).cost ((get a mA).exec s) + 0) :=
    ⟨rfl, rfl⟩
  rcases Nat.eq_zero_or_pos (σ a) with h0 | hpos
  · have hs1 : update (update s mMEM (enc b1)) mA (rep (σ a)) = update s mMEM (enc b1) := by
      rw [h0]; stacks_ext_with [c7]
    obtain ⟨b2, e2, g2, k2⟩ := ht h0 b1 g1
    have hA : update s mMEM (enc b1) mA = [] := by simp [c7]
    refine ⟨b2, ?_, g2, ?_⟩
    · rw [hsplit.1, e1, hs1, exec_read_nil hA, e2, update_idem]
    · rw [hsplit.2, e1, hs1, cost_read_nil hA]; omega
  · have hA : update (update s mMEM (enc b1)) mA (rep (σ a)) mA = true :: rep (σ a - 1) := by
      simp [rep_ne_nil hpos]
    have hs2 : (clear mA).exec (update (update (update s mMEM (enc b1)) mA (rep (σ a))) mA
        (rep (σ a - 1))) = update s mMEM (enc b1) := by
      rw [exec_clear]; stacks_ext_with [c7]
    obtain ⟨b2, e2, g2, k2⟩ := he (by omega) b1 g1
    refine ⟨b2, ?_, g2, ?_⟩
    · rw [hsplit.1, e1, exec_read_true hA, exec_seq, hs2, e2, update_idem]
    · rw [hsplit.2, e1, cost_read_true hA, cost_seq, hs2, cost_clear]
      have := hσ a
      simp only [update_self, length_rep]
      omega

/-! ### `ifLt` -/

theorem cmpBody_uses : cmpBody.uses mA = false := by decide

theorem cmp_spec : ∀ (x y z : ℕ) (s : Stacks), s mB = rep y → s mF = rep z →
    (rep x).foldl (bodyF cmpBody cmpBody) s =
      update (update s mB (rep (y - x))) mF (rep (z + (x - y))) ∧
    foldCost (bodyF cmpBody cmpBody) (bodyC cmpBody cmpBody) s (rep x) ≤ 2 * x
  | 0, y, z, s, hB, hF => by
      refine ⟨?_, by simp [rep]⟩
      simp only [rep_zero, List.foldl_nil, Nat.sub_zero, Nat.zero_sub, Nat.add_zero]
      stacks_ext_with [hB, hF]
  | x + 1, y, z, s, hB, hF => by
      rw [rep_succ, List.foldl_cons, foldCost_cons]
      rcases Nat.eq_zero_or_pos y with hy | hy
      · subst hy
        have hB0 : s mB = [] := by simpa using hB
        have e : bodyF cmpBody cmpBody s true = update s mF (rep (z + 1)) := by
          simp only [bodyF, cond_true, cmpBody]
          rw [exec_read_nil hB0, exec_push, hF, rep_succ]
        have ec : bodyC cmpBody cmpBody s true = 2 := by
          simp only [bodyC, cond_true, cmpBody]; rw [cost_read_nil hB0, cost_push]
        have ih := cmp_spec x 0 (z + 1) (update s mF (rep (z + 1))) (by simp [hB0]) (by simp)
        rw [e, ec, ih.1]
        refine ⟨?_, by have := ih.2; omega⟩
        rw [show z + 1 + (x - 0) = z + (x + 1 - 0) by omega]
        stacks_ext_with [hB0]
      · have hB1 : s mB = true :: rep (y - 1) := by rw [hB, rep_ne_nil hy]
        have e : bodyF cmpBody cmpBody s true = update s mB (rep (y - 1)) := by
          simp only [bodyF, cond_true, cmpBody]
          rw [exec_read_true hB1]; rfl
        have ec : bodyC cmpBody cmpBody s true = 1 := by
          simp only [bodyC, cond_true, cmpBody]; rw [cost_read_true hB1]; rfl
        have ih := cmp_spec x (y - 1) z (update s mB (rep (y - 1))) (by simp) (by simp [hF])
        rw [e, ec, ih.1]
        refine ⟨?_, by have := ih.2; omega⟩
        rw [show y - 1 - x = y - (x + 1) by omega, show z + (x - (y - 1)) = z + (x + 1 - y) by omega]
        stacks_ext_with []

set_option maxHeartbeats 2000000 in
theorem ifLt_post (a b : ℕ) (Pt Pe : SProg) {s : Stacks} {σ σ' : Memory} {Λ M c : ℕ}
    (h : Pre s σ Λ M) (ha : a < Λ) (hb : b < Λ)
    (ht : σ a < σ b → ∀ bs₁, Good bs₁ σ Λ → Post Pt (update s mMEM (enc bs₁)) σ' Λ c)
    (he : ¬ σ a < σ b → ∀ bs₁, Good bs₁ σ Λ → Post Pe (update s mMEM (enc bs₁)) σ' Λ c) :
    Post (seqs [get a mA, get b mB, loop mA cmpBody cmpBody,
      read mB (seq (clear mB) Pt) skip (seq (clear mF) Pe)]) s σ' Λ (64 * W Λ M + 64 + c) := by
  obtain ⟨bs, hM, hG, hC, hσ⟩ := h
  obtain ⟨c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15⟩ := hC.facts
  have hW := W_ge Λ M
  obtain ⟨b1, g1, e1, k1⟩ := get_spec a mA (Or.inl rfl) s σ bs Λ M hM hG hσ ha hC
  obtain ⟨b2, g2, e2, k2⟩ := get_spec b mB (Or.inr rfl) (update s mMEM (enc b1)) σ b1 Λ M
    (by simp) g1 hσ hb (hC.update_mem _)
  have e2' : (get b mB).exec (update (update s mMEM (enc b1)) mA (rep (σ a))) =
      update (update (update s mMEM (enc b2)) mB (rep (σ b))) mA (rep (σ a)) := by
    rw [exec_update _ _ _ (get_uses_A b), e2]
    stacks_ext_with []
  have k2' : (get b mB).cost (update (update s mMEM (enc b1)) mA (rep (σ a))) =
      (get b mB).cost (update s mMEM (enc b1)) := cost_update _ _ _ (get_uses_A b)
  set S := update (update (update s mMEM (enc b2)) mB (rep (σ b))) mA (rep (σ a)) with hS
  have hcmp := cmp_spec (σ a) (σ b) 0 S (by simp [hS]) (by simp [hS, c10])
  have hL : (loop mA cmpBody cmpBody).exec S = update (update (update s mMEM (enc b2)) mB
      (rep (σ b - σ a))) mF (rep (σ a - σ b)) := by
    rw [exec_loop_fold cmpBody_uses cmpBody_uses, show S mA = rep (σ a) by simp [hS], hcmp.1]
    rw [hS]; stacks_ext_with [c7]
  have hLc : (loop mA cmpBody cmpBody).cost S ≤ 3 * σ a + 1 := by
    rw [cost_loop_fold cmpBody_uses cmpBody_uses, show S mA = rep (σ a) by simp [hS]]
    have := hcmp.2; simp only [length_rep]; omega
  have hsplit : (seqs [get a mA, get b mB, loop mA cmpBody cmpBody,
      read mB (seq (clear mB) Pt) skip (seq (clear mF) Pe)]).exec s =
      (read mB (seq (clear mB) Pt) skip (seq (clear mF) Pe)).exec
        ((loop mA cmpBody cmpBody).exec ((get b mB).exec ((get a mA).exec s))) ∧
      (seqs [get a mA, get b mB, loop mA cmpBody cmpBody,
      read mB (seq (clear mB) Pt) skip (seq (clear mF) Pe)]).cost s =
      (get a mA).cost s + ((get b mB).cost ((get a mA).exec s) +
      ((loop mA cmpBody cmpBody).cost ((get b mB).exec ((get a mA).exec s)) +
      ((read mB (seq (clear mB) Pt) skip (seq (clear mF) Pe)).cost
        ((loop mA cmpBody cmpBody).exec ((get b mB).exec ((get a mA).exec s))) + 0))) :=
    ⟨rfl, rfl⟩
  have := hσ a; have := hσ b
  by_cases hlt : σ a < σ b
  · have hB : update (update (update s mMEM (enc b2)) mB (rep (σ b - σ a))) mF
        (rep (σ a - σ b)) mB = true :: rep (σ b - σ a - 1) := by
      simp [rep_ne_nil (show 0 < σ b - σ a by omega)]
    have hs2 : (clear mB).exec (update (update (update (update s mMEM (enc b2)) mB
        (rep (σ b - σ a))) mF (rep (σ a - σ b))) mB (rep (σ b - σ a - 1))) =
        update s mMEM (enc b2) := by
      rw [exec_clear, show σ a - σ b = 0 by omega]; stacks_ext_with [c8, c10]
    obtain ⟨b3, e3, g3, k3⟩ := ht hlt b2 g2
    refine ⟨b3, ?_, g3, ?_⟩
    · rw [hsplit.1, e1, e2', hL, exec_read_true hB, exec_seq, hs2, e3, update_idem]
    · rw [hsplit.2, e1, e2', k2', hL, cost_read_true hB, cost_seq, hs2, cost_clear]
      simp only [update_self, length_rep]
      omega
  · have hB : update (update (update s mMEM (enc b2)) mB (rep (σ b - σ a))) mF
        (rep (σ a - σ b)) mB = [] := by simp [show σ b - σ a = 0 by omega]
    have hs2 : (clear mF).exec (update (update (update s mMEM (enc b2)) mB
        (rep (σ b - σ a))) mF (rep (σ a - σ b))) = update s mMEM (enc b2) := by
      rw [exec_clear, show σ b - σ a = 0 by omega]; stacks_ext_with [c8, c10]
    obtain ⟨b3, e3, g3, k3⟩ := he hlt b2 g2
    refine ⟨b3, ?_, g3, ?_⟩
    · rw [hsplit.1, e1, e2', hL, exec_read_nil hB, exec_seq, hs2, e3, update_idem]
    · rw [hsplit.2, e1, e2', k2', hL, cost_read_nil hB, cost_seq, hs2, cost_clear]
      simp only [update_self, length_rep]
      omega

end Factoring.Aux.Sim
