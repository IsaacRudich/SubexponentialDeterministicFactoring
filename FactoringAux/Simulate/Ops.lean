/-
FactoringAux/Simulate/Ops.lean — L2′: reading and writing registers of the simulated memory.

Not audited.

`Good bs σ Λ`: the memory stack `enc bs` represents the `Program` memory `σ`, with at most `Λ`
registers written out.  `get d X` puts register `d` (unary) on `X`; `put d` writes the unary value
on `V` into register `d`.  Each costs `O(W)`, `W = Λ (M + 1) + Λ + M + 1`, when every value is
`≤ M`.
-/
module

public import FactoringAux.Simulate.Swap
public import FactoringAux.Copied.MachineLemmas

@[expose] public section

namespace Factoring.Aux.Sim

open SProg Function Factoring.Aux.Copied Factoring.Aux.Copied.Aux

/-- `enc bs` represents `σ`, with at most `Λ` registers written out. -/
def Good (bs : List ℕ) (σ : Memory) (Λ : ℕ) : Prop := (∀ i, getR bs i = σ i) ∧ bs.length ≤ Λ

/-- The work stacks `2 … 15` are empty. -/
def Clean (s : Stacks) : Prop := ∀ j, 2 ≤ j → j < 16 → s j = []

/-- The size bound of one memory pass. -/
def W (Λ M : ℕ) : ℕ := Λ * (M + 1) + Λ + M + 1

theorem sum_le_of_getR : ∀ (bs : List ℕ) (m : ℕ), (∀ i, getR bs i ≤ m) → bs.sum ≤ bs.length * m
  | [], _, _ => by simp
  | b :: bs, m, h => by
      have h0 := h 0
      have := sum_le_of_getR bs m (fun i => h (i + 1))
      simp only [getR] at h0
      simp only [List.sum_cons, List.length_cons]
      nlinarith

theorem enc_length_le {bs : List ℕ} {σ : Memory} {Λ M : ℕ} (hG : Good bs σ Λ) (hσ : ∀ i, σ i ≤ M) :
    (enc bs).length ≤ Λ * (M + 1) := by
  rw [length_enc]
  have := sum_le_of_getR bs M (fun i => by rw [hG.1 i]; exact hσ i)
  have := hG.2
  nlinarith

theorem Good.set {bs : List ℕ} {σ : Memory} {Λ : ℕ} (hG : Good bs σ Λ) {r : ℕ} (hr : r < Λ)
    (v : ℕ) : Good (setL bs r v) (σ.set r v) Λ := by
  refine ⟨fun i => ?_, ?_⟩
  · rw [getR_setL, Memory.set]; split_ifs <;> simp [hG.1 i]
  · rw [length_setL]; have := hG.2; omega

/-- Swap, in terms of the represented memory. -/
theorem swap_good (s : Stacks) (σ : Memory) (bs : List ℕ) (Λ M r v : ℕ)
    (hM : s mMEM = enc bs) (hG : Good bs σ Λ) (hσ : ∀ i, σ i ≤ M) (hr : r < Λ) (hv : v ≤ M)
    (hR : s mR = rep r) (hV : s mV = rep v) (hTM : s mTM = []) (hO : s mOLD = [])
    (hD : s mDONE = []) :
    ∃ bs', Good bs' (σ.set r v) Λ ∧
      swap.exec s = update (update (update s mMEM (enc bs')) mR []) mV (rep (σ r)) ∧
      swap.cost s ≤ 10 * W Λ M + 12 := by
  obtain ⟨he, hc⟩ := swap_spec s bs r v hM hR hV hTM hO hD
  refine ⟨setL bs r v, hG.set hr v, by rw [he, hG.1 r], ?_⟩
  have := enc_length_le hG hσ
  unfold W; omega

/-! ### Pushing a constant -/

/-- Push `n` marks on stack `k`. -/
def pushN (k n : ℕ) : SProg := seqs (List.replicate n (push k true))

theorem pushN_spec (k : ℕ) : ∀ (n : ℕ) (s : Stacks),
    (pushN k n).exec s = update s k (rep n ++ s k) ∧ (pushN k n).cost s = n
  | 0, s => by simp [pushN]
  | n + 1, s => by
      have ih := pushN_spec k n (update s k (true :: s k))
      simp only [pushN, List.replicate_succ, exec_seqs_cons, cost_seqs_cons, exec_push,
        cost_push] at ih ⊢
      rw [ih.1, ih.2]
      refine ⟨?_, by omega⟩
      simp [rep_append_cons, rep_succ]

theorem Clean.facts {s : Stacks} (h : Clean s) :
    s 2 = [] ∧ s 3 = [] ∧ s 4 = [] ∧ s 5 = [] ∧ s 6 = [] ∧ s 7 = [] ∧ s 8 = [] ∧ s 9 = [] ∧
      s 10 = [] ∧ s 11 = [] ∧ s 12 = [] ∧ s 13 = [] ∧ s 14 = [] ∧ s 15 = [] :=
  ⟨h 2 (by norm_num) (by norm_num), h 3 (by norm_num) (by norm_num),
    h 4 (by norm_num) (by norm_num), h 5 (by norm_num) (by norm_num),
    h 6 (by norm_num) (by norm_num), h 7 (by norm_num) (by norm_num),
    h 8 (by norm_num) (by norm_num), h 9 (by norm_num) (by norm_num),
    h 10 (by norm_num) (by norm_num), h 11 (by norm_num) (by norm_num),
    h 12 (by norm_num) (by norm_num), h 13 (by norm_num) (by norm_num),
    h 14 (by norm_num) (by norm_num), h 15 (by norm_num) (by norm_num)⟩

/-! ### Reading a register -/

/-- `X := σ d` (unary), for `X` empty; the memory keeps its contents. -/
def get (d X : ℕ) : SProg :=
  seqs [pushN mR d, swap, copy mV X mT1, pushN mR d, swap]

set_option maxHeartbeats 1000000 in
theorem get_spec (d X : ℕ) (hX : X = mA ∨ X = mB) (s : Stacks) (σ : Memory) (bs : List ℕ)
    (Λ M : ℕ) (hM : s mMEM = enc bs) (hG : Good bs σ Λ) (hσ : ∀ i, σ i ≤ M) (hd : d < Λ)
    (hC : Clean s) :
    ∃ bs', Good bs' σ Λ ∧ (get d X).exec s = update (update s mMEM (enc bs')) X (rep (σ d)) ∧
      (get d X).cost s ≤ 30 * W Λ M + 30 := by
  obtain ⟨c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15⟩ := hC.facts
  have hdW : d ≤ W Λ M := by unfold W; nlinarith
  have hMW : M ≤ W Λ M := by unfold W; omega
  -- first swap: register d := 0, V := σ d
  have p1 := pushN_spec mR d s
  rw [c3, List.append_nil] at p1
  obtain ⟨b1, g1, e1, k1⟩ := swap_good (update s mR (rep d)) σ bs Λ M d 0 (by simp [hM]) hG hσ hd
    (Nat.zero_le _) (by simp) (by simp [c4]) (by simp [c2]) (by simp [c5]) (by simp [c6])
  set s2 := update (update (update (update s mR (rep d)) mMEM (enc b1)) mR []) mV (rep (σ d))
    with hs2
  have hσ1 : ∀ i, σ.set d 0 i ≤ M := memory_set_le hσ (Nat.zero_le _)
  have hX1 : X ≠ 1 := by rcases hX with rfl | rfl <;> decide
  have hX2 : X ≠ 2 := by rcases hX with rfl | rfl <;> decide
  have hX3 : X ≠ 3 := by rcases hX with rfl | rfl <;> decide
  have hX4 : X ≠ 4 := by rcases hX with rfl | rfl <;> decide
  have hX5 : X ≠ 5 := by rcases hX with rfl | rfl <;> decide
  have hX6 : X ≠ 6 := by rcases hX with rfl | rfl <;> decide
  have hX9 : X ≠ 9 := by rcases hX with rfl | rfl <;> decide
  have hXe : s X = [] := by rcases hX with rfl | rfl <;> assumption
  have cp := exec_copy (a := mV) (b := X) (t := mT1) (Ne.symm hX4) (by decide) hX9 s2
    (by simp [s2, c9])
  have cpc := cost_copy (a := mV) (b := X) (t := mT1) (Ne.symm hX4) (by decide) hX9 s2
    (by simp [s2, c9])
  set s3 := (copy mV X mT1).exec s2 with hs3
  have p2 := pushN_spec mR d s3
  have hs3R : s3 mR = [] := by rw [cp]; simp [s2, hX3, Ne.symm hX3]
  rw [hs3R, List.append_nil] at p2
  obtain ⟨b2, g2, e2, k2⟩ := swap_good (update s3 mR (rep d)) (σ.set d 0) b1 Λ M d (σ d)
    (by rw [cp]; simp [s2, hX1, Ne.symm hX1]) g1 hσ1 hd (hσ d) (by simp) (by rw [cp]; simp [s2, hX4, Ne.symm hX4])
    (by rw [cp]; simp [s2, c2, hX2, Ne.symm hX2]) (by rw [cp]; simp [s2, c5, hX5, Ne.symm hX5])
    (by rw [cp]; simp [s2, c6, hX6, Ne.symm hX6])
  have hset : (σ.set d 0).set d (σ d) = σ := by
    rw [memory_set_set, memory_set_eq_self]
  rw [hset] at g2
  refine ⟨b2, g2, ?_, ?_⟩
  · show swap.exec ((pushN mR d).exec ((copy mV X mT1).exec (swap.exec ((pushN mR d).exec s)))) = _
    rw [p1.1, e1, ← hs3, p2.1, e2, cp]
    simp only [s2, Memory.set, if_true]
    stacks_ext_with [c3, c4, rep, hXe, hX1, hX2, hX3, hX4, hX5, hX6, hX9, Ne.symm hX1,
      Ne.symm hX3, Ne.symm hX4]
  · show (pushN mR d).cost s + (swap.cost ((pushN mR d).exec s) + ((copy mV X mT1).cost
      (swap.exec ((pushN mR d).exec s)) + ((pushN mR d).cost ((copy mV X mT1).exec
      (swap.exec ((pushN mR d).exec s))) + (swap.cost ((pushN mR d).exec ((copy mV X mT1).exec
      (swap.exec ((pushN mR d).exec s)))) + 0)))) ≤ _
    rw [p1.1, p1.2, e1, cpc, ← hs3, p2.2, p2.1]
    have : (s2 mV).length = σ d := by simp [s2]
    have := hσ d
    omega

/-! ### Writing a register -/

/-- Register `d := ` the unary value on `V`; `V` is emptied. -/
def put (d : ℕ) : SProg := seqs [pushN mR d, swap, clear mV]

set_option maxHeartbeats 1000000 in
theorem put_spec (d v : ℕ) (s : Stacks) (σ : Memory) (bs : List ℕ) (Λ M : ℕ)
    (hM : s mMEM = enc bs) (hG : Good bs σ Λ) (hσ : ∀ i, σ i ≤ M) (hd : d < Λ) (hv : v ≤ M)
    (hV : s mV = rep v) (hC : ∀ j, 2 ≤ j → j < 16 → j ≠ mV → s j = []) :
    ∃ bs', Good bs' (σ.set d v) Λ ∧ (put d).exec s = update (update s mMEM (enc bs')) mV [] ∧
      (put d).cost s ≤ 12 * W Λ M + 14 := by
  have c2 := hC 2 (by norm_num) (by norm_num) (by decide)
  have c3 := hC 3 (by norm_num) (by norm_num) (by decide)
  have c5 := hC 5 (by norm_num) (by norm_num) (by decide)
  have c6 := hC 6 (by norm_num) (by norm_num) (by decide)
  have hdW : d ≤ W Λ M := by unfold W; nlinarith
  have hMW : M ≤ W Λ M := by unfold W; omega
  have p1 := pushN_spec mR d s
  rw [c3, List.append_nil] at p1
  obtain ⟨b1, g1, e1, k1⟩ := swap_good (update s mR (rep d)) σ bs Λ M d v (by simp [hM]) hG hσ hd
    hv (by simp) (by simp [hV]) (by simp [c2]) (by simp [c5]) (by simp [c6])
  refine ⟨b1, g1, ?_, ?_⟩
  · show (clear mV).exec (swap.exec ((pushN mR d).exec s)) = _
    rw [p1.1, e1, exec_clear]
    stacks_ext_with [c3]
  · show (pushN mR d).cost s + (swap.cost ((pushN mR d).exec s) +
      ((clear mV).cost (swap.exec ((pushN mR d).exec s)) + 0)) ≤ _
    rw [p1.1, p1.2, e1, cost_clear]
    have := hσ d
    simp
    omega

end Factoring.Aux.Sim
