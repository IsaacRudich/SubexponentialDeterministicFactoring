/-
Lemma 1 of the paper, assembled: cost parameters of a network (`Net.cc`, `Net.Fits`, `Net.total`), the bits shared
by two groups of the coarsened network (`coarsen_c_eq`), and the statement `lemma1`: a network on `3K^8` nodes that
fits `P` has a good grouping into `K` groups (at most `2g/K` nodes per group, and every pair of groups sharing at most
`(U + gP/K)/K²` bits), and the written-out clique of (26) has the network's value.

Not an audit surface.
-/
module

public import FactoringAux.Clique
public import FactoringAux.Grouping

@[expose] public section

namespace Factoring.Aux

open Finset

namespace Net

variable {R : Type*} [CommRing R] {g K : ℕ}

/-- The bits shared by `a` and `b`, symmetric, `0` on the diagonal. -/
def cc (N : Net R g) (a b : Fin g) : ℕ := if a < b then N.c a b else if b < a then N.c b a else 0

theorem cc_symm (N : Net R g) (a b : Fin g) : N.cc a b = N.cc b a := by
  unfold cc
  rcases lt_trichotomy a b with h | h | h
  · simp [h, not_lt.mpr h.le]
  · subst h; rfl
  · simp [h, not_lt.mpr h.le]

theorem cc_self (N : Net R g) (a : Fin g) : N.cc a a = 0 := by simp [cc]

/-- Definition 2 (i): every node shares at most `P` bits in all. -/
def Fits (N : Net R g) (P : ℕ) : Prop := ∀ a, ∑ b, N.cc a b ≤ P

/-- The total `U`, over ordered pairs. -/
def total (N : Net R g) : ℕ := ∑ a, ∑ b, N.cc a b

theorem totU_cc (N : Net R g) : totU N.cc = N.total := by
  simp [totU, total, Fintype.sum_prod_type]

/-- Two different groups of the coarsened network share `Y_{γ,γ'}` bits. -/
theorem coarsen_c_eq (N : Net R g) (χ : Fin g → Fin K) {γ γ' : Fin K} (hne : γ ≠ γ') :
    (((N.coarsen χ).c γ γ' : ℕ) : ℤ) = grpY N.cc χ γ γ' := by
  have h1 : (((N.coarsen χ).c γ γ' : ℕ) : ℤ) =
      ∑ p ∈ pairs g, if Cross χ γ γ' p then (N.c p.1 p.2 : ℤ) else 0 := by
    show ((((crossList χ γ γ').map (fun p => N.c p.1 p.2)).sum : ℕ) : ℤ) = _
    rw [Nat.cast_list_sum, List.map_map, ← Finset.sum_filter, crossList,
      ← List.sum_toFinset _ ((pairsList_nodup g).filter _)]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext p; simp [mem_pairsList]
  rw [h1]
  unfold grpY ind2 cc
  -- split the ordered pairs into `a < b` and `b < a`
  have hsplit : ∀ q : Fin g × Fin g,
      ((if q.1 < q.2 then N.c q.1 q.2 else if q.2 < q.1 then N.c q.2 q.1 else 0 : ℕ) : ℤ) *
        (if χ q.1 = γ ∧ χ q.2 = γ' then 1 else 0) =
      (if q.1 < q.2 ∧ χ q.1 = γ ∧ χ q.2 = γ' then (N.c q.1 q.2 : ℤ) else 0) +
        (if q.2 < q.1 ∧ χ q.1 = γ ∧ χ q.2 = γ' then (N.c q.2 q.1 : ℤ) else 0) := by
    intro q
    rcases lt_trichotomy q.1 q.2 with h | h | h
    · simp [h, not_lt.mpr h.le]
    · simp [h]
    · simp [h, not_lt.mpr h.le]
  rw [Finset.sum_congr rfl fun q _ => hsplit q, Finset.sum_add_distrib]
  have hA : ∑ q : Fin g × Fin g, (if q.1 < q.2 ∧ χ q.1 = γ ∧ χ q.2 = γ' then (N.c q.1 q.2 : ℤ) else 0) =
      ∑ p ∈ pairs g, if χ p.1 = γ ∧ χ p.2 = γ' then (N.c p.1 p.2 : ℤ) else 0 := by
    rw [pairs, Finset.sum_filter]
    exact Finset.sum_congr rfl fun q _ => by by_cases h : q.1 < q.2 <;> simp [h]
  have hB : ∑ q : Fin g × Fin g, (if q.2 < q.1 ∧ χ q.1 = γ ∧ χ q.2 = γ' then (N.c q.2 q.1 : ℤ) else 0) =
      ∑ p ∈ pairs g, if χ p.1 = γ' ∧ χ p.2 = γ then (N.c p.1 p.2 : ℤ) else 0 := by
    rw [pairs, Finset.sum_filter, ← (Equiv.prodComm (Fin g) (Fin g)).sum_comp]
    exact Finset.sum_congr rfl fun q _ => by
      by_cases h : q.1 < q.2 <;> simp [h, and_comm]
  rw [hA, hB, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  unfold Cross
  by_cases h1 : χ p.1 = γ ∧ χ p.2 = γ'
  · have h2 : ¬ (χ p.1 = γ' ∧ χ p.2 = γ) := fun h2 => hne (h1.1.symm.trans h2.1)
    simp [h1, hne]
  · by_cases h2 : χ p.1 = γ' ∧ χ p.2 = γ
    · simp [h2, hne, Ne.symm hne]
    · simp [h1, h2]

/-- **Lemma 1** (without the running time): a network on `g = 3K^8` nodes that fits `P` has a grouping into `K`
groups with (G1) at most `2g/K` nodes per group and (G2) at most `(U + gP/K)/K²` bits shared by any two groups; and
for every `L` at least the bits shared by any two groups, the written-out `(K, L)`-clique of (26) has the network's
value. -/
theorem lemma1 (N : Net R g) (P : ℕ) (hfit : N.Fits P) (hK : 2 ≤ K) (hg : g = 3 * K ^ 8) :
    ∃ χ : Fin g → Fin K,
      (∀ γ, K * (univ.filter (χ · = γ)).card ≤ 2 * g) ∧
      (∀ γ γ', γ ≠ γ' → K ^ 3 * (N.coarsen χ).c γ γ' ≤ K * N.total + g * P) ∧
      ∀ L, (∀ γ γ', γ < γ' → (N.coarsen χ).c γ γ' ≤ L) → ((N.coarsen χ).toClique L).value = N.value := by
  obtain ⟨χ, h1, h2⟩ := exists_good hK N.cc N.cc_self N.cc_symm P hfit hg
  refine ⟨χ, fun γ => ?_, fun γ γ' hne => ?_, fun L hL => value_group N χ L hL⟩
  · have := h1 γ
    have hs : grpSize χ γ = ((univ.filter (χ · = γ)).card : ℤ) := by
      simp [grpSize, Finset.sum_boole]
    rw [hs] at this
    exact_mod_cast this
  · have := h2 γ γ' hne
    rw [← coarsen_c_eq N χ hne, totU_cc] at this
    exact_mod_cast this

end Net

end Factoring.Aux
