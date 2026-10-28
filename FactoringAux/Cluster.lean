/-
Clustering and the sizes of the multiplication network.

Generic, for any network and grouping:
* `coarsen_cc_eq`: two different groups share `Y_{γ,γ'}` bits (both orders);
* `coarsen_rowsum_le`: a group shares at most what its nodes share; `coarsen_total_le`: the total does not grow.

The multiplication network:
* `mC_row_le`: per gate, the bits it shares (`A·fw` for `faP`, `faQ`; `3A·fw` for `mid`; `2A·fw` for `ib`;
  `3·fw` for `carry`);
* `clMG g`: gates into `g` clusters, each kind split evenly by index (`card_div_eq_le`: at most `n/g + 2` indices
  `r < n` have `r g / n = γ`);
* **`clusterNet`** (`(mulNet …).coarsen`), with value the count (`clusterNet_value`), fitting
  `P = 10A²·fw/g + 20A·fw + 6fw` (`clusterNet_fits`), total at most `10A²·fw` (`clusterNet_total_le`).

Not an audit surface.
-/
module

public import FactoringAux.MulCount
public import FactoringAux.Lemma1

@[expose] public section

namespace Factoring.Aux

open Finset

namespace Net

variable {R : Type*} [CommRing R] {g K : ℕ}

theorem grpY_symm (c : Fin g → Fin g → ℕ) (hsym : ∀ a b, c a b = c b a) (χ : Fin g → Fin K) (γ γ' : Fin K) :
    grpY c χ γ γ' = grpY c χ γ' γ := by
  unfold grpY ind2
  rw [← (Equiv.prodComm (Fin g) (Fin g)).sum_comp]
  refine sum_congr rfl fun q _ => ?_
  simp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap, hsym q.2 q.1]
  by_cases h : χ q.1 = γ' ∧ χ q.2 = γ <;> simp [h, and_comm]

/-- Two different groups share `Y_{γ,γ'}` bits, in either order. -/
theorem coarsen_cc_eq (N : Net R g) (χ : Fin g → Fin K) {γ γ' : Fin K} (hne : γ ≠ γ') :
    (((N.coarsen χ).cc γ γ' : ℕ) : ℤ) = grpY N.cc χ γ γ' := by
  rw [show (N.coarsen χ).cc γ γ' = if γ < γ' then (N.coarsen χ).c γ γ' else
    if γ' < γ then (N.coarsen χ).c γ' γ else 0 from rfl]
  rcases lt_or_gt_of_ne hne with h | h
  · rw [if_pos h]; exact coarsen_c_eq N χ hne
  · rw [if_neg (not_lt.mpr h.le), if_pos h, coarsen_c_eq N χ hne.symm, grpY_symm _ N.cc_symm]

/-- A group shares at most the bits its nodes share. -/
theorem coarsen_rowsum_le (N : Net R g) (χ : Fin g → Fin K) (γ : Fin K) :
    ∑ γ', (N.coarsen χ).cc γ γ' ≤ ∑ a, if χ a = γ then ∑ b, N.cc a b else 0 := by
  have key : ((∑ γ', (N.coarsen χ).cc γ γ' : ℕ) : ℤ) ≤ ∑ γ', grpY N.cc χ γ γ' := by
    push_cast
    refine sum_le_sum fun γ' _ => ?_
    by_cases h : γ = γ'
    · subst h; rw [cc_self]
      show ((0 : ℕ) : ℤ) ≤ grpY N.cc χ γ γ
      unfold grpY
      rw [Nat.cast_zero]
      exact Finset.sum_nonneg (fun q _ => mul_nonneg (Nat.cast_nonneg _) (ind2_nonneg χ γ γ q))
    · exact (coarsen_cc_eq N χ h).le
  have hsum : ∑ γ', grpY N.cc χ γ γ' = ∑ a, if χ a = γ then ∑ b, (N.cc a b : ℤ) else 0 := by
    unfold grpY
    rw [sum_comm]
    simp_rw [← mul_sum]
    have hind : ∀ q : Fin g × Fin g, ∑ γ', ind2 χ γ γ' q = if χ q.1 = γ then 1 else 0 := by
      intro q; unfold ind2
      by_cases h : χ q.1 = γ
      · simp only [h, true_and]; rw [sum_ite_eq]; simp
      · simp [h]
    simp_rw [hind]
    rw [Fintype.sum_prod_type]
    refine sum_congr rfl fun a _ => ?_
    split_ifs with ha <;> simp
  rw [hsum] at key
  have : ((∑ a, if χ a = γ then ∑ b, N.cc a b else 0 : ℕ) : ℤ) =
      ∑ a, if χ a = γ then ∑ b, (N.cc a b : ℤ) else 0 := by
    push_cast; rfl
  exact_mod_cast key.trans this.symm.le

/-- Coarsening does not increase the total. -/
theorem coarsen_total_le (N : Net R g) (χ : Fin g → Fin K) : (N.coarsen χ).total ≤ N.total := by
  unfold total
  calc ∑ γ, ∑ γ', (N.coarsen χ).cc γ γ' ≤ ∑ γ, ∑ a, (if χ a = γ then ∑ b, N.cc a b else 0) :=
        sum_le_sum fun γ _ => coarsen_rowsum_le N χ γ
    _ = ∑ a, ∑ b, N.cc a b := by
        rw [sum_comm]
        refine sum_congr rfl fun a _ => ?_
        rw [sum_ite_eq]; simp

end Net

/-- At most `n/g + 2` indices `r < n` have `r g / n = γ`. -/
theorem card_div_eq_le (n g γ : ℕ) (hg : 0 < g) :
    ((range n).filter (fun r => r * g / n = γ)).card ≤ n / g + 2 := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  set q := γ * n / g
  have hsub : (range n).filter (fun r => r * g / n = γ) ⊆ Ico q (q + n / g + 2) := by
    intro r hr
    simp only [mem_filter, mem_range] at hr
    obtain ⟨-, hr⟩ := hr
    have h1 : γ * n ≤ r * g := by
      have := Nat.div_mul_le_self (r * g) n; rw [hr] at this; exact this
    have h2 : r * g < (γ + 1) * n := by
      have := Nat.lt_succ_self (r * g / n)
      rw [hr] at this
      exact (Nat.div_lt_iff_lt_mul hn).mp (by omega)
    simp only [mem_Ico]
    constructor
    · exact Nat.div_le_of_le_mul (by linarith [h1])
    · have h3 : γ * n < g * (q + 1) := Nat.lt_mul_div_succ _ hg
      have h4 : n < g * (n / g + 1) := Nat.lt_mul_div_succ _ hg
      have h5 : r * g < g * (q + n / g + 2) := by nlinarith
      rw [mul_comm] at h5
      exact Nat.lt_of_mul_lt_mul_left h5
  calc _ ≤ (Ico q (q + n / g + 2)).card := card_le_card hsub
    _ = n / g + 2 := by rw [Nat.card_Ico, add_assoc, Nat.add_sub_cancel_left]

/-! ### The multiplication network: shared bits per gate -/

section MulSizes

variable (s : ℕ)

theorem sum_MG {M : Type*} [AddCommMonoid M] {A : ℕ} (f : MG A → M) :
    ∑ i, f i = ∑ r, f (.faP r) + (∑ r, f (.faQ r) + (∑ k, f (.mid k) + (∑ j, f (.ib j) +
      ∑ j, f (.carry j)))) := by
  rw [← (MG.sumEquiv (A := A)).symm.sum_comp]
  simp only [Fintype.sum_sum_type]
  rfl

theorem mC_symm (i j : MG (pA s)) : mC s i j = mC s j i := by
  unfold mC
  cases i <;> cases j <;> simp only [mLink] <;> (try rfl) <;> simp [or_comm]

/-- At most one index of `Fin n` has a given value. -/
theorem sum_fin_ite_eq_le (n c a : ℕ) : ∑ j : Fin n, (if j.val = c then a else 0) ≤ a := by
  by_cases h : c < n
  · rw [Finset.sum_eq_single ⟨c, h⟩ (fun b _ hb => if_neg (fun e => hb (Fin.ext e))) (by simp)]
    simp
  · rw [Finset.sum_eq_zero fun j _ => if_neg (fun (e : j.val = c) => h (e ▸ j.isLt))]; exact Nat.zero_le _

/-- At most `A` indices `j < A·A` have `j mod A = j₁`. -/
theorem card_mod_eq_le (A j₁ : ℕ) : ((univ : Finset (Fin (A * A))).filter (fun j => j.val % A = j₁)).card ≤ A := by
  rcases Nat.eq_zero_or_pos A with hA | hA
  · subst hA; simp
  calc _ ≤ (range A).card := by
        refine card_le_card_of_injOn (fun j => j.val / A) (fun j _ => ?_) (fun a ha b hb hab => ?_)
        · simp only [coe_range, Set.mem_Iio]; exact (Nat.div_lt_iff_lt_mul hA).mpr j.isLt
        · simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at ha hb
          apply Fin.ext
          rw [← Nat.mod_add_div a.val A, ← Nat.mod_add_div b.val A, ha, hb]
          simp only at hab; rw [hab]
    _ = A := card_range A

/-- The bits a gate shares, by kind. -/
def rowB : MG (pA s) → ℕ
  | .faP _ => pA s * fw s
  | .faQ _ => pA s * fw s
  | .mid _ => 3 * pA s * fw s
  | .ib _ => 2 * pA s * fw s
  | .carry _ => 3 * fw s

theorem mC_row_le (i : MG (pA s)) : ∑ j, mC s i j ≤ rowB s i := by
  rw [sum_MG]
  cases i with
  | faP r => simp [mC, mLink, rowB]
  | faQ r => simp [mC, mLink, rowB]
  | mid k => simp [mC, mLink, rowB]; ring_nf; omega
  | ib j₁ =>
      simp only [mC, mLink, rowB, Bool.false_eq_true, if_false, if_true, decide_eq_true_eq,
        sum_const_zero, zero_add, sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
      have : ∑ j : Fin (pA s * pA s), (if j.val % pA s = j₁.val then fw s else 0) ≤ pA s * fw s := by
        rw [← sum_filter, sum_const, smul_eq_mul]
        exact Nat.mul_le_mul_right _ (card_mod_eq_le _ _)
      nlinarith
  | carry j =>
      simp only [mC, mLink, rowB, Bool.false_eq_true, if_false, decide_eq_true_eq, sum_const_zero, zero_add]
      have h1 : ∑ j₁ : Fin (pA s), (if j.val % pA s = j₁.val then fw s else 0) ≤ fw s := by
        simpa only [eq_comm] using sum_fin_ite_eq_le (pA s) (j.val % pA s) (fw s)
      have h2 : ∑ j' : Fin (pA s * pA s), (if j'.val = j.val + 1 ∨ j.val = j'.val + 1 then fw s else 0) ≤
          2 * fw s := by
        calc _ ≤ ∑ j' : Fin (pA s * pA s), ((if j'.val = j.val + 1 then fw s else 0) +
              (if j'.val = j.val - 1 then fw s else 0)) := by
              refine sum_le_sum fun j' _ => ?_
              by_cases a : j'.val = j.val + 1
              · rw [if_pos (Or.inl a), if_pos a]; omega
              · by_cases b : j.val = j'.val + 1
                · rw [if_pos (Or.inr b), if_neg a, if_pos (by omega)]; omega
                · rw [if_neg (by tauto)]; omega
          _ ≤ fw s + fw s := by
              rw [sum_add_distrib]
              exact Nat.add_le_add (sum_fin_ite_eq_le _ _ _) (sum_fin_ite_eq_le _ _ _)
          _ = 2 * fw s := by ring
      omega

theorem idx_div_lt {r n g : ℕ} (hr : r < n) (hg : 0 < g) : r * g / n < g := by
  rw [Nat.div_lt_iff_lt_mul (by omega)]; rw [mul_comm g n]; exact Nat.mul_lt_mul_of_pos_right hr hg

/-- Gates into `g` clusters: each kind is split evenly by index. -/
def clMG (g : ℕ) (hg : 0 < g) : MG (pA s) → Fin g
  | .faP r => ⟨r * g / pA s, idx_div_lt r.isLt hg⟩
  | .faQ r => ⟨r * g / pA s, idx_div_lt r.isLt hg⟩
  | .mid k => ⟨k * g / pA s, idx_div_lt k.isLt hg⟩
  | .ib j => ⟨j * g / pA s, idx_div_lt j.isLt hg⟩
  | .carry j => ⟨j * g / (pA s * pA s), idx_div_lt j.isLt hg⟩

/-- The fit of a cluster. -/
def clP (g : ℕ) : ℕ := 7 * (pA s / g + 2) * pA s * fw s + 3 * (pA s * pA s / g + 2) * fw s

theorem kind_sum_le (n g c : ℕ) (hg : 0 < g) (γ : Fin g) :
    ∑ r : Fin n, (if r.val * g / n = γ.val then c else 0) ≤ c * (n / g + 2) := by
  rw [Fin.sum_univ_eq_sum_range (fun r => if r * g / n = γ.val then c else 0), ← sum_filter, sum_const,
    smul_eq_mul, mul_comm]
  exact Nat.mul_le_mul_left _ (card_div_eq_le n g γ hg)

variable (R : Type*) [CommRing R]

/-- **The cluster network**: the multiplication network grouped into `g` clusters. -/
def clusterNet (N k x g : ℕ) (hg : 0 < g) : Net R g :=
  (mulNet s R N k x).coarsen (fun a => clMG s g hg ((MG.enum (pA s)).symm a))

theorem clusterNet_value (N k x g : ℕ) (hg : 0 < g) (hN1 : 1 ≤ N) (hN : N < 2 ^ (pL s * pL s)) :
    (clusterNet s R N k x g hg).value = ((N.divisors.filter (fun d => d / 2 ^ k = x)).card : R) := by
  unfold clusterNet; rw [Net.value_coarsen, mulNet_value s N k x hN1 hN]

theorem mulNet_row_le (N k x : ℕ) (a : Fin (pA s + (pA s + (pA s + (pA s + pA s * pA s))))) :
    ∑ b, (mulNet s R N k x).cc a b ≤ rowB s ((MG.enum (pA s)).symm a) := by
  calc ∑ b, (mulNet s R N k x).cc a b ≤ ∑ b, mC s ((MG.enum (pA s)).symm a) ((MG.enum (pA s)).symm b) := by
        refine sum_le_sum fun b _ => ?_
        unfold Net.cc
        split_ifs
        · exact le_rfl
        · exact (mC_symm s _ _).le
        · exact Nat.zero_le _
    _ = ∑ j, mC s ((MG.enum (pA s)).symm a) j :=
        Fintype.sum_equiv (MG.enum (pA s)).symm _ _ fun _ => rfl
    _ ≤ _ := mC_row_le s _

/-- **The clusters fit `clP g`.** -/
theorem clusterNet_fits (N k x g : ℕ) (hg : 0 < g) : (clusterNet s R N k x g hg).Fits (clP s g) := by
  intro γ
  refine (Net.coarsen_rowsum_le _ _ γ).trans ?_
  calc ∑ a, (if clMG s g hg ((MG.enum (pA s)).symm a) = γ then ∑ b, (mulNet s R N k x).cc a b else 0)
      ≤ ∑ a, (if clMG s g hg ((MG.enum (pA s)).symm a) = γ then rowB s ((MG.enum (pA s)).symm a) else 0) :=
        sum_le_sum fun a _ => by split_ifs; exacts [mulNet_row_le s R N k x a, le_rfl]
    _ = ∑ i, (if clMG s g hg i = γ then rowB s i else 0) :=
        Fintype.sum_equiv (MG.enum (pA s)).symm _ _ fun _ => rfl
    _ ≤ clP s g := by
        rw [sum_MG]
        simp only [clMG, rowB, Fin.ext_iff]
        have h1 := kind_sum_le (pA s) g (pA s * fw s) hg γ
        have h2 := kind_sum_le (pA s) g (3 * pA s * fw s) hg γ
        have h3 := kind_sum_le (pA s) g (2 * pA s * fw s) hg γ
        have h4 := kind_sum_le (pA s * pA s) g (3 * fw s) hg γ
        unfold clP
        nlinarith

/-- **The total of the clusters is at most `10A²·fw`.** -/
theorem clusterNet_total_le (N k x g : ℕ) (hg : 0 < g) :
    (clusterNet s R N k x g hg).total ≤ 10 * (pA s * pA s) * fw s := by
  refine (Net.coarsen_total_le _ _).trans ?_
  calc (mulNet s R N k x).total ≤ ∑ a, rowB s ((MG.enum (pA s)).symm a) :=
        sum_le_sum fun a _ => mulNet_row_le s R N k x a
    _ = ∑ i, rowB s i := Fintype.sum_equiv (MG.enum (pA s)).symm _ _ fun _ => rfl
    _ = 10 * (pA s * pA s) * fw s := by
        rw [sum_MG]; simp only [rowB, sum_const, card_univ, Fintype.card_fin, smul_eq_mul]; ring

end MulSizes

end Factoring.Aux
