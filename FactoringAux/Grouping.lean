/-
A good grouping exists (the first half of the paper's Lemma 1), by first and second moments over all `K^g`
groupings `χ : Fin g → Fin K` (the probabilistic argument, written as counting).

For a symmetric `c : Fin g → Fin g → ℕ` with zero diagonal and row sums at most `P`, put
`Y_{γ,γ'} = ∑_{χ a = γ, χ b = γ'} c a b` and `U = ∑_{a,b} c a b`.  A grouping is good (`Good`) if
* (G1) every group has at most `2g/K` nodes, and
* (G2) `Y_{γ,γ'} ≤ (U + gP/K)/K²` for `γ ≠ γ'`,
both written without division.  `exists_good`: for `K ≥ 2` and `g = 3K^8` a good grouping exists.

Tools: `sum_prod_fix` (`∑_χ ∏_{x ∈ S} [χ x = f x] = K^(g − |S|)`), the second moments `sum_dev_sq_le` (for `Y`)
and `sum_size_dev_sq` (for group sizes), and counting Chebyshev (`card_mul_le_sum_sq`).

Not an audit surface.
-/
module

public import FactoringAux.Bits
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.LinearCombination

@[expose] public section

namespace Factoring.Aux

open Finset

variable {g K : ℕ}

/-! ### Fixing coordinates -/

/-- The number of groupings with prescribed groups on a set `S` of nodes. -/
theorem sum_prod_fix (S : Finset (Fin g)) (f : Fin g → Fin K) :
    ∑ χ : Fin g → Fin K, ∏ x ∈ S, (if χ x = f x then (1 : ℤ) else 0) = (K : ℤ) ^ (g - S.card) := by
  have h1 : ∀ χ : Fin g → Fin K, ∏ x ∈ S, (if χ x = f x then (1 : ℤ) else 0) =
      ∏ x, (fun x k => if x ∈ S then (if k = f x then (1 : ℤ) else 0) else 1) x (χ x) := by
    intro χ
    rw [← Finset.prod_filter_mul_prod_filter_not univ (· ∈ S)]
    simp only [Finset.filter_mem_eq_inter, univ_inter]
    rw [Finset.prod_congr rfl (fun x hx => if_pos hx), Finset.prod_eq_one (fun x hx => if_neg (by
      simpa using hx)), mul_one]
  simp only [h1]
  rw [← Fintype.prod_sum (fun x (k : Fin K) => if x ∈ S then (if k = f x then (1 : ℤ) else 0) else 1)]
  have h2 : ∀ x, ∑ k : Fin K, (if x ∈ S then (if k = f x then (1 : ℤ) else 0) else 1) =
      if x ∈ S then 1 else (K : ℤ) := by
    intro x; split_ifs <;> simp
  simp only [h2]
  rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
  congr 1
  rw [Finset.filter_not, Finset.filter_mem_eq_inter, univ_inter, Finset.card_sdiff_of_subset (subset_univ _),
    card_univ, Fintype.card_fin]

theorem sum_ind_one (a : Fin g) (γ : Fin K) :
    ∑ χ : Fin g → Fin K, (if χ a = γ then (1 : ℤ) else 0) = (K : ℤ) ^ (g - 1) := by
  have := sum_prod_fix {a} (fun _ => γ)
  simpa using this

theorem sum_ind_two {a b : Fin g} (hab : a ≠ b) (γ γ' : Fin K) :
    ∑ χ : Fin g → Fin K, (if χ a = γ ∧ χ b = γ' then (1 : ℤ) else 0) = (K : ℤ) ^ (g - 2) := by
  have := sum_prod_fix {a, b} (fun x => if x = a then γ else γ')
  rw [Finset.card_pair hab] at this
  rw [← this]
  refine Finset.sum_congr rfl fun χ _ => ?_
  rw [Finset.prod_pair hab, if_pos rfl, if_neg hab.symm, ite_and]
  split_ifs <;> simp

theorem sum_ind_four {a b a' b' : Fin g} (h1 : a ≠ b) (h2 : a ≠ a') (h3 : a ≠ b') (h4 : b ≠ a')
    (h5 : b ≠ b') (h6 : a' ≠ b') (γ γ' : Fin K) :
    ∑ χ : Fin g → Fin K, (if χ a = γ ∧ χ b = γ' then (1 : ℤ) else 0) *
      (if χ a' = γ ∧ χ b' = γ' then (1 : ℤ) else 0) = (K : ℤ) ^ (g - 4) := by
  have := sum_prod_fix {a, b, a', b'} (fun x => if x = a ∨ x = a' then γ else γ')
  have hc : ({a, b, a', b'} : Finset (Fin g)).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [h1, h2, h3]), Finset.card_insert_of_notMem (by simp [h4, h5]),
      Finset.card_pair h6]
  rw [hc] at this
  rw [← this]
  refine Finset.sum_congr rfl fun χ _ => ?_
  rw [Finset.prod_insert (by simp [h1, h2, h3]), Finset.prod_insert (by simp [h4, h5]), Finset.prod_pair h6]
  simp only [true_or, if_true, or_true, h1.symm, h6.symm, h3.symm, h2.symm, if_false,
    false_or, or_false, ite_and]
  split_ifs <;> simp

/-! ### The quantities -/

/-- The indicator that pair `q` runs from group `γ` to group `γ'`. -/
def ind2 (χ : Fin g → Fin K) (γ γ' : Fin K) (q : Fin g × Fin g) : ℤ :=
  if χ q.1 = γ ∧ χ q.2 = γ' then 1 else 0

/-- `Y_{γ,γ'}`: the bits shared between groups `γ` and `γ'` (ordered pairs `a ∈ G_γ`, `b ∈ G_γ'`). -/
def grpY (c : Fin g → Fin g → ℕ) (χ : Fin g → Fin K) (γ γ' : Fin K) : ℤ :=
  ∑ q : Fin g × Fin g, (c q.1 q.2 : ℤ) * ind2 χ γ γ' q

/-- `U`: the total, over ordered pairs. -/
def totU (c : Fin g → Fin g → ℕ) : ℤ := ∑ q : Fin g × Fin g, (c q.1 q.2 : ℤ)

/-- The size of group `γ`. -/
def grpSize (χ : Fin g → Fin K) (γ : Fin K) : ℤ := ∑ a, if χ a = γ then 1 else 0

/-- A good grouping: (G1) `K |G_γ| ≤ 2g`; (G2) `K³ Y_{γ,γ'} ≤ K U + g P` for `γ ≠ γ'`. -/
def Good (c : Fin g → Fin g → ℕ) (P : ℕ) (χ : Fin g → Fin K) : Prop :=
  (∀ γ, (K : ℤ) * grpSize χ γ ≤ 2 * g) ∧
    ∀ γ γ', γ ≠ γ' → (K : ℤ) ^ 3 * grpY c χ γ γ' ≤ K * totU c + g * P

theorem ind2_nonneg (χ : Fin g → Fin K) (γ γ' : Fin K) (q : Fin g × Fin g) : 0 ≤ ind2 χ γ γ' q := by
  unfold ind2; split_ifs <;> norm_num

theorem ind2_le_one (χ : Fin g → Fin K) (γ γ' : Fin K) (q : Fin g × Fin g) : ind2 χ γ γ' q ≤ 1 := by
  unfold ind2; split_ifs <;> norm_num

/-! ### Moments -/

section Moments

variable (c : Fin g → Fin g → ℕ)

/-- `∑_χ [pair q from γ to γ'] = K^(g−2)` for `q.1 ≠ q.2`. -/
theorem sum_ind2 {q : Fin g × Fin g} (hq : q.1 ≠ q.2) (γ γ' : Fin K) :
    ∑ χ : Fin g → Fin K, ind2 χ γ γ' q = (K : ℤ) ^ (g - 2) := sum_ind_two hq γ γ'

theorem sum_grpY (hdiag : ∀ a, c a a = 0) (γ γ' : Fin K) :
    ∑ χ : Fin g → Fin K, grpY c χ γ γ' = (K : ℤ) ^ (g - 2) * totU c := by
  unfold grpY totU
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  by_cases hq : q.1 = q.2
  · simp [hq, hdiag]
  · rw [← Finset.mul_sum, sum_ind2 hq, mul_comm]

/-- `E(q, q') = ∑_χ X_q X_q'`: equal to `K^(g−4)` for four distinct nodes, at most `K^(g−2)` in general. -/
theorem sum_ind2_mul_le {q : Fin g × Fin g} (hq : q.1 ≠ q.2) (q' : Fin g × Fin g) (γ γ' : Fin K) :
    ∑ χ : Fin g → Fin K, ind2 χ γ γ' q * ind2 χ γ γ' q' ≤ (K : ℤ) ^ (g - 2) := by
  rw [← sum_ind2 hq γ γ']
  exact Finset.sum_le_sum fun χ _ =>
    mul_le_of_le_one_right (ind2_nonneg χ γ γ' q) (ind2_le_one χ γ γ' q')

/-- The count of a pair of pairs that do not meet. -/
theorem sum_ind2_mul_disj {q q' : Fin g × Fin g} (h1 : q.1 ≠ q.2) (h2 : q.1 ≠ q'.1) (h3 : q.1 ≠ q'.2)
    (h4 : q.2 ≠ q'.1) (h5 : q.2 ≠ q'.2) (h6 : q'.1 ≠ q'.2) (γ γ' : Fin K) :
    ∑ χ : Fin g → Fin K, ind2 χ γ γ' q * ind2 χ γ γ' q' = (K : ℤ) ^ (g - 4) :=
  sum_ind_four h1 h2 h3 h4 h5 h6 γ γ'

/-- The overlap count `m(q, q') = [q'.1 = q.1] + [q'.1 = q.2] + [q'.2 = q.1] + [q'.2 = q.2]`. -/
def meet (q q' : Fin g × Fin g) : ℤ :=
  (if q'.1 = q.1 then 1 else 0) + (if q'.1 = q.2 then 1 else 0) + (if q'.2 = q.1 then 1 else 0) +
    (if q'.2 = q.2 then 1 else 0)

theorem meet_nonneg (q q' : Fin g × Fin g) : 0 ≤ meet q q' := by
  unfold meet; split_ifs <;> norm_num

/-- `∑_{q'} c_{q'} m(q, q') ≤ 4P`. -/
theorem sum_meet_le (hsym : ∀ a b, c a b = c b a) (P : ℕ) (hrow : ∀ a, ∑ b, c a b ≤ P) (q : Fin g × Fin g) :
    ∑ q' : Fin g × Fin g, (c q'.1 q'.2 : ℤ) * meet q q' ≤ 4 * P := by
  have hr : ∀ a, ∑ b, (c a b : ℤ) ≤ P := fun a => by exact_mod_cast hrow a
  have hcol : ∀ b, ∑ a, (c a b : ℤ) ≤ P := fun b => by
    simpa [hsym] using hr b
  have e1 : ∀ a, ∑ q' : Fin g × Fin g, (c q'.1 q'.2 : ℤ) * (if q'.1 = a then 1 else 0) = ∑ b, (c a b : ℤ) := by
    intro a
    rw [Fintype.sum_prod_type]
    simp
  have e2 : ∀ b, ∑ q' : Fin g × Fin g, (c q'.1 q'.2 : ℤ) * (if q'.2 = b then 1 else 0) = ∑ a, (c a b : ℤ) := by
    intro b
    rw [Fintype.sum_prod_type]
    simp
  unfold meet
  simp only [mul_add, Finset.sum_add_distrib, e1, e2]
  linarith [hr q.1, hr q.2, hcol q.1, hcol q.2]

/-- The second moment: `∑_χ (K² Y − U)² ≤ 4 P U K^(g+2)`. -/
theorem sum_dev_sq_le (hdiag : ∀ a, c a a = 0) (hsym : ∀ a b, c a b = c b a) (P : ℕ)
    (hrow : ∀ a, ∑ b, c a b ≤ P) (hg : 4 ≤ g) (γ γ' : Fin K) :
    ∑ χ : Fin g → Fin K, ((K : ℤ) ^ 2 * grpY c χ γ γ' - totU c) ^ 2 ≤
      (K : ℤ) ^ (g + 2) * (4 * P * totU c) := by
  set U := totU c with hU
  have hKg : (K : ℤ) ^ 2 * (K : ℤ) ^ (g - 2) = (K : ℤ) ^ g := by
    rw [← pow_add]; congr 1; omega
  have hKg4 : (K : ℤ) ^ 4 * (K : ℤ) ^ (g - 4) = (K : ℤ) ^ g := by
    rw [← pow_add]; congr 1; omega
  have hKg2 : (K : ℤ) ^ 4 * (K : ℤ) ^ (g - 2) = (K : ℤ) ^ (g + 2) := by
    rw [← pow_add]; congr 1; omega
  -- expand the square
  have hexp : ∑ χ : Fin g → Fin K, ((K : ℤ) ^ 2 * grpY c χ γ γ' - U) ^ 2 =
      (K : ℤ) ^ 4 * ∑ χ : Fin g → Fin K, grpY c χ γ γ' ^ 2 - (K : ℤ) ^ g * U ^ 2 := by
    have : ∀ χ : Fin g → Fin K, ((K : ℤ) ^ 2 * grpY c χ γ γ' - U) ^ 2 =
        (K : ℤ) ^ 4 * grpY c χ γ γ' ^ 2 - 2 * (K : ℤ) ^ 2 * U * grpY c χ γ γ' + U ^ 2 := fun χ => by ring
    simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, sum_grpY c hdiag,
      Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    rw [← hU]
    linear_combination (-2 * U ^ 2) * hKg
  -- the square of Y as a double sum
  have hY2 : ∑ χ : Fin g → Fin K, grpY c χ γ γ' ^ 2 =
      ∑ q : Fin g × Fin g, ∑ q' : Fin g × Fin g, (c q.1 q.2 : ℤ) * c q'.1 q'.2 *
        ∑ χ : Fin g → Fin K, ind2 χ γ γ' q * ind2 χ γ γ' q' := by
    have : ∀ χ : Fin g → Fin K, grpY c χ γ γ' ^ 2 = ∑ q : Fin g × Fin g, ∑ q' : Fin g × Fin g,
        (c q.1 q.2 : ℤ) * c q'.1 q'.2 * (ind2 χ γ γ' q * ind2 χ γ γ' q') := by
      intro χ
      rw [grpY, sq, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun q' _ => by ring
    simp only [this]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun q' _ => (Finset.mul_sum _ _ _).symm
  have hU2 : U ^ 2 = ∑ q : Fin g × Fin g, ∑ q' : Fin g × Fin g, (c q.1 q.2 : ℤ) * c q'.1 q'.2 := by
    rw [hU, totU, sq, Finset.sum_mul_sum]
  -- the per-term bound
  have hterm : ∀ q q' : Fin g × Fin g,
      (c q.1 q.2 : ℤ) * c q'.1 q'.2 * ((K : ℤ) ^ 4 * ∑ χ : Fin g → Fin K, ind2 χ γ γ' q * ind2 χ γ γ' q' -
        (K : ℤ) ^ g) ≤ (K : ℤ) ^ (g + 2) * ((c q.1 q.2 : ℤ) * (c q'.1 q'.2 * meet q q')) := by
    intro q q'
    have hc0 : (0 : ℤ) ≤ c q.1 q.2 * c q'.1 q'.2 := by positivity
    have hK : (0 : ℤ) ≤ (K : ℤ) ^ g := by positivity
    by_cases hq : q.1 = q.2
    · rw [hq, hdiag]; simp
    by_cases hq' : q'.1 = q'.2
    · rw [hq', hdiag]; simp
    by_cases hm : q.1 ≠ q'.1 ∧ q.1 ≠ q'.2 ∧ q.2 ≠ q'.1 ∧ q.2 ≠ q'.2
    · rw [sum_ind2_mul_disj hq hm.1 hm.2.1 hm.2.2.1 hm.2.2.2 hq' γ γ', hKg4, sub_self, mul_zero]
      have := meet_nonneg q q'
      positivity
    · have hm1 : 1 ≤ meet q q' := by
        unfold meet
        simp only [not_and_or, not_not] at hm
        rcases hm with h | h | h | h <;> simp only [h] <;> split_ifs <;> norm_num
      have hE := sum_ind2_mul_le hq q' γ γ'
      calc (c q.1 q.2 : ℤ) * c q'.1 q'.2 * ((K : ℤ) ^ 4 * ∑ χ : Fin g → Fin K,
              ind2 χ γ γ' q * ind2 χ γ γ' q' - (K : ℤ) ^ g)
          ≤ (c q.1 q.2 : ℤ) * c q'.1 q'.2 * ((K : ℤ) ^ 4 * (K : ℤ) ^ (g - 2)) := by
            apply mul_le_mul_of_nonneg_left _ hc0
            have : (0 : ℤ) ≤ (K : ℤ) ^ 4 := by positivity
            nlinarith
        _ = (K : ℤ) ^ (g + 2) * ((c q.1 q.2 : ℤ) * c q'.1 q'.2 * 1) := by rw [hKg2]; ring
        _ ≤ (K : ℤ) ^ (g + 2) * ((c q.1 q.2 : ℤ) * c q'.1 q'.2 * meet q q') := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact mul_le_mul_of_nonneg_left hm1 hc0
        _ = _ := by ring
  rw [hexp, hY2, hU2, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc _ ≤ ∑ q : Fin g × Fin g, ∑ q' : Fin g × Fin g,
          (K : ℤ) ^ (g + 2) * ((c q.1 q.2 : ℤ) * (c q'.1 q'.2 * meet q q')) := by
        refine Finset.sum_le_sum fun q _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_le_sum fun q' _ => ?_
        have := hterm q q'
        linarith
    _ = (K : ℤ) ^ (g + 2) * ∑ q : Fin g × Fin g, (c q.1 q.2 : ℤ) *
          ∑ q' : Fin g × Fin g, (c q'.1 q'.2 * meet q q') := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum]
    _ ≤ (K : ℤ) ^ (g + 2) * ∑ q : Fin g × Fin g, (c q.1 q.2 : ℤ) * (4 * P) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Finset.sum_le_sum fun q _ =>
          mul_le_mul_of_nonneg_left (sum_meet_le c hsym P hrow q) (by positivity)
    _ = (K : ℤ) ^ (g + 2) * (4 * P * U) := by
        rw [hU, totU, ← Finset.sum_mul]; ring

/-- The group sizes: `∑_χ (K |G_γ| − g)² ≤ g K^(g+1)`. -/
theorem sum_size_dev_sq (hg : 2 ≤ g) (γ : Fin K) :
    ∑ χ : Fin g → Fin K, ((K : ℤ) * grpSize χ γ - g) ^ 2 ≤ (g : ℤ) * (K : ℤ) ^ (g + 1) := by
  have hs1 : ∑ χ : Fin g → Fin K, grpSize χ γ = g * (K : ℤ) ^ (g - 1) := by
    unfold grpSize
    rw [Finset.sum_comm]
    simp only [sum_ind_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hs2 : ∑ χ : Fin g → Fin K, grpSize χ γ ^ 2 =
      g * (K : ℤ) ^ (g - 1) + (g * (g - 1) : ℤ) * (K : ℤ) ^ (g - 2) := by
    have : ∀ χ : Fin g → Fin K, grpSize χ γ ^ 2 =
        ∑ q : Fin g × Fin g, (if χ q.1 = γ ∧ χ q.2 = γ then (1 : ℤ) else 0) := by
      intro χ
      rw [grpSize, sq, Finset.sum_mul_sum, ← Finset.univ_product_univ, Finset.sum_product]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      split_ifs <;> simp_all
    simp only [this]
    rw [Finset.sum_comm]
    rw [← Finset.sum_filter_add_sum_filter_not univ (fun q : Fin g × Fin g => q.1 = q.2)]
    have hd : ∀ q ∈ univ.filter (fun q : Fin g × Fin g => q.1 = q.2),
        ∑ χ : Fin g → Fin K, (if χ q.1 = γ ∧ χ q.2 = γ then (1 : ℤ) else 0) = (K : ℤ) ^ (g - 1) := by
      intro q hq
      rw [(Finset.mem_filter.mp hq).2]
      simpa using sum_ind_one (K := K) q.2 γ
    have hnd : ∀ q ∈ univ.filter (fun q : Fin g × Fin g => ¬ q.1 = q.2),
        ∑ χ : Fin g → Fin K, (if χ q.1 = γ ∧ χ q.2 = γ then (1 : ℤ) else 0) = (K : ℤ) ^ (g - 2) :=
      fun q hq => sum_ind_two (Finset.mem_filter.mp hq).2 γ γ
    rw [Finset.sum_congr rfl hd, Finset.sum_congr rfl hnd, Finset.sum_const, Finset.sum_const]
    have hc1 : (univ.filter (fun q : Fin g × Fin g => q.1 = q.2)).card = g := by
      rw [show univ.filter (fun q : Fin g × Fin g => q.1 = q.2) = univ.image (fun a => (a, a)) by
        ext q; simp [eq_comm, Prod.ext_iff]]
      rw [Finset.card_image_of_injective _ (fun a b h => (Prod.ext_iff.mp h).1), card_univ, Fintype.card_fin]
    have hc2 : (univ.filter (fun q : Fin g × Fin g => ¬ q.1 = q.2)).card = g * (g - 1) := by
      have := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin g × Fin g)))
        (fun q => q.1 = q.2)
      rw [hc1, card_univ, Fintype.card_prod, Fintype.card_fin] at this
      have : g * (g - 1) + g = g * g := by
        cases g with
        | zero => omega
        | succ n => rw [Nat.add_sub_cancel]; ring
      omega
    rw [hc1, hc2, nsmul_eq_mul, nsmul_eq_mul]
    push_cast [Nat.cast_sub (by omega : 1 ≤ g)]
    ring
  have hK1 : (K : ℤ) * (K : ℤ) ^ (g - 1) = (K : ℤ) ^ g := by
    rw [← pow_succ']; congr 1; omega
  have hK2 : (K : ℤ) ^ 2 * (K : ℤ) ^ (g - 2) = (K : ℤ) ^ g := by
    rw [← pow_add]; congr 1; omega
  have hK3 : (K : ℤ) ^ 2 * (K : ℤ) ^ (g - 1) = (K : ℤ) ^ (g + 1) := by
    rw [← pow_add]; congr 1; omega
  have : ∀ χ : Fin g → Fin K, ((K : ℤ) * grpSize χ γ - g) ^ 2 =
      (K : ℤ) ^ 2 * grpSize χ γ ^ 2 - 2 * g * K * grpSize χ γ + g ^ 2 := fun χ => by ring
  simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hs1, hs2,
    Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  have hKg : (0 : ℤ) ≤ (K : ℤ) ^ g := by positivity
  nlinarith [hK1, hK2, hK3]

end Moments

/-! ### Counting Chebyshev and existence -/

/-- If `D² > T²` on a set `B` of groupings, then `|B| T² ≤ ∑_χ D²`. -/
theorem card_mul_le_sum_sq {ι : Type*} [Fintype ι] (D : ι → ℤ) (T : ℤ) (B : Finset ι)
    (hB : ∀ i ∈ B, T ^ 2 ≤ D i ^ 2) : (B.card : ℤ) * T ^ 2 ≤ ∑ i, D i ^ 2 := by
  calc (B.card : ℤ) * T ^ 2 = ∑ _i ∈ B, T ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ i ∈ B, D i ^ 2 := Finset.sum_le_sum hB
    _ ≤ ∑ i, D i ^ 2 := Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun i _ _ => sq_nonneg _)

/-- `U ≤ g P`. -/
theorem totU_le (c : Fin g → Fin g → ℕ) (P : ℕ) (hrow : ∀ a, ∑ b, c a b ≤ P) : totU c ≤ (g : ℤ) * P := by
  unfold totU
  rw [Fintype.sum_prod_type]
  calc ∑ a, ∑ b, (c a b : ℤ) ≤ ∑ _a : Fin g, (P : ℤ) :=
        Finset.sum_le_sum fun a _ => by exact_mod_cast hrow a
    _ = (g : ℤ) * P := by simp

theorem totU_nonneg (c : Fin g → Fin g → ℕ) : 0 ≤ totU c :=
  Finset.sum_nonneg fun _ _ => by positivity

/-- Lemma 1, existence: for `K ≥ 2` and `g = 3K^8`, some grouping is good. -/
theorem exists_good (hK : 2 ≤ K) (c : Fin g → Fin g → ℕ) (hdiag : ∀ a, c a a = 0)
    (hsym : ∀ a b, c a b = c b a) (P : ℕ) (hrow : ∀ a, ∑ b, c a b ≤ P) (hg : g = 3 * K ^ 8) :
    ∃ χ : Fin g → Fin K, Good c P χ := by
  have h256 : 256 ≤ K ^ 8 := by
    calc 256 = 2 ^ 8 := by norm_num
      _ ≤ K ^ 8 := Nat.pow_le_pow_left hK 8
  have hg4 : 4 ≤ g := by rw [hg]; linarith
  have hgpos : (0 : ℤ) < g := by exact_mod_cast (by omega : 0 < g)
  have hKpos : (0 : ℤ) < K := by exact_mod_cast (by omega : 0 < K)
  set B1 : Fin K → Finset (Fin g → Fin K) :=
    fun γ => univ.filter (fun χ => 2 * (g : ℤ) < K * grpSize χ γ) with hB1def
  set B2 : Fin K × Fin K → Finset (Fin g → Fin K) :=
    fun q => univ.filter (fun χ => (K : ℤ) * totU c + g * P < (K : ℤ) ^ 3 * grpY c χ q.1 q.2) with hB2def
  -- the group-size bound
  have hB1 : ∀ γ, ((B1 γ).card : ℤ) * g ≤ (K : ℤ) ^ (g + 1) := by
    intro γ
    have h1 := card_mul_le_sum_sq (fun χ => (K : ℤ) * grpSize χ γ - g) g (B1 γ) (fun χ hχ => by
      have := (Finset.mem_filter.mp hχ).2
      exact pow_le_pow_left₀ hgpos.le (by linarith) 2)
    have h2 := sum_size_dev_sq (K := K) (by omega : 2 ≤ g) γ
    have h3 : ((B1 γ).card : ℤ) * g * g ≤ (K : ℤ) ^ (g + 1) * g := by nlinarith
    exact le_of_mul_le_mul_right h3 hgpos
  -- the shared-bits bound
  have hB2 : ∀ q : Fin K × Fin K, ((B2 q).card : ℤ) * g ≤ 4 * (K : ℤ) ^ (g + 4) := by
    intro q
    have hU := totU_le c P hrow
    have hU0 := totU_nonneg c
    have hP0 : (0 : ℤ) ≤ P := by positivity
    have h1 := card_mul_le_sum_sq (fun χ => (K : ℤ) * ((K : ℤ) ^ 2 * grpY c χ q.1 q.2 - totU c))
      ((g : ℤ) * P + 1) (B2 q) (fun χ hχ => by
        have := (Finset.mem_filter.mp hχ).2
        have h' : (g : ℤ) * P + 1 ≤ (K : ℤ) * ((K : ℤ) ^ 2 * grpY c χ q.1 q.2 - totU c) := by
          have : (K : ℤ) * ((K : ℤ) ^ 2 * grpY c χ q.1 q.2 - totU c) =
              (K : ℤ) ^ 3 * grpY c χ q.1 q.2 - K * totU c := by ring
          rw [this]; linarith
        exact pow_le_pow_left₀ (by positivity) h' 2)
    have h2 := sum_dev_sq_le c hdiag hsym P hrow hg4 q.1 q.2
    have h3 : ∑ χ : Fin g → Fin K, ((K : ℤ) * ((K : ℤ) ^ 2 * grpY c χ q.1 q.2 - totU c)) ^ 2 =
        (K : ℤ) ^ 2 * ∑ χ : Fin g → Fin K, ((K : ℤ) ^ 2 * grpY c χ q.1 q.2 - totU c) ^ 2 := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun χ _ => by ring
    have hKp : (K : ℤ) ^ 2 * (K : ℤ) ^ (g + 2) = (K : ℤ) ^ (g + 4) := by rw [← pow_add]; ring_nf
    have hK4 : (0 : ℤ) ≤ (K : ℤ) ^ (g + 4) := by positivity
    have h4 : ((B2 q).card : ℤ) * ((g : ℤ) * P + 1) ^ 2 ≤ (K : ℤ) ^ (g + 4) * (4 * P * (g * P)) := by
      rw [h3] at h1
      calc _ ≤ _ := h1
        _ ≤ (K : ℤ) ^ 2 * ((K : ℤ) ^ (g + 2) * (4 * P * totU c)) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = (K : ℤ) ^ (g + 4) * (4 * P * totU c) := by rw [← mul_assoc, hKp]
        _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hU (by positivity)) hK4
    have hc0 : (0 : ℤ) ≤ (B2 q).card := by positivity
    have h5 : ((B2 q).card : ℤ) * g * ((g : ℤ) * P + 1) ^ 2 ≤ 4 * (K : ℤ) ^ (g + 4) * ((g : ℤ) * P + 1) ^ 2 := by
      have hgP : ((g : ℤ) * P) ^ 2 ≤ ((g : ℤ) * P + 1) ^ 2 := by nlinarith
      calc ((B2 q).card : ℤ) * g * ((g : ℤ) * P + 1) ^ 2 = g * (((B2 q).card : ℤ) * ((g : ℤ) * P + 1) ^ 2) := by
            ring
        _ ≤ g * ((K : ℤ) ^ (g + 4) * (4 * P * (g * P))) := mul_le_mul_of_nonneg_left h4 hgpos.le
        _ = 4 * (K : ℤ) ^ (g + 4) * ((g : ℤ) * P) ^ 2 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hgP (by positivity)
    exact le_of_mul_le_mul_right h5 (by positivity)
  -- every grouping is bad, if none is good
  by_contra hno
  push Not at hno
  have hcover : (univ : Finset (Fin g → Fin K)) ⊆ (univ.biUnion B1) ∪ (univ.biUnion B2) := by
    intro χ _
    have hχ := hno χ
    unfold Good at hχ
    simp only [not_and_or, not_forall, not_le, exists_prop] at hχ
    rcases hχ with ⟨γ, hγ⟩ | ⟨γ, γ', _, hγ⟩
    · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨γ, mem_univ _, by simp [hB1def, hγ]⟩)
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨(γ, γ'), mem_univ _, by simp [hB2def, hγ]⟩)
  have hcard : (K : ℤ) ^ g ≤ ∑ γ, ((B1 γ).card : ℤ) + ∑ q, ((B2 q).card : ℤ) := by
    have := Finset.card_le_card hcover
    have h2 := (Finset.card_union_le _ _).trans (add_le_add (Finset.card_biUnion_le (s := univ) (t := B1))
      (Finset.card_biUnion_le (s := univ) (t := B2)))
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin] at this
    have := this.trans h2
    exact_mod_cast this
  have hsum : (g : ℤ) * (K : ℤ) ^ g ≤ (K : ℤ) * (K : ℤ) ^ (g + 1) + (K : ℤ) ^ 2 * (4 * (K : ℤ) ^ (g + 4)) := by
    calc (g : ℤ) * (K : ℤ) ^ g ≤ (g : ℤ) * (∑ γ, ((B1 γ).card : ℤ) + ∑ q, ((B2 q).card : ℤ)) :=
          mul_le_mul_of_nonneg_left hcard hgpos.le
      _ = ∑ γ, ((B1 γ).card : ℤ) * g + ∑ q, ((B2 q).card : ℤ) * g := by
          rw [mul_add, Finset.mul_sum, Finset.mul_sum]
          congr 1 <;> exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
      _ ≤ ∑ _γ : Fin K, (K : ℤ) ^ (g + 1) + ∑ _q : Fin K × Fin K, 4 * (K : ℤ) ^ (g + 4) :=
          add_le_add (Finset.sum_le_sum fun γ _ => hB1 γ) (Finset.sum_le_sum fun q _ => hB2 q)
      _ = _ := by
          rw [Finset.sum_const, Finset.sum_const, card_univ, card_univ, Fintype.card_prod, Fintype.card_fin,
            nsmul_eq_mul, nsmul_eq_mul]
          push_cast; ring
  have hA : (0 : ℤ) < (K : ℤ) ^ g := by positivity
  have e1 : (K : ℤ) * (K : ℤ) ^ (g + 1) = (K : ℤ) ^ 2 * (K : ℤ) ^ g := by ring
  have e2 : (K : ℤ) ^ 2 * (4 * (K : ℤ) ^ (g + 4)) = 4 * (K : ℤ) ^ 6 * (K : ℤ) ^ g := by ring
  rw [e1, e2] at hsum
  have hgK : (g : ℤ) = 3 * (K : ℤ) ^ 8 := by exact_mod_cast hg
  rw [hgK] at hsum
  have hK2 : (2 : ℤ) ≤ K := by exact_mod_cast hK
  have hK6 : (K : ℤ) ^ 2 ≤ (K : ℤ) ^ 6 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have h4 : (4 : ℤ) ≤ (K : ℤ) ^ 2 := by nlinarith
  have hK8 : 4 * (K : ℤ) ^ 6 ≤ (K : ℤ) ^ 8 := by
    calc 4 * (K : ℤ) ^ 6 ≤ (K : ℤ) ^ 2 * (K : ℤ) ^ 6 := mul_le_mul_of_nonneg_right h4 (by positivity)
      _ = (K : ℤ) ^ 8 := by ring
  have hsum' : 3 * (K : ℤ) ^ 8 * (K : ℤ) ^ g ≤ ((K : ℤ) ^ 2 + 4 * (K : ℤ) ^ 6) * (K : ℤ) ^ g := by
    linarith
  have := le_of_mul_le_mul_right hsum' hA
  have h6 : (0 : ℤ) < (K : ℤ) ^ 6 := by positivity
  linarith

end Factoring.Aux
