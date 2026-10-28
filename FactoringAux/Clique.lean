/-
Cliques with written-out tables (the paper's Definition 3) and the passage from a network to a clique (the second
half of the value part of Lemma 1).

* `Clique R K L`: one table `T γ : (Fin K → Bits L) → R` per node.  Node `γ` holds one `L`-bit string `Θ γ'` per other
  node `γ'`; its own coordinate `Θ γ` is ignored (the weight vanishes unless it is `0`).  The value is that of the
  network `toNet`: weights `T`, and on each pair the equality test `[Θ_γ(γ') = Θ_γ'(γ)]`, through `L` bits.
* `Net.toClique N L`: for a network on `Fin K` whose pair factorizations use at most `L` bits, the clique with
  tables (26): `T_γ(Θ) = ∑_{z_γ} W_γ(z_γ) ∏_{γ' > γ} f^L_{γ,γ'}(z_γ, Θ γ') ∏_{γ' < γ} f^R_{γ',γ}(z_γ, Θ γ')`, each
  factorization padded to `L` bits (the appended bits must be `0`).  `value_toClique`: same value.
* `value_group`: Lemma 1's value statement, `((N.coarsen χ).toClique L).value = N.value` when every pair of groups
  shares at most `L` bits.

The combinatorial core is `sum_symm_pairs`: summing over all `K × K` arrays with a zero diagonal and equal mirror
entries is summing over one string per pair.

Not an audit surface.
-/
module

public import FactoringAux.Net

@[expose] public section

namespace Factoring.Aux

open Finset

variable {R : Type*} [CommRing R]

/-! ### Symmetric arrays -/

section Symm

variable {K : ℕ} {α : Type*} [Fintype α] [DecidableEq α]

/-- The symmetric array with zero diagonal (`a0`) whose entries above the diagonal are `u`. -/
def symArr (a0 : α) (u : {q // q ∈ pairs K} → α) (γ γ' : Fin K) : α :=
  if h : γ < γ' then u ⟨(γ, γ'), mem_pairs.mpr h⟩
  else if h' : γ' < γ then u ⟨(γ', γ), mem_pairs.mpr h'⟩ else a0

omit [Fintype α] [DecidableEq α] in
theorem symArr_injective (a0 : α) : Function.Injective (symArr (K := K) a0) := by
  intro u v h
  funext q
  have := congrFun (congrFun h q.1.1) q.1.2
  simp only [symArr, dif_pos (mem_pairs.mp q.2)] at this
  exact this

/-- Summing over symmetric arrays with diagonal `a0` is summing over one entry per pair. -/
theorem sum_symm_pairs (a0 : α) (H : Fin K × Fin K → α → R) :
    ∑ Θ : Fin K → Fin K → α,
        (∏ γ, if Θ γ γ = a0 then (1 : R) else 0) *
          ∏ q ∈ pairs K, (if Θ q.1 q.2 = Θ q.2 q.1 then H q (Θ q.1 q.2) else 0) =
      ∏ q ∈ pairs K, ∑ θ, H q θ := by
  symm
  rw [← Finset.prod_coe_sort, Fintype.prod_sum]
  refine Fintype.sum_of_injective (symArr a0) (symArr_injective a0) _ _ ?_ ?_
  · intro Θ hΘ
    by_contra hne
    apply hΘ
    have hd : ∀ γ, Θ γ γ = a0 := by
      intro γ; by_contra h
      exact hne (by rw [Finset.prod_eq_zero (mem_univ γ) (if_neg h), zero_mul])
    have hs : ∀ q ∈ pairs K, Θ q.1 q.2 = Θ q.2 q.1 := by
      intro q hq; by_contra h
      exact hne (by rw [Finset.prod_eq_zero hq (if_neg h), mul_zero])
    refine ⟨fun q => Θ q.1.1 q.1.2, ?_⟩
    funext γ γ'
    unfold symArr
    split_ifs with h1 h2
    · rfl
    · exact hs (γ', γ) (mem_pairs.mpr h2)
    · have : γ = γ' := le_antisymm (not_lt.mp h2) (not_lt.mp h1)
      subst this; exact (hd γ).symm
  · intro u
    have hd : ∀ γ, symArr a0 u γ γ = a0 := fun γ => by simp [symArr]
    have hs : ∀ q (hq : q ∈ pairs K), symArr a0 u q.1 q.2 = u ⟨q, hq⟩ := fun q hq => by
      simp [symArr, dif_pos (mem_pairs.mp hq)]
    have hs' : ∀ q (hq : q ∈ pairs K), symArr a0 u q.2 q.1 = u ⟨q, hq⟩ := fun q hq => by
      have h := mem_pairs.mp hq
      simp [symArr, not_lt.mpr h.le, dif_pos h]
    have h1 : (∏ γ, if symArr a0 u γ γ = a0 then (1 : R) else 0) = 1 :=
      Finset.prod_eq_one (fun γ _ => by rw [if_pos (hd γ)])
    rw [h1, one_mul, ← Finset.prod_coe_sort (pairs K)]
    refine Finset.prod_congr rfl fun q _ => ?_
    rw [hs q.1 q.2, hs' q.1 q.2, if_pos rfl]

end Symm

/-! ### Cliques -/

/-- A `(K, L)`-clique with written-out tables (Definition 3). -/
abbrev Clique (R : Type*) (K L : ℕ) := Fin K → (Fin K → Bits L) → R

namespace Clique

variable {K L : ℕ}

/-- The clique as a network: node `γ` holds `Θ : Fin K → Bits L`, the pair `γ, γ'` tests `Θ_γ(γ') = Θ_γ'(γ)`. -/
def toNet (T : Clique R K L) : Net R K where
  S _ := Fin K → Bits L
  fS _ := inferInstance
  dS _ := inferInstance
  W γ Θ := if Θ γ = zeroBits L then T γ Θ else 0
  c _ _ := L
  F γ γ' := ⟨fun Θ θ => if Θ γ' = θ then 1 else 0, fun Θ θ => if Θ γ = θ then 1 else 0⟩

theorem toNet_Ψ (T : Clique R K L) (γ γ' : Fin K) (Θ : T.toNet.S γ) (Θ' : T.toNet.S γ') :
    T.toNet.Ψ γ γ' Θ Θ' = if (Θ : Fin K → Bits L) γ' = (Θ' : Fin K → Bits L) γ then 1 else 0 := by
  show (∑ θ : Bits L, (if (Θ : Fin K → Bits L) γ' = θ then (1 : R) else 0) *
    (if (Θ' : Fin K → Bits L) γ = θ then 1 else 0)) = _
  simp only [ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp [eq_comm]

/-- The value of a clique: the sum over all arrays `Θ` (row `γ` held by node `γ`) with zero diagonal, of the
product of the tables, when every pair of mirror entries agrees. -/
def value (T : Clique R K L) : R :=
  ∑ Θ : Fin K → Fin K → Bits L, (∏ γ, if Θ γ γ = zeroBits L then T γ (Θ γ) else 0) *
    ∏ q ∈ pairs K, (if Θ q.1 q.2 = Θ q.2 q.1 then (1 : R) else 0)

/-- The clique's value is the value of its network. -/
theorem value_eq_toNet (T : Clique R K L) : T.value = T.toNet.value := by
  unfold value Net.value
  refine Finset.sum_congr rfl fun Θ _ => ?_
  congr 1
  exact Finset.prod_congr rfl fun q _ => (toNet_Ψ T q.1 q.2 (Θ q.1) (Θ q.2)).symm

end Clique

/-! ### From a network to a clique -/

namespace Net

variable {K : ℕ}

/-- The factorization of pair `(γ, γ')`, padded to `L` bits (zero if it does not fit). -/
def padF (N : Net R K) (L : ℕ) (γ γ' : Fin K) : Fac R (N.S γ) (N.S γ') L :=
  if h : N.c γ γ' ≤ L then (N.F γ γ').pad L h else Fac.zero L

/-- The clique tables (26). -/
def toClique (N : Net R K) (L : ℕ) : Clique R K L := fun γ Θ =>
  ∑ zγ : N.S γ, N.W γ zγ * (∏ γ' ∈ univ.filter (γ < ·), (N.padF L γ γ').l zγ (Θ γ')) *
    ∏ γ' ∈ univ.filter (· < γ), (N.padF L γ' γ).r zγ (Θ γ')

/-- Products over the upper and the lower triangle are products over pairs. -/
theorem prod_upper {M : Type*} [CommMonoid M] (f : Fin K → Fin K → M) :
    ∏ γ, ∏ γ' ∈ univ.filter (γ < ·), f γ γ' = ∏ q ∈ pairs K, f q.1 q.2 := by
  rw [pairs, Finset.prod_filter, ← Finset.univ_product_univ, Finset.prod_product]
  exact Finset.prod_congr rfl fun γ _ => Finset.prod_filter _ _

theorem prod_lower {M : Type*} [CommMonoid M] (f : Fin K → Fin K → M) :
    ∏ γ, ∏ γ' ∈ univ.filter (· < γ), f γ' γ = ∏ q ∈ pairs K, f q.1 q.2 := by
  rw [pairs, Finset.prod_filter, ← Finset.univ_product_univ, Finset.prod_product_right]
  exact Finset.prod_congr rfl fun γ _ => Finset.prod_filter _ _

/-- The clique of (26) has the network's value, when every pair factorization fits in `L` bits. -/
theorem value_toClique (N : Net R K) (L : ℕ) (hc : ∀ γ γ', γ < γ' → N.c γ γ' ≤ L) :
    (N.toClique L).value = N.value := by
  unfold Clique.value value
  -- expand the tables and exchange the sums
  have hexp : ∀ Θ : Fin K → Fin K → Bits L,
      (∏ γ, if Θ γ γ = zeroBits L then N.toClique L γ (Θ γ) else 0) =
      ∑ z : (∀ γ, N.S γ), ∏ γ, ((if Θ γ γ = zeroBits L then (1 : R) else 0) * (N.W γ (z γ) *
        (∏ γ' ∈ univ.filter (γ < ·), (N.padF L γ γ').l (z γ) (Θ γ γ')) *
          ∏ γ' ∈ univ.filter (· < γ), (N.padF L γ' γ).r (z γ) (Θ γ γ'))) := by
    intro Θ
    rw [← Fintype.prod_sum (fun γ (zγ : N.S γ) => (if Θ γ γ = zeroBits L then (1 : R) else 0) *
      (N.W γ zγ * (∏ γ' ∈ univ.filter (γ < ·), (N.padF L γ γ').l zγ (Θ γ γ')) *
        ∏ γ' ∈ univ.filter (· < γ), (N.padF L γ' γ).r zγ (Θ γ γ')))]
    refine Finset.prod_congr rfl fun γ _ => ?_
    simp only [toClique, ← Finset.mul_sum]
    split_ifs <;> simp
  simp only [hexp, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  -- for fixed node settings, sum over the arrays
  have hrw : ∀ Θ : Fin K → Fin K → Bits L,
      (∏ γ, ((if Θ γ γ = zeroBits L then (1 : R) else 0) * (N.W γ (z γ) *
        (∏ γ' ∈ univ.filter (γ < ·), (N.padF L γ γ').l (z γ) (Θ γ γ')) *
          ∏ γ' ∈ univ.filter (· < γ), (N.padF L γ' γ).r (z γ) (Θ γ γ')))) *
        ∏ q ∈ pairs K, (if Θ q.1 q.2 = Θ q.2 q.1 then (1 : R) else 0) =
      (∏ γ, N.W γ (z γ)) * ((∏ γ, if Θ γ γ = zeroBits L then (1 : R) else 0) *
        ∏ q ∈ pairs K, (if Θ q.1 q.2 = Θ q.2 q.1 then
          (N.padF L q.1 q.2).l (z q.1) (Θ q.1 q.2) * (N.padF L q.1 q.2).r (z q.2) (Θ q.1 q.2) else 0)) := by
    intro Θ
    simp only [Finset.prod_mul_distrib, prod_upper (fun γ γ' => (N.padF L γ γ').l (z γ) (Θ γ γ')),
      prod_lower (fun γ' γ => (N.padF L γ' γ).r (z γ) (Θ γ γ'))]
    have : ∀ q ∈ pairs K, (if Θ q.1 q.2 = Θ q.2 q.1 then
          (N.padF L q.1 q.2).l (z q.1) (Θ q.1 q.2) * (N.padF L q.1 q.2).r (z q.2) (Θ q.1 q.2) else 0) =
        (N.padF L q.1 q.2).l (z q.1) (Θ q.1 q.2) * (N.padF L q.1 q.2).r (z q.2) (Θ q.2 q.1) *
          (if Θ q.1 q.2 = Θ q.2 q.1 then 1 else 0) := by
      intro q _; split_ifs with h <;> simp [h]
    rw [Finset.prod_congr rfl this, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    ring
  simp only [hrw]
  rw [← Finset.mul_sum, sum_symm_pairs (zeroBits L)
    (fun q θ => (N.padF L q.1 q.2).l (z q.1) θ * (N.padF L q.1 q.2).r (z q.2) θ)]
  congr 1
  refine Finset.prod_congr rfl fun q hq => ?_
  have h := hc q.1 q.2 (mem_pairs.mp hq)
  show (N.padF L q.1 q.2).eval (z q.1) (z q.2) = _
  simp only [padF, dif_pos h, Fac.eval_pad, Ψ]

/-- Lemma 1, the value: grouping a network into `K` groups and writing out the `(K, L)`-clique of (26) keeps the
value, provided every pair of groups shares at most `L` bits. -/
theorem value_group {g : ℕ} (N : Net R g) (χ : Fin g → Fin K) (L : ℕ)
    (hY : ∀ γ γ', γ < γ' → (N.coarsen χ).c γ γ' ≤ L) :
    ((N.coarsen χ).toClique L).value = N.value := by
  rw [value_toClique _ L hY, value_coarsen]

end Net

end Factoring.Aux
