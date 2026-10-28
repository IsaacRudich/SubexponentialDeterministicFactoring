/-
The cost of the counting expression: generic facts on groups.

* **`GroupEx.tab_bdd`**: value bounds of the written-out table of a grouped network (`clique_bdd` over
  `coarsen_bdd`), from value bounds of the inner network, the coarse sizes and the widths.
* `pp_sg_le`, **`coarsen_s_le`**: a coarse size is at most `2^(∑ of the members' bits)`; `coarsen_s_le_unif`.
* `Net.c_le_fits`, `Net.c_le_total`, `Net.coarsen_c_le_total`: widths below a fit or the total.

Not an audit surface.
-/
module

public import FactoringAux.EngineBddGrid
public import FactoringAux.EngineBddSearch
public import FactoringAux.EngineBddClique
public import FactoringAux.Cluster

@[expose] public section

namespace Factoring.Aux

open Finset Ex SB

/-! ### Widths -/

section Widths

variable {R : Type*} [CommRing R] {g : ℕ}

theorem Net.c_le_fits (N : Net R g) {P : ℕ} (h : N.Fits P) (a b : Fin g) (hab : a < b) : N.c a b ≤ P := by
  have h1 : N.cc a b = N.c a b := by simp [Net.cc, hab]
  calc N.c a b = N.cc a b := h1.symm
    _ ≤ ∑ b', N.cc a b' := single_le_sum (f := fun b' => N.cc a b') (fun _ _ => Nat.zero_le _) (mem_univ b)
    _ ≤ P := h a

theorem Net.c_le_total (N : Net R g) (a b : Fin g) (hab : a < b) : N.c a b ≤ N.total := by
  have h1 : N.cc a b = N.c a b := by simp [Net.cc, hab]
  calc N.c a b = N.cc a b := h1.symm
    _ ≤ ∑ b', N.cc a b' := single_le_sum (f := fun b' => N.cc a b') (fun _ _ => Nat.zero_le _) (mem_univ b)
    _ ≤ N.total := single_le_sum (f := fun a' => ∑ b', N.cc a' b') (fun _ _ => Nat.zero_le _) (mem_univ a)

theorem Net.coarsen_c_le_total {K : ℕ} (N : Net R g) (χ : Fin g → Fin K) (γ γ' : Fin K) (h : γ < γ') :
    (N.coarsen χ).c γ γ' ≤ N.total :=
  (Net.c_le_total _ γ γ' h).trans (Net.coarsen_total_le N χ)

end Widths

/-! ### Coarse sizes -/

section Sizes

variable {R : Type*} [CommRing R] {g K : ℕ} {N : Net R g}

theorem pp_sg_le (κ : Coding N) (χ : Fin g → Fin K) (γ : Fin K) (w : Fin g → ℕ)
    (hw : ∀ a : Fin g, χ a = γ → κ.s a ≤ 2 ^ w a) :
    ∀ n, pp (Coding.sg κ χ γ) n ≤ 2 ^ (∑ i ∈ range n, if h : i < g then (if χ ⟨i, h⟩ = γ then w ⟨i, h⟩ else 0)
      else 0)
  | 0 => by simp [pp]
  | n + 1 => by
      rw [pp, sum_range_succ, pow_add]
      refine Nat.mul_le_mul (pp_sg_le κ χ γ w hw n) ?_
      unfold Coding.sg
      split_ifs with h1 h2
      · exact hw _ h2
      · simp
      · simp

/-- **A coarse size is at most `2^(∑ of the members' bits)`.** -/
theorem coarsen_s_le (κ : Coding N) (χ : Fin g → Fin K) (γ : Fin K) (w : Fin g → ℕ)
    (hw : ∀ a : Fin g, χ a = γ → κ.s a ≤ 2 ^ w a) :
    (κ.coarsen χ).s γ ≤ 2 ^ (∑ a : Fin g, if χ a = γ then w a else 0) := by
  show (if h : (γ : ℕ) < K then pp (Coding.sg κ χ ⟨γ, h⟩) g else 1) ≤ _
  rw [dif_pos γ.2, sum_fin_range]
  exact pp_sg_le κ χ γ w hw g

theorem coarsen_s_le_unif (κ : Coding N) (χ : Fin g → Fin K) (γ : Fin K) (w c : ℕ)
    (hw : ∀ a : Fin g, κ.s a ≤ 2 ^ w) (hc : (univ.filter (fun a => χ a = γ)).card ≤ c) :
    (κ.coarsen χ).s γ ≤ 2 ^ (w * c) := by
  refine (coarsen_s_le κ χ γ (fun _ => w) fun a _ => hw a).trans (Nat.pow_le_pow_right (by norm_num) ?_)
  rw [← sum_filter, sum_const, smul_eq_mul, mul_comm]
  exact Nat.mul_le_mul_left _ hc

end Sizes

/-! ### The table of a grouped network -/

namespace GroupEx

variable {V m B : ℕ} {S : GS} {σ₀ : ℕ → ℕ} {A : ℕ → ℕ → ℕ} {N : Net (ZMod m) S.g} {κ : Coding N}

/-- **Value bounds of the written-out table of a grouped network.** -/
theorem tab_bdd (hK : 0 < S.K) (hg : 0 < S.g) (hm : 1 < m) (h : NRep m S.vm B σ₀ A (NVars.std S.u) S.E N κ)
    (hE : NBdd V B σ₀ A (NVars.std S.u) S.E S.g)
    (hvm : S.vm < B) (hχ : S.vχ < B) (hL : S.vL < B) (hu : B ≤ S.u) {x L : ℕ} (hx : σ₀ S.vχ = x)
    (hLσ : σ₀ S.vL = L) (hxV : x ≤ V) (hKg : S.K ^ S.g ≤ V) (hgg : S.g * S.g ≤ V) (hmm : m * m ≤ V)
    (hsz : ∀ γ : Fin S.K, (κ.coarsen (chiOf S.K S.g x hK)).s γ ≤ V)
    (hcw : ∀ γ γ' : Fin S.K, γ < γ' → 2 ^ (N.coarsen (chiOf S.K S.g x hK)).c γ γ' ≤ V)
    (hcin : ∀ a b : Fin S.g, a < b → chiOf S.K S.g x hK a = chiOf S.K S.g x hK b → 2 ^ N.c a b ≤ V)
    (hLK : 2 ^ (L * S.K) ≤ V) :
    TBdd V B σ₀ A (S.u + 56) (S.u + 57) (tab S) S.K := by
  have hKV : S.K ≤ V := le_trans (Nat.le_self_pow (by omega) _) hKg
  have hgV : S.g ≤ V := le_trans (Nat.le_mul_of_pos_left _ hg) hgg
  have hLV : L ≤ V := by
    refine le_trans ?_ hLK
    calc L ≤ L * S.K := Nat.le_mul_of_pos_right _ hK
      _ ≤ 2 ^ (L * S.K) := Nat.lt_two_pow_self.le
  have HC := coarsenHyp hK hg hm h hχ hu hx
  have Hb : CoarsenBddHyp V m B σ₀ A (Pc S) N κ (chiOf S.K S.g x hK) :=
    { E := hE
      gE := fun _ _ => B_lit hgV
      χE := fun σ hσ hu' => B_chiE hKg hgV hK hg (by rw [hσ _ hχ, hx]; exact hxV) hu'
      mm := hmm
      KV := hKV
      gg := hgg
      sz := hsz
      cw := hcw
      cin := hcin }
  have hcE := coarsen_bdd HC Hb hvm
  refine clique_bdd (P := Pk S) (B := B) (L := L)
    { rep := coarsen_rep HC hvm
      kE := fun _ _ => rfl
      LE := fun σ hσ => by show σ S.vL = L; rw [hσ _ hL, hLσ]
      hu := by show B ≤ S.u + 46; omega
      hw := by show S.u + 46 + 4 ≤ S.u + 56; omega
      hm := hm
      hvm := hvm } hcE (fun _ _ => B_lit hKV) (fun σ hσ => B_var (by show σ S.vL ≤ V; rw [hσ _ hL, hLσ]; exact hLV))
    hmm hLK

end GroupEx

end Factoring.Aux
