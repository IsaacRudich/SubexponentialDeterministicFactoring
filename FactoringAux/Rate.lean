/-
`e* = 0`: the exponent recurrence of the levels tends to `0` (the end of the paper's Proposition 3).

Stated generically, because the exact recurrence is fixed by the program's cost: if `e ≥ 0`, `ρ < 1`, and
`e_{ℓ+1} ≤ (ρ + a_ℓ) e_ℓ + b_ℓ` with `a_ℓ, b_ℓ → 0`, then `e_ℓ → 0` (`rec_tendsto_zero`); in particular every `η > 0`
is reached (`rec_small`).  The paper's `e' = (ρ + 2/K) e + 2/K` and the written-out variant
`e' = max(3/K, (11/12 + 2/K) e)` are both of this form once `K_ℓ → ∞` (`inv_nat_tendsto`).

Not an audit surface.
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

namespace Factoring.Aux

open Filter Topology

/-- The recurrence tends to `0`. -/
theorem rec_tendsto_zero (e a b : ℕ → ℝ) (ρ : ℝ) (hρ : ρ < 1) (he : ∀ ℓ, 0 ≤ e ℓ)
    (ha : Tendsto a atTop (𝓝 0)) (hb : Tendsto b atTop (𝓝 0))
    (hrec : ∀ ℓ, e (ℓ + 1) ≤ (ρ + a ℓ) * e ℓ + b ℓ) : Tendsto e atTop (𝓝 0) := by
  set σ := (1 + ρ) / 2 with hσ
  have hσ1 : σ < 1 := by rw [hσ]; linarith
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- from some `N` on, `ρ + a ≤ max σ 0` and `b ≤ (ε/2)(1 − σ')`
  set σ' := max σ 0 with hσ'
  have hσ'1 : σ' < 1 := max_lt hσ1 one_pos
  have hσ'0 : 0 ≤ σ' := le_max_right _ _
  have hδ : 0 < (1 - ρ) / 2 := by linarith
  obtain ⟨N1, hN1⟩ := (Metric.tendsto_atTop.mp ha) _ hδ
  have hη : 0 < ε / 2 * (1 - σ') := by have : 0 < 1 - σ' := by linarith
                                       positivity
  obtain ⟨N2, hN2⟩ := (Metric.tendsto_atTop.mp hb) _ hη
  set N := max N1 N2
  have hstep : ∀ ℓ, N ≤ ℓ → e (ℓ + 1) - ε / 2 ≤ σ' * (e ℓ - ε / 2) := by
    intro ℓ hℓ
    have h1 : a ℓ < (1 - ρ) / 2 := by
      have := hN1 ℓ (le_trans (le_max_left _ _) hℓ)
      rw [Real.dist_eq, sub_zero] at this
      exact lt_of_abs_lt this
    have h2 : b ℓ < ε / 2 * (1 - σ') := by
      have := hN2 ℓ (le_trans (le_max_right _ _) hℓ)
      rw [Real.dist_eq, sub_zero] at this
      exact lt_of_abs_lt this
    have h3 : (ρ + a ℓ) * e ℓ ≤ σ' * e ℓ :=
      mul_le_mul_of_nonneg_right (le_trans (by rw [hσ]; linarith) (le_max_left _ _)) (he ℓ)
    have := hrec ℓ
    nlinarith
  have hiter : ∀ k, e (N + k) - ε / 2 ≤ σ' ^ k * (e N - ε / 2) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc e (N + (k + 1)) - ε / 2 ≤ σ' * (e (N + k) - ε / 2) := hstep (N + k) (Nat.le_add_right _ _)
        _ ≤ σ' * (σ' ^ k * (e N - ε / 2)) := mul_le_mul_of_nonneg_left ih hσ'0
        _ = σ' ^ (k + 1) * (e N - ε / 2) := by ring
  -- `σ'^k (e N) → 0`
  have hpow : Tendsto (fun k => σ' ^ k * e N) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hσ'0 hσ'1).mul_const (e N)
  obtain ⟨M, hM⟩ := (Metric.tendsto_atTop.mp hpow) (ε / 2) (by positivity)
  refine ⟨N + M, fun ℓ hℓ => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, ℓ = N + k := ⟨ℓ - N, by omega⟩
  have hk : M ≤ k := by omega
  have h1 := hiter k
  have h2 := hM k hk
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by have := he N; positivity)] at h2
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (he _)]
  have : σ' ^ k * (e N - ε / 2) ≤ σ' ^ k * e N := by
    have : 0 ≤ σ' ^ k := pow_nonneg hσ'0 k
    nlinarith
  linarith

/-- Every `η > 0` is reached. -/
theorem rec_small (e a b : ℕ → ℝ) (ρ : ℝ) (hρ : ρ < 1) (he : ∀ ℓ, 0 ≤ e ℓ)
    (ha : Tendsto a atTop (𝓝 0)) (hb : Tendsto b atTop (𝓝 0))
    (hrec : ∀ ℓ, e (ℓ + 1) ≤ (ρ + a ℓ) * e ℓ + b ℓ) (η : ℝ) (hη : 0 < η) : ∃ ℓ, e ℓ < η := by
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (rec_tendsto_zero e a b ρ hρ he ha hb hrec) η hη
  refine ⟨N, ?_⟩
  have := hN N le_rfl
  rw [Real.dist_eq, sub_zero] at this
  exact lt_of_abs_lt this

/-- `c / K_ℓ → 0` when `K_ℓ → ∞`. -/
theorem inv_nat_tendsto (K : ℕ → ℕ) (hK : Tendsto K atTop atTop) (c : ℝ) :
    Tendsto (fun ℓ => c / (K ℓ : ℝ)) atTop (𝓝 0) := by
  have : Tendsto (fun ℓ => (K ℓ : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hK
  simpa [div_eq_mul_inv] using this.inv_tendsto_atTop.const_mul c

end Factoring.Aux
