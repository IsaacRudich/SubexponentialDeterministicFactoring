/-
The counting expression meets the driver's contract (`BitSpec`), given its variable bound and a cost bound.

* **`bitSpec_mainE`**; **`count_of_mainE`**: for every `k`, parameters `K0, ℓ` with a cost bound `≤ C · 2^(n/k)`
  give the counting lemma that `everyRoot_of_count` needs.

Not an audit surface.
-/
module

public import FactoringAux.EngineMain
public import FactoringAux.Driver

@[expose] public section

namespace Factoring.Aux

open Ex

/-- **The counting expression meets `BitSpec`**, given its variable bound and a cost bound. -/
theorem bitSpec_mainE (K0 ℓ T : ℕ) (hK : 2 ≤ K0) (hvb : VB 10 (Ex.blk T (mainE K0 ℓ))) (B : ℕ → ℕ)
    (hcost : ∀ σ A, σ 2 < σ 0 → (∀ j, A 1 j ≤ 1) → cost σ A (mainE K0 ℓ) ≤ B (σ 0)) :
    BitSpec (Ex.blk T (mainE K0 ℓ)) B where
  vb := hvb
  le_one σ A := mainE_le_one K0 ℓ σ A
  val _ _ hkn hN hD := eval_mainE K0 ℓ hK hkn hN hD
  cost σ A hkn hA := hcost σ A hkn hA

/-- **The counting lemma from parameters.** -/
theorem count_of_mainE
    (H : ∀ k : ℕ, 1 ≤ k → ∃ (K0 ℓ T : ℕ) (B : ℕ → ℕ) (C : ℕ), 2 ≤ K0 ∧ VB 10 (Ex.blk T (mainE K0 ℓ)) ∧
      (∀ σ A, σ 2 < σ 0 → (∀ j, A 1 j ≤ 1) → cost σ A (mainE K0 ℓ) ≤ B (σ 0)) ∧ ∀ n, B n ≤ C * 2 ^ (n / k)) :
    ∀ k : ℕ, 1 ≤ k → ∃ (e : Ex) (B : ℕ → ℕ) (C : ℕ), BitSpec e B ∧ ∀ n, B n ≤ C * 2 ^ (n / k) := by
  intro k hk
  obtain ⟨K0, ℓ, T, B, C, hK, hvb, hc, hB⟩ := H k hk
  exact ⟨_, B, C, bitSpec_mainE K0 ℓ T hK hvb B hc, hB⟩

end Factoring.Aux
