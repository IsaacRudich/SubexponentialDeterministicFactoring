/-
The variable bound of the counting expression: `VB 10 (blk (100ℓ + 165) (mainE K0 ℓ))`.

Not an audit surface.
-/
module

public import FactoringAux.EngineBit
public import FactoringAux.EngineVBMain

@[expose] public section

namespace Factoring.Aux

open Ex

theorem mainE_blk_vb (K0 ℓ : ℕ) : VB 10 (Ex.blk (100 * ℓ + 165) (mainE K0 ℓ)) :=
  VB_blk (FV_mono (fun y hy => by rcases hy with rfl | rfl <;> norm_num) _ (mainE_fv K0 ℓ)) (mainE_vb K0 ℓ)

end Factoring.Aux

namespace Factoring.Aux

open Ex

/-- The canonical environment: `n` in `0`, `k` in `2`, `0` elsewhere. -/
def envNK (n k : ℕ) : ℕ → ℕ := fun y => if y = 0 then n else if y = 2 then k else 0

/-- **The cost reduces to canonical environments and `0/1` arrays.** -/
theorem cost_reduce (K0 ℓ : ℕ) (B : ℕ → ℕ)
    (h : ∀ n k, k < n → ∀ A : ℕ → ℕ → ℕ, (∀ a j, A a j ≤ 1) → cost (envNK n k) A (mainE K0 ℓ) ≤ B n) :
    ∀ σ A, σ 2 < σ 0 → (∀ j, A 1 j ≤ 1) → cost σ A (mainE K0 ℓ) ≤ B (σ 0) := by
  intro σ A hk _
  have h1 := (FV_congr A (mainE K0 ℓ) _ σ (envNK (σ 0) (σ 2))
    (fun y hy => by rcases hy with rfl | rfl <;> simp [envNK]) (mainE_fv K0 ℓ)).2
  rw [h1, (eval_cost_normA (mainE_rdn K0 ℓ) _ A).2]
  exact h (σ 0) (σ 2) hk _ (normA_le A)

end Factoring.Aux
