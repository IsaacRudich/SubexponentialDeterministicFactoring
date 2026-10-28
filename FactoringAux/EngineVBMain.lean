/-
Free variables, variable bounds and array reads of the counting expression `Ex.mainE`.

* `mlE`, `dmE` (by induction on the depth), `multE`, `c1E`.
* **`mainE_fv`**: the free variables of `mainE K0 ℓ` are among `0`, `2`; **`mainE_vb`**: every variable is below
  `100 ℓ + 165`; **`mainE_rdn`**: arrays are read only through `bitRd`.

Not an audit surface.
-/
module

public import FactoringAux.EngineVBRd
public import FactoringAux.EngineMain

@[expose] public section

namespace Factoring.Aux

open Ex MulEx

set_option linter.unusedSimpArgs false

theorem mlE_fv (K0 : ℕ) : ∀ (d vL b : ℕ) (s : ℕ → Prop), s vL → FV s (mlE K0 d vL b)
  | 0, _, _, _, _ => trivial
  | d + 1, vL, b, s, h => by
      have ih := mlE_fv K0 d (b + 1) (b + 2) (fun y => s y ∨ y = b + 1) (Or.inr rfl)
      simp only [mlE, LevelEx.LnE, lpOf, tBE, FV, ih, h, true_or, and_true, true_and, and_self]

theorem mlE_vb (K0 : ℕ) : ∀ (d vL b t : ℕ), vL < t → b + 2 * d ≤ t → VB t (mlE K0 d vL b)
  | 0, _, _, _, _, _ => trivial
  | d + 1, vL, b, t, h, hb => by
      have ih := mlE_vb K0 d (b + 1) (b + 2) t (by omega) (by omega)
      simp only [mlE, LevelEx.LnE, lpOf, tBE, VB, ih, and_true, true_and, and_self]
      omega

theorem mlE_rdn (K0 : ℕ) : ∀ (d vL b : ℕ), RdN false (mlE K0 d vL b)
  | 0, _, _ => trivial
  | d + 1, vL, b => by
      have ih := mlE_rdn K0 d (b + 1) (b + 2)
      simp only [mlE, LevelEx.LnE, lpOf, tBE, RdN, ih, and_true, true_and, and_self]

theorem dmE_fv (K0 : ℕ) : ∀ (d vL b vm : ℕ) (s : ℕ → Prop), s vL → s vm → FV s (dmE K0 d vL b vm)
  | 0, _, _, _, _, _, _ => trivial
  | d + 1, vL, b, vm, s, h, hm => by
      have ih := dmE_fv K0 d (b + 1) (b + 2) vm (fun y => s y ∨ y = b + 1) (Or.inr rfl) (Or.inl hm)
      simp only [dmE, multE, LevelEx.LnE, lpOf, tBE, zmul, zprod, FV, ih, h, hm, true_or, and_true, true_and,
        and_self]

theorem dmE_vb (K0 : ℕ) : ∀ (d vL b vm t : ℕ), vL < t → vm < t → b + 2 * d ≤ t → VB t (dmE K0 d vL b vm)
  | 0, _, _, _, _, _, _, _ => trivial
  | d + 1, vL, b, vm, t, h, hm, hb => by
      have ih := dmE_vb K0 d (b + 1) (b + 2) vm t (by omega) hm (by omega)
      simp only [dmE, multE, LevelEx.LnE, lpOf, tBE, zmul, zprod, VB, ih, and_true, true_and, and_self]
      omega

theorem dmE_rdn (K0 : ℕ) : ∀ (d vL b vm : ℕ), RdN false (dmE K0 d vL b vm)
  | 0, _, _, _ => trivial
  | d + 1, vL, b, vm => by
      have ih := dmE_rdn K0 d (b + 1) (b + 2) vm
      simp only [dmE, multE, LevelEx.LnE, lpOf, tBE, zmul, zprod, RdN, ih, and_true, true_and, and_self]

/-- **The free variables of the counting expression are among `0`, `2`.** -/
theorem mainE_fv (K0 ℓ : ℕ) : FV (fun y => y = 0 ∨ y = 2) (mainE K0 ℓ) := by
  have hT : ∀ s : ℕ → Prop, s 0 → s 2 → s 10 → FV s (topE K0 ℓ) := fun s h0 h2 h10 =>
    FV_mono (fun y hy => by rcases hy with rfl | rfl | rfl <;> assumption) _ (topE_fv K0 ℓ)
  have hM := fun s => mlE_fv K0 ℓ 12 30 s
  have hD := fun s => dmE_fv K0 ℓ 12 30 10 s
  simp only [mainE, sE, L0E, clPE, AE, fwE, LLE, c1E, xBit, bitRd, pow2, nsum, zmul, ifEq, FV, hT, hM, hD,
    true_or, or_true, and_true, true_and, and_self]

/-- **Every variable of the counting expression is below `100 ℓ + 165`.** -/
theorem mainE_vb (K0 ℓ : ℕ) : VB (100 * ℓ + 165) (mainE K0 ℓ) := by
  have hT := topE_vb K0 ℓ
  have hM := mlE_vb K0 ℓ 12 30 (100 * ℓ + 165) (by omega) (by omega)
  have hD := dmE_vb K0 ℓ 12 30 10 (100 * ℓ + 165) (by omega) (by omega) (by omega)
  simp only [mainE, sE, L0E, clPE, AE, fwE, LLE, c1E, xBit, bitRd, pow2, nsum, zmul, ifEq, VB, hT, hM, hD,
    and_true, true_and, and_self]
  omega

/-- **The counting expression reads arrays only through `bitRd`.** -/
theorem mainE_rdn (K0 ℓ : ℕ) : RdN false (mainE K0 ℓ) := by
  have hT := RdN_any (topE_rdn K0 ℓ)
  have hM := RdN_any (mlE_rdn K0 ℓ 12 30)
  have hD := RdN_any (dmE_rdn K0 ℓ 12 30 10)
  simp only [mainE, sE, L0E, clPE, AE, fwE, LLE, c1E, xBit, bitRd, pow2, nsum, zmul, ifEq, RdN, isZ, hT, hM, hD,
    and_true, true_and, and_self]

end Factoring.Aux
