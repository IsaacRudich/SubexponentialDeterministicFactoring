/-
The widths along the chain (for the cost): the bits `N = K² L` of a clique decay by about `11/12` per level.

* **`N_next`**: `12 K · (K² · Lnext K G λ) ≤ (11K + 24) · G⁴λ + 24 K · G⁴` when `G ≥ K`.

Not an audit surface.
-/
module

public import FactoringAux.EngineGroup

@[expose] public section

namespace Factoring.Aux

theorem N_next (K G lam : ℕ) (hGK : K ≤ G) :
    12 * K * (K ^ 2 * Lnext K G lam) ≤ (11 * K + 24) * (G ^ 4 * lam) + 24 * K * G ^ 4 := by
  unfold Lnext Umax
  set U := (12 * G ^ 3 * lam + 11 * G ^ 4 * lam + 24 * G ^ 4) / 12
  have hU : 12 * U ≤ 12 * G ^ 3 * lam + 11 * G ^ 4 * lam + 24 * G ^ 4 := Nat.mul_div_le _ _
  have hL : K ^ 3 * ((K * U + G * (G ^ 3 * lam)) / K ^ 3) ≤ K * U + G * (G ^ 3 * lam) := Nat.mul_div_le _ _
  have hG3 : K * (G ^ 3 * lam) ≤ G ^ 4 * lam := by
    have : K * G ^ 3 ≤ G ^ 4 := by rw [pow_succ G 3]; nlinarith [Nat.zero_le (G ^ 3)]
    nlinarith [Nat.zero_le lam]
  have hG4 : G * (G ^ 3 * lam) = G ^ 4 * lam := by ring
  nlinarith [Nat.zero_le U, Nat.zero_le lam]

end Factoring.Aux
