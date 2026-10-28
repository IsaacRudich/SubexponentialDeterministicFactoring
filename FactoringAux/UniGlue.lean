/-
The uniform engine: from a cost bound polynomial in a value bound `V = 2^(Z n)` with `Z n = o(n)` to the
audited statement (**`subexp_of_poly`**), through `subexp_of_cspec`.

Not an audit surface.
-/
module

public import FactoringAux.UniValSpec
public import FactoringAux.UniFinal

@[expose] public section

namespace Factoring.Aux

open Factoring.Aux.Copied Factoring.Aux.Copied.PLib

/-- `2^(Z+1)` to the `E` absorbs into `2^(n/k)` when `Z ≤ n / ((E+1) k) + C`. -/
theorem pow_absorb (E k C n Z : ℕ) (hk : 1 ≤ k) (hZ : Z ≤ n / ((E + 1) * k) + C) :
    (2 ^ Z + 1) ^ E ≤ 2 ^ (E * (C + 1)) * 2 ^ (n / k) := by
  have h1 : 2 ^ Z + 1 ≤ 2 ^ (Z + 1) := by rw [pow_succ]; have := Nat.one_le_two_pow (n := Z); omega
  have h2 : E * (n / ((E + 1) * k)) ≤ n / k := by
    have := mul_div_mul_le (E + 1) k n
    calc E * (n / ((E + 1) * k)) ≤ (E + 1) * (n / ((E + 1) * k)) := Nat.mul_le_mul_right _ (by omega)
      _ ≤ n / k := this
  calc (2 ^ Z + 1) ^ E ≤ (2 ^ (Z + 1)) ^ E := Nat.pow_le_pow_left h1 E
    _ = 2 ^ (E * (Z + 1)) := by rw [← pow_mul, mul_comm]
    _ ≤ 2 ^ (E * (C + 1) + n / k) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
    _ = 2 ^ (E * (C + 1)) * 2 ^ (n / k) := by rw [pow_add]

/-- **From a polynomial cost bound and an `o(n)` exponent to the main result.** -/
theorem subexp_of_poly (R : ℕ → ℕ → Prop)
    (hcost : ∃ c E : ℕ, ∀ (V : ℕ) (st : St), st.sc 2 < st.sc 0 → (∀ j, st.ar 1 j ≤ 1) → R V (st.sc 0) →
      (Cmd.run (uniC UP) st).2 ≤ c * (V + 1) ^ E)
    (hZ : ∃ Z : ℕ → ℕ, (∀ n, R (2 ^ Z n) n) ∧ ∀ k : ℕ, 1 ≤ k → ∃ C : ℕ, ∀ n, Z n ≤ n / k + C) :
    ∃ M : FactoringMachine, ∀ k : ℕ, 1 ≤ k → ∃ C : ℕ, FactorsWithin M (fun n => C * 2 ^ (n / k)) := by
  obtain ⟨c, E, hc⟩ := hcost
  obtain ⟨Z, hR, hZ⟩ := hZ
  refine subexp_of_cspec (uniC UP) (fun n => c * (2 ^ Z n + 1) ^ E) ?_ ?_
  · refine ⟨fun st => ?_, uniC_le_one, fun st hkn hN hD _ => uniC_val st hkn hN hD,
      fun st hkn hA => hc _ st hkn hA (hR _)⟩
    obtain ⟨h1, h2⟩ := uniC_keeps st
    exact ⟨h1 0 (by norm_num) (by simp [Uni.Wu]), h1 2 (by norm_num) (by simp [Uni.Wu]),
      h1 4 (by norm_num) (by simp [Uni.Wu]), fun a ha => h2 a (by omega)⟩
  · intro k hk
    obtain ⟨C, hC⟩ := hZ ((E + 1) * k) (by nlinarith)
    exact ⟨c * 2 ^ (E * (C + 1)), fun n => by
      rw [mul_assoc]; exact Nat.mul_le_mul_left _ (pow_absorb E k C n (Z n) hk (hC n))⟩

end Factoring.Aux
