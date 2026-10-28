/-
The assembly: the value bound `V = 2^(16 Z + 127)` (`Z` from `uni_exp`) meets every requirement of
`uniC_cost` (`UniReq`), and `subexp_of_poly` gives **`Aux.subexponentialRate`**.

Not an audit surface.
-/
module

public import FactoringAux.UniCost
public import FactoringAux.UniExp
public import FactoringAux.UniGlue

@[expose] public section

namespace Factoring.Aux

theorem MainReq.mono {V W K0 ℓ n : ℕ} (h : MainReq V K0 ℓ n) (hVW : V ≤ W) : MainReq W K0 ℓ n where
  top m h1 h2 := UCost.TopReq.mono (h.top m h1 h2) hVW
  hM := le_trans h.hM hVW

theorem Kb_succ_pow (K0 ℓ : ℕ) : Kb K0 (ℓ + 1) ^ 40 = 9 ^ 40 * (Kb K0 ℓ ^ 40) ^ 16 := by
  rw [Kb_succ]; ring

/-- **The requirements are met** by `V = 2^(16 Z + 127)`. -/
theorem uniReq_exp : ∃ Z : ℕ → ℕ, (∀ n, UniReq (2 ^ Z n) n) ∧ ∀ k : ℕ, 1 ≤ k → ∃ C : ℕ, ∀ n, Z n ≤ n / k + C := by
  obtain ⟨Z, hT, hD, hNP, hM, hS, hK, hL, hZ⟩ := uni_exp
  refine ⟨fun n => 16 * Z n + 127, fun n => ?_, fun k hk => ?_⟩
  · have hmono : 2 ^ Z n ≤ 2 ^ (16 * Z n + 127) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hmain : MainReq (2 ^ Z n) K0u (ellOf n) n :=
      mainReq_of (by norm_num) (hT n) (hD n) le_rfl
    refine ⟨hmain.mono hmono, le_trans (hNP n) hmono, le_trans (hL n) hmono, le_trans (hS n) hmono, ?_⟩
    rw [Kb_succ_pow]
    calc 9 ^ 40 * (Kb K0u (ellOf n) ^ 40) ^ 16 ≤ 2 ^ 127 * (2 ^ Z n) ^ 16 :=
          Nat.mul_le_mul (by norm_num) (Nat.pow_le_pow_left (hK n) 16)
      _ = 2 ^ (16 * Z n + 127) := by rw [← pow_mul, ← pow_add]; ring_nf
  · obtain ⟨C, hC⟩ := hZ (16 * k) (by omega)
    refine ⟨16 * C + 127, fun n => ?_⟩
    show 16 * Z n + 127 ≤ n / k + (16 * C + 127)
    have := mul_div_mul_le 16 k n
    have := hC n
    omega

/-- **The main result**: one machine factors within `C_k · 2^(n/k)` for every `k`. -/
theorem subexponentialRate :
    ∃ M : FactoringMachine, ∀ k : ℕ, 1 ≤ k → ∃ C : ℕ, FactorsWithin M (fun n => C * 2 ^ (n / k)) :=
  subexp_of_poly UniReq uniC_cost uniReq_exp

end Factoring.Aux
