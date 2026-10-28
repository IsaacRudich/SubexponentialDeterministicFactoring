/-
The uniform glue of the main result: one counting command `c` (`CSpec c B`) whose cost `B n` is at most
`C_k · 2^(n/k)` for every `k ≥ 1` gives **one** machine that factors within `C'_k · 2^(n/k)` for every `k ≥ 1`.

The machine is built once: `drvC c` (`drvC_spec`, cost `S n = 200 (n + 1)^3 (B n + 1)`), one compile
(`timeComp_wrapFn`), one simulation (`Sim.factoringInTime_of_timeComp`) with the fixed time bound
`T n = Q (n + k₀ + S n + 1)^2`, so `M.time n ≤ c (T n + n + 1)^3`.  Per `k` only the bound is shown, from `B` at
`24k`: with `P = 2^(n/(24k))`, `T n + n + 1 ≤ E P^8`, and `P^24 ≤ 2^(n/k)`.

* **`subexp_of_cspec`**.

Not an audit surface.
-/
module

public import FactoringAux.UniDrvSpec
public import FactoringAux.Final

@[expose] public section

namespace Factoring.Aux

open Factoring.Aux.Copied Factoring.Aux.Copied.PLib Computability

theorem pow24_le (n k : ℕ) : (2 ^ (n / (24 * k))) ^ 24 ≤ 2 ^ (n / k) := by
  have h := mul_div_mul_le 24 k n
  calc (2 ^ (n / (24 * k))) ^ 24 = 2 ^ (24 * (n / (24 * k))) := by rw [← pow_mul, mul_comm]
    _ ≤ 2 ^ (n / k) := Nat.pow_le_pow_right (by norm_num) h

/-- The per-`k` bound: if `B n ≤ C · 2^(n/(24k))`, then the fixed time bound of the uniform machine is at most
`c (Q D² + 24k + 1)^3 · 2^(n/k)`, with `D = 24k + k₀ + 200 (24k + 1)^3 (C + 1) + 1`. -/
theorem uni_time_le (B : ℕ → ℕ) (Q k0 cc k C : ℕ) (hk : 1 ≤ k) (hB : ∀ n, B n ≤ C * 2 ^ (n / (24 * k)))
    (n : ℕ) :
    cc * (Q * (n + k0 + 200 * (n + 1) ^ 3 * (B n + 1) + 1) ^ 2 + n + 1) ^ 3 ≤
      cc * (Q * (24 * k + k0 + 200 * (24 * k + 1) ^ 3 * (C + 1) + 1) ^ 2 + 24 * k + 1) ^ 3 * 2 ^ (n / k) := by
  set P := 2 ^ (n / (24 * k)) with hPdef
  set A := 200 * (24 * k + 1) ^ 3 * (C + 1) with hA
  set D := 24 * k + k0 + A + 1 with hD
  set E := Q * D ^ 2 + 24 * k + 1 with hE
  clear_value P A D E
  have hP : 1 ≤ P := hPdef ▸ Nat.one_le_two_pow
  have hn : n ≤ 24 * k * P := hPdef ▸ le_two_pow_div n (24 * k) (by omega)
  have hn1 : n + 1 ≤ (24 * k + 1) * P := by nlinarith
  have hcube : (n + 1) ^ 3 ≤ (24 * k + 1) ^ 3 * P ^ 3 := by
    calc (n + 1) ^ 3 ≤ ((24 * k + 1) * P) ^ 3 := Nat.pow_le_pow_left hn1 3
      _ = _ := by ring
  have hb : B n + 1 ≤ (C + 1) * P := by have := hB n; rw [← hPdef] at this; nlinarith
  have hS : 200 * (n + 1) ^ 3 * (B n + 1) ≤ A * P ^ 4 := by
    calc 200 * (n + 1) ^ 3 * (B n + 1) ≤ 200 * ((24 * k + 1) ^ 3 * P ^ 3) * ((C + 1) * P) := by gcongr
      _ = A * P ^ 4 := by rw [hA]; ring
  have hP4 : 1 ≤ P ^ 4 := Nat.one_le_pow _ _ (by omega)
  have hPP4 : P ≤ P ^ 4 := by
    calc P = P * 1 := (mul_one P).symm
      _ ≤ P * P ^ 3 := Nat.mul_le_mul_left _ (Nat.one_le_pow _ _ (by omega))
      _ = P ^ 4 := by ring
  have h1 : n + k0 + 200 * (n + 1) ^ 3 * (B n + 1) + 1 ≤ D * P ^ 4 := by
    have : n ≤ 24 * k * P ^ 4 := le_trans hn (Nat.mul_le_mul_left _ hPP4)
    have : k0 ≤ k0 * P ^ 4 := Nat.le_mul_of_pos_right _ hP4
    rw [hD]; nlinarith
  have hP8 : 1 ≤ P ^ 8 := Nat.one_le_pow _ _ (by omega)
  have hPP8 : P ≤ P ^ 8 := by
    calc P = P * 1 := (mul_one P).symm
      _ ≤ P * P ^ 7 := Nat.mul_le_mul_left _ (Nat.one_le_pow _ _ (by omega))
      _ = P ^ 8 := by ring
  have h2 : Q * (n + k0 + 200 * (n + 1) ^ 3 * (B n + 1) + 1) ^ 2 + n + 1 ≤ E * P ^ 8 := by
    have hsq : (n + k0 + 200 * (n + 1) ^ 3 * (B n + 1) + 1) ^ 2 ≤ D ^ 2 * P ^ 8 := by
      calc _ ≤ (D * P ^ 4) ^ 2 := Nat.pow_le_pow_left h1 2
        _ = D ^ 2 * P ^ 8 := by ring
    have hq : Q * (n + k0 + 200 * (n + 1) ^ 3 * (B n + 1) + 1) ^ 2 ≤ Q * D ^ 2 * P ^ 8 := by
      calc _ ≤ Q * (D ^ 2 * P ^ 8) := Nat.mul_le_mul_left Q hsq
        _ = Q * D ^ 2 * P ^ 8 := (mul_assoc _ _ _).symm
    have hn8 : n ≤ 24 * k * P ^ 8 := le_trans hn (Nat.mul_le_mul_left _ hPP8)
    rw [hE]; nlinarith
  have h3 : (Q * (n + k0 + 200 * (n + 1) ^ 3 * (B n + 1) + 1) ^ 2 + n + 1) ^ 3 ≤ E ^ 3 * P ^ 24 := by
    calc _ ≤ (E * P ^ 8) ^ 3 := Nat.pow_le_pow_left h2 3
      _ = E ^ 3 * P ^ 24 := by ring
  have h4 : P ^ 24 ≤ 2 ^ (n / k) := hPdef ▸ pow24_le n k
  calc cc * (Q * (n + k0 + 200 * (n + 1) ^ 3 * (B n + 1) + 1) ^ 2 + n + 1) ^ 3
      ≤ cc * (E ^ 3 * P ^ 24) := Nat.mul_le_mul_left _ h3
    _ ≤ cc * (E ^ 3 * 2 ^ (n / k)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h4)
    _ = cc * E ^ 3 * 2 ^ (n / k) := by ring

/-- **The uniform glue.**  One counting command whose cost is `≤ C_k · 2^(n/k)` for every `k ≥ 1` gives one machine
that, for every `k ≥ 1`, factors within `C'_k · 2^(n/k)` steps (`subexponentialRate`'s statement). -/
theorem subexp_of_cspec (c : Cmd) (B : ℕ → ℕ) (hc : CSpec c B)
    (hB : ∀ k : ℕ, 1 ≤ k → ∃ C : ℕ, ∀ n, B n ≤ C * 2 ^ (n / k)) :
    ∃ M : FactoringMachine, ∀ k : ℕ, 1 ≤ k → ∃ C : ℕ, FactorsWithin M (fun n => C * 2 ^ (n / k)) := by
  obtain ⟨hout, hcost⟩ := drvC_spec c B hc
  obtain ⟨Q, k0, hT⟩ := timeComp_wrapFn (drvC c) 2 (fun xs => outOf ((srcOut (drvC c) xs).ar 2))
    (fun xs => 200 * (xs.length + 1) ^ 3 * (B xs.length + 1)) (fun _ => rfl) hcost
  obtain ⟨cc, M, hfin, htime⟩ := Sim.factoringInTime_of_timeComp (wrapFn (drvC c) 2) _ _ hT hout
    (fun n => Q * (n + k0 + 200 * (n + 1) ^ 3 * (B n + 1) + 1) ^ 2) (fun N => le_rfl)
  refine ⟨M, fun k hk => ?_⟩
  obtain ⟨C, hC⟩ := hB (24 * k) (by omega)
  exact ⟨_, hfin, fun n => le_trans (htime n) (uni_time_le B Q k0 cc k C hk hC n)⟩

end Factoring.Aux
