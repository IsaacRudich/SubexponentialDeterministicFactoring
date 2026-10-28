/-
The last step of `everyRootRate`: a source program (`Cmd`, compiled once by `wrapFn`) that outputs
`encodeNat (minFac N)` on `encodeNat N` within `C · 2^(n/(6k))` source steps gives a Mathlib machine within
`C' · 2^(n/k)` steps.

The overheads: one compile squares (`timeComp_wrapFn`), the simulation of `Program` in `SProg` cubes
(`Sim.factoringInTime_of_timeComp`), so `2^(n/(6k))` becomes `2^(6·⌊n/(6k)⌋) ≤ 2^(n/k)`, up to
constants (`n ≤ 6k·2^(n/(6k))` absorbs the input length).

* `factoringInTime_mono`; `le_two_pow_div` (`n ≤ d · 2^(n/d)`); **`everyRoot_of_src`**.

Not an audit surface.
-/
module

public import FactoringAux.Time
public import FactoringAux.Simulate.Main

@[expose] public section

namespace Factoring.Aux

open Factoring.Aux.Copied Factoring.Aux.Copied.PLib Computability

theorem factoringInTime_mono {T T' : ℕ → ℕ} (h : FactoringInTime T) (hT : ∀ n, T n ≤ T' n) :
    FactoringInTime T' := by
  obtain ⟨M, hfin, htime⟩ := h
  exact ⟨M, hfin, fun n => le_trans (htime n) (hT n)⟩

theorem le_two_pow_div (n d : ℕ) (hd : 0 < d) : n ≤ d * 2 ^ (n / d) := by
  have h1 : n < d * (n / d + 1) := Nat.lt_mul_div_succ n hd
  have h2 : n / d + 1 ≤ 2 ^ (n / d) := Nat.lt_two_pow_self
  calc n ≤ d * (n / d + 1) := h1.le
    _ ≤ d * 2 ^ (n / d) := Nat.mul_le_mul_left _ h2

theorem six_div_le (n k : ℕ) : 6 * (n / (6 * k)) ≤ n / k := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; simp
  rw [Nat.le_div_iff_mul_le hk]
  calc 6 * (n / (6 * k)) * k = 6 * k * (n / (6 * k)) := by ring
    _ ≤ n := Nat.mul_div_le n (6 * k)

/-- **From the engine to the rate.** -/
theorem everyRoot_of_src (k : ℕ) (hk : 1 ≤ k) (s : Cmd) (out C : ℕ)
    (hout : ∀ N, outOf ((srcOut s (encodeNat N)).ar out) = encodeNat N.minFac)
    (hcost : ∀ xs, srcCost s xs ≤ C * 2 ^ (xs.length / (6 * k))) :
    ∃ C' : ℕ, FactoringInTime (fun n => C' * 2 ^ (n / k)) := by
  obtain ⟨Q, k0, hT⟩ := timeComp_wrapFn s out (fun xs => outOf ((srcOut s xs).ar out))
    (fun xs => C * 2 ^ (xs.length / (6 * k))) (fun _ => rfl) hcost
  obtain ⟨c, hc⟩ := Sim.factoringInTime_of_timeComp (wrapFn s out) _ _ hT hout
    (fun n => Q * (n + k0 + C * 2 ^ (n / (6 * k)) + 1) ^ 2) (fun N => le_rfl)
  set D := 6 * k + k0 + C + 1
  refine ⟨c * (Q * D ^ 2 + 6 * k + 1) ^ 3, factoringInTime_mono hc fun n => ?_⟩
  set P := 2 ^ (n / (6 * k))
  have hP : 1 ≤ P := Nat.one_le_two_pow
  have hn : n ≤ 6 * k * P := le_two_pow_div n (6 * k) (by omega)
  have h1 : n + k0 + C * P + 1 ≤ D * P := by
    simp only [D]; nlinarith
  have h2 : Q * (n + k0 + C * P + 1) ^ 2 + n + 1 ≤ (Q * D ^ 2 + 6 * k + 1) * P ^ 2 := by
    have := Nat.pow_le_pow_left h1 2
    have hP2 : P ≤ P ^ 2 := by nlinarith
    nlinarith
  have h3 : (Q * (n + k0 + C * P + 1) ^ 2 + n + 1) ^ 3 ≤ (Q * D ^ 2 + 6 * k + 1) ^ 3 * P ^ 6 := by
    calc _ ≤ ((Q * D ^ 2 + 6 * k + 1) * P ^ 2) ^ 3 := Nat.pow_le_pow_left h2 3
      _ = _ := by ring
  have h4 : P ^ 6 ≤ 2 ^ (n / k) := by
    simp only [P]; rw [← pow_mul, mul_comm]
    exact Nat.pow_le_pow_right (by norm_num) (six_div_le n k)
  calc c * (Q * (n + k0 + C * P + 1) ^ 2 + n + 1) ^ 3
      ≤ c * ((Q * D ^ 2 + 6 * k + 1) ^ 3 * P ^ 6) := Nat.mul_le_mul_left _ h3
    _ ≤ c * ((Q * D ^ 2 + 6 * k + 1) ^ 3 * 2 ^ (n / k)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h4)
    _ = _ := by ring

end Factoring.Aux
