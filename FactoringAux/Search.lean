/-
The search (adapted to the audited output `Nat.minFac N`): the smallest prime factor of `N` from
`W` counts of divisors with prescribed high bits.

`cntPre N k x` is the number of divisors `d ≥ 2` of `N` whose bits above position `k` are `x` (`d / 2^k = x`): this
is what one run of the counting engine returns, for the pattern fixing those bits (the divisor `1` is subtracted by
the caller when it matches).  `search c W` fixes the bits of the answer from the top: at position `k` it keeps the
smaller extension `2x` when some divisor `≥ 2` has those high bits, and `2x + 1` otherwise.

`search_eq_minFac`: if `c = cntPre N` and `2 ≤ N < 2^W`, the search returns `Nat.minFac N`, after `W` counts.

Not an audit surface.
-/
module

public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.NumberTheory.Divisors

@[expose] public section

namespace Factoring.Aux

open Finset

/-- Divisors `d ≥ 2` of `N` with `d / 2^k = x`. -/
def cntPre (N k x : ℕ) : ℕ := ((N.divisors).filter (fun d => 2 ≤ d ∧ d / 2 ^ k = x)).card

/-- One step: keep `2x` if some counted divisor has high bits `2x`, else `2x + 1`. -/
def searchStep (c : ℕ → ℕ → ℕ) (k x : ℕ) : ℕ := if 0 < c k (2 * x) then 2 * x else 2 * x + 1

/-- Fix the bits from position `k − 1` down to `0`, starting from the high bits `x`. -/
def searchGo (c : ℕ → ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, x => x
  | k + 1, x => searchGo c k (searchStep c k x)

/-- The search over `W`-bit numbers. -/
def search (c : ℕ → ℕ → ℕ) (W : ℕ) : ℕ := searchGo c W 0

theorem div_two_pow_succ' (m k : ℕ) : m / 2 ^ k = 2 * (m / 2 ^ (k + 1)) ∨ m / 2 ^ k = 2 * (m / 2 ^ (k + 1)) + 1 := by
  have : m / 2 ^ (k + 1) = m / 2 ^ k / 2 := by rw [pow_succ, Nat.div_div_eq_div_mul]
  rw [this]
  omega

/-- One step keeps the high bits of `minFac N`. -/
theorem searchStep_minFac {N : ℕ} (hN : 2 ≤ N) (k : ℕ) :
    searchStep (cntPre N) k (N.minFac / 2 ^ (k + 1)) = N.minFac / 2 ^ k := by
  set m := N.minFac
  have hm2 : 2 ≤ m := (Nat.minFac_prime (by omega)).two_le
  have hmN : m ∣ N := Nat.minFac_dvd N
  unfold searchStep
  rcases div_two_pow_succ' m k with h | h
  · -- `m` itself is counted
    have : 0 < cntPre N k (2 * (m / 2 ^ (k + 1))) := by
      unfold cntPre
      refine Finset.card_pos.mpr ⟨m, ?_⟩
      simp only [Finset.mem_filter, Nat.mem_divisors]
      exact ⟨⟨hmN, by omega⟩, hm2, h⟩
    rw [if_pos this, h]
  · -- no divisor `≥ 2` lies below `m`
    have : cntPre N k (2 * (m / 2 ^ (k + 1))) = 0 := by
      unfold cntPre
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro d hd ⟨hd2, hdk⟩
      have hdN : d ∣ N := (Nat.mem_divisors.mp hd).1
      have hlt : d / 2 ^ k < m / 2 ^ k := by omega
      have hdm : d < m := by
        by_contra hge
        exact absurd (Nat.div_le_div_right (c := 2 ^ k) (not_lt.mp hge)) (not_le.mpr hlt)
      exact absurd (Nat.minFac_le_of_dvd hd2 hdN) (not_le.mpr hdm)
    rw [this, if_neg (lt_irrefl 0), h]

theorem searchGo_minFac {N : ℕ} (hN : 2 ≤ N) :
    ∀ k, searchGo (cntPre N) k (N.minFac / 2 ^ k) = N.minFac
  | 0 => by simp [searchGo]
  | k + 1 => by
      rw [searchGo, searchStep_minFac hN k]
      exact searchGo_minFac hN k

/-- **The search**: from `W` divisor counts, the smallest prime factor of every `2 ≤ N < 2^W`. -/
theorem search_eq_minFac {N W : ℕ} (hN : 2 ≤ N) (hW : N < 2 ^ W) : search (cntPre N) W = N.minFac := by
  have h0 : N.minFac / 2 ^ W = 0 :=
    Nat.div_eq_of_lt (lt_of_le_of_lt (Nat.minFac_le (by omega)) hW)
  unfold search
  rw [← h0]
  exact searchGo_minFac hN W

end Factoring.Aux
