/-
Deciding `V > 0` from residues modulo small numbers (the engine counts modulo `m`, for every `m ≤ 2M`).

* `centralBinom_dvd_of_all`: if every `m` with `1 ≤ m ≤ 2M` divides `V`, so does `centralBinom M` (each prime
  power in it is at most `2M`, `Nat.factorization_choose_le_log`).
* **`eq_zero_of_all_dvd`**: if moreover `(2M+1)·V < 4^M`, then `V = 0`.

Not an audit surface.
-/
module

public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.Data.Nat.Choose.Factorization
public import Mathlib.Data.Nat.Factorization.Basic

@[expose] public section

namespace Factoring.Aux

theorem centralBinom_dvd_of_all {V M : ℕ} (hV : V ≠ 0) (hM : 0 < M) (h : ∀ m, 1 ≤ m → m ≤ 2 * M → m ∣ V) :
    M.centralBinom ∣ V := by
  have hc : M.centralBinom ≠ 0 := Nat.centralBinom_ne_zero M
  rw [← Nat.factorization_prime_le_iff_dvd hc hV]
  intro p hp
  set e := M.centralBinom.factorization p
  have he : e ≤ Nat.log p (2 * M) := by
    rw [Nat.centralBinom_eq_two_mul_choose] at *
    exact Nat.factorization_choose_le_log
  have hpe : p ^ e ≤ 2 * M :=
    le_trans (Nat.pow_le_pow_right hp.pos he) (Nat.pow_log_le_self p (by omega))
  have hdvd : p ^ e ∣ V := h _ (Nat.one_le_pow _ _ hp.pos) hpe
  exact (hp.pow_dvd_iff_le_factorization hV).mp hdvd

/-- **Positivity from residues**: if every `1 ≤ m ≤ 2M` divides `V` and `(2M+1) V < 4^M`, then `V = 0`. -/
theorem eq_zero_of_all_dvd {V M : ℕ} (hM : 0 < M) (h : ∀ m, 1 ≤ m → m ≤ 2 * M → m ∣ V)
    (hlt : (2 * M + 1) * V < 4 ^ M) : V = 0 := by
  by_contra hV
  have hd := centralBinom_dvd_of_all hV hM h
  have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero hV) hd
  have h4 := Nat.four_pow_le_two_mul_self_mul_centralBinom M hM
  have : 2 * M * M.centralBinom ≤ (2 * M + 1) * V :=
    le_trans (Nat.mul_le_mul_left _ hle) (Nat.mul_le_mul_right _ (by omega))
  omega

end Factoring.Aux
