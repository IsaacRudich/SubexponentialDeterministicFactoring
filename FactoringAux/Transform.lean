/-
The transform of the multiplication network: the three gate layers `FA`, `MID`,
`IB` compute the convolution of two zero-padded digit sequences, and in `ZMod (2^m+1)` the residue is the integer.

Generic part, in any commutative ring with `ω^L = -1`, `L = 2^k`, `T = 2L = A·A`, and `tInv · T = 1`:
* `sum_root`: `∑_{t<T} ω^(e t) = T` if `T ∣ e`, else `0` (principal root, from `ω^L = -1`);
* `sum_range_sq`: the index split `i = r + A i'` of `range (A·A)`;
* `stage`: one stage of Cooley–Tukey, `∑_{i<A²} X_i ζ^(i(k₁+Ak₂)) = ∑_r ζ^(A r k₂) faOut ζ X r k₁`;
* gates: `faOut` (forward stage 1, gate `FA[r]`), `midOut` (forward stage 2, pointwise product, inverse stage 1,
  gate `MID[k₁]`), `ibOut` (inverse stage 2 and `T⁻¹`, gate `IB[j₁]`);
* **`ib_mid_fa`**: the three layers output the convolution coefficient `cv P Q (j₁ + A j₂)`, for inputs supported
  below `L`.

In `ZMod (2^m+1)` with `m = 4L`: `ω = 16` (`omega16_pow_L`), `tInv` (`tInv_mul`), and exactness
(`val_cv`): the coefficient of two sequences of digits `< 2^L` is below `2^m`, so the residue's value is the integer.

Not an audit surface.
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Tactic.Positivity

@[expose] public section

namespace Factoring.Aux

open Finset

section Ring

variable {R : Type*} [CommRing R]

/-- `∑_{i<2^k} x^i = ∏_{s<k} (1 + x^(2^s))`. -/
theorem geom_two_pow (x : R) :
    ∀ k : ℕ, ∑ i ∈ range (2 ^ k), x ^ i = ∏ s ∈ range k, (1 + x ^ (2 ^ s))
  | 0 => by simp
  | k + 1 => by
      rw [prod_range_succ, ← geom_two_pow x k, pow_succ, mul_two, sum_range_add]
      have : ∑ i ∈ range (2 ^ k), x ^ (2 ^ k + i) = x ^ (2 ^ k) * ∑ i ∈ range (2 ^ k), x ^ i := by
        rw [mul_sum]; exact sum_congr rfl (fun i _ => pow_add _ _ _)
      rw [this]; ring

/-- **Principal root.** If `ω^(2^k) = -1` then `∑_{i<2^(k+1)} (ω^j)^i = 0` for `0 < j < 2^(k+1)`. -/
theorem sum_pow_eq_zero (ω : R) (k : ℕ) (hω : ω ^ (2 ^ k) = -1)
    (j : ℕ) (hj0 : 0 < j) (hj : j < 2 ^ (k + 1)) :
    ∑ i ∈ range (2 ^ (k + 1)), (ω ^ j) ^ i = 0 := by
  rw [geom_two_pow]
  obtain ⟨s, o, ho, rfl⟩ : ∃ s o, Odd o ∧ j = 2 ^ s * o :=
    ⟨j.factorization 2, j / 2 ^ j.factorization 2,
      Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 (Nat.not_dvd_ordCompl Nat.prime_two hj0.ne')),
      (Nat.ordProj_mul_ordCompl_eq_self j 2).symm⟩
  have hs : s ≤ k := by
    by_contra h
    have : 2 ^ (k + 1) ≤ 2 ^ s * o :=
      le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) (Nat.le_mul_of_pos_right _ ho.pos)
    omega
  apply prod_eq_zero (i := k - s) (mem_range.2 (by omega))
  rw [← pow_mul, show 2 ^ s * o * 2 ^ (k - s) = 2 ^ k * o by
    rw [mul_comm (2 ^ s), mul_assoc, ← pow_add, Nat.add_sub_cancel' hs, mul_comm]]
  rw [pow_mul, hω, ho.neg_one_pow]; ring

/-- `ω^(2^(k+1)) = 1` when `ω^(2^k) = -1`. -/
theorem pow_T_eq_one (ω : R) (k : ℕ) (hω : ω ^ (2 ^ k) = -1) : ω ^ (2 ^ (k + 1)) = 1 := by
  rw [pow_succ, pow_mul, hω]; ring

/-- `ω^e` depends on `e` modulo `T` when `ω^T = 1`. -/
theorem pow_mod_T (ω : R) {T : ℕ} (hT : ω ^ T = 1) (e : ℕ) : ω ^ e = ω ^ (e % T) := by
  conv_lhs => rw [← Nat.mod_add_div e T, pow_add, pow_mul, hT, one_pow, mul_one]

/-- **The root sums**: `∑_{t<T} ω^(e t)` is `T` if `T ∣ e`, else `0`. -/
theorem sum_root (ω : R) (k : ℕ) (hω : ω ^ (2 ^ k) = -1) (e : ℕ) :
    ∑ t ∈ range (2 ^ (k + 1)), ω ^ (e * t) = if 2 ^ (k + 1) ∣ e then ((2 ^ (k + 1) : ℕ) : R) else 0 := by
  have hT := pow_T_eq_one ω k hω
  have hTpos : 0 < 2 ^ (k + 1) := Nat.pow_pos (by norm_num)
  simp_rw [pow_mul]
  rw [pow_mod_T ω hT e]
  split_ifs with hd
  · rw [Nat.eq_zero_of_dvd_of_lt (Nat.dvd_mod_iff dvd_rfl |>.mpr hd) (Nat.mod_lt _ hTpos)]
    simp
  · refine sum_pow_eq_zero ω k hω _ ?_ (Nat.mod_lt _ hTpos)
    rcases Nat.eq_zero_or_pos (e % 2 ^ (k + 1)) with h | h
    · exact absurd (Nat.dvd_of_mod_eq_zero h) hd
    · exact h

/-- The index split `i = A i' + r` of `range (A·B)`. -/
theorem sum_range_mul' {M : Type*} [AddCommMonoid M] (A : ℕ) (f : ℕ → M) :
    ∀ B : ℕ, ∑ i ∈ range (A * B), f i = ∑ i' ∈ range B, ∑ r ∈ range A, f (A * i' + r)
  | 0 => by simp
  | B + 1 => by
      rw [Nat.mul_succ, sum_range_add, sum_range_mul' A f B, sum_range_succ]

/-- The index split `i = r + A i'` of `range (A·A)`. -/
theorem sum_range_sq {M : Type*} [AddCommMonoid M] (A : ℕ) (f : ℕ → M) :
    ∑ i ∈ range (A * A), f i = ∑ r ∈ range A, ∑ i' ∈ range A, f (r + A * i') := by
  rw [sum_range_mul' A f A, sum_comm]
  exact sum_congr rfl fun r _ => sum_congr rfl fun i' _ => by rw [add_comm]

/-! ### One stage of Cooley–Tukey, and the gates -/

variable (A : ℕ)

/-- The transform of length `A·A` (`X` read on `range (A·A)`). -/
def dft (ζ : R) (X : ℕ → R) (k : ℕ) : R := ∑ i ∈ range (A * A), X i * ζ ^ (i * k)

/-- Gate `FA[r]` (forward stage 1): from its inputs `u i' = X (r + A i')`, output `k₁`. -/
def faOut (ζ : R) (r : ℕ) (u : ℕ → R) (k₁ : ℕ) : R :=
  ζ ^ (r * k₁) * ∑ i' ∈ range A, u i' * ζ ^ (A * i' * k₁)

/-- Stage 2 of a transform: `∑_r a_r ζ^(A r k₂)`. -/
def hatOut (ζ : R) (a : ℕ → R) (k₂ : ℕ) : R := ∑ r ∈ range A, a r * ζ ^ (A * r * k₂)

/-- Gate `MID[k₁]`: from `a r = y_p[r][k₁]`, `b r = y_q[r][k₁]`, the forward stage 2 of both, their pointwise
product, and the inverse stage 1 (root `ω'`); output `j₁`. -/
def midOut (ω ω' : R) (k₁ : ℕ) (a b : ℕ → R) (j₁ : ℕ) : R :=
  faOut A ω' k₁ (fun k₂ => hatOut A ω a k₂ * hatOut A ω b k₂) j₁

/-- Gate `IB[j₁]`: from `z r' = z[r'][j₁]`, the inverse stage 2 and `T⁻¹`; output `j₂` (coefficient `j₁ + A j₂`). -/
def ibOut (ω' tInv : R) (z : ℕ → R) (j₂ : ℕ) : R := tInv * hatOut A ω' z j₂

theorem stage_pow (ζ : R) (hζ : ζ ^ (A * A) = 1) (r i' k₁ k₂ : ℕ) :
    ζ ^ ((r + A * i') * (k₁ + A * k₂)) = ζ ^ (A * r * k₂) * (ζ ^ (r * k₁) * ζ ^ (A * i' * k₁)) := by
  have : (r + A * i') * (k₁ + A * k₂) = A * r * k₂ + (r * k₁ + A * i' * k₁) + A * A * (i' * k₂) := by ring
  rw [this, pow_add, pow_mul ζ (A * A), hζ, one_pow, mul_one, pow_add, pow_add]

/-- **One stage**: the transform at `k₁ + A k₂` is stage 2 of the outputs of the gates `FA[r]` at `k₁`. -/
theorem stage (ζ : R) (hζ : ζ ^ (A * A) = 1) (X : ℕ → R) (k₁ k₂ : ℕ) :
    dft A ζ X (k₁ + A * k₂) = hatOut A ζ (fun r => faOut A ζ r (fun i' => X (r + A * i')) k₁) k₂ := by
  unfold dft hatOut faOut
  rw [sum_range_sq]
  refine sum_congr rfl fun r _ => ?_
  simp only [mul_sum, sum_mul]
  refine sum_congr rfl fun i' _ => ?_
  rw [stage_pow A ζ hζ]; ring

/-! ### The convolution -/

/-- The convolution coefficient `∑_{i+i'=j} P_i Q_i'` (indices below `T`). -/
def cv {S : Type*} [CommSemiring S] (T : ℕ) (P Q : ℕ → S) (j : ℕ) : S :=
  ∑ i ∈ range T, ∑ i' ∈ range T, if i + i' = j then P i * Q i' else 0

theorem cast_cv (T : ℕ) (P Q : ℕ → ℕ) (j : ℕ) :
    ((cv T P Q j : ℕ) : R) = cv T (fun i => (P i : R)) (fun i => (Q i : R)) j := by
  simp [cv, Nat.cast_sum, Nat.cast_ite, Nat.cast_mul]

theorem dvd_iff_eq_of_lt {T s j : ℕ} (hs : s < T) (hj : j < T) : T ∣ s + (T - 1) * j ↔ s = j := by
  have hT : 1 ≤ T := by omega
  have key : s + (T - 1) * j + j = s + T * j := by
    have : (T - 1) * j + j = T * j := by
      rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hT]
    omega
  constructor
  · rintro ⟨c, hc⟩
    have h1 : (s + T * j) % T = (j + T * c) % T := by rw [← key, hc]; ring_nf
    rw [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hs,
      Nat.mod_eq_of_lt hj] at h1
    exact h1
  · rintro rfl
    exact ⟨s, by
      have : (T - 1) * s + s = T * s := by
        rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hT]
      omega⟩

/-- **The convolution theorem**, for sequences supported below `L` with `2L = T = 2^(k+1)`: the inverse transform
(root `ω^(T-1)`) of the pointwise product of the transforms is `T` times the convolution. -/
theorem conv_thm (ω : R) (k : ℕ) (hω : ω ^ (2 ^ k) = -1) (P Q : ℕ → R)
    (hP : ∀ i, 2 ^ k ≤ i → P i = 0) (hQ : ∀ i, 2 ^ k ≤ i → Q i = 0) (j : ℕ) (hj : j < 2 ^ (k + 1)) :
    ∑ t ∈ range (2 ^ (k + 1)), (∑ i ∈ range (2 ^ (k + 1)), P i * ω ^ (i * t)) *
        (∑ i' ∈ range (2 ^ (k + 1)), Q i' * ω ^ (i' * t)) * (ω ^ (2 ^ (k + 1) - 1)) ^ (t * j) =
      ((2 ^ (k + 1) : ℕ) : R) * cv (2 ^ (k + 1)) P Q j := by
  set T := 2 ^ (k + 1) with hTdef
  have hLT : 2 ^ k + 2 ^ k = T := by rw [hTdef, pow_succ]; ring
  have expand : ∀ t, (∑ i ∈ range T, P i * ω ^ (i * t)) * (∑ i' ∈ range T, Q i' * ω ^ (i' * t)) *
      (ω ^ (T - 1)) ^ (t * j) =
      ∑ i ∈ range T, ∑ i' ∈ range T, P i * Q i' * ω ^ ((i + i' + (T - 1) * j) * t) := by
    intro t
    rw [sum_mul_sum, sum_mul]
    refine sum_congr rfl fun i _ => ?_
    rw [sum_mul]
    refine sum_congr rfl fun i' _ => ?_
    rw [← pow_mul, show (i + i' + (T - 1) * j) * t = i * t + i' * t + (T - 1) * (t * j) by ring,
      pow_add, pow_add]
    ring
  simp_rw [expand]
  rw [sum_comm]
  unfold cv
  rw [mul_sum]
  refine sum_congr rfl fun i hi => ?_
  rw [sum_comm, mul_sum]
  refine sum_congr rfl fun i' hi' => ?_
  rw [← mul_sum]
  have hsr := sum_root ω k hω (i + i' + (T - 1) * j)
  rw [← hTdef] at hsr
  rw [hsr]
  by_cases hPi : 2 ^ k ≤ i
  · simp [hP i hPi]
  by_cases hQi : 2 ^ k ≤ i'
  · simp [hQ i' hQi]
  have hs : i + i' < T := by omega
  by_cases he : i + i' = j
  · rw [if_pos ((dvd_iff_eq_of_lt hs hj).mpr he), if_pos he]; ring
  · rw [if_neg (fun h => he ((dvd_iff_eq_of_lt hs hj).mp h)), if_neg he]; ring

/-- **The three layers compute the convolution.**  With `ω^L = -1` (`L = 2^k`), `T = 2L = A·A`, `tInv · T = 1`,
and inputs supported below `L`: gate `IB[j₁]`'s output `j₂`, fed by the `MID` gates, fed by the `FA` gates, is the
convolution coefficient at `j₁ + A j₂`. -/
theorem ib_mid_fa (ω tInv : R) (k : ℕ) (hω : ω ^ (2 ^ k) = -1) (hA : A * A = 2 ^ (k + 1))
    (htInv : tInv * ((2 ^ (k + 1) : ℕ) : R) = 1) (P Q : ℕ → R)
    (hP : ∀ i, 2 ^ k ≤ i → P i = 0) (hQ : ∀ i, 2 ^ k ≤ i → Q i = 0) (j₁ j₂ : ℕ) (h₁ : j₁ < A) (h₂ : j₂ < A) :
    ibOut A (ω ^ (2 ^ (k + 1) - 1)) tInv
        (fun r' => midOut A ω (ω ^ (2 ^ (k + 1) - 1)) r'
          (fun r => faOut A ω r (fun i' => P (r + A * i')) r')
          (fun r => faOut A ω r (fun i' => Q (r + A * i')) r') j₁) j₂ =
      cv (2 ^ (k + 1)) P Q (j₁ + A * j₂) := by
  have hT := pow_T_eq_one ω k hω
  have hζ : ω ^ (A * A) = 1 := by rw [hA]; exact hT
  have hζ' : (ω ^ (2 ^ (k + 1) - 1)) ^ (A * A) = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]
  have hfw : ∀ X : ℕ → R, ∀ r' k₂,
      hatOut A ω (fun r => faOut A ω r (fun i' => X (r + A * i')) r') k₂ = dft A ω X (r' + A * k₂) :=
    fun X r' k₂ => (stage A ω hζ X r' k₂).symm
  have hmid : ∀ r', midOut A ω (ω ^ (2 ^ (k + 1) - 1)) r' (fun r => faOut A ω r (fun i' => P (r + A * i')) r')
      (fun r => faOut A ω r (fun i' => Q (r + A * i')) r') j₁ =
      faOut A (ω ^ (2 ^ (k + 1) - 1)) r'
        (fun k₂ => (fun t => dft A ω P t * dft A ω Q t) (r' + A * k₂)) j₁ := by
    intro r'
    unfold midOut
    simp only [hfw]
  unfold ibOut
  simp only [hmid]
  rw [← stage A _ hζ' (fun t => dft A ω P t * dft A ω Q t) j₁ j₂]
  have hj : j₁ + A * j₂ < 2 ^ (k + 1) := by
    rw [← hA]
    calc j₁ + A * j₂ < A + A * j₂ := by omega
      _ = A * (j₂ + 1) := by ring
      _ ≤ A * A := Nat.mul_le_mul_left _ h₂
  unfold dft
  rw [hA, conv_thm ω k hω P Q hP hQ (j₁ + A * j₂) hj, ← mul_assoc, htInv, one_mul]

end Ring

/-! ### The ring `ZMod (2^m+1)` -/

/-- `A = 2^(s+1)`: gates per layer. -/
def pA (s : ℕ) : ℕ := 2 ^ (s + 1)
/-- `L = 2^(2s+1)`: digits per factor, and bits per digit. -/
def pL (s : ℕ) : ℕ := 2 ^ (2 * s + 1)
/-- `m = 4L`: the ring is `ZMod (2^m+1)`. -/
def pm (s : ℕ) : ℕ := 4 * pL s
/-- The modulus `2^m + 1`. -/
abbrev pM (s : ℕ) : ℕ := 2 ^ pm s + 1

theorem pA_sq (s : ℕ) : pA s * pA s = 2 ^ (2 * s + 1 + 1) := by
  unfold pA; rw [← pow_add]; ring_nf

theorem pL_pos (s : ℕ) : 0 < pL s := Nat.pow_pos (by norm_num)

/-- In `ZMod (2^m+1)`, `2^m = -1`. -/
theorem two_pow_eq_neg_one (m : ℕ) : (2 : ZMod (2 ^ m + 1)) ^ m = -1 := by
  have h : ((2 ^ m + 1 : ℕ) : ZMod (2 ^ m + 1)) = 0 := ZMod.natCast_self _
  push_cast at h
  exact eq_neg_of_add_eq_zero_left h

/-- `ω = 16` has `ω^L = -1` in `ZMod (2^m+1)`, `m = 4L`. -/
theorem omega16_pow_L (s : ℕ) : (16 : ZMod (pM s)) ^ (2 ^ (2 * s + 1)) = -1 := by
  have h := two_pow_eq_neg_one (pm s)
  rw [show (16 : ZMod (pM s)) = 2 ^ 4 by norm_num, ← pow_mul]
  exact h

/-- `T⁻¹ = 2^((2m-1)(2s+2))` (as `2^(2m) = 1`). -/
def tInv (s : ℕ) : ZMod (pM s) := 2 ^ ((2 * pm s - 1) * (2 * s + 2))

theorem tInv_mul (s : ℕ) : tInv s * ((2 ^ (2 * s + 1 + 1) : ℕ) : ZMod (pM s)) = 1 := by
  have h := two_pow_eq_neg_one (pm s)
  have hm : 1 ≤ pm s := by unfold pm; have := pL_pos s; omega
  have h2 : (2 : ZMod (pM s)) ^ (2 * pm s) = 1 := by rw [mul_comm, pow_mul, h]; norm_num
  unfold tInv
  push_cast
  rw [← pow_add, show (2 * pm s - 1) * (2 * s + 2) + (2 * s + 1 + 1) = 2 * pm s * (2 * s + 2) by
    have : 2 * pm s - 1 + 1 = 2 * pm s := by omega
    calc (2 * pm s - 1) * (2 * s + 2) + (2 * s + 1 + 1) = (2 * pm s - 1 + 1) * (2 * s + 2) := by ring
      _ = _ := by rw [this], pow_mul, h2, one_pow]

/-- **Exactness**: digits `< 2^L` supported below `L` have convolution coefficients `< 2^m`. -/
theorem cv_lt (s : ℕ) (P Q : ℕ → ℕ) (hP : ∀ i, P i < 2 ^ pL s) (hQ : ∀ i, Q i < 2 ^ pL s)
    (hPs : ∀ i, pL s ≤ i → P i = 0) (j : ℕ) : cv (2 ^ (2 * s + 1 + 1)) P Q j < 2 ^ pm s := by
  set L := pL s
  have hT : 2 ^ (2 * s + 1 + 1) = L + L := by simp only [L, pL]; rw [pow_succ]; ring
  have inner : ∀ i, ∑ i' ∈ range (2 ^ (2 * s + 1 + 1)), (if i + i' = j then P i * Q i' else 0) ≤
      if i < L then 2 ^ L * 2 ^ L else 0 := by
    intro i
    split_ifs with hi
    · calc ∑ i' ∈ range (2 ^ (2 * s + 1 + 1)), (if i + i' = j then P i * Q i' else 0)
          ≤ ∑ i' ∈ range (2 ^ (2 * s + 1 + 1)), (if i' = j - i then P i * Q i' else 0) := by
            refine sum_le_sum fun i' _ => ?_
            split_ifs with h1 h2 <;> first | exact le_rfl | omega
        _ ≤ P i * Q (j - i) := by
            rw [sum_ite_eq']; split_ifs <;> simp
        _ ≤ 2 ^ L * 2 ^ L := Nat.mul_le_mul (hP i).le (hQ _).le
    · rw [hPs i (by omega)]; simp
  unfold cv
  calc ∑ i ∈ range (2 ^ (2 * s + 1 + 1)), ∑ i' ∈ range (2 ^ (2 * s + 1 + 1)),
        (if i + i' = j then P i * Q i' else 0)
      ≤ ∑ i ∈ range (2 ^ (2 * s + 1 + 1)), (if i < L then 2 ^ L * 2 ^ L else 0) := sum_le_sum fun i _ => inner i
    _ = L * (2 ^ L * 2 ^ L) := by
        rw [hT, sum_range_add]
        have h1 : ∑ x ∈ range L, (if x < L then 2 ^ L * 2 ^ L else 0) = L * (2 ^ L * 2 ^ L) := by
          rw [sum_congr rfl fun x hx => if_pos (mem_range.mp hx)]; simp
        have h2 : ∑ x ∈ range L, (if L + x < L then 2 ^ L * 2 ^ L else 0) = 0 :=
          sum_eq_zero fun x _ => if_neg (by omega)
        rw [h1, h2, add_zero]
    _ < 2 ^ L * (2 ^ L * 2 ^ L) := Nat.mul_lt_mul_of_pos_right (Nat.lt_two_pow_self) (by positivity)
    _ ≤ 2 ^ pm s := by
        rw [← pow_add, ← pow_add]
        exact Nat.pow_le_pow_right (by norm_num) (by simp only [pm, L]; omega)

/-- The residue of the coefficient is the coefficient. -/
theorem val_cv (s : ℕ) (P Q : ℕ → ℕ) (hP : ∀ i, P i < 2 ^ pL s) (hQ : ∀ i, Q i < 2 ^ pL s)
    (hPs : ∀ i, pL s ≤ i → P i = 0) (j : ℕ) :
    ((cv (2 ^ (2 * s + 1 + 1)) P Q j : ℕ) : ZMod (pM s)).val = cv (2 ^ (2 * s + 1 + 1)) P Q j :=
  ZMod.val_natCast_of_lt (lt_of_lt_of_le (cv_lt s P Q hP hQ hPs j) (Nat.le_succ _))

end Factoring.Aux
