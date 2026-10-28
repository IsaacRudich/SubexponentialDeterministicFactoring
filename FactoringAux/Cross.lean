/-
The eight-square identity and the crossing identity (paper §4, eqs. (27), (28), (30), (31)).

Blocks are 3-bit strings `Blk = Bits 3`; `⊕` is `bxor`.  For blocks `p, q`:
* `phi p q = Σ_{1≤i≤j≤3} p_i q_j + q₁p₂p₃ + p₁q₂p₃ + p₁p₂q₃` (mod 2), `sgn p q = (-1)^(phi p q)`  (27);
* `psi k p q = [p ⊕ q = k] · sgn p q`;
* `Rx x y u v = Σ_k psi k x y · psi k v u`,  `Cx x y u v = Σ_k psi k x u · psi k v y`  (30).

Results: `eightSquare` (28), `crossing` (31): `Rx + Cx = 2 [x = v][y = u]`, and the closed forms and bounds of `Rx`,
`Cx`.  Both identities are checked by `decide` on 12 Boolean variables (kernel reduction, no `native_decide`).

Not an audit surface.
-/
module

public import FactoringAux.Bits
public import Mathlib.Tactic.FinCases
public import Mathlib.Algebra.Order.Ring.Abs

@[expose] public section

namespace Factoring.Aux

open Finset

/-- A block: three bits. -/
abbrev Blk := Bits 3

/-- `p ⊕ q`, bit by bit. -/
def bxor (p q : Blk) : Blk := fun j => xor (p j) (q j)

/-- The exponent of the sign, on the six bits of two blocks (bits `0, 1, 2` stand for `1, 2, 3`). -/
def phiB (p1 p2 p3 q1 q2 q3 : Bool) : Bool :=
  (p1 && q1) ^^ (p1 && q2) ^^ (p1 && q3) ^^ (p2 && q2) ^^ (p2 && q3) ^^ (p3 && q3) ^^
  (q1 && p2 && p3) ^^ (p1 && q2 && p3) ^^ (p1 && p2 && q3)

/-- eq. (27): `σ(p, q) = (-1)^φ(p, q)`. -/
def sgn (p q : Blk) : ℤ := if phiB (p 0) (p 1) (p 2) (q 0) (q 1) (q 2) then -1 else 1

/-- `ψ_k(p, q) = [p ⊕ q = k] σ(p, q)`. -/
def psi (k p q : Blk) : ℤ := if bxor p q = k then sgn p q else 0

/-- The row choice `R` of (30). -/
def Rx (x y u v : Blk) : ℤ := ∑ k : Blk, psi k x y * psi k v u

/-- The column choice `C` of (30). -/
def Cx (x y u v : Blk) : ℤ := ∑ k : Blk, psi k x u * psi k v y

theorem blk_eq_iff (p q : Blk) : p = q ↔ p 0 = q 0 ∧ p 1 = q 1 ∧ p 2 = q 2 := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨h0, h1, h2⟩
    funext j
    fin_cases j <;> assumption

theorem bxor_eq_iff (p q p' q' : Blk) :
    bxor p q = bxor p' q' ↔
      (xor (p 0) (q 0) = xor (p' 0) (q' 0) ∧ xor (p 1) (q 1) = xor (p' 1) (q' 1) ∧
        xor (p 2) (q 2) = xor (p' 2) (q' 2)) := by
  rw [blk_eq_iff]; rfl

theorem sgn_mul_self (p q : Blk) : sgn p q * sgn p q = 1 := by
  unfold sgn; split <;> norm_num

theorem abs_sgn (p q : Blk) : |sgn p q| = 1 := by
  unfold sgn; split <;> simp

/-- Closed form of `R`. -/
theorem Rx_eq (x y u v : Blk) :
    Rx x y u v = if bxor x y = bxor v u then sgn x y * sgn v u else 0 := by
  unfold Rx psi
  simp only [ite_mul, mul_ite, mul_zero, zero_mul]
  rw [Finset.sum_ite_eq]
  simp only [mem_univ, if_true]

/-- Closed form of `C`. -/
theorem Cx_eq (x y u v : Blk) :
    Cx x y u v = if bxor x u = bxor v y then sgn x u * sgn v y else 0 := by
  unfold Cx psi
  simp only [ite_mul, mul_ite, mul_zero, zero_mul]
  rw [Finset.sum_ite_eq]
  simp only [mem_univ, if_true]

theorem abs_Rx_le (x y u v : Blk) : |Rx x y u v| ≤ 1 := by
  rw [Rx_eq]; split
  · rw [abs_mul, abs_sgn, abs_sgn]; norm_num
  · simp

theorem abs_Cx_le (x y u v : Blk) : |Cx x y u v| ≤ 1 := by
  rw [Cx_eq]; split
  · rw [abs_mul, abs_sgn, abs_sgn]; norm_num
  · simp

/-- The eight-square identity on bits: (28) with the blocks written out. -/
private theorem eightSquare_bits : ∀ p1 p2 p3 q1 q2 q3 r1 r2 r3 s1 s2 s3 : Bool,
    (xor p1 q1 = xor r1 s1 ∧ xor p2 q2 = xor r2 s2 ∧ xor p3 q3 = xor r3 s3) →
    ¬ (q1 = s1 ∧ q2 = s2 ∧ q3 = s3) →
    (if phiB p1 p2 p3 q1 q2 q3 then (-1 : ℤ) else 1) * (if phiB r1 r2 r3 s1 s2 s3 then -1 else 1) +
      (if phiB p1 p2 p3 s1 s2 s3 then -1 else 1) * (if phiB r1 r2 r3 q1 q2 q3 then -1 else 1) = 0 := by
  decide +kernel

/-- eq. (28), the eight-square identity (Degen 1818, Graves 1843): for `p ⊕ q = p' ⊕ q'` and `q ≠ q'`,
`σ(p, q) σ(p', q') + σ(p, q') σ(p', q) = 0`. -/
theorem eightSquare (p q p' q' : Blk) (h : bxor p q = bxor p' q') (hq : q ≠ q') :
    sgn p q * sgn p' q' + sgn p q' * sgn p' q = 0 := by
  rw [bxor_eq_iff] at h
  rw [Ne, blk_eq_iff] at hq
  exact eightSquare_bits _ _ _ _ _ _ _ _ _ _ _ _ h hq

/-- The crossing identity on bits. -/
private theorem crossing_bits : ∀ x1 x2 x3 y1 y2 y3 u1 u2 u3 v1 v2 v3 : Bool,
    (if (xor x1 y1 = xor v1 u1 ∧ xor x2 y2 = xor v2 u2 ∧ xor x3 y3 = xor v3 u3) then
        (if phiB x1 x2 x3 y1 y2 y3 then (-1 : ℤ) else 1) * (if phiB v1 v2 v3 u1 u2 u3 then -1 else 1)
      else 0) +
    (if (xor x1 u1 = xor v1 y1 ∧ xor x2 u2 = xor v2 y2 ∧ xor x3 u3 = xor v3 y3) then
        (if phiB x1 x2 x3 u1 u2 u3 then (-1 : ℤ) else 1) * (if phiB v1 v2 v3 y1 y2 y3 then -1 else 1)
      else 0) =
    if (x1 = v1 ∧ x2 = v2 ∧ x3 = v3) ∧ (y1 = u1 ∧ y2 = u2 ∧ y3 = u3) then 2 else 0 := by
  decide +kernel

/-- eq. (31), the crossing identity: `R + C = 2 [x = v][y = u]`. -/
theorem crossing (x y u v : Blk) :
    Rx x y u v + Cx x y u v = if x = v ∧ y = u then 2 else 0 := by
  rw [Rx_eq, Cx_eq]
  convert crossing_bits (x 0) (x 1) (x 2) (y 0) (y 1) (y 2) (u 0) (u 1) (u 2) (v 0) (v 1) (v 2)
    using 3
  · exact bxor_eq_iff _ _ _ _
  · rfl
  · exact bxor_eq_iff _ _ _ _
  · rfl
  · exact blk_eq_iff _ _
  · exact blk_eq_iff _ _

end Factoring.Aux
