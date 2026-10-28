/-
Lemma 2 of the paper (§4): two crossing equalities as a sum of `t + 1` cheaper functions, `t = ⌈λ/3⌉`.

For strings `x, y, u, v` of `λ` bits, padded with zeros to `t` blocks of 3 bits (`blk`), the pieces `A_0, …, A_t`
are the coefficients in `∏_s (R(x_s, y_s, u_s, v_s) + T · C(x_s, y_s, u_s, v_s)) = ∑_i A_i T^i` (Definition 5,
`pieceA`).  Then:

* (a) `sum_pieceA`: `A_0 + … + A_t = 2^t [x = v][y = u]`; `abs_pieceA_le`: `|A_i| ≤ 2^t`.
* (b) `eval_rowFac`: `A_i`, as a function of `(x, y)` and `(u, v)`, is the value of the explicit factorization
  `rowFac λ i` through `cRow λ i = min(2λ, 4t + 3i)` bits; `eval_colFac`: as a function of `(x, u)` and `(y, v)`,
  of `colFac λ i` through `cCol λ i = min(2λ, 7t − 3i)` bits (for `i ≤ t`).  Also as `FactorsThrough` statements.
* (c) `cRow_le`, `cCol_le`, `cRow_add_cCol`: both are at most `2λ`, and `3 (cRow + cCol) ≤ 11λ + 24`, i.e.
  `cRow + cCol ≤ 4ρλ + 8` with `ρ = 11/12`.

**How (b) is built.**  `coefV t c e j` is the coefficient of `T^j` in `∏_s (c_s + T e_s)`, defined by recursion on
the last factor.  If each `c_s` factors through 3 bits and each `e_s` through 6, then `coefV t c e j` factors through
`4t + 3j` bits (`coefFac`): the recursion `A' = A·c + A_{-1}·e` costs `(4t + 3j) + 3 = (4t + 3(j−1)) + 6` bits for
either term and one selector bit for the sum.  Row-wise `R` is the cheap factor (3 bits, `psiFac`) and `C` the
expensive one (6 bits, trivially); column-wise the roles are exchanged, and `coefV_swap` turns "`j` blocks with `R`"
into "`t − j` blocks with `C`".  This is the paper's factorization through `t + 3(t − i) + 6i` bits, with the set
`Q` spread over one selector bit per block.

Not an audit surface.
-/
module

public import FactoringAux.Cross
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity

@[expose] public section

namespace Factoring.Aux

open Finset

/-! ### Coefficients of a product of linear factors -/

/-- `coefV t c e j`: the coefficient of `T^j` in `∏_{s < t} (c s + T · e s)`, i.e. the sum over the sets `Q` of
`j` blocks of `∏_{s ∈ Q} e s · ∏_{s ∉ Q} c s`.  Recursion on the last factor. -/
def coefV : (t : ℕ) → (Fin t → ℤ) → (Fin t → ℤ) → ℕ → ℤ
  | 0, _, _, j => if j = 0 then 1 else 0
  | t + 1, c, e, 0 => coefV t (Fin.init c) (Fin.init e) 0 * c (Fin.last t)
  | t + 1, c, e, j + 1 =>
      coefV t (Fin.init c) (Fin.init e) (j + 1) * c (Fin.last t) +
        coefV t (Fin.init c) (Fin.init e) j * e (Fin.last t)

theorem coefV_eq_zero : ∀ (t : ℕ) (c e : Fin t → ℤ) (j : ℕ), t < j → coefV t c e j = 0
  | 0, _, _, j, hj => by simp [coefV]; omega
  | t + 1, c, e, 0, hj => by omega
  | t + 1, c, e, j + 1, hj => by
      simp only [coefV]
      rw [coefV_eq_zero t _ _ (j + 1) (by omega), coefV_eq_zero t _ _ j (by omega)]
      ring

/-- Setting `T = 1`: the coefficients sum to the product. -/
theorem coefV_sum : ∀ (t : ℕ) (c e : Fin t → ℤ),
    ∑ j ∈ range (t + 1), coefV t c e j = ∏ s, (c s + e s)
  | 0, c, e => by simp [coefV]
  | t + 1, c, e => by
      have ih := coefV_sum t (Fin.init c) (Fin.init e)
      have hz := coefV_eq_zero t (Fin.init c) (Fin.init e) (t + 1) (by omega)
      have h2 : ∑ j ∈ range (t + 1), coefV t (Fin.init c) (Fin.init e) (j + 1) +
          coefV t (Fin.init c) (Fin.init e) 0 = ∑ j ∈ range (t + 1), coefV t (Fin.init c) (Fin.init e) j := by
        rw [← Finset.sum_range_succ', Finset.sum_range_succ, hz, add_zero]
      rw [Finset.sum_range_succ', Fin.prod_univ_castSucc]
      simp only [coefV, Finset.sum_add_distrib, ← Finset.sum_mul]
      have ih' : ∑ j ∈ range (t + 1), coefV t (Fin.init c) (Fin.init e) j =
          ∏ s : Fin t, (c (Fin.castSucc s) + e (Fin.castSucc s)) := ih
      rw [← ih']
      linear_combination (c (Fin.last t)) * h2

/-- Exchanging the two factors: `j` blocks with `c` are `t − j` blocks with `e`. -/
theorem coefV_swap : ∀ (t : ℕ) (c e : Fin t → ℤ) (j : ℕ), j ≤ t → coefV t e c j = coefV t c e (t - j)
  | 0, c, e, j, hj => by
      obtain rfl : j = 0 := by omega
      simp [coefV]
  | t + 1, c, e, 0, _ => by
      rw [Nat.sub_zero]
      simp only [coefV]
      rw [coefV_swap t (Fin.init c) (Fin.init e) 0 (Nat.zero_le _),
        coefV_eq_zero t (Fin.init c) (Fin.init e) (t + 1) (by omega), Nat.sub_zero]
      ring
  | t + 1, c, e, j + 1, hj => by
      rw [show t + 1 - (j + 1) = t - j by omega]
      rcases Nat.lt_or_ge j t with h | h
      · obtain ⟨m, hm⟩ : ∃ m, t - j = m + 1 := ⟨t - j - 1, by omega⟩
        rw [hm]
        simp only [coefV]
        rw [coefV_swap t _ _ (j + 1) (by omega), coefV_swap t _ _ j (by omega),
          show t - (j + 1) = m by omega, hm]
        ring
      · obtain rfl : j = t := by omega
        rw [Nat.sub_self]
        simp only [coefV]
        rw [coefV_eq_zero j (Fin.init e) (Fin.init c) (j + 1) (by omega),
          coefV_swap j (Fin.init c) (Fin.init e) j le_rfl, Nat.sub_self]
        ring

/-- With factors bounded by `1`, `|coefV t c e j| ≤ (t choose j)`. -/
theorem abs_coefV_le : ∀ (t : ℕ) (c e : Fin t → ℤ), (∀ s, |c s| ≤ 1) → (∀ s, |e s| ≤ 1) →
    ∀ j, |coefV t c e j| ≤ (t.choose j : ℤ)
  | 0, c, e, _, _, j => by
      rcases j with _ | j <;> simp [coefV]
  | t + 1, c, e, hc, he, 0 => by
      simp only [coefV, Nat.choose_zero_right, Nat.cast_one]
      have ih := abs_coefV_le t (Fin.init c) (Fin.init e) (fun s => hc _) (fun s => he _) 0
      rw [Nat.choose_zero_right, Nat.cast_one] at ih
      rw [abs_mul]
      calc _ ≤ (1 : ℤ) * 1 := mul_le_mul ih (hc _) (abs_nonneg _) zero_le_one
        _ = 1 := by norm_num
  | t + 1, c, e, hc, he, j + 1 => by
      simp only [coefV]
      have ih1 := abs_coefV_le t (Fin.init c) (Fin.init e) (fun s => hc _) (fun s => he _) (j + 1)
      have ih2 := abs_coefV_le t (Fin.init c) (Fin.init e) (fun s => hc _) (fun s => he _) j
      rw [Nat.choose_succ_succ', Nat.cast_add]
      calc _ ≤ |coefV t (Fin.init c) (Fin.init e) (j + 1) * c (Fin.last t)| +
              |coefV t (Fin.init c) (Fin.init e) j * e (Fin.last t)| := abs_add_le _ _
        _ = |coefV t (Fin.init c) (Fin.init e) (j + 1)| * |c (Fin.last t)| +
              |coefV t (Fin.init c) (Fin.init e) j| * |e (Fin.last t)| := by rw [abs_mul, abs_mul]
        _ ≤ (t.choose (j + 1) : ℤ) * 1 + (t.choose j : ℤ) * 1 := by
              gcongr
              · exact hc _
              · exact he _
        _ = _ := by ring

/-! ### The explicit factorization of the coefficients -/

/-- If every cheap factor `c_s` is the value of `cF` (3 bits) and every expensive one `e_s` of `eF` (6 bits), the
coefficient `coefV t c e j` is the value of a factorization through `4t + 3j` bits. -/
def coefFac {α β : Type*} (cF : Fac ℤ α β 3) (eF : Fac ℤ α β 6) :
    (t j : ℕ) → Fac ℤ (Fin t → α) (Fin t → β) (4 * t + 3 * j)
  | 0, 0 => Fac.one.cast (by norm_num)
  | 0, _ + 1 => Fac.zero _
  | t + 1, 0 =>
      ((((coefFac cF eF t 0).comp (fun x => Fin.init x) (fun y => Fin.init y)).mul
          (cF.comp (fun x => x (Fin.last t)) (fun y => y (Fin.last t)))).add (Fac.zero _)).cast
        (by ring)
  | t + 1, j + 1 =>
      ((((((coefFac cF eF t (j + 1)).comp (fun x => Fin.init x) (fun y => Fin.init y)).mul
          (cF.comp (fun x => x (Fin.last t)) (fun y => y (Fin.last t)))).cast
            (show 4 * t + 3 * (j + 1) + 3 = 4 * t + 3 * j + 6 by ring)).add
        (((coefFac cF eF t j).comp (fun x => Fin.init x) (fun y => Fin.init y)).mul
          (eF.comp (fun x => x (Fin.last t)) (fun y => y (Fin.last t))))).cast (by ring))

theorem eval_coefFac {α β : Type*} (cF : Fac ℤ α β 3) (eF : Fac ℤ α β 6) :
    ∀ (t j : ℕ) (x : Fin t → α) (y : Fin t → β),
      (coefFac cF eF t j).eval x y =
        coefV t (fun s => cF.eval (x s) (y s)) (fun s => eF.eval (x s) (y s)) j
  | 0, 0, x, y => by simp [coefFac, coefV]
  | 0, j + 1, x, y => by simp [coefFac, coefV]
  | t + 1, 0, x, y => by
      simp only [coefFac, coefV, Fac.eval_cast, Fac.eval_add, Fac.eval_mul, Fac.eval_comp, Fac.eval_zero,
        add_zero, eval_coefFac cF eF t 0]
      rfl
  | t + 1, j + 1, x, y => by
      simp only [coefFac, coefV, Fac.eval_cast, Fac.eval_add, Fac.eval_mul, Fac.eval_comp,
        eval_coefFac cF eF t (j + 1), eval_coefFac cF eF t j]
      rfl

/-! ### Strings, blocks, pieces -/

/-- `t = ⌈λ/3⌉`, the number of blocks. -/
def tB (lam : ℕ) : ℕ := (lam + 2) / 3

/-- Block `s` of a `λ`-bit string, padded with zeros (Definition 5). -/
def blk {lam : ℕ} (x : Bits lam) (s : Fin (tB lam)) : Blk :=
  fun j => if h : 3 * s.val + j.val < lam then x ⟨3 * s.val + j.val, h⟩ else false

/-- The blocks determine the string. -/
theorem blk_ext {lam : ℕ} {x v : Bits lam} : (∀ s, blk x s = blk v s) ↔ x = v := by
  constructor
  · intro h
    funext i
    have hs : i.val / 3 < tB lam := by unfold tB; omega
    have hj : i.val % 3 < 3 := Nat.mod_lt _ (by norm_num)
    have := congrFun (h ⟨i.val / 3, hs⟩) ⟨i.val % 3, hj⟩
    have hi : 3 * (i.val / 3) + i.val % 3 = i.val := Nat.div_add_mod _ _
    simp only [blk] at this
    rw [dif_pos (show 3 * (i.val / 3) + i.val % 3 < lam by omega),
      dif_pos (show 3 * (i.val / 3) + i.val % 3 < lam by omega)] at this
    convert this using 2 <;> exact Fin.ext hi.symm
  · rintro rfl _
    rfl

/-- Definition 5: the pieces `A_i`, coefficients of `∏_s (R_s + T C_s)`. -/
def pieceA (lam i : ℕ) (x y u v : Bits lam) : ℤ :=
  coefV (tB lam) (fun s => Rx (blk x s) (blk y s) (blk u s) (blk v s))
    (fun s => Cx (blk x s) (blk y s) (blk u s) (blk v s)) i

/-- Lemma 2(a): `A_0 + ⋯ + A_t = 2^t [x = v][y = u]`. -/
theorem sum_pieceA (lam : ℕ) (x y u v : Bits lam) :
    ∑ i ∈ range (tB lam + 1), pieceA lam i x y u v = 2 ^ tB lam * if x = v ∧ y = u then 1 else 0 := by
  unfold pieceA
  rw [coefV_sum]
  simp only [crossing]
  rw [Fintype.prod_ite_zero, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have : (∀ s, blk x s = blk v s ∧ blk y s = blk u s) ↔ x = v ∧ y = u := by
    rw [← blk_ext, ← blk_ext]
    exact ⟨fun h => ⟨fun s => (h s).1, fun s => (h s).2⟩, fun h s => ⟨h.1 s, h.2 s⟩⟩
  by_cases h : x = v ∧ y = u
  · rw [if_pos (this.mpr h), if_pos h, mul_one]
  · rw [if_neg (mt this.mp h), if_neg h, mul_zero]

/-- Lemma 2(a): `|A_i| ≤ 2^t` (indeed `≤ (t choose i)`). -/
theorem abs_pieceA_le (lam i : ℕ) (x y u v : Bits lam) : |pieceA lam i x y u v| ≤ 2 ^ tB lam := by
  have h := abs_coefV_le (tB lam) (fun s => Rx (blk x s) (blk y s) (blk u s) (blk v s))
    (fun s => Cx (blk x s) (blk y s) (blk u s) (blk v s)) (fun _ => abs_Rx_le _ _ _ _)
    (fun _ => abs_Cx_le _ _ _ _) i
  refine h.trans ?_
  exact_mod_cast Nat.choose_le_two_pow _ _

/-! ### The two factorizations (Lemma 2(b)) -/

/-- `ψ` as a factorization through the 3 bits of `k`: value at `((a, b), (c, d))` is `∑_k ψ_k(a, b) ψ_k(d, c)`.
Row-wise (`(x, y)`, `(u, v)`) this is `R`; column-wise (`(x, u)`, `(y, v)`) it is `C`. -/
def psiFac : Fac ℤ (Blk × Blk) (Blk × Blk) 3 := ⟨fun p k => psi k p.1 p.2, fun q k => psi k q.2 q.1⟩

/-- Two blocks are six bits. -/
def blk2Equiv : Blk × Blk ≃ Bits 6 := Fin.appendEquiv 3 3

/-- `C` row-wise, through the six bits of `(x, y)`. -/
def rowExp : Fac ℤ (Blk × Blk) (Blk × Blk) 6 := Fac.ofEquiv blk2Equiv (fun p q => Cx p.1 p.2 q.1 q.2)

/-- `R` column-wise, through the six bits of `(x, u)`. -/
def colExp : Fac ℤ (Blk × Blk) (Blk × Blk) 6 := Fac.ofEquiv blk2Equiv (fun p q => Rx p.1 q.1 p.2 q.2)

/-- Row-wise: the blocks of `(x, y)`, of `(u, v)`. -/
def rowSide {lam : ℕ} (p : Bits lam × Bits lam) (s : Fin (tB lam)) : Blk × Blk := (blk p.1 s, blk p.2 s)

/-- `A_i` row-wise through `4t + 3i` bits (with no cap at `2λ`). -/
def rowFacB (lam i : ℕ) : Fac ℤ (Bits lam × Bits lam) (Bits lam × Bits lam) (4 * tB lam + 3 * i) :=
  (coefFac psiFac rowExp (tB lam) i).comp rowSide rowSide

theorem eval_rowFacB (lam i : ℕ) (p q : Bits lam × Bits lam) :
    (rowFacB lam i).eval p q = pieceA lam i p.1 p.2 q.1 q.2 := by
  simp only [rowFacB, Fac.eval_comp, eval_coefFac, pieceA, rowExp, Fac.eval_ofEquiv]
  rfl

/-- `coefV t C R j` column-wise through `4t + 3j` bits: `j` blocks with `R`, so this is `A_{t−j}`. -/
def colFacB (lam j : ℕ) : Fac ℤ (Bits lam × Bits lam) (Bits lam × Bits lam) (4 * tB lam + 3 * j) :=
  (coefFac psiFac colExp (tB lam) j).comp rowSide rowSide

theorem eval_colFacB (lam j : ℕ) (hj : j ≤ tB lam) (p q : Bits lam × Bits lam) :
    (colFacB lam j).eval p q = pieceA lam (tB lam - j) p.1 q.1 p.2 q.2 := by
  simp only [colFacB, Fac.eval_comp, eval_coefFac, pieceA, colExp, Fac.eval_ofEquiv]
  exact coefV_swap _ _ _ _ hj

/-- `c^row_i = min(2λ, 4t + 3i)`. -/
def cRow (lam i : ℕ) : ℕ := min (2 * lam) (4 * tB lam + 3 * i)

/-- `c^col_i = min(2λ, 7t − 3i)`, written `4t + 3(t − i)` (equal for `i ≤ t`, `cCol_eq`). -/
def cCol (lam i : ℕ) : ℕ := min (2 * lam) (4 * tB lam + 3 * (tB lam - i))

theorem cCol_eq (lam i : ℕ) (hi : i ≤ tB lam) : cCol lam i = min (2 * lam) (7 * tB lam - 3 * i) := by
  unfold cCol; congr 1; omega

/-- Two strings are `2λ` bits. -/
def strPairEquiv (lam : ℕ) : Bits lam × Bits lam ≃ Bits (lam + lam) := Fin.appendEquiv lam lam

/-- Lemma 2(b), row-wise: `A_i` as a function of `(x, y)` and `(u, v)`, through `cRow λ i` bits. -/
def rowFac (lam i : ℕ) : Fac ℤ (Bits lam × Bits lam) (Bits lam × Bits lam) (cRow lam i) :=
  if h : 4 * tB lam + 3 * i ≤ 2 * lam then
    (rowFacB lam i).cast (by unfold cRow; omega)
  else
    (Fac.ofEquiv (strPairEquiv lam) (fun p q => pieceA lam i p.1 p.2 q.1 q.2)).cast (by unfold cRow; omega)

theorem eval_rowFac (lam i : ℕ) (p q : Bits lam × Bits lam) :
    (rowFac lam i).eval p q = pieceA lam i p.1 p.2 q.1 q.2 := by
  unfold rowFac
  split
  · rw [Fac.eval_cast, eval_rowFacB]
  · rw [Fac.eval_cast, Fac.eval_ofEquiv]

/-- Lemma 2(b), column-wise: `A_i` as a function of `(x, u)` and `(y, v)`, through `cCol λ i` bits (`i ≤ t`). -/
def colFac (lam i : ℕ) : Fac ℤ (Bits lam × Bits lam) (Bits lam × Bits lam) (cCol lam i) :=
  if h : 4 * tB lam + 3 * (tB lam - i) ≤ 2 * lam then
    (colFacB lam (tB lam - i)).cast (by unfold cCol; omega)
  else
    (Fac.ofEquiv (strPairEquiv lam) (fun p q => pieceA lam i p.1 q.1 p.2 q.2)).cast (by unfold cCol; omega)

theorem eval_colFac (lam i : ℕ) (hi : i ≤ tB lam) (p q : Bits lam × Bits lam) :
    (colFac lam i).eval p q = pieceA lam i p.1 q.1 p.2 q.2 := by
  unfold colFac
  split
  · rw [Fac.eval_cast, eval_colFacB _ _ (Nat.sub_le _ _), Nat.sub_sub_self hi]
  · rw [Fac.eval_cast, Fac.eval_ofEquiv]

/-- Lemma 2(b), row-wise, as Definition 1. -/
theorem pieceA_factors_row (lam i : ℕ) :
    FactorsThrough (fun p q : Bits lam × Bits lam => pieceA lam i p.1 p.2 q.1 q.2) (cRow lam i) :=
  ⟨rowFac lam i, fun p q => (eval_rowFac lam i p q).symm⟩

/-- Lemma 2(b), column-wise, as Definition 1: the arguments are `(x, u)` and `(y, v)`. -/
theorem pieceA_factors_col (lam i : ℕ) (hi : i ≤ tB lam) :
    FactorsThrough (fun p q : Bits lam × Bits lam => pieceA lam i p.1 q.1 p.2 q.2) (cCol lam i) :=
  ⟨colFac lam i, fun p q => (eval_colFac lam i hi p q).symm⟩

/-! ### Lemma 2(c) -/

theorem cRow_le (lam i : ℕ) : cRow lam i ≤ 2 * lam := min_le_left _ _

theorem cCol_le (lam i : ℕ) : cCol lam i ≤ 2 * lam := min_le_left _ _

/-- Lemma 2(c): `c^row_i + c^col_i ≤ 11t ≤ 11λ/3 + 22/3`, so `3 (c^row_i + c^col_i) ≤ 11λ + 24`. -/
theorem cRow_add_cCol (lam i : ℕ) (hi : i ≤ tB lam) : 3 * (cRow lam i + cCol lam i) ≤ 11 * lam + 24 := by
  have h1 : cRow lam i ≤ 4 * tB lam + 3 * i := min_le_right _ _
  have h2 : cCol lam i ≤ 4 * tB lam + 3 * (tB lam - i) := min_le_right _ _
  unfold tB at *
  omega

end Factoring.Aux
