/-
The block functions of Lemma 2 (`sgn`, `ψ`, `R`, `C`) on 3-bit codes, as numbers, with expressions.

* `bitN X i = X / 2^i % 2`; `par3`, `par4`: parities of three (four) codes on each of the 3 bits, i.e.
  `bxor p q = k` and `bxor x y = bxor v u` (`par3_iff`, `par4_iff`).
* `phiN`, `sgnN m P Q` (`m − 1` for `−1`), `psiN`, `RxN`, `CxN`; **`sgnN_cast`, `psiN_cast`, `RxN_cast`, `CxN_cast`**:
  their images in `ZMod m` are those of `sgn`, `psi`, `Rx`, `Cx` at `bdec 3`.
* Expressions `bitE`, `par3E`, `par4E`, `phiE`, `sgnE`, `psiE`, `RxE`, `CxE` with exact value lemmas.

Not an audit surface.
-/
module

public import FactoringAux.EngineNet
public import FactoringAux.Cross

@[expose] public section

namespace Factoring.Aux

open Finset

/-- Bit `i` of `X`. -/
def bitN (X i : ℕ) : ℕ := X / 2 ^ i % 2

theorem bitN_eq (X i : ℕ) : bitN X i = (X.testBit i).toNat := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (X / 2 ^ i) with h | h <;> simp [bitN, h]

/-- The three bits of three codes have even sum. -/
def par3 (X Y Z : ℕ) : Prop := ∀ i < 3, (bitN X i + bitN Y i + bitN Z i) % 2 = 0

/-- The three bits of four codes have even sum. -/
def par4 (X Y Z W : ℕ) : Prop := ∀ i < 3, (bitN X i + bitN Y i + bitN Z i + bitN W i) % 2 = 0

instance (X Y Z : ℕ) : Decidable (par3 X Y Z) := by unfold par3; infer_instance
instance (X Y Z W : ℕ) : Decidable (par4 X Y Z W) := by unfold par4; infer_instance

theorem blk3_ext {p q : Blk} : p = q ↔ ∀ i (h : i < 3), p ⟨i, h⟩ = q ⟨i, h⟩ := by
  constructor
  · rintro rfl _ _; rfl
  · intro h; funext i; exact h i.1 i.2

theorem par3_iff (P Q K : ℕ) : par3 P Q K ↔ bxor (bdec 3 P) (bdec 3 Q) = bdec 3 K := by
  rw [blk3_ext]
  refine forall_congr' fun i => forall_congr' fun _ => ?_
  simp only [bxor, bdec, bitN_eq]
  cases P.testBit i <;> cases Q.testBit i <;> cases K.testBit i <;> decide

theorem par4_iff (X Y V U : ℕ) : par4 X Y V U ↔ bxor (bdec 3 X) (bdec 3 Y) = bxor (bdec 3 V) (bdec 3 U) := by
  rw [blk3_ext]
  refine forall_congr' fun i => forall_congr' fun _ => ?_
  simp only [bxor, bdec, bitN_eq]
  cases X.testBit i <;> cases Y.testBit i <;> cases V.testBit i <;> cases U.testBit i <;> decide

/-- The exponent of the sign. -/
def phiN (P Q : ℕ) : ℕ :=
  (bitN P 0 * bitN Q 0 + bitN P 0 * bitN Q 1 + bitN P 0 * bitN Q 2 + bitN P 1 * bitN Q 1 + bitN P 1 * bitN Q 2 +
    bitN P 2 * bitN Q 2 + bitN Q 0 * bitN P 1 * bitN P 2 + bitN P 0 * bitN Q 1 * bitN P 2 +
    bitN P 0 * bitN P 1 * bitN Q 2) % 2

theorem phiN_iff (P Q : ℕ) : phiN P Q = 1 ↔ phiB (bdec 3 P 0) (bdec 3 P 1) (bdec 3 P 2) (bdec 3 Q 0) (bdec 3 Q 1)
    (bdec 3 Q 2) = true := by
  simp only [phiN, bdec, bitN_eq]
  simp only [Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two]
  cases P.testBit 0 <;> cases P.testBit 1 <;> cases P.testBit 2 <;> cases Q.testBit 0 <;> cases Q.testBit 1 <;>
    cases Q.testBit 2 <;> decide

/-- The sign, `m − 1` standing for `−1`. -/
def sgnN (m P Q : ℕ) : ℕ := if phiN P Q = 1 then m - 1 else 1

/-- `ψ`. -/
def psiN (m K P Q : ℕ) : ℕ := if par3 P Q K then sgnN m P Q else 0

/-- `R`, closed form. -/
def RxN (m X Y U V : ℕ) : ℕ := if par4 X Y V U then sgnN m X Y * sgnN m V U % m else 0

/-- `C`, closed form. -/
def CxN (m X Y U V : ℕ) : ℕ := if par4 X U V Y then sgnN m X U * sgnN m V Y % m else 0

variable {m : ℕ}

theorem sgnN_cast (hm : 0 < m) (P Q : ℕ) :
    ((sgnN m P Q : ℕ) : ZMod m) = ((sgn (bdec 3 P) (bdec 3 Q) : ℤ) : ZMod m) := by
  unfold sgnN sgn
  by_cases h : phiN P Q = 1
  · rw [if_pos h, if_pos ((phiN_iff P Q).mp h)]
    rw [Nat.cast_sub (by omega), ZMod.natCast_self]
    simp
  · rw [if_neg h, if_neg (fun h' => h ((phiN_iff P Q).mpr h'))]
    simp

theorem psiN_cast (hm : 0 < m) (K P Q : ℕ) :
    ((psiN m K P Q : ℕ) : ZMod m) = ((psi (bdec 3 K) (bdec 3 P) (bdec 3 Q) : ℤ) : ZMod m) := by
  unfold psiN psi
  by_cases h : par3 P Q K
  · rw [if_pos h, if_pos ((par3_iff P Q K).mp h), sgnN_cast hm]
  · rw [if_neg h, if_neg (fun h' => h ((par3_iff P Q K).mpr h'))]
    simp

theorem RxN_cast (hm : 0 < m) (X Y U V : ℕ) :
    ((RxN m X Y U V : ℕ) : ZMod m) = ((Rx (bdec 3 X) (bdec 3 Y) (bdec 3 U) (bdec 3 V) : ℤ) : ZMod m) := by
  rw [Rx_eq]
  unfold RxN
  by_cases h : par4 X Y V U
  · rw [if_pos h, if_pos ((par4_iff X Y V U).mp h), ZMod.natCast_mod, Nat.cast_mul, sgnN_cast hm, sgnN_cast hm,
      Int.cast_mul]
  · rw [if_neg h, if_neg (fun h' => h ((par4_iff X Y V U).mpr h'))]
    simp

theorem CxN_cast (hm : 0 < m) (X Y U V : ℕ) :
    ((CxN m X Y U V : ℕ) : ZMod m) = ((Cx (bdec 3 X) (bdec 3 Y) (bdec 3 U) (bdec 3 V) : ℤ) : ZMod m) := by
  rw [Cx_eq]
  unfold CxN
  by_cases h : par4 X U V Y
  · rw [if_pos h, if_pos ((par4_iff X U V Y).mp h), ZMod.natCast_mod, Nat.cast_mul, sgnN_cast hm, sgnN_cast hm,
      Int.cast_mul]
  · rw [if_neg h, if_neg (fun h' => h ((par4_iff X U V Y).mpr h'))]
    simp

theorem sgnN_lt (hm : 1 < m) (P Q : ℕ) : sgnN m P Q < m := by unfold sgnN; split_ifs <;> omega

theorem psiN_lt (hm : 1 < m) (K P Q : ℕ) : psiN m K P Q < m := by
  unfold psiN; split_ifs
  · exact sgnN_lt hm P Q
  · omega

theorem RxN_lt (hm : 1 < m) (X Y U V : ℕ) : RxN m X Y U V < m := by
  unfold RxN; split_ifs
  · exact Nat.mod_lt _ (by omega)
  · omega

theorem CxN_lt (hm : 1 < m) (X Y U V : ℕ) : CxN m X Y U V < m := by
  unfold CxN; split_ifs
  · exact Nat.mod_lt _ (by omega)
  · omega

/-! ### Expressions -/

namespace Ex

/-- Bit `i` (`i < 3`) of `e`. -/
def bitE (e : Ex) (i : ℕ) : Ex := .mod (.div e (.lit (2 ^ i))) (.lit 2)

/-- `[(b0 + b1 + b2) mod 2 = 0]` on each bit. -/
def par3E (e f h : Ex) : Ex :=
  .mul (.mul (eqE (.mod (.add (.add (bitE e 0) (bitE f 0)) (bitE h 0)) (.lit 2)) (.lit 0))
    (eqE (.mod (.add (.add (bitE e 1) (bitE f 1)) (bitE h 1)) (.lit 2)) (.lit 0)))
    (eqE (.mod (.add (.add (bitE e 2) (bitE f 2)) (bitE h 2)) (.lit 2)) (.lit 0))

/-- The same for four codes. -/
def par4E (e f h k : Ex) : Ex :=
  .mul (.mul (eqE (.mod (.add (.add (.add (bitE e 0) (bitE f 0)) (bitE h 0)) (bitE k 0)) (.lit 2)) (.lit 0))
    (eqE (.mod (.add (.add (.add (bitE e 1) (bitE f 1)) (bitE h 1)) (bitE k 1)) (.lit 2)) (.lit 0)))
    (eqE (.mod (.add (.add (.add (bitE e 2) (bitE f 2)) (bitE h 2)) (bitE k 2)) (.lit 2)) (.lit 0))

/-- `phiN`. -/
def phiE (p q : Ex) : Ex :=
  .mod (.add (.add (.add (.add (.add (.add (.add (.add
    (.mul (bitE p 0) (bitE q 0)) (.mul (bitE p 0) (bitE q 1))) (.mul (bitE p 0) (bitE q 2)))
    (.mul (bitE p 1) (bitE q 1))) (.mul (bitE p 1) (bitE q 2))) (.mul (bitE p 2) (bitE q 2)))
    (.mul (.mul (bitE q 0) (bitE p 1)) (bitE p 2))) (.mul (.mul (bitE p 0) (bitE q 1)) (bitE p 2)))
    (.mul (.mul (bitE p 0) (bitE p 1)) (bitE q 2))) (.lit 2)

/-- `sgnN` (modulus variable `vm`). -/
def sgnE (vm : ℕ) (p q : Ex) : Ex := ifEq (phiE p q) (.lit 1) (.sub (.var vm) (.lit 1)) (.lit 1)

/-- `psiN`. -/
def psiE (vm : ℕ) (k p q : Ex) : Ex := ifEq (par3E p q k) (.lit 1) (sgnE vm p q) (.lit 0)

/-- `RxN`. -/
def RxE (vm : ℕ) (x y u v : Ex) : Ex :=
  ifEq (par4E x y v u) (.lit 1) (.mod (.mul (sgnE vm x y) (sgnE vm v u)) (.var vm)) (.lit 0)

/-- `CxN`. -/
def CxE (vm : ℕ) (x y u v : Ex) : Ex :=
  ifEq (par4E x u v y) (.lit 1) (.mod (.mul (sgnE vm x u) (sgnE vm v y)) (.var vm)) (.lit 0)

variable {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ}

theorem eval_bitE (e : Ex) (i : ℕ) : eval σ A (bitE e i) = bitN (eval σ A e) i := rfl

theorem forall_lt_three {P : ℕ → Prop} : (∀ i < 3, P i) ↔ P 0 ∧ P 1 ∧ P 2 := by
  constructor
  · intro h; exact ⟨h 0 (by norm_num), h 1 (by norm_num), h 2 (by norm_num)⟩
  · rintro ⟨h0, h1, h2⟩ i hi
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl <;> assumption

theorem ite3_mul (a b c : Prop) [Decidable a] [Decidable b] [Decidable c] :
    ((if a then 1 else 0) * (if b then 1 else 0) * (if c then 1 else 0) : ℕ) = if a ∧ b ∧ c then 1 else 0 := by
  by_cases ha : a <;> by_cases hb : b <;> by_cases hc : c <;> simp [ha, hb, hc]

theorem eval_par3E (e f h : Ex) :
    eval σ A (par3E e f h) = if par3 (eval σ A e) (eval σ A f) (eval σ A h) then 1 else 0 := by
  simp only [par3E, eval, eval_eqE, eval_bitE, par3, forall_lt_three]
  exact ite3_mul _ _ _

theorem eval_par4E (e f h k : Ex) :
    eval σ A (par4E e f h k) = if par4 (eval σ A e) (eval σ A f) (eval σ A h) (eval σ A k) then 1 else 0 := by
  simp only [par4E, eval, eval_eqE, eval_bitE, par4, forall_lt_three]
  exact ite3_mul _ _ _

theorem eval_phiE (p q : Ex) : eval σ A (phiE p q) = phiN (eval σ A p) (eval σ A q) := rfl

theorem eval_sgnE (vm : ℕ) (p q : Ex) : eval σ A (sgnE vm p q) = sgnN (σ vm) (eval σ A p) (eval σ A q) := by
  simp only [sgnE, eval_ifEq, eval_phiE, eval, sgnN]
  by_cases h : phiN (eval σ A p) (eval σ A q) = 1 <;> simp [h]

theorem eval_psiE (vm : ℕ) (k p q : Ex) :
    eval σ A (psiE vm k p q) = psiN (σ vm) (eval σ A k) (eval σ A p) (eval σ A q) := by
  simp only [psiE, eval_ifEq, eval_par3E, eval_sgnE, eval, psiN]
  split_ifs <;> simp_all

theorem eval_RxE (vm : ℕ) (x y u v : Ex) :
    eval σ A (RxE vm x y u v) = RxN (σ vm) (eval σ A x) (eval σ A y) (eval σ A u) (eval σ A v) := by
  simp only [RxE, eval_ifEq, eval_par4E, eval_sgnE, eval, RxN]
  split_ifs <;> simp_all

theorem eval_CxE (vm : ℕ) (x y u v : Ex) :
    eval σ A (CxE vm x y u v) = CxN (σ vm) (eval σ A x) (eval σ A y) (eval σ A u) (eval σ A v) := by
  simp only [CxE, eval_ifEq, eval_par4E, eval_sgnE, eval, CxN]
  split_ifs <;> simp_all

end Ex

end Factoring.Aux
