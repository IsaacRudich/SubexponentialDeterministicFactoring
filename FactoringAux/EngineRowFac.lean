/-
Lemma 2's row and column factorizations (`rowFacB`, `colFacB`) at codes: strings of `λ` bits are given by codes
`X < 2^λ`, the factor strings by codes `Q`.

* `append_bdec_iff`: two strings side by side are the string of `Q` iff `Q mod 2^(a+b) = X + 2^a Y`;
  `appendEquiv_symm_bdec`, `blk_bdec`, `bdec_mod`.
* `cvP`, `evRowL`, `evRowR`, `evColR`: the block functions of the decoder.
* **`rowFacB_l_code`, `rowFacB_r_code`, `colFacB_r_code`**: the factor functions as decoder runs (in `ZMod m`).

Not an audit surface.
-/
module

public import FactoringAux.EnginePieces
public import FactoringAux.EngineBlk

@[expose] public section

namespace Factoring.Aux

open Finset

theorem bdec_mod (c P : ℕ) : bdec c (P % 2 ^ c) = bdec c P := by
  funext i; simp [bdec, Nat.testBit_mod_two_pow, i.2]

theorem append_bdec_testBit (a b X Y : ℕ) (hX : X < 2 ^ a) (i : Fin (a + b)) :
    Fin.append (bdec a X) (bdec b Y) i = (2 ^ a * Y + X).testBit i := by
  refine Fin.addCases (fun i => ?_) (fun j => ?_) i
  · rw [Fin.append_left, Nat.testBit_two_pow_mul_add _ hX]
    simp [bdec, i.2]
  · rw [Fin.append_right, Nat.testBit_two_pow_mul_add _ hX]
    simp [bdec]

theorem append_bdec_iff (a b X Y Q : ℕ) (hX : X < 2 ^ a) (hY : Y < 2 ^ b) :
    Fin.append (bdec a X) (bdec b Y) = bdec (a + b) Q ↔ Q % 2 ^ (a + b) = X + 2 ^ a * Y := by
  have hN : 2 ^ a * Y + X < 2 ^ (a + b) := by
    rw [pow_add]
    have : 2 ^ a * Y + 2 ^ a ≤ 2 ^ a * 2 ^ b := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hY
    omega
  rw [show X + 2 ^ a * Y = 2 ^ a * Y + X by ring]
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_mod_two_pow]
    by_cases hi : i < a + b
    · have := congrFun h ⟨i, hi⟩
      rw [append_bdec_testBit a b X Y hX] at this
      simp only [bdec] at this
      simp [hi, this]
    · simp only [hi, decide_false, Bool.false_and]
      exact (Nat.testBit_lt_two_pow (lt_of_lt_of_le hN (Nat.pow_le_pow_right (by norm_num) (by omega)))).symm
  · intro h
    funext i
    rw [append_bdec_testBit a b X Y hX, ← h]
    simp [bdec, Nat.testBit_mod_two_pow, i.2]

theorem appendEquiv_symm_bdec (a b Q : ℕ) :
    (Fin.appendEquiv a b).symm (bdec (a + b) Q) = (bdec a Q, bdec b (Q / 2 ^ a)) := by
  simp only [Fin.appendEquiv_symm_apply]
  exact Prod.ext (Fac.bdec_low a b Q) (Fac.bdec_high a b Q)

theorem blk_bdec {lam X : ℕ} (hX : X < 2 ^ lam) (s : Fin (tB lam)) :
    blk (bdec lam X) s = bdec 3 (X / 2 ^ (3 * (s : ℕ))) := by
  funext j
  simp only [blk, bdec, Nat.testBit_div_two_pow]
  split_ifs with h
  · rw [Nat.add_comm]
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hX (Nat.pow_le_pow_right (by norm_num) (by omega)))]

/-! ### The block functions of the decoder -/

/-- `ψ` side: `ψ_k(P, Q)` on the blocks `s` of `X`, `Y`. -/
def cvP (m X Y s Qs : ℕ) : ℕ := psiN m Qs (X / 2 ^ (3 * s)) (Y / 2 ^ (3 * s))

/-- The expensive block, left side (both factorizations): `[Qs = (X_s, Y_s)]`. -/
def evL (X Y s Qs : ℕ) : ℕ := if Qs % 2 ^ (3 + 3) = X / 2 ^ (3 * s) % 2 ^ 3 + 2 ^ 3 * (Y / 2 ^ (3 * s) % 2 ^ 3) then 1 else 0

/-- The expensive block, right side of the row factorization: `C(θ₁, θ₂, U_s, V_s)`. -/
def evRowR (m U V s Qs : ℕ) : ℕ := CxN m Qs (Qs / 2 ^ 3) (U / 2 ^ (3 * s)) (V / 2 ^ (3 * s))

/-- The expensive block, right side of the column factorization: `R(θ₁, Q1_s, θ₂, Q2_s)`. -/
def evColR (m U V s Qs : ℕ) : ℕ := RxN m Qs (U / 2 ^ (3 * s)) (Qs / 2 ^ 3) (V / 2 ^ (3 * s))

theorem app6_iff (X Y Q : ℕ) (hX : X < 2 ^ 3) (hY : Y < 2 ^ 3) :
    Fin.append (bdec 3 X) (bdec 3 Y) = bdec 6 Q ↔ Q % 2 ^ (3 + 3) = X + 2 ^ 3 * Y :=
  append_bdec_iff 3 3 X Y Q hX hY

theorem app6_symm (Q : ℕ) : (Fin.appendEquiv 3 3).symm (bdec 6 Q) = (bdec 3 Q, bdec 3 (Q / 2 ^ 3)) :=
  appendEquiv_symm_bdec 3 3 Q

section Codes

variable {m lam X Y : ℕ}

theorem rowSide_bdec (hX : X < 2 ^ lam) (hY : Y < 2 ^ lam) :
    rowSide (bdec lam X, bdec lam Y) =
      fun k : Fin (tB lam) => ((bdec 3 (X / 2 ^ (3 * (k : ℕ))), bdec 3 (Y / 2 ^ (3 * (k : ℕ)))) : Blk × Blk) := by
  funext k
  simp only [rowSide, blk_bdec hX, blk_bdec hY]

theorem evL_cast (hm : 0 < m) (s Qs : ℕ) :
    ((evL X Y s Qs : ℕ) : ZMod m) =
      (((Fac.ofEquiv blk2Equiv (fun _ _ => (0 : ℤ)) : Fac ℤ (Blk × Blk) (Blk × Blk) 6).l
        (bdec 3 (X / 2 ^ (3 * s)), bdec 3 (Y / 2 ^ (3 * s))) (bdec 6 Qs) : ℤ) : ZMod m) := by
  have key : blk2Equiv (bdec 3 (X / 2 ^ (3 * s)), bdec 3 (Y / 2 ^ (3 * s))) = bdec 6 Qs ↔
      Qs % 2 ^ (3 + 3) = X / 2 ^ (3 * s) % 2 ^ 3 + 2 ^ 3 * (Y / 2 ^ (3 * s) % 2 ^ 3) := by
    show Fin.append (bdec 3 (X / 2 ^ (3 * s))) (bdec 3 (Y / 2 ^ (3 * s))) = bdec 6 Qs ↔ _
    rw [← bdec_mod 3 (X / 2 ^ (3 * s)), ← bdec_mod 3 (Y / 2 ^ (3 * s))]
    exact app6_iff _ _ Qs (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))
  simp only [Fac.ofEquiv]
  unfold evL
  by_cases h : blk2Equiv (bdec 3 (X / 2 ^ (3 * s)), bdec 3 (Y / 2 ^ (3 * s))) = bdec 6 Qs
  · rw [if_pos h, if_pos (key.mp h)]; simp
  · rw [if_neg h, if_neg (fun h' => h (key.mpr h'))]; simp

/-- **The left function of `rowFacB` at codes.** -/
theorem rowFacB_l_code (hm : 0 < m) (i : ℕ) (hX : X < 2 ^ lam) (hY : Y < 2 ^ lam) (Q : ℕ) :
    ((cfOut m (cfRun m Q (cvP m X Y) (evL X Y) (tB lam) (i * m + 1 % m)) : ℕ) : ZMod m) =
      (((rowFacB lam i).l (bdec lam X, bdec lam Y) (bdec _ Q) : ℤ) : ZMod m) := by
  rw [coefFac_l_run psiFac rowExp hm Q (fun s => ((bdec 3 (X / 2 ^ (3 * s)), bdec 3 (Y / 2 ^ (3 * s))) : Blk × Blk))
    (cvP m X Y) (evL X Y)]
  · obtain ⟨d1, d2⟩ := div_mod_pack (j := i) hm (Nat.mod_lt 1 hm)
    rw [d1, d2, ZMod.natCast_mod, Nat.cast_one, one_mul]
    simp only [rowFacB, Fac.comp, rowSide_bdec hX hY]
  · intro s Qs
    simp only [cvP, psiFac]
    exact psiN_cast hm _ _ _
  · intro s Qs
    rw [evL_cast hm]
    rfl

/-- The right function of `rowFacB` at codes. -/
theorem rowFacB_r_code (hm : 0 < m) (i : ℕ) (hX : X < 2 ^ lam) (hY : Y < 2 ^ lam) (Q : ℕ) :
    ((cfOut m (cfRun m Q (fun s Qs => psiN m Qs (Y / 2 ^ (3 * s)) (X / 2 ^ (3 * s))) (evRowR m X Y)
        (tB lam) (i * m + 1 % m)) : ℕ) : ZMod m) =
      (((rowFacB lam i).r (bdec lam X, bdec lam Y) (bdec _ Q) : ℤ) : ZMod m) := by
  rw [coefFac_r_run psiFac rowExp hm Q (fun s => ((bdec 3 (X / 2 ^ (3 * s)), bdec 3 (Y / 2 ^ (3 * s))) : Blk × Blk))]
  · obtain ⟨d1, d2⟩ := div_mod_pack (j := i) hm (Nat.mod_lt 1 hm)
    rw [d1, d2, ZMod.natCast_mod, Nat.cast_one, one_mul]
    simp only [rowFacB, Fac.comp, rowSide_bdec hX hY]
  · intro s Qs
    simp only [psiFac]
    exact psiN_cast hm _ _ _
  · intro s Qs
    simp only [evRowR, rowExp, Fac.ofEquiv, blk2Equiv]
    rw [app6_symm, CxN_cast hm]

/-- The right function of `colFacB` at codes. -/
theorem colFacB_r_code (hm : 0 < m) (j : ℕ) (hX : X < 2 ^ lam) (hY : Y < 2 ^ lam) (Q : ℕ) :
    ((cfOut m (cfRun m Q (fun s Qs => psiN m Qs (Y / 2 ^ (3 * s)) (X / 2 ^ (3 * s))) (evColR m X Y)
        (tB lam) (j * m + 1 % m)) : ℕ) : ZMod m) =
      (((colFacB lam j).r (bdec lam X, bdec lam Y) (bdec _ Q) : ℤ) : ZMod m) := by
  rw [coefFac_r_run psiFac colExp hm Q (fun s => ((bdec 3 (X / 2 ^ (3 * s)), bdec 3 (Y / 2 ^ (3 * s))) : Blk × Blk))]
  · obtain ⟨d1, d2⟩ := div_mod_pack (j := j) hm (Nat.mod_lt 1 hm)
    rw [d1, d2, ZMod.natCast_mod, Nat.cast_one, one_mul]
    simp only [colFacB, Fac.comp, rowSide_bdec hX hY]
  · intro s Qs
    simp only [psiFac]
    exact psiN_cast hm _ _ _
  · intro s Qs
    simp only [evColR, colExp, Fac.ofEquiv, blk2Equiv]
    rw [app6_symm, RxN_cast hm]

/-- The left function of `colFacB` at codes. -/
theorem colFacB_l_code (hm : 0 < m) (j : ℕ) (hX : X < 2 ^ lam) (hY : Y < 2 ^ lam) (Q : ℕ) :
    ((cfOut m (cfRun m Q (cvP m X Y) (evL X Y) (tB lam) (j * m + 1 % m)) : ℕ) : ZMod m) =
      (((colFacB lam j).l (bdec lam X, bdec lam Y) (bdec _ Q) : ℤ) : ZMod m) := by
  rw [coefFac_l_run psiFac colExp hm Q (fun s => ((bdec 3 (X / 2 ^ (3 * s)), bdec 3 (Y / 2 ^ (3 * s))) : Blk × Blk))
    (cvP m X Y) (evL X Y)]
  · obtain ⟨d1, d2⟩ := div_mod_pack (j := j) hm (Nat.mod_lt 1 hm)
    rw [d1, d2, ZMod.natCast_mod, Nat.cast_one, one_mul]
    simp only [colFacB, Fac.comp, rowSide_bdec hX hY]
  · intro s Qs
    simp only [cvP, psiFac]
    exact psiN_cast hm _ _ _
  · intro s Qs
    rw [evL_cast hm]
    rfl

end Codes

end Factoring.Aux
