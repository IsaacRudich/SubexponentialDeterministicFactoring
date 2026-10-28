/-
The multiplication network as expressions: variables.

* **`mul_vb`**: every variable (bound ones included) of the five expressions is below `u + 7`.
* **`mul_fv`**: their free variables are `0`, `2`, `vm`, `vs` and the arguments `u … u+3`.

Not an audit surface.
-/
module

public import FactoringAux.EngineMulBdd
public import FactoringAux.MulCount

@[expose] public section

namespace Factoring.Aux

open Finset Ex MulEx

section VBs

variable {u vs vm : ℕ}

theorem msg_vb (hvs : vs < u) {va vb : ℕ} (hva : va < u + 4) (hvb : vb < u + 4) :
    VB (u + 7) (msg u vs va vb) := by
  have h1 : vs < u + 7 := by omega
  have h2 : va < u + 7 := by omega
  have h3 : vb < u + 7 := by omega
  simp [msg, sel, kA, AE, hE, LLE, fwE, ME, TLE, PfE, PZE, PDE, mM, sM, pw, pwi, tE, dD, dZ, zv, z1E, z2E, cyE,
    ccE, faMsg, hat, midMsg, ibMsg, ifEq, eqE, pow2, nprod, nsum, VB, h1, h2, h3]

/-- **Every variable of the five expressions is below `u + 7`.** -/
theorem mul_vb (_hvm : vm < u) (hvs : vs < u) (h2 : 2 < u) :
    VB (u + 7) (mulNEx u vm vs).sz ∧ VB (u + 7) (mulNEx u vm vs).W ∧ VB (u + 7) (mulNEx u vm vs).c ∧
      VB (u + 7) (mulNEx u vm vs).l ∧ VB (u + 7) (mulNEx u vm vs).r := by
  have h1 : vs < u + 7 := by omega
  have h0 : 0 < u + 7 := by omega
  have h27 : 2 < u + 7 := by omega
  have m1 := msg_vb hvs (show u < u + 4 by omega) (show u + 1 < u + 4 by omega)
  have m2 := msg_vb hvs (show u + 1 < u + 4 by omega) (show u < u + 4 by omega)
  simp [mulNEx, sel, kA, AE, hE, LLE, fwE, ME, TLE, PfE, PZE, PDE, mM, sM, pw, pwi, tE, dD, dZ, zv, z1E, z2E, cyE,
    ccE, lnk, cE, posE, faW, jE, dgE, cW, xBit, nBit, bitRd, ifEq, eqE, pow2, nprod, nsum, VB, h1, h0, h27, m1, m2]

theorem msg_fv (p : ℕ → Prop) (hp : ∀ y, (y = vs ∨ (u ≤ y ∧ y < u + 4)) → p y) {va vb : ℕ} (hva : u ≤ va)
    (hva' : va < u + 4) (hvb : u ≤ vb) (hvb' : vb < u + 4) : FV p (msg u vs va vb) := by
  have h1 : p vs := hp _ (Or.inl rfl)
  have h2 : p va := hp _ (Or.inr ⟨hva, hva'⟩)
  have h3 : p vb := hp _ (Or.inr ⟨hvb, hvb'⟩)
  have h4 : p (u + 2) := hp _ (Or.inr ⟨by omega, by omega⟩)
  simp [msg, sel, kA, AE, hE, LLE, fwE, ME, TLE, PfE, PZE, PDE, mM, sM, pw, pwi, tE, dD, dZ, zv, z1E, z2E, cyE,
    ccE, faMsg, hat, midMsg, ibMsg, ifEq, eqE, pow2, nprod, nsum, FV, h1, h2, h3, h4]

/-- **The free variables of the five expressions.** -/
theorem mul_fv :
    let S : ℕ → Prop := fun y => y = 0 ∨ y = 2 ∨ y = vm ∨ y = vs ∨ (u ≤ y ∧ y < u + 4)
    FV S (mulNEx u vm vs).sz ∧ FV S (mulNEx u vm vs).W ∧ FV S (mulNEx u vm vs).c ∧
      FV S (mulNEx u vm vs).l ∧ FV S (mulNEx u vm vs).r := by
  intro S
  have hS : ∀ y, (y = vs ∨ (u ≤ y ∧ y < u + 4)) → S y := by
    intro y hy; rcases hy with hy | hy
    · exact Or.inr (Or.inr (Or.inr (Or.inl hy)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr hy)))
  have m1 := msg_fv S hS (va := u) (vb := u + 1) (le_refl u) (by omega) (by omega) (by omega)
  have m2 := msg_fv S hS (va := u + 1) (vb := u) (by omega) (by omega) (le_refl u) (by omega)
  have e0 : S 0 := Or.inl rfl
  have e2 : S 2 := Or.inr (Or.inl rfl)
  have ev : S vs := hS _ (Or.inl rfl)
  have eu : S u := hS _ (Or.inr ⟨le_rfl, by omega⟩)
  have eu1 : S (u + 1) := hS _ (Or.inr ⟨by omega, by omega⟩)
  have eu2 : S (u + 2) := hS _ (Or.inr ⟨by omega, by omega⟩)
  have eu3 : S (u + 3) := hS _ (Or.inr ⟨by omega, by omega⟩)
  simp only [mulNEx] at m1 m2 ⊢
  simp [sel, kA, AE, hE, LLE, fwE, ME, TLE, PfE, PZE, PDE, dD, zv, z1E, z2E, cyE,
    ccE, lnk, cE, posE, faW, jE, dgE, cW, xBit, nBit, bitRd, ifEq, eqE, pow2, nprod, nsum, FV, e0, e2, ev, eu, eu1,
    eu2, eu3, m1, m2]

end VBs

/-! ### The sizes -/

theorem pZ_le_fw (s : ℕ) : pZ s ≤ 2 ^ (fw s * pA s) := by
  rw [pZ, pp_const, pow_mul]; exact Nat.pow_le_pow_left (pM_le_fw s) _

/-- **The sizes are at most `2^(2 A fw)`.** -/
theorem mulSz_le (s a : ℕ) : mulSz s a ≤ 2 ^ (2 * pA s * fw s) := by
  have hA2 := two_le_pA s
  have hZ := pZ_le_fw s
  have hfw : 1 ≤ fw s := by unfold fw; omega
  have h1 : fw s * pA s ≤ 2 * pA s * fw s := by nlinarith
  have h2 : fw s * pA s + fw s * pA s = 2 * pA s * fw s := by ring
  unfold mulSz
  split_ifs
  · generalize (MG.enum (pA s)).symm _ = i
    cases i <;> simp only [gsz]
    · rw [pD, pp_const, ← pow_mul]
      refine Nat.pow_le_pow_right (by norm_num) ?_
      have := ph_le_pA s
      have : pL s ≤ fw s := by unfold fw pm; omega
      nlinarith
    · rw [pD, pp_const, ← pow_mul]
      refine Nat.pow_le_pow_right (by norm_num) ?_
      have := ph_le_pA s
      have : pL s ≤ fw s := by unfold fw pm; omega
      nlinarith
    · rw [← h2, pow_add]; exact Nat.mul_le_mul hZ hZ
    · exact le_trans hZ (Nat.pow_le_pow_right (by norm_num) h1)
    · calc pM s * 2 ^ fw s ≤ 2 ^ fw s * 2 ^ fw s := Nat.mul_le_mul_right _ (pM_le_fw s)
        _ = 2 ^ (fw s + fw s) := by rw [pow_add]
        _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  · exact Nat.one_le_two_pow

end Factoring.Aux
