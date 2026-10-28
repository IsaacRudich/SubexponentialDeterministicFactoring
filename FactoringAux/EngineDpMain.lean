/-
The nesting depth of the counting expression.

* `mainE_dp`: `dp (mainE K0 ℓ) ≤ 24 ℓ + 84`, independent of `K0` (the bound is attained, e.g. at `K0 = 0`).

Built from `EngineDpBase` (the grid lines, coarsening, clique table) and `EngineDpLevel` (a group step, a level,
the chain `deepEx`: `+24` per level). Not an audit surface.
-/
module

public import FactoringAux.EngineDpLevel

@[expose] public section

set_option linter.unusedSectionVars false

namespace Factoring.Aux

open Ex MulEx

/-! ### The multiplication network -/

section Mul

variable (u vm vs : ℕ)

theorem dpT_mul_sz : dp (mulNEx u vm vs).sz ≤ 12 := by
  dp_tac [mulNEx, sel, kA, AE, PDE, PZE, ME, PfE, fwE, LLE, hE, TLE, nprod, pow2]

theorem dpT_mul_W : dp (mulNEx u vm vs).W ≤ 21 := by
  dp_tac [mulNEx, sel, kA, AE, faW, cW, posE, dD, eqE, xBit, bitRd, ifEq, jE, dgE, nBit, ccE, cyE, zv, PfE, fwE,
    LLE, hE, TLE, ME, nprod, nsum, pow2]

theorem dpT_mul_c : dp (mulNEx u vm vs).c ≤ 19 := by
  dp_tac [mulNEx, cE, lnk, sel, kA, AE, fwE, LLE, eqE, ifEq, pow2]

set_option maxHeartbeats 4000000 in
theorem dpT_mul_l : dp (mulNEx u vm vs).l ≤ 31 := by
  dp_tac [mulNEx, msg, cE, lnk, sel, kA, AE, fwE, LLE, eqE, ifEq, pow2, faMsg, midMsg, ibMsg, hat, mM, sM, pw, pwi,
    tE, dD, dZ, zv, z1E, z2E, cyE, ccE, hE, ME, TLE, PfE, PZE, nprod]

set_option maxHeartbeats 4000000 in
theorem dpT_mul_r : dp (mulNEx u vm vs).r ≤ 31 := by
  dp_tac [mulNEx, msg, cE, lnk, sel, kA, AE, fwE, LLE, eqE, ifEq, pow2, faMsg, midMsg, ibMsg, hat, mM, sM, pw, pwi,
    tE, dD, dZ, zv, z1E, z2E, cyE, ccE, hE, ME, TLE, PfE, PZE, nprod]

end Mul

/-! ### The top table -/

section Top

variable (g K : ℕ)

theorem dpT_nodesE : dp nodesE ≤ 8 := by
  dp_tac [nodesE, AE, pow2]

theorem dpT_clχE : dp (clχE g) ≤ 11 := by
  dp_tac [clχE, sel, kA, AE, pow2]

macro "dpm" : tactic => `(tactic| ((try simp only [clPc]) <;> omega))

theorem dpT_cl_bounds :
    dp (CoarsenEx.nex (clPc g)).sz ≤ 15 ∧ dp (CoarsenEx.nex (clPc g)).W ≤ 44 ∧
      dp (CoarsenEx.nex (clPc g)).c ≤ 26 ∧ dp (CoarsenEx.nex (clPc g)).l ≤ 42 ∧
      dp (CoarsenEx.nex (clPc g)).r ≤ 42 := by
  have := dpT_mul_sz 16 10 11
  have := dpT_mul_W 16 10 11
  have := dpT_mul_c 16 10 11
  have := dpT_mul_l 16 10 11
  have := dpT_mul_r 16 10 11
  have := dpT_nodesE
  have := dpT_clχE g
  exact ⟨dpT_coarsen_sz (by dpm) (by dpm) (by dpm),
    dpT_coarsen_W (by dpm) (by dpm) (by dpm) (by dpm) (by dpm) (by dpm) (by dpm),
    dpT_coarsen_c (by dpm) (by dpm) (by dpm),
    dpT_coarsen_l (by dpm) (by dpm) (by dpm) (by dpm) (by dpm) (by dpm),
    dpT_coarsen_r (by dpm) (by dpm) (by dpm) (by dpm) (by dpm) (by dpm)⟩

theorem dpT_top_tab : dp (GroupEx.tab (gsTop K g)) ≤ 65 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := dpT_cl_bounds g
  apply dpT_group_tab <;> (try simp only [gsTop]) <;> omega

theorem dpT_top_search (vx vs : ℕ) : dp (GroupEx.searchE (gsTop K g) vx vs) ≤ 42 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := dpT_cl_bounds g
  apply dpT_group_search <;> (try simp only [gsTop]) <;> omega

theorem dpT_sE : dp sE ≤ 6 := by
  dp_tac [sE, pow2]

theorem dpT_L0E : dp (L0E K g) ≤ 12 := by
  dp_tac [L0E, clPE, AE, fwE, LLE, pow2]

/-- The whole count modulo the modulus. -/
theorem dpT_topE (K0 ℓ : ℕ) : dp (topE K0 ℓ) ≤ 24 * ℓ + 76 := by
  have h1 := dpT_top_tab (Gs K0 ℓ) (Kb K0 ℓ)
  have h2 := dpT_top_search (Gs K0 ℓ) (Kb K0 ℓ) 13 14
  have h3 := dpT_deepEx K0 ℓ 100 10 12 82 83 (GroupEx.tab (gsTop (Kb K0 ℓ) (Gs K0 ℓ)))
  have h4 := dpT_sE
  have h5 := dpT_L0E (Gs K0 ℓ) (Kb K0 ℓ)
  simp only [topE, Ex.dp]
  omega

end Top

/-! ### The multiplier, its exponent, the counting expression -/

theorem dpT_multE (G vL vm x : ℕ) : dp (multE G vL vm x) ≤ 8 := by
  dp_tac [multE, zmul, zprod, tBE]

theorem dpT_dmE (K0 : ℕ) : ∀ d vL b vm, dp (dmE K0 d vL b vm) ≤ 3 * d + 8
  | 0, _, _, _ => by simp [dmE, Ex.dp]
  | d + 1, vL, b, vm => by
      have h1 := dpT_dmE K0 d (b + 1) (b + 2) vm
      have h2 := dpT_multE (Gs K0 d) vL vm b
      have h3 := dpT_LnE (lpOf K0 d vm vL)
      simp only [dmE, zmul, Ex.dp]
      omega

theorem dpT_mlE (K0 : ℕ) : ∀ d vL b, dp (mlE K0 d vL b) ≤ 2 * d + 8
  | 0, _, _ => by simp [mlE, Ex.dp]
  | d + 1, vL, b => by
      have h1 := dpT_mlE K0 d (b + 1) (b + 2)
      have h3 := dpT_LnE (lpOf K0 d 0 vL)
      simp only [mlE, tBE, Ex.dp]
      omega

theorem dpT_c1E : dp c1E ≤ 9 := by
  dp_tac [c1E, ifEq, nsum, xBit, bitRd]

/-- **The nesting depth of the counting expression** is at most `24 ℓ + 84`, whatever `K0`. -/
theorem mainE_dp (K0 ℓ : ℕ) : Ex.dp (Ex.mainE K0 ℓ) ≤ 24 * ℓ + 84 := by
  have h1 := dpT_topE K0 ℓ
  have h2 := dpT_dmE K0 ℓ 12 30 10
  have h3 := dpT_mlE K0 ℓ 12 30
  have h4 := dpT_c1E
  have h5 := dpT_sE
  have h6 := dpT_L0E (Gs K0 ℓ) (Kb K0 ℓ)
  simp only [mainE, nsum, ifEq, zmul, Ex.dp]
  omega

end Factoring.Aux
