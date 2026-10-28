/-
Nesting depth (`Ex.dp`) of the engine's expressions, part 1.

* `dp_tac [defs]`: unfold `defs` and `dp`, split `max a b + 1 ≤ n` into leaf inequalities, close each by `omega`.
* The grid lines (`GridEx.nex P tr`): `W ≤ max (dp TE + 7) 15`, `sz ≤ 3`, `c ≤ 16`, `l ≤ 42`, `r ≤ 51`.
* Coarsening and clique tables: each field of the output is `≤ n` given `dp (input field) + offset ≤ n`.

Not an audit surface.
-/
module

public import FactoringAux.EngineMain

@[expose] public section

set_option linter.unusedSectionVars false

namespace Factoring.Aux

open Ex

theorem dpT_pos (e : Ex) : 1 ≤ dp e := by cases e <;> simp [Ex.dp]

theorem dpT_add_lt {a b c : ℕ} : a + b < c ↔ a < c - b := (Nat.lt_sub_iff_add_lt).symm

macro "dp_simp" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (simp only [$ts,*, Ex.dp, Nat.add_one_le_iff, max_lt_iff, max_le_iff, dpT_add_lt, and_true, true_and,
    and_self, if_true, if_false, Bool.false_eq_true]))

macro "dp_tac" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (dp_simp [$ts,*] <;> (try split_ands) <;> omega))

set_option maxHeartbeats 1000000 in
theorem dpT_grid_W (P : GP) (tr : Bool) : dp (GridEx.nex P tr).W ≤ max (dp P.TE + 7) 15 := by
  cases tr <;> dp_tac [GridEx.nex, GridEx.W, GridEx.slcE, GridEx.ptIE, GridEx.p2, zmul, zprod, ifEq, pow2]

theorem dpT_grid_sz (P : GP) (tr : Bool) : dp (GridEx.nex P tr).sz ≤ 3 := by
  dp_tac [GridEx.nex, GridEx.sz, GridEx.p2, pow2]

theorem dpT_grid_c (P : GP) (tr : Bool) : dp (GridEx.nex P tr).c ≤ 16 := by
  cases tr <;> dp_tac [GridEx.nex, GridEx.c, GridEx.cwE, GridEx.cXE, GridEx.minE, GridEx.phiDE, GridEx.qIdxE,
    GridEx.powE, tBE, nsum]

set_option maxHeartbeats 4000000 in
theorem dpT_grid_l (P : GP) (tr : Bool) : dp (GridEx.nex P tr).l ≤ 42 := by
  cases tr <;> dp_tac [GridEx.nex, GridEx.F, GridEx.slcE, GridEx.ptIE, GridEx.p2, GridEx.offE, GridEx.cwE,
    GridEx.cXE, GridEx.minE, GridEx.phiDE, GridEx.qIdxE, GridEx.powE, tBE, nsum, zmul, zprod, ifEq, pow2, facLE, jOf,
    decLE, decE, cvPE, evLE, blkAt, psiE, sgnE, par3E, phiE, bitE, eqE]

set_option maxHeartbeats 4000000 in
theorem dpT_grid_r (P : GP) (tr : Bool) : dp (GridEx.nex P tr).r ≤ 51 := by
  cases tr <;> dp_tac [GridEx.nex, GridEx.F, GridEx.slcE, GridEx.ptIE, GridEx.p2, GridEx.offE, GridEx.cwE,
    GridEx.cXE, GridEx.minE, GridEx.phiDE, GridEx.qIdxE, GridEx.powE, tBE, nsum, zmul, zprod, zsum, ifEq, pow2, facRE,
    jOf, decRRE, decCRE, decE, cvRE, evRRE, evCRE, blkAt, psiE, sgnE, par3E, par4E, phiE, bitE, eqE, RxE, CxE, pieceE,
    decLE, cvPE, evLE]

section Coarsen

variable {P : CP} {n : ℕ}

theorem dpT_coarsen_sz (hs : dp P.E.sz + 3 ≤ n) (hg : dp P.gE + 1 ≤ n) (hx : dp P.χE + 3 ≤ n) :
    dp (CoarsenEx.nex P).sz ≤ n := by
  have := dpT_pos P.χE
  dp_tac [CoarsenEx.nex, CoarsenEx.sz, CoarsenEx.sgE, nprod, ifEq]

theorem dpT_coarsen_c (hc : dp P.E.c + 5 ≤ n) (hg : dp P.gE + 4 ≤ n) (hx : dp P.χE + 15 ≤ n) :
    dp (CoarsenEx.nex P).c ≤ n := by
  have := dpT_pos P.χE
  dp_tac [CoarsenEx.nex, CoarsenEx.c, CoarsenEx.atPair, CoarsenEx.usedE, CoarsenEx.crossE, CoarsenEx.chiB, nsum, ifEq]

set_option maxHeartbeats 4000000 in
theorem dpT_coarsen_l (hs : dp P.E.sz + 17 ≤ n) (hc : dp P.E.c + 13 ≤ n) (hl : dp P.E.l + 9 ≤ n)
    (hr : dp P.E.r + 11 ≤ n) (hg : dp P.gE + 12 ≤ n) (hx : dp P.χE + 23 ≤ n) : dp (CoarsenEx.nex P).l ≤ n := by
  have := dpT_pos P.χE
  dp_tac [CoarsenEx.nex, CoarsenEx.l, CoarsenEx.atPair, CoarsenEx.usedE, CoarsenEx.crossE, CoarsenEx.chiB,
    CoarsenEx.offE, CoarsenEx.digE, CoarsenEx.digB, CoarsenEx.ppE, CoarsenEx.sgE, nsum, nprod, zprod, pow2, ifEq]

set_option maxHeartbeats 4000000 in
theorem dpT_coarsen_r (hs : dp P.E.sz + 16 ≤ n) (hc : dp P.E.c + 13 ≤ n) (hl : dp P.E.l + 11 ≤ n)
    (hr : dp P.E.r + 9 ≤ n) (hg : dp P.gE + 12 ≤ n) (hx : dp P.χE + 23 ≤ n) : dp (CoarsenEx.nex P).r ≤ n := by
  have := dpT_pos P.χE
  dp_tac [CoarsenEx.nex, CoarsenEx.r, CoarsenEx.atPair, CoarsenEx.usedE, CoarsenEx.crossE, CoarsenEx.chiB,
    CoarsenEx.offE, CoarsenEx.digE, CoarsenEx.digB, CoarsenEx.ppE, CoarsenEx.sgE, nsum, nprod, zprod, pow2, ifEq]

set_option maxHeartbeats 4000000 in
theorem dpT_coarsen_W (hs : dp P.E.sz + 19 ≤ n) (hW : dp P.E.W + 6 ≤ n) (hc : dp P.E.c + 11 ≤ n)
    (hl : dp P.E.l + 13 ≤ n) (hr : dp P.E.r + 13 ≤ n) (hg : dp P.gE + 4 ≤ n) (hx : dp P.χE + 19 ≤ n) :
    dp (CoarsenEx.nex P).W ≤ n := by
  have := dpT_pos P.χE
  dp_tac [CoarsenEx.nex, CoarsenEx.W, CoarsenEx.chiB, CoarsenEx.digE, CoarsenEx.digB, CoarsenEx.ppE,
    CoarsenEx.sgE, nprod, zprod, zsum, zmul, pow2, ifEq]

end Coarsen

set_option maxHeartbeats 4000000 in
theorem dpT_clique_tab {P : KP} {n : ℕ} (hs : dp P.E.sz + 2 ≤ n) (hW : dp P.E.W + 6 ≤ n)
    (hc : dp P.E.c + 17 ≤ n) (hl : dp P.E.l + 12 ≤ n) (hr : dp P.E.r + 11 ≤ n) (hk : dp P.kE + 7 ≤ n)
    (hL : dp P.LE + 17 ≤ n) : dp (CliqueEx.tab P) ≤ n := by
  have := dpT_pos P.LE
  dp_tac [CliqueEx.tab, CliqueEx.padL, CliqueEx.padR, CliqueEx.unitE, CliqueEx.blkQ, zprod, zsum, zmul, pow2, ifEq]

end Factoring.Aux
