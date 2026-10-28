/-
The cost of the uniform counting command: frames of the count modulo `m` and of one modulus,
without the correctness hypotheses (`Keeps`, as `uniC_keeps`).

Not an audit surface.
-/
module

public import FactoringAux.UniCostDm

@[expose] public section

namespace Factoring.Aux

open Factoring.Aux.Copied Factoring.Aux.Copied.PLib Ex Uni

namespace UCost

section Keep

set_option linter.unusedTactic false
set_option linter.unreachableTactic false

attribute [local irreducible] cset fillC UP lvlSet topSet

set_option maxRecDepth 20000 in
theorem countM_keeps : Keeps (countM UP) (fun y => WC y ∨ 990 ≤ y) := by
  unfold countM pathBody lvlBody
  repeat' (first | apply Keeps.seq | apply Keeps.loop | apply Keeps.ifLt | apply Keeps.skip | apply Keeps.copy | apply Keeps.setK | apply keeps_fill | apply keeps_lset | apply Keeps.cset)
  all_goals first
    | exact UP_ok.vlnE | exact UP_ok.vsrE _ | exact UP_ok.vnxE | exact UP_ok.vl0E | exact UP_ok.vtsE
    | exact UP_ok.vttE | exact vb_dE | exact vb_kbE _ (by norm_num) | exact vb_NcE | exact vb_bruteU | exact vb_c1E
    | (simp only [WC, WP, WL]; omega)
    | (simp [WC, WP, WL]; done)
    | (intro y hy; simp only [WC, WP, WL]; omega)
    | (norm_num; done)
    | (simp [VB, pow2]; done)

set_option maxRecDepth 20000 in
theorem modBody_keeps : Keeps (modBody UP) (fun y => WM y ∨ 990 ≤ y) := by
  unfold modBody countM pathBody lvlBody dmLoop dmBody
  repeat' (first | apply Keeps.seq | apply Keeps.loop | apply Keeps.ifLt | apply Keeps.skip | apply Keeps.copy | apply Keeps.setK | apply keeps_fill | apply keeps_lset | apply Keeps.cset)
  all_goals first
    | exact UP_ok.vlnE | exact UP_ok.vsrE _ | exact UP_ok.vnxE | exact UP_ok.vl0E | exact UP_ok.vtsE
    | exact UP_ok.vttE | exact vb_dE | exact vb_kbE _ (by norm_num) | exact vb_NcE | exact vb_bruteU | exact vb_c1E
    | (simp only [WM, WC, WP, WL]; omega)
    | (simp [WM, WC, WP, WL]; done)
    | (intro y hy; simp only [WM, WC, WP, WL]; omega)
    | (norm_num; done)
    | (simp [VB, pow2, flagE, ifEq, c1E, nsum, xBit, bitRd, multVm, gE, powE, tBE]; done)

end Keep

theorem countM_frame (st : St) {y : ℕ} (hy : y < 990) (hW : ¬ WC y) : (Cmd.run (countM UP) st).1.sc y = st.sc y :=
  (countM_keeps st).1 y hy (fun h => h.elim hW (by omega))

theorem modBody_frame (st : St) {y : ℕ} (hy : y < 990) (hW : ¬ WM y) : (Cmd.run (modBody UP) st).1.sc y = st.sc y :=
  (modBody_keeps st).1 y hy (fun h => h.elim hW (by omega))

end UCost

end Factoring.Aux
