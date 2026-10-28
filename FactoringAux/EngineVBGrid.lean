/-
Free variables and variable bounds of the line networks' expressions (`GridEx.nex`).

* **`grid_fvw`**: the free variables are the context's (`vm`, `vl`, `vc`, those of the table besides its arguments
  `vγ`, `vΘ`) and the arguments `u … u+3`; **`grid_vb`**: every variable is below `t` if `u + 41 ≤ t` and the
  context's variables are below `t`.

Not an audit surface.
-/
module

public import FactoringAux.EngineVBBase
public import FactoringAux.EngineGridEx

@[expose] public section

namespace Factoring.Aux

open Ex GridEx

set_option linter.unusedSimpArgs false

variable {s : ℕ → Prop} {P : GP}

/-- **The free variables of a line network's expressions.** -/
theorem grid_fvw (tr : Bool) (hvm : s P.vm) (hvl : s P.vl) (hvc : s P.vc) (hT : FVw s [P.vγ, P.vΘ] P.TE) :
    (nex P tr).FVw s (NVars.std P.u) := by
  simp only [FVw, List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true, and_true, and_imp] at hT
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intro s' hs hv <;>
    simp only [NVars.std, List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true, and_true] at hv <;>
    cases tr <;>
    simp (config := {contextual := true}) only [nex, sz, W, c, F, offE, cwE, p2, powE, slcE, ptIE, phiDE, qIdxE,
      minE, cXE, facLE, facRE, jOf, pieceE, decLE, decRRE, decCRE, decE, tBE, blkAt, cvPE, evLE, cvRE, evRRE, evCRE,
      psiE, sgnE, phiE, par3E, par4E, bitE, RxE, CxE, eqE, ifEq, pow2, zsum, zmul, zprod, nsum, nprod,
      Bool.false_eq_true, ↓reduceIte, FV, true_or, or_true, and_true, true_and, and_self, implies_true, hs, hvm,
      hvl, hvc, hv, hT]

/-- **Every variable of a line network's expressions is below `t`.** -/
theorem grid_vb {t : ℕ} (tr : Bool) (hT : VB t P.TE) (hvm : P.vm < t) (hvl : P.vl < t) (hvc : P.vc < t)
    (hγ : P.vγ < t) (hΘ : P.vΘ < t) (hu : P.u + 41 ≤ t) : (nex P tr).VB t := by
  cases tr <;>
  simp only [NEx.VB, nex, sz, W, c, F, offE, cwE, p2, powE, slcE, ptIE, phiDE, qIdxE,
      minE, cXE, facLE, facRE, jOf, pieceE, decLE, decRRE, decCRE, decE, tBE, blkAt, cvPE, evLE, cvRE, evRRE, evCRE,
      psiE, sgnE, phiE, par3E, par4E, bitE, RxE, CxE, eqE, ifEq, pow2, zsum, zmul, zprod, nsum, nprod,
      Bool.false_eq_true, ↓reduceIte, VB, hT, and_true, true_and, and_self] <;>
  omega

end Factoring.Aux
