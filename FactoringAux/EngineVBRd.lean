/-
Array reads of the engine's expressions: every builder reads arrays only through `bitRd`
(`Ex.RdN false`, `FactoringAux/EngineRd.lean`).

* `RdN_any`: `RdN false e` gives `RdN b e` for either flag.
* `NEx.Rd`: the five expressions of a network satisfy `RdN false`.
* Per builder: `mulNEx_rdn`, `coarsen_rdn`, `clique_rdn`, `grid_rdn`, `group_tab_rdn`, `group_search_rdn`,
  `level_nextTE_rdn`, `level_pre_rdn`, `deep_rdn`; **`topE_rdn`**.

Not an audit surface.
-/
module

public import FactoringAux.EngineVBTop
public import FactoringAux.EngineRd

@[expose] public section

namespace Factoring.Aux

open Ex MulEx

set_option linter.unusedSimpArgs false

theorem Ex.RdN_any {e : Ex} (h : RdN false e) (b : Bool) : RdN b e := by
  cases e <;> first | exact h | exact absurd h.1 (by decide)

/-- The five expressions of a network read arrays only through `bitRd`. -/
def NEx.Rd (E : NEx) : Prop := RdN false E.sz ∧ RdN false E.W ∧ RdN false E.c ∧ RdN false E.l ∧ RdN false E.r

theorem mulNEx_rdn (u vm vs : ℕ) : (mulNEx u vm vs).Rd := by
  simp only [NEx.Rd, mulNEx, msg, sel, kA, AE, hE, LLE, fwE, ME, TLE, PfE, PZE, PDE, mM,
      sM, pw, pwi, tE, dD, dZ, zv, z1E, z2E, cyE, ccE, faMsg, hat, midMsg, ibMsg, lnk, cE, posE, faW, jE, dgE, cW,
      xBit, nBit, bitRd, ifEq, eqE, pow2, nprod, nsum, RdN, isZ, and_true, true_and, and_self]

theorem coarsen_rdn {P : CP} (hE : P.E.Rd) (hg : RdN false P.gE) (hχ : RdN false P.χE) : (CoarsenEx.nex P).Rd := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hE
  have k1 := RdN_any h1; have k2 := RdN_any h2; have k3 := RdN_any h3; have k4 := RdN_any h4
  have k5 := RdN_any h5; have kg := RdN_any hg; have kχ := RdN_any hχ
  simp only [NEx.Rd, CoarsenEx.nex, CoarsenEx.sz, CoarsenEx.W, CoarsenEx.c, CoarsenEx.l, CoarsenEx.r,
    CoarsenEx.offE, CoarsenEx.sgE, CoarsenEx.ppE, CoarsenEx.digE, CoarsenEx.digB, CoarsenEx.chiB, CoarsenEx.atPair,
    CoarsenEx.usedE, CoarsenEx.crossE, zmul, zprod, zsum, nsum, pow2, nprod, ifEq, RdN, isZ, k1, k2, k3, k4, k5, kg,
    kχ, and_true, true_and, and_self]

theorem clique_rdn {P : KP} (hE : P.E.Rd) (hk : RdN false P.kE) (hL : RdN false P.LE) :
    RdN false (CliqueEx.tab P) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hE
  have k1 := RdN_any h1; have k2 := RdN_any h2; have k3 := RdN_any h3; have k4 := RdN_any h4
  have k5 := RdN_any h5; have kk := RdN_any hk; have kL := RdN_any hL
  simp only [CliqueEx.tab, CliqueEx.padL, CliqueEx.padR, CliqueEx.unitE, CliqueEx.blkQ, zmul, zprod, zsum, pow2,
    nprod, ifEq, RdN, isZ, k1, k2, k3, k4, k5, kk, kL, and_true, true_and, and_self]

theorem grid_rdn {P : GP} (tr : Bool) (hT : RdN false P.TE) : (GridEx.nex P tr).Rd := by
  have kT := RdN_any hT
  cases tr <;>
  simp only [NEx.Rd, GridEx.nex, GridEx.sz, GridEx.W, GridEx.c, GridEx.F, GridEx.offE, GridEx.cwE, GridEx.p2,
      GridEx.powE, GridEx.slcE, GridEx.ptIE, GridEx.phiDE, GridEx.qIdxE, GridEx.minE, GridEx.cXE, facLE, facRE, jOf,
      pieceE, decLE, decRRE, decCRE, decE, tBE, blkAt, cvPE, evLE, cvRE, evRRE, evCRE,
      psiE, sgnE, phiE, par3E, par4E, bitE, RxE, CxE, eqE, ifEq, pow2, zsum, zmul, zprod, nsum, nprod,
      Bool.false_eq_true, ↓reduceIte, RdN, isZ, kT, and_true, true_and, and_self]

theorem group_tab_rdn {S : GS} (hE : S.E.Rd) : RdN false (GroupEx.tab S) :=
  clique_rdn (P := GroupEx.Pk S)
    (coarsen_rdn (P := GroupEx.Pc S) hE trivial (by simp [GroupEx.Pc, GroupEx.chiE, RdN])) trivial trivial

theorem group_search_rdn {S : GS} (hE : S.E.Rd) (vx vs : ℕ) : RdN false (GroupEx.searchE S vx vs) := by
  have hc := (coarsen_rdn (P := GroupEx.Pc S) hE trivial (by simp [GroupEx.Pc, GroupEx.chiE, RdN])).2.2.1
  have kc := RdN_any hc
  simp only [CoarsenEx.nex] at kc
  simp only [GroupEx.searchE, GroupEx.okE, GroupEx.chiE, ifEq, nsum, nprod, RdN, isZ, kc, and_true, true_and,
    and_self]

theorem level_nextTE_rdn {P : LP} (hT : RdN false P.TE) : RdN false (LevelEx.nextTE P) := by
  have hg : ∀ tr, (GridEx.nex (LevelEx.gp P) tr).Rd := fun tr => grid_rdn (P := LevelEx.gp P) tr hT
  have ht := fun tr => RdN_any (group_tab_rdn (S := LevelEx.gs P tr) (hg tr))
  have hc := fun tr => RdN_any (hg tr).2.2.1
  simp only [GridEx.nex] at hc
  simp only [LevelEx.nextTE, LevelEx.UE, nsum, RdN, isZ, ht, hc, and_true, true_and, and_self]

theorem level_pre_rdn {P : LP} (hT : RdN false P.TE) {body : Ex} (hB : RdN false body) :
    RdN false (LevelEx.pre P body) := by
  have hs := fun tr b => RdN_any (group_search_rdn (S := LevelEx.gs P tr)
    (grid_rdn (P := LevelEx.gp P) tr hT) (P.b + 2) (P.b + 3)) b
  simp only [LevelEx.pre, LevelEx.LnE, RdN, isZ, hs, hB, and_true, true_and, and_self]

theorem deep_rdn (K0 : ℕ) : ∀ (d b vm vl vγ vΘ : ℕ) (TE : Ex), RdN false TE →
    RdN false (deepEx K0 d b vm vl vγ vΘ TE)
  | 0, b, vm, vl, vγ, vΘ, TE, hT => by
      have kT := RdN_any hT
      simp only [deepEx, bruteE, blkKE, zsum, zmul, zprod, pow2, ifEq, RdN, isZ, kT, and_true, true_and, and_self]
  | d + 1, b, vm, vl, vγ, vΘ, TE, hT => by
      have hD := deep_rdn K0 d (b + 100) vm (b + 1) (b + 62) (b + 63) _
        (level_nextTE_rdn (P := ⟨b, vm, vl, vγ, vΘ, Kb K0 d, Gs K0 d, TE⟩) hT)
      have hP := level_pre_rdn (P := ⟨b, vm, vl, vγ, vΘ, Kb K0 d, Gs K0 d, TE⟩) hT hD
      simp only [deepEx, zsum, tBE, RdN, hP, and_true, true_and, and_self]

/-- **The whole counting expression reads arrays only through `bitRd`.** -/
theorem topE_rdn (K0 ℓ : ℕ) : Ex.RdN false (Ex.topE K0 ℓ) := by
  have hC : (CoarsenEx.nex (clPc (Gs K0 ℓ))).Rd :=
    coarsen_rdn (P := clPc (Gs K0 ℓ)) (mulNEx_rdn 16 10 11)
      (by simp [clPc, nodesE, AE, pow2, RdN])
      (by simp [clPc, clχE, sel, kA, AE, pow2, RdN])
  have hS := group_search_rdn (S := gsTop (Kb K0 ℓ) (Gs K0 ℓ)) hC 13 14
  have hD := deep_rdn K0 ℓ 100 10 12 82 83 _ (group_tab_rdn (S := gsTop (Kb K0 ℓ) (Gs K0 ℓ)) hC)
  simp only [topE, sE, L0E, clPE, AE, fwE, LLE, pow2, RdN, isZ, hS, hD, and_true, true_and, and_self]

end Factoring.Aux
