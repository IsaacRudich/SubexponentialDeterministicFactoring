/-
The uniform engine: the counting command.

`uniC U` is one `Cmd` for every input length.  It computes `s = sOf n`, the number of levels `ℓ = ellOf n`, the top
group count `Kb 48 ℓ`, the top width; then (`sweep`) the number of paths `NPof`, the multiplier `deepMult` and its
exponent bound `mlogN`; then for every modulus `m < 2M + 1` (`M = n + mlogN + 4`, as in `mainE`): the top table
(slot `2` of array `3`), and for every path the levels (slots `0`, `1` alternately) and the brute force, summed
modulo `m`; the modulus is flagged when the sum differs from `deepMult · [divisor 1 counts]`.  The output bit (scalar
`3`) is `1` iff no modulus is flagged.

The level and top expressions with their literals read from variables are the parameters `U : UParts` (the
literal-free copies; their specification is `UOK`, in `UniEngineSpec.lean`).

Scalars: `10` m, `11` s, `12` L_top, `15` χ_top, `40` λ, `41` slot read, `42` its node count, `43` K, `45` height `d`,
`47` `Nc`, `100` choice code, `101` L', `104, 105` the searches,
`300` modulus counter, `301` flags, `303` NP, `304` path, `305` remaining path, `306` level counter, `307` ℓ,
`308` sum, `309` deepMult modulo m, `310` mlogN, `311` entry counter, `312` brute force, `314` 2M+1, `315` the constant 2,
`316` K_top, `320` slot written, `321` entry count.

Not an audit surface.
-/
module

public import FactoringAux.UniTab
public import FactoringAux.UniParams
public import FactoringAux.EngineMain

@[expose] public section

namespace Factoring.Aux

open Factoring.Aux.Copied Factoring.Aux.Copied.PLib Ex

/-- The literal-free copies of the level and top expressions (and the commands setting their literal variables). -/
structure UParts where
  /-- Sets the level literal variables (in `20 … 39`) from `K` in scalar `43`. -/
  lset : Cmd
  lnE : Ex
  srE : Bool → Ex
  nxE : Ex
  /-- Sets the top literal variables (in `{1, 3, 5, …, 9}`) from `K` in scalar `43`. -/
  tset : Cmd
  l0E : Ex
  tsE : Ex
  ttE : Ex

namespace Uni

/-- The table read by a level or by the brute force. -/
def rdT : Ex := rdTE 42 40 41 60 61 59

/-- `mult (3 K^8) λ` modulo `m` (`K` in `vK`, `λ` in `vl`, `m` in `vm`), every product reduced. -/
def multVm (vK vl vm : ℕ) : Ex :=
  .lett 910 (gE vK) (.lett 911 (.div (.mul (.var 910) (.sub (.var 910) (.lit 1))) (.lit 2))
    (.lett 912 (.mul (.var 911) (.var 911))
      (.mod (.mul (.prod 913 (.sub (powE 914 (.var 910) 4) (.var 912)) (.var vm)
          (.mod (.add (tBE vl) (.lit 1)) (.var vm)))
        (.prod 913 (.mul (tBE vl) (.var 912)) (.var vm) (.mod (.lit 2) (.var vm)))) (.var vm))))

/-- The level data for group count `K`. -/
def lvP (K : ℕ) : LP := ⟨100, 10, 40, 60, 61, K, 3 * K ^ 8, rdT⟩

/-- The brute force. -/
def bruteU : Ex := bruteE 100 10 40 60 61 K0u rdT

/-- `ℓ - 1 - j`. -/
def dE : Ex := .sub (.sub (.var 307) (.lit 1)) (.var 306)

/-- One level of one path. -/
def lvlBody (U : UParts) : Cmd :=
  .seq (cset dE 45) <| .seq (cset (kbE 45) 43) <| .seq U.lset <| .seq (cset (NcE 43 40) 47) <|
  .seq (cset (.mod (.var 305) (.var 47)) 100) <| .seq (cset (.div (.var 305) (.var 47)) 305) <|
  .seq (cset U.lnE 101) <| .seq (cset (U.srE false) 104) <| .seq (cset (U.srE true) 105) <|
  .seq (cset (.mod (.var 306) (.lit 2)) 320) <|
  .seq (cset (.mul (.var 43) (pow2 915 (.mul (.var 101) (.var 43)))) 321) <|
  .seq (fillC U.nxE 321 311 43 162 163 320) <| .seq (.copy 40 101) <| .seq (.copy 41 320) (.copy 42 43)

/-- One path: the levels, then the brute force, added to the sum. -/
def pathBody (U : UParts) : Cmd :=
  .seq (.copy 305 304) <| .seq (.copy 40 12) <| .seq (.setK 41 2) <| .seq (.copy 42 316) <|
  .seq (.loop 307 306 (lvlBody U)) <| .seq (cset bruteU 312) (cset (.mod (.add (.var 308) (.var 312)) (.var 10)) 308)

/-- The whole count modulo `m` (in `10`), into `308`. -/
def countM (U : UParts) : Cmd :=
  .seq (cset U.tsE 15) <| .seq (cset (.mul (.var 316) (pow2 915 (.mul (.var 12) (.var 316)))) 321) <|
  .seq (.setK 320 2) <| .seq (fillC U.ttE 321 311 316 82 83 320) <| .seq (.setK 308 0) (.loop 303 304 (pathBody U))

/-- The new flag count. -/
def flagE : Ex :=
  ifEq (.var 308) (.mod (.mul (.mod (.var 309) (.var 10)) c1E) (.var 10)) (.var 301) (.add (.var 301) (.lit 1))

/-- One level of the multiplier modulo `m` (in `10`). -/
def dmBody (U : UParts) : Cmd :=
  .seq (cset dE 45) <| .seq (cset (kbE 45) 43) <|
  .seq (cset (.mod (.mul (.var 309) (multVm 43 40 10)) (.var 10)) 309) <|
  .seq U.lset <| .seq (cset U.lnE 101) (.copy 40 101)

/-- The multiplier `deepMult` modulo `m`, into `309`. -/
def dmLoop (U : UParts) : Cmd :=
  .seq (.copy 40 12) <| .seq (.setK 309 1) (.loop 307 306 (dmBody U))

/-- One modulus. -/
def modBody (U : UParts) : Cmd :=
  .seq (.copy 10 300) <| .seq (.setK 315 2)
    (.ifLt 10 315 .skip (.seq (countM U) (.seq (dmLoop U) (cset flagE 301))))

/-- One level of the sweep (number of paths, multiplier, its exponent bound). -/
def sweepBody (U : UParts) : Cmd :=
  .seq (cset dE 45) <| .seq (cset (kbE 45) 43) <| .seq (cset (NcE 43 40) 47) <|
  .seq (cset (.mul (.var 303) (.var 47)) 303) <|
  .seq (cset (.add (.var 310) (.mul (.mul (.lit 2) (g4E 43)) (tBE 40))) 310) <|
  .seq U.lset <| .seq (cset U.lnE 101) (.copy 40 101)

/-- The parameters and the sweep. -/
def setup (U : UParts) : Cmd :=
  .seq (cset sE 11) <| .seq (cset ellE 307) <| .seq (cset (kbE 307) 43) <| .seq (.copy 316 43) <|
  .seq U.tset <| .seq (cset U.l0E 12) <|
  .seq (.copy 40 12) <| .seq (.setK 303 1) <| .seq (.setK 310 0) <|
  .loop 307 306 (sweepBody U)

/-- `2 M + 1`. -/
def mE : Ex := .add (.mul (.lit 2) (.add (.add (.var 0) (.var 310)) (.lit 4))) (.lit 1)

/-- The output bit. -/
def bitE : Ex := .ifLt (.lit 0) (.var 301) (.lit 0) (.lit 1)

end Uni

open Uni in
/-- **The uniform counting command.** -/
def uniC (U : UParts) : Cmd :=
  .seq (setup U) <| .seq (cset mE 314) <| .seq (.setK 301 0) <| .seq (.loop 314 300 (modBody U)) (cset bitE 3)

end Factoring.Aux
