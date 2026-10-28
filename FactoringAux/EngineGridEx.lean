/-
The row and column networks of a level as expressions (from the codes of `EngineGrid.lean`).

* `decE`: the decoder of `coefFac` as a state fold (`iter`); **`eval_decE`**: its value is `decN`.
* `facLE`, `facRE`: the rectangle factors (`facLN`, `facRN`), with the pieces `pieceN` as sums of decoder products.

Not an audit surface.
-/
module

public import FactoringAux.EngineGrid
public import FactoringAux.EngineIn

@[expose] public section

namespace Factoring.Aux

open Finset Ex

theorem testBit_iff (x i : ℕ) : x.testBit i = true ↔ x / 2 ^ i % 2 = 1 := by
  rw [← Nat.zero_add i, ← Nat.testBit_div_two_pow, Nat.testBit_zero]; simp

/-- Look up variables in updated environments (the side conditions by `omega`). -/
macro "upd" : tactic => `(tactic| simp (disch := omega) only [Function.update_self, Function.update_of_ne])

/-- `σ'` agrees with `σ` below `b`. -/
def AgB (b : ℕ) (σ σ' : ℕ → ℕ) : Prop := ∀ y < b, σ' y = σ y

theorem AgB.upd {b : ℕ} {σ σ' : ℕ → ℕ} (h : AgB b σ σ') {x : ℕ} (hx : b ≤ x) (v : ℕ) :
    AgB b σ (Function.update σ' x v) := fun y hy => by
  rw [Function.update_of_ne (by omega)]; exact h y hy

theorem AgB.refl (b : ℕ) (σ : ℕ → ℕ) : AgB b σ σ := fun _ _ => rfl

namespace Ex

/-- The decoder: state in `b`, scratch `b+1 … b+6`; `cvE`, `evE` read the block index `b+3` and the block code
`b+5`. -/
def decE (b vm : ℕ) (tE QE jE cvE evE : Ex) : Ex :=
  .lett b (.iter (b + 1) (b + 2) tE (.add (.mul jE (.var vm)) (.mod (.lit 1) (.var vm)))
    (.lett (b + 3) (.sub (.sub tE (.lit 1)) (.var (b + 1)))
      (.lett (b + 4) (.div (.var (b + 2)) (.var vm))
        (ifEq (.mod (.div QE (pow2 (b + 6) (.add (.add (.mul (.lit 4) (.var (b + 3))) (.mul (.lit 3) (.var (b + 4))))
            (.lit 3)))) (.lit 2)) (.lit 1)
          (.add (.mul (.var (b + 4)) (.var vm)) (.mod (.mul (.mod (.var (b + 2)) (.var vm))
            (.lett (b + 5) (.div QE (pow2 (b + 6) (.add (.mul (.lit 4) (.var (b + 3))) (.mul (.lit 3) (.var (b + 4))))))
              cvE)) (.var vm)))
          (ifEq (.var (b + 4)) (.lit 0) (.lit 0)
            (.add (.mul (.sub (.var (b + 4)) (.lit 1)) (.var vm)) (.mod (.mul (.mod (.var (b + 2)) (.var vm))
              (.lett (b + 5) (.div QE (pow2 (b + 6) (.add (.mul (.lit 4) (.var (b + 3)))
                (.mul (.lit 3) (.sub (.var (b + 4)) (.lit 1)))))) evE)) (.var vm))))))))
    (ifEq (.div (.var b) (.var vm)) (.lit 0) (.mod (.var b) (.var vm)) (.lit 0))

end Ex

variable {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ}

theorem eval_lett (x : ℕ) (e b : Ex) : eval σ A (.lett x e b) = eval (Function.update σ x (eval σ A e)) A b := rfl

theorem eval_iter (x y : ℕ) (n i b : Ex) : eval σ A (.iter x y n i b) =
    iterF (fun j s => eval (Function.update (Function.update σ x j) y s) A b) (eval σ A i) (eval σ A n) := rfl

theorem eval_decE {b vm m : ℕ} (hvm : vm < b) (hm : σ vm = m) {tE QE jE cvE evE : Ex}
    {t Q j : ℕ} {cv ev : ℕ → ℕ → ℕ}
    (ht : ∀ σ', AgB b σ σ' → eval σ' A tE = t) (hQ : ∀ σ', AgB b σ σ' → eval σ' A QE = Q)
    (hj : eval σ A jE = j)
    (hcv : ∀ σ', AgB b σ σ' → eval σ' A cvE = cv (σ' (b + 3)) (σ' (b + 5)))
    (hev : ∀ σ', AgB b σ σ' → eval σ' A evE = ev (σ' (b + 3)) (σ' (b + 5))) :
    eval σ A (decE b vm tE QE jE cvE evE) = decN m Q cv ev t j := by
  have hstep : ∀ i st, eval (Function.update (Function.update σ (b + 1) i) (b + 2) st) A
      (.lett (b + 3) (.sub (.sub tE (.lit 1)) (.var (b + 1)))
      (.lett (b + 4) (.div (.var (b + 2)) (.var vm))
        (ifEq (.mod (.div QE (pow2 (b + 6) (.add (.add (.mul (.lit 4) (.var (b + 3))) (.mul (.lit 3) (.var (b + 4))))
            (.lit 3)))) (.lit 2)) (.lit 1)
          (.add (.mul (.var (b + 4)) (.var vm)) (.mod (.mul (.mod (.var (b + 2)) (.var vm))
            (.lett (b + 5) (.div QE (pow2 (b + 6) (.add (.mul (.lit 4) (.var (b + 3))) (.mul (.lit 3) (.var (b + 4))))))
              cvE)) (.var vm)))
          (ifEq (.var (b + 4)) (.lit 0) (.lit 0)
            (.add (.mul (.sub (.var (b + 4)) (.lit 1)) (.var vm)) (.mod (.mul (.mod (.var (b + 2)) (.var vm))
              (.lett (b + 5) (.div QE (pow2 (b + 6) (.add (.mul (.lit 4) (.var (b + 3)))
                (.mul (.lit 3) (.sub (.var (b + 4)) (.lit 1)))))) evE)) (.var vm))))))) =
      cfAt m Q cv ev (t - 1 - i) st := by
    intro i st
    set σ2 := Function.update (Function.update σ (b + 1) i) (b + 2) st
    have a2 : AgB b σ σ2 := ((AgB.refl b σ).upd (by omega) i).upd (by omega) st
    set σ3 := Function.update σ2 (b + 3) (t - 1 - i)
    have a3 : AgB b σ σ3 := a2.upd (by omega) _
    set σ4 := Function.update σ3 (b + 4) (st / m)
    have a4 : AgB b σ σ4 := a3.upd (by omega) _
    have e3 : eval σ2 A (.sub (.sub tE (.lit 1)) (.var (b + 1))) = t - 1 - i := by
      simp only [Ex.eval, ht σ2 a2, σ2]; upd
    have e4 : eval σ3 A (.div (.var (b + 2)) (.var vm)) = st / m := by
      simp only [Ex.eval, σ3, σ2]; upd; rw [hm]
    have hm4 : σ4 vm = m := by rw [a4 vm hvm, hm]
    have v3 : σ4 (b + 3) = t - 1 - i := by simp only [σ4, σ3]; upd
    have v4 : σ4 (b + 4) = st / m := by simp only [σ4]; upd
    have v2 : σ4 (b + 2) = st := by simp only [σ4, σ3, σ2]; upd
    rw [eval_lett, e3, ← show σ3 = Function.update σ2 (b + 3) (t - 1 - i) from rfl, eval_lett, e4,
      ← show σ4 = Function.update σ3 (b + 4) (st / m) from rfl]
    rw [eval_ifEq]
    simp only [Ex.eval, eval_pow2, hQ σ4 a4, v3, v4, hm4, v2]
    unfold cfAt
    by_cases hb : Q.testBit (4 * (t - 1 - i) + 3 * (st / m) + 3) = true
    · rw [if_pos ((testBit_iff _ _).mp hb), if_pos hb]
      have a5 : AgB b σ (Function.update σ4 (b + 5) (Q / 2 ^ (4 * (t - 1 - i) + 3 * (st / m)))) := a4.upd (by omega) _
      rw [hcv _ a5]
      have w3 : Function.update σ4 (b + 5) (Q / 2 ^ (4 * (t - 1 - i) + 3 * (st / m))) (b + 3) = t - 1 - i := by
        upd; exact v3
      rw [w3, Function.update_self]
    · rw [if_neg (fun h => hb ((testBit_iff _ _).mpr h)), if_neg hb, eval_ifEq]
      simp only [Ex.eval, v4]
      by_cases h0 : st / m = 0
      · rw [if_pos h0, if_pos h0]
      · rw [if_neg h0, if_neg h0]
        simp only [Ex.eval, eval_pow2, hQ σ4 a4, v3, v4, hm4, v2]
        have a5 : AgB b σ (Function.update σ4 (b + 5) (Q / 2 ^ (4 * (t - 1 - i) + 3 * (st / m - 1)))) :=
          a4.upd (by omega) _
        rw [hev _ a5]
        have w3 : Function.update σ4 (b + 5) (Q / 2 ^ (4 * (t - 1 - i) + 3 * (st / m - 1))) (b + 3) = t - 1 - i := by
          upd; exact v3
        rw [w3, Function.update_self]
  unfold decE decN
  rw [eval_lett, eval_iter]
  simp only [hstep]
  have hinit : eval σ A (.add (.mul jE (.var vm)) (.mod (.lit 1) (.var vm))) = j * m + 1 % m := by
    simp only [Ex.eval, hj, hm]
  rw [hinit, ht σ (AgB.refl _ _), iterF_cfAt, eval_ifEq]
  have hmb : Function.update σ b (cfRun m Q cv ev t (j * m + 1 % m)) vm = m := by upd; exact hm
  simp only [Ex.eval, Function.update_self, hmb]
  rfl

namespace Ex

/-- `t = ⌈λ/3⌉` from the variable `vl`. -/
def tBE (vl : ℕ) : Ex := .div (.add (.var vl) (.lit 2)) (.lit 3)

/-- `X / 2^(3s)` for the block index `s = var (b+3)`. -/
def blkAt (b vX : ℕ) : Ex := .div (.var vX) (pow2 (b + 6) (.mul (.lit 3) (.var (b + 3))))

def cvPE (b vm vX vY : ℕ) : Ex := psiE vm (.var (b + 5)) (blkAt b vX) (blkAt b vY)
def evLE (b vX vY : ℕ) : Ex :=
  ifEq (.mod (.var (b + 5)) (.lit 64)) (.add (.mod (blkAt b vX) (.lit 8)) (.mul (.lit 8) (.mod (blkAt b vY) (.lit 8))))
    (.lit 1) (.lit 0)
def cvRE (b vm vU vV : ℕ) : Ex := psiE vm (.var (b + 5)) (blkAt b vV) (blkAt b vU)
def evRRE (b vm vU vV : ℕ) : Ex := CxE vm (.var (b + 5)) (.div (.var (b + 5)) (.lit 8)) (blkAt b vU) (blkAt b vV)
def evCRE (b vm vU vV : ℕ) : Ex := RxE vm (.var (b + 5)) (blkAt b vU) (.div (.var (b + 5)) (.lit 8)) (blkAt b vV)

/-- The decoders of `decL`, `decRR`, `decCR`. -/
def decLE (b vm vl vX vY : ℕ) (jE QE : Ex) : Ex := decE b vm (tBE vl) QE jE (cvPE b vm vX vY) (evLE b vX vY)
def decRRE (b vm vl vU vV : ℕ) (jE QE : Ex) : Ex := decE b vm (tBE vl) QE jE (cvRE b vm vU vV) (evRRE b vm vU vV)
def decCRE (b vm vl vU vV : ℕ) (jE QE : Ex) : Ex := decE b vm (tBE vl) QE jE (cvRE b vm vU vV) (evCRE b vm vU vV)

/-- `pieceN` (piece index in `vi`, codes in `vX vY vU vV`); scratch from `b`. -/
def pieceE (b vm vl vi vX vY vU vV : ℕ) : Ex :=
  zsum b (pow2 (b + 1) (.add (.mul (.lit 4) (tBE vl)) (.mul (.lit 3) (.var vi)))) vm
    (zmul vm (decLE (b + 2) vm vl vX vY (.var vi) (.var b)) (decRRE (b + 10) vm vl vU vV (.var vi) (.var b)))

/-- The piece index read by the decoders: `t − i` for columns, `i` for rows. -/
def jOf (tr : Bool) (vl vi : ℕ) : Ex := if tr then .sub (tBE vl) (.var vi) else .var vi

/-- `facLN tr` (piece index `vi`, codes `vX vY`, factor code `vQ`); scratch from `b`. -/
def facLE (tr : Bool) (b vm vl vi vX vY vQ : ℕ) : Ex :=
  .lett b (jOf tr vl vi) (.ifLt (.add (.mul (.lit 4) (tBE vl)) (.mul (.lit 3) (.var b))) (.add (.mul (.lit 2) (.var vl)) (.lit 1))
    (decLE (b + 1) vm vl vX vY (.var b) (.var vQ))
    (ifEq (.mod (.var vQ) (pow2 (b + 1) (.add (.var vl) (.var vl))))
      (.add (.var vX) (.mul (pow2 (b + 1) (.var vl)) (.var vY))) (.lit 1) (.lit 0)))

/-- `facRN tr`; scratch from `b`. -/
def facRE (tr : Bool) (b vm vl vi vU vV vQ : ℕ) : Ex :=
  .lett b (jOf tr vl vi) (.ifLt (.add (.mul (.lit 4) (tBE vl)) (.mul (.lit 3) (.var b))) (.add (.mul (.lit 2) (.var vl)) (.lit 1))
    (if tr then decCRE (b + 1) vm vl vU vV (.var b) (.var vQ) else decRRE (b + 1) vm vl vU vV (.var b) (.var vQ))
    (.lett (b + 1) (.mod (.var vQ) (pow2 (b + 3) (.var vl)))
      (.lett (b + 2) (.mod (.div (.var vQ) (pow2 (b + 3) (.var vl))) (pow2 (b + 3) (.var vl)))
        (if tr then pieceE (b + 4) vm vl vi (b + 1) vU (b + 2) vV else pieceE (b + 4) vm vl vi (b + 1) (b + 2) vU vV))))

end Ex

section Dec

variable {b vm vl m lam : ℕ}

theorem eval_tBE {σ' : ℕ → ℕ} (h : σ' vl = lam) : eval σ' A (tBE vl) = tB lam := by
  simp only [tBE, Ex.eval, h, tB]

theorem eval_blkAt {σ' : ℕ → ℕ} (vX : ℕ) : eval σ' A (blkAt b vX) = σ' vX / 2 ^ (3 * σ' (b + 3)) := by
  simp only [blkAt, Ex.eval, eval_pow2]

theorem eval_cvPE {σ' : ℕ → ℕ} (vX vY : ℕ) (hm : σ' vm = m) :
    eval σ' A (cvPE b vm vX vY) = cvP m (σ' vX) (σ' vY) (σ' (b + 3)) (σ' (b + 5)) := by
  simp only [cvPE, eval_psiE, eval_blkAt, Ex.eval, hm, cvP]

theorem eval_evLE {σ' : ℕ → ℕ} (vX vY : ℕ) :
    eval σ' A (evLE b vX vY) = evL (σ' vX) (σ' vY) (σ' (b + 3)) (σ' (b + 5)) := by
  simp only [evLE, eval_ifEq, eval_blkAt, Ex.eval, evL]
  norm_num

theorem eval_cvRE {σ' : ℕ → ℕ} (vU vV : ℕ) (hm : σ' vm = m) :
    eval σ' A (cvRE b vm vU vV) = psiN m (σ' (b + 5)) (σ' vV / 2 ^ (3 * σ' (b + 3))) (σ' vU / 2 ^ (3 * σ' (b + 3))) := by
  simp only [cvRE, eval_psiE, eval_blkAt, Ex.eval, hm]

theorem eval_evRRE {σ' : ℕ → ℕ} (vU vV : ℕ) (hm : σ' vm = m) :
    eval σ' A (evRRE b vm vU vV) = evRowR m (σ' vU) (σ' vV) (σ' (b + 3)) (σ' (b + 5)) := by
  simp only [evRRE, eval_CxE, eval_blkAt, Ex.eval, hm, evRowR]
  norm_num

theorem eval_evCRE {σ' : ℕ → ℕ} (vU vV : ℕ) (hm : σ' vm = m) :
    eval σ' A (evCRE b vm vU vV) = evColR m (σ' vU) (σ' vV) (σ' (b + 3)) (σ' (b + 5)) := by
  simp only [evCRE, eval_RxE, eval_blkAt, Ex.eval, hm, evColR]
  norm_num

theorem eval_decLE {vX vY : ℕ} (hvm : vm < b) (hvl : vl < b) (hX : vX < b) (hY : vY < b) (hm : σ vm = m)
    (hl : σ vl = lam) {jE QE : Ex} {j Q : ℕ} (hj : eval σ A jE = j)
    (hQ : ∀ σ', AgB b σ σ' → eval σ' A QE = Q) :
    eval σ A (decLE b vm vl vX vY jE QE) = decL m lam (σ vX) (σ vY) j Q := by
  unfold decLE decL
  refine eval_decE hvm hm (fun σ' h => eval_tBE (by rw [h vl hvl, hl])) hQ hj (fun σ' h => ?_) (fun σ' h => ?_)
  · rw [eval_cvPE vX vY (by rw [h vm hvm, hm]), h vX hX, h vY hY]
  · rw [eval_evLE, h vX hX, h vY hY]

theorem eval_decRRE {vU vV : ℕ} (hvm : vm < b) (hvl : vl < b) (hU : vU < b) (hV : vV < b) (hm : σ vm = m)
    (hl : σ vl = lam) {jE QE : Ex} {j Q : ℕ} (hj : eval σ A jE = j)
    (hQ : ∀ σ', AgB b σ σ' → eval σ' A QE = Q) :
    eval σ A (decRRE b vm vl vU vV jE QE) = decRR m lam (σ vU) (σ vV) j Q := by
  unfold decRRE decRR
  refine eval_decE hvm hm (fun σ' h => eval_tBE (by rw [h vl hvl, hl])) hQ hj (fun σ' h => ?_) (fun σ' h => ?_)
  · rw [eval_cvRE vU vV (by rw [h vm hvm, hm]), h vU hU, h vV hV]
  · rw [eval_evRRE vU vV (by rw [h vm hvm, hm]), h vU hU, h vV hV]

theorem eval_decCRE {vU vV : ℕ} (hvm : vm < b) (hvl : vl < b) (hU : vU < b) (hV : vV < b) (hm : σ vm = m)
    (hl : σ vl = lam) {jE QE : Ex} {j Q : ℕ} (hj : eval σ A jE = j)
    (hQ : ∀ σ', AgB b σ σ' → eval σ' A QE = Q) :
    eval σ A (decCRE b vm vl vU vV jE QE) = decCR m lam (σ vU) (σ vV) j Q := by
  unfold decCRE decCR
  refine eval_decE hvm hm (fun σ' h => eval_tBE (by rw [h vl hvl, hl])) hQ hj (fun σ' h => ?_) (fun σ' h => ?_)
  · rw [eval_cvRE vU vV (by rw [h vm hvm, hm]), h vU hU, h vV hV]
  · rw [eval_evCRE vU vV (by rw [h vm hvm, hm]), h vU hU, h vV hV]

theorem eval_pieceE {vi vX vY vU vV : ℕ} (hvm : vm < b) (hvl : vl < b) (hi : vi < b) (hX : vX < b) (hY : vY < b)
    (hU : vU < b) (hV : vV < b) (hm : σ vm = m) (hl : σ vl = lam) :
    eval σ A (pieceE b vm vl vi vX vY vU vV) = pieceN m lam (σ vi) (σ vX) (σ vY) (σ vU) (σ vV) := by
  unfold pieceE zsum
  rw [Ex.eval]
  have hn : eval σ A (pow2 (b + 1) (.add (.mul (.lit 4) (tBE vl)) (.mul (.lit 3) (.var vi)))) =
      2 ^ (4 * tB lam + 3 * σ vi) := by
    rw [eval_pow2]; simp only [Ex.eval, eval_tBE hl]
  rw [hn, show eval σ A (.var vm) = m from hm, foldSum_eq, pieceN, Finset.sum_nat_mod (range _) m
    (fun q => decL m lam (σ vX) (σ vY) (σ vi) q * decRR m lam (σ vU) (σ vV) (σ vi) q)]
  congr 1
  refine sum_congr rfl fun q _ => ?_
  have hm' : Function.update σ b q vm = m := by upd; exact hm
  have hl' : Function.update σ b q vl = lam := by upd; exact hl
  have e1 : ∀ v, v < b → Function.update σ b q v = σ v := fun v hv => by upd
  simp only [zmul, Ex.eval, hm']
  rw [eval_decLE (j := σ vi) (Q := q) (by omega) (by omega) (by omega) (by omega) hm' hl'
      (by simp only [Ex.eval]; exact e1 vi hi)
      (fun σ' h => by simp only [Ex.eval]; rw [h b (by omega)]; upd),
    eval_decRRE (j := σ vi) (Q := q) (by omega) (by omega) (by omega) (by omega) hm' hl'
      (by simp only [Ex.eval]; exact e1 vi hi)
      (fun σ' h => by simp only [Ex.eval]; rw [h b (by omega)]; upd)]
  rw [e1 vX hX, e1 vY hY, e1 vU hU, e1 vV hV]

theorem eval_jOf (tr : Bool) {vi : ℕ} {σ' : ℕ → ℕ} (hl : σ' vl = lam) :
    eval σ' A (jOf tr vl vi) = if tr then tB lam - σ' vi else σ' vi := by
  cases tr <;> simp [jOf, Ex.eval, eval_tBE hl]

theorem eval_facLE (tr : Bool) {vi vX vY vQ : ℕ} (hvm : vm < b) (hvl : vl < b) (hi : vi < b) (hX : vX < b)
    (hY : vY < b) (hQ : vQ < b) (hm : σ vm = m) (hl : σ vl = lam) :
    eval σ A (facLE tr b vm vl vi vX vY vQ) = facLN tr m lam (σ vi) (σ vX) (σ vY) (σ vQ) := by
  unfold facLE facLN
  rw [eval_lett, eval_jOf tr hl]
  set j := if tr = true then tB lam - σ vi else σ vi
  set σ1 := Function.update σ b j
  have e1 : ∀ v, v < b → σ1 v = σ v := fun v hv => by simp only [σ1]; upd
  rw [eval_ifLt']
  have hc : eval σ1 A (.add (.mul (.lit 4) (tBE vl)) (.mul (.lit 3) (.var b))) = 4 * tB lam + 3 * j := by
    simp only [Ex.eval, eval_tBE (show σ1 vl = lam by rw [e1 vl hvl, hl]), σ1, Function.update_self]
  have hc2 : eval σ1 A (.add (.mul (.lit 2) (.var vl)) (.lit 1)) = 2 * lam + 1 := by
    simp only [Ex.eval, e1 vl hvl, hl]
  rw [hc, hc2]
  dsimp only
  by_cases h : 4 * tB lam + 3 * j ≤ 2 * lam
  · rw [if_pos (by omega), if_pos h]
    rw [eval_decLE (j := j) (by omega) (by omega) (by omega) (by omega) (by rw [e1 vm hvm, hm]) (by rw [e1 vl hvl, hl])
      (by simp only [Ex.eval, σ1, Function.update_self]) (fun σ' h' => by simp only [Ex.eval]; rw [h' vQ (by omega), e1 vQ hQ])]
    rw [e1 vX hX, e1 vY hY]
  · rw [if_neg (by omega), if_neg h, eval_ifEq]
    simp only [Ex.eval, eval_pow2, e1 vQ hQ, e1 vl hvl, hl, e1 vX hX, e1 vY hY]

theorem eval_facRE (tr : Bool) {vi vU vV vQ : ℕ} (hvm : vm < b) (hvl : vl < b) (hi : vi < b) (hU : vU < b)
    (hV : vV < b) (hQ : vQ < b) (hm : σ vm = m) (hl : σ vl = lam) :
    eval σ A (facRE tr b vm vl vi vU vV vQ) = facRN tr m lam (σ vi) (σ vU) (σ vV) (σ vQ) := by
  unfold facRE facRN
  rw [eval_lett, eval_jOf tr hl]
  set j := if tr = true then tB lam - σ vi else σ vi
  set σ1 := Function.update σ b j
  have e1 : ∀ v, v < b → σ1 v = σ v := fun v hv => by simp only [σ1]; upd
  rw [eval_ifLt']
  have hc : eval σ1 A (.add (.mul (.lit 4) (tBE vl)) (.mul (.lit 3) (.var b))) = 4 * tB lam + 3 * j := by
    simp only [Ex.eval, eval_tBE (show σ1 vl = lam by rw [e1 vl hvl, hl]), σ1, Function.update_self]
  have hc2 : eval σ1 A (.add (.mul (.lit 2) (.var vl)) (.lit 1)) = 2 * lam + 1 := by
    simp only [Ex.eval, e1 vl hvl, hl]
  rw [hc, hc2]
  dsimp only
  have hm1 : σ1 vm = m := by rw [e1 vm hvm, hm]
  have hl1 : σ1 vl = lam := by rw [e1 vl hvl, hl]
  have hj1 : eval σ1 A (.var b) = j := by simp only [Ex.eval, σ1, Function.update_self]
  have hQ1 : ∀ σ', AgB (b + 1) σ1 σ' → eval σ' A (.var vQ) = σ vQ := fun σ' h' => by
    simp only [Ex.eval]; rw [h' vQ (by omega), e1 vQ hQ]
  by_cases h : 4 * tB lam + 3 * j ≤ 2 * lam
  · rw [if_pos (by omega), if_pos h]
    cases tr
    · simp only [Bool.false_eq_true, if_false]
      rw [eval_decRRE (by omega) (by omega) (by omega) (by omega) hm1 hl1 hj1 hQ1, e1 vU hU, e1 vV hV]
    · simp only [if_true]
      rw [eval_decCRE (by omega) (by omega) (by omega) (by omega) hm1 hl1 hj1 hQ1, e1 vU hU, e1 vV hV]
  · rw [if_neg (by omega), if_neg h, eval_lett, eval_lett]
    set σ2 := Function.update σ1 (b + 1) (eval σ1 A (.mod (.var vQ) (pow2 (b + 3) (.var vl))))
    set σ3 := Function.update σ2 (b + 2)
      (eval σ2 A (.mod (.div (.var vQ) (pow2 (b + 3) (.var vl))) (pow2 (b + 3) (.var vl))))
    have e3 : ∀ v, v < b → σ3 v = σ v := fun v hv => by simp only [σ3, σ2]; upd; exact e1 v hv
    have v1 : σ3 (b + 1) = σ vQ % 2 ^ lam := by
      simp only [σ3, σ2]; upd; simp only [Ex.eval, eval_pow2, e1 vQ hQ, e1 vl hvl, hl]
    have v2 : σ3 (b + 2) = σ vQ / 2 ^ lam % 2 ^ lam := by
      simp only [σ3]; upd
      simp only [Ex.eval, eval_pow2, σ2]; upd; rw [e1 vQ hQ, e1 vl hvl, hl]
    cases tr
    · simp only [Bool.false_eq_true, if_false]
      rw [eval_pieceE (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by rw [e3 vm hvm, hm]) (by rw [e3 vl hvl, hl]), e3 vi hi, v1, v2, e3 vU hU, e3 vV hV]
    · simp only [if_true]
      rw [eval_pieceE (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by rw [e3 vm hvm, hm]) (by rw [e3 vl hvl, hl]), e3 vi hi, v1, v2, e3 vU hU, e3 vV hV]

end Dec

/-! ### The line networks as expressions -/

/-- The data of the line expressions. -/
structure GP where
  /-- Argument base (`a b z q` at `u … u+3`; scratch `u+4 … u+45`). -/
  u : ℕ
  /-- The modulus variable. -/
  vm : ℕ
  /-- The variable holding `λ`. -/
  vl : ℕ
  /-- The variable holding the choice code. -/
  vc : ℕ
  /-- The table's argument variables. -/
  vγ : ℕ
  vΘ : ℕ
  /-- The grid side. -/
  g : ℕ
  /-- The table. -/
  TE : Ex

namespace GridEx

variable (P : GP) (tr : Bool)

def p2 (e : Ex) : Ex := pow2 (P.u + 19) e
def powE (base e : Ex) : Ex := .prod (P.u + 18) e (.lit 0) base
def slcE (Q i w : Ex) : Ex :=
  .mod (.div Q (p2 P (.mul (.var P.vl) (.add w (.mul (.lit (P.g * P.g)) i))))) (p2 P (.var P.vl))
def ptIE (n i : Ex) : Ex := if tr then .add n (.mul (.lit P.g) i) else .add i (.mul (.lit P.g) n)
def phiDE (q : Ex) : Ex := .mod (.div (.var P.vc) (powE P (.add (tBE P.vl) (.lit 1)) q)) (.add (tBE P.vl) (.lit 1))
def qIdxE (n n' i i' : Ex) : Ex :=
  if tr then .add (.add n' (.mul (.lit P.g) n)) (.mul (.lit (P.g * P.g)) (.add i' (.mul (.lit P.g) i)))
  else .add (.add i' (.mul (.lit P.g) i)) (.mul (.lit (P.g * P.g)) (.add n' (.mul (.lit P.g) n)))
def minE (a b : Ex) : Ex := .ifLt a b a b
def cXE (i : Ex) : Ex :=
  if tr then minE (.mul (.lit 2) (.var P.vl)) (.add (.mul (.lit 4) (tBE P.vl)) (.mul (.lit 3) (.sub (tBE P.vl) i)))
  else minE (.mul (.lit 2) (.var P.vl)) (.add (.mul (.lit 4) (tBE P.vl)) (.mul (.lit 3) i))

/-- The width of the pair at quadruple slots `(var x, var y)`. -/
def cwE (x y : ℕ) : Ex := cXE P tr (phiDE P (qIdxE P tr (.var P.u) (.var (P.u + 1)) (.var x) (.var y)))

def sz : Ex := p2 P (.mul (.var P.vl) (.lit (P.g * (P.g * P.g))))

def W : Ex :=
  zmul P.vm
    (zprod (P.u + 4) (.lit P.g) P.vm
      (ifEq (slcE P (.var (P.u + 2)) (.var (P.u + 4)) (ptIE P tr (.var P.u) (.var (P.u + 4)))) (.lit 0)
        (.lett P.vγ (ptIE P tr (.var P.u) (.var (P.u + 4)))
          (.lett P.vΘ (.div (.var (P.u + 2)) (p2 P (.mul (.var P.vl) (.mul (.lit (P.g * P.g)) (.var (P.u + 4))))))
            P.TE))
        (.lit 0)))
    (zprod (P.u + 4) (.lit P.g) P.vm (zprod (P.u + 5) (.lit P.g) P.vm
      (.ifLt (.var (P.u + 4)) (.var (P.u + 5))
        (ifEq (slcE P (.var (P.u + 2)) (.var (P.u + 4)) (ptIE P tr (.var P.u) (.var (P.u + 5))))
          (slcE P (.var (P.u + 2)) (.var (P.u + 5)) (ptIE P tr (.var P.u) (.var (P.u + 4)))) (.lit 1) (.lit 0))
        (.lit 1))))

def c : Ex :=
  .add (.mul (.lit P.g) (.var P.vl)) (nsum (P.u + 4) (.lit P.g) (nsum (P.u + 5) (.lit P.g)
    (.ifLt (.var (P.u + 4)) (.var (P.u + 5)) (cwE P tr (P.u + 4) (P.u + 5)) (.lit 0))))

/-- The offset of pair `var (u+4)`. -/
def offE : Ex :=
  nsum (P.u + 7) (.var (P.u + 4)) (.lett (P.u + 8) (.mod (.div (.var (P.u + 7)) (.lit P.g)) (.lit P.g))
    (.lett (P.u + 9) (.mod (.var (P.u + 7)) (.lit P.g))
      (.ifLt (.var (P.u + 8)) (.var (P.u + 9)) (cwE P tr (P.u + 8) (P.u + 9)) (.lit 0))))

/-- A factor function: the line `nE` (the other node for the left side, the node for the right side) and the
rectangle factor `fac` (reading the piece index, `X`, `Y`, the factor code at `u+10 … u+13`). -/
def F (nE fac : Ex) : Ex :=
  zmul P.vm
    (zprod (P.u + 4) (.lit P.g) P.vm
      (ifEq (slcE P (.var (P.u + 2)) (.var (P.u + 4)) (ptIE P tr nE (.var (P.u + 4))))
        (.mod (.div (.var (P.u + 3)) (p2 P (.mul (.var P.vl) (.var (P.u + 4))))) (p2 P (.var P.vl))) (.lit 1) (.lit 0)))
    (zprod (P.u + 4) (.lit (P.g * P.g)) P.vm
      (.lett (P.u + 5) (.mod (.div (.var (P.u + 4)) (.lit P.g)) (.lit P.g))
        (.lett (P.u + 6) (.mod (.var (P.u + 4)) (.lit P.g))
          (.ifLt (.var (P.u + 5)) (.var (P.u + 6))
            (.lett (P.u + 10) (phiDE P (qIdxE P tr (.var P.u) (.var (P.u + 1)) (.var (P.u + 5)) (.var (P.u + 6))))
              (.lett (P.u + 11) (slcE P (.var (P.u + 2)) (.var (P.u + 5)) (ptIE P tr nE (.var (P.u + 6))))
                (.lett (P.u + 12) (slcE P (.var (P.u + 2)) (.var (P.u + 6)) (ptIE P tr nE (.var (P.u + 5))))
                  (.lett (P.u + 13) (.div (.div (.var (P.u + 3)) (p2 P (.mul (.lit P.g) (.var P.vl)))) (p2 P (offE P tr)))
                    fac))))
            (.lit 1)))))

/-- The line network's expressions. -/
def nex : NEx :=
  ⟨sz P, W P tr, c P tr,
    F P tr (.var (P.u + 1)) (facLE tr (P.u + 20) P.vm P.vl (P.u + 10) (P.u + 11) (P.u + 12) (P.u + 13)),
    F P tr (.var P.u) (facRE tr (P.u + 20) P.vm P.vl (P.u + 10) (P.u + 11) (P.u + 12) (P.u + 13))⟩

end GridEx

namespace GridEx

variable {P : GP} {tr : Bool} {σ : ℕ → ℕ} {lam cc : ℕ}

theorem eval_p2 (e : Ex) : eval σ A (p2 P e) = 2 ^ eval σ A e := eval_pow2 _ _

theorem eval_powE {base e : Ex} (hb : ∀ j, eval (Function.update σ (P.u + 18) j) A base = eval σ A base) :
    eval σ A (powE P base e) = eval σ A base ^ eval σ A e := by
  simp only [powE, Ex.eval, foldProd_zero, hb]
  exact pp_const _ _

theorem eval_slcE (hl : σ P.vl = lam) (Q i w : Ex) :
    eval σ A (slcE P Q i w) = slc lam P.g (eval σ A Q) (eval σ A i) (eval σ A w) := by
  simp only [slcE, Ex.eval, eval_p2, hl, slc]

theorem eval_ptIE (n i : Ex) : eval σ A (ptIE P tr n i) = ptI tr P.g (eval σ A n) (eval σ A i) := by
  cases tr <;> simp [ptIE, ptI, Ex.eval]

theorem eval_qIdxE (n n' i i' : Ex) :
    eval σ A (qIdxE P tr n n' i i') = qIdx tr P.g (eval σ A n) (eval σ A n') (eval σ A i) (eval σ A i') := by
  cases tr <;> simp [qIdxE, qIdx, Ex.eval]

theorem eval_phiDE (hl : σ P.vl = lam) (hc : σ P.vc = cc) (hvl : P.vl ≠ P.u + 18) (q : Ex) :
    eval σ A (phiDE P q) = phiD (tB lam) cc (eval σ A q) := by
  have hp := eval_powE (σ := σ) (A := A) (P := P) (base := .add (tBE P.vl) (.lit 1)) (e := q) (fun j => by
    simp only [Ex.eval, tBE]
    rw [Function.update_of_ne hvl])
  unfold phiDE
  simp only [Ex.eval, hp]
  simp only [eval_tBE hl, hc, phiD]

theorem eval_minE (a b : Ex) : eval σ A (minE a b) = min (eval σ A a) (eval σ A b) := by
  rw [minE, eval_ifLt']
  split_ifs with h
  · exact (min_eq_left h.le).symm
  · exact (min_eq_right (by omega)).symm

/-- The width function of a line network. -/
def cX (tr : Bool) (lam : ℕ) : ℕ → ℕ := if tr then cCol lam else cRow lam

theorem eval_cXE (hl : σ P.vl = lam) (i : Ex) : eval σ A (cXE P tr i) = cX tr lam (eval σ A i) := by
  cases tr
  · simp only [cXE, cX, Bool.false_eq_true, if_false, eval_minE, cRow]
    simp only [Ex.eval, eval_tBE hl, hl]
  · simp only [cXE, cX, if_true, eval_minE, cCol]
    simp only [Ex.eval, eval_tBE hl, hl]

theorem ptI_lt {g n i : ℕ} (hn : n < g) (hi : i < g) (tr : Bool) : ptI tr g n i < g * g := by
  cases tr <;> simp only [ptI, Bool.false_eq_true, if_false, if_true] <;> nlinarith

/-- Hypotheses of the line expressions. -/
structure GridHyp (m BT B : ℕ) (σ₀ : ℕ → ℕ) (A : ℕ → ℕ → ℕ) (P : GP) (lam cc : ℕ)
    (Tab : Clique (ZMod m) (P.g * P.g) lam) : Prop where
  hm : 1 < m
  hg : 0 < P.g
  rep : TRep m BT σ₀ A P.vγ P.vΘ P.TE Tab
  vm : σ₀ P.vm = m
  vl : σ₀ P.vl = lam
  vc : σ₀ P.vc = cc
  hvm : P.vm < BT
  hγ : BT ≤ P.vγ
  hΘ : BT ≤ P.vΘ
  hγΘ : P.vγ ≠ P.vΘ
  hlγ : P.vl ≠ P.vγ
  hBT : BT ≤ B
  hl : P.vl < B
  hc : P.vc < B
  hγB : P.vγ < B
  hΘB : P.vΘ < B
  hu : B ≤ P.u

variable {m BT B : ℕ} {σ₀ : ℕ → ℕ} {Tab : Clique (ZMod m) (P.g * P.g) lam}

theorem ZR_W (H : GridHyp m BT B σ₀ A P lam cc Tab) (hσ : Ag B σ₀ σ) {n Q : ℕ} (hn : n < P.g)
    (h0 : σ P.u = n) (h2 : σ (P.u + 2) = Q) :
    ZR m (eval σ A (W P tr)) (lineW (tabAt Tab) tr P.g lam Q n) := by
  have hu := H.hu; have hl := H.hl; have hγB := H.hγB; have hΘB := H.hΘB; have hBT := H.hBT
  have hvm := H.hvm; have hγ := H.hγ; have hΘ := H.hΘ
  have hmσ : σ P.vm = m := by rw [hσ _ (by omega), H.vm]
  have hlσ : σ P.vl = lam := by rw [hσ _ hl, H.vl]
  unfold W lineW
  refine ZR_zmul hmσ (by have := H.hm; omega) ?_ ?_
  · refine ZR_zprod hmσ H.hm (P.u + 4) (by rfl) _ fun i hi => ?_
    set σ1 := Function.update σ (P.u + 4) i
    have l1 : σ1 P.vl = lam := by simp only [σ1]; upd; exact hlσ
    have q1 : σ1 (P.u + 2) = Q := by simp only [σ1]; upd; exact h2
    have n1 : σ1 P.u = n := by simp only [σ1]; upd; exact h0
    have i1 : σ1 (P.u + 4) = i := by simp only [σ1]; upd
    rw [eval_ifEq, eval_slcE l1, eval_ptIE]
    simp only [Ex.eval, q1, n1, i1]
    split_ifs with hz
    · simp only [eval_ptIE, Ex.eval, eval_p2, n1, i1]
      have hlt := ptI_lt hn hi tr
      have hq : Function.update σ1 P.vγ (ptI tr P.g n i) (P.u + 2) = Q := by upd; exact q1
      have hl2 : Function.update σ1 P.vγ (ptI tr P.g n i) P.vl = lam := by
        rw [Function.update_of_ne H.hlγ]; exact l1
      have hi2 : Function.update σ1 P.vγ (ptI tr P.g n i) (P.u + 4) = i := by upd; exact i1
      simp only [hq, hl2, hi2]
      set σ3 := Function.update (Function.update σ1 P.vγ (ptI tr P.g n i)) P.vΘ (Q / 2 ^ (lam * (P.g * P.g * i)))
      have a3 : Ag BT σ₀ σ3 := ((((hσ.mono hBT).upd (by omega) i).upd hγ _).upd hΘ _)
      have g3 : σ3 P.vγ = ptI tr P.g n i := by simp only [σ3]; rw [Function.update_of_ne H.hγΘ]; simp
      have t3 : σ3 P.vΘ = Q / 2 ^ (lam * (P.g * P.g * i)) := by simp [σ3]
      have := H.rep σ3 a3 ⟨_, hlt⟩ _ g3 t3
      rw [tabAt, dif_pos hlt]
      exact this
    · exact ZR_zero (by have := H.hm; omega)
  · refine ZR_zprod hmσ H.hm (P.u + 4) (by rfl) _ fun i hi => ?_
    refine ZR_zprod (by upd; exact hmσ) H.hm (P.u + 5) (by rfl) _ fun i' hi' => ?_
    rw [eval_ifLt']
    simp only [Ex.eval]
    have e4 : Function.update (Function.update σ (P.u + 4) i) (P.u + 5) i' (P.u + 4) = i := by upd
    have e5 : Function.update (Function.update σ (P.u + 4) i) (P.u + 5) i' (P.u + 5) = i' := by upd
    simp only [e4, e5]
    by_cases hii : i < i'
    · rw [if_pos hii, if_pos hii, eval_ifEq, eval_slcE (by upd; exact hlσ), eval_slcE (by upd; exact hlσ),
        eval_ptIE, eval_ptIE]
      simp only [Ex.eval]
      have e2 : Function.update (Function.update σ (P.u + 4) i) (P.u + 5) i' (P.u + 2) = Q := by upd; exact h2
      have e0 : Function.update (Function.update σ (P.u + 4) i) (P.u + 5) i' P.u = n := by upd; exact h0
      simp only [e2, e0, e4, e5]
      exact ZR_ite (ZR_one H.hm) (ZR_zero (by have := H.hm; omega))
    · rw [if_neg hii, if_neg hii]
      exact ZR_one H.hm

theorem eval_cwE (hvl : P.vl ≠ P.u + 18) {σ' : ℕ → ℕ} (hl : σ' P.vl = lam) (hc : σ' P.vc = cc) {n n' : ℕ}
    (h0 : σ' P.u = n) (h1 : σ' (P.u + 1) = n') (x y : ℕ) :
    eval σ' A (cwE P tr x y) = cX tr lam (phiD (tB lam) cc (qIdx tr P.g n n' (σ' x) (σ' y))) := by
  simp only [cwE, eval_cXE hl, eval_phiDE hl hc hvl, eval_qIdxE, Ex.eval, h0, h1]

theorem eval_c (H : GridHyp m BT B σ₀ A P lam cc Tab) (hσ : Ag B σ₀ σ) {n n' : ℕ} (h0 : σ P.u = n)
    (h1 : σ (P.u + 1) = n') :
    eval σ A (c P tr) = lineC (cX tr lam) tr P.g lam (tB lam) cc n n' := by
  have hu := H.hu; have hl := H.hl; have hc := H.hc
  have hlσ : σ P.vl = lam := by rw [hσ _ hl, H.vl]
  have hcσ : σ P.vc = cc := by rw [hσ _ hc, H.vc]
  unfold c lineC
  rw [Ex.eval, eval_nsum]
  simp only [Ex.eval, hlσ]
  congr 1
  refine sum_congr rfl fun i _ => ?_
  rw [eval_nsum]
  refine sum_congr rfl fun i' _ => ?_
  rw [eval_ifLt']
  have e4 : Function.update (Function.update σ (P.u + 4) i) (P.u + 5) i' (P.u + 4) = i := by upd
  have e5 : Function.update (Function.update σ (P.u + 4) i) (P.u + 5) i' (P.u + 5) = i' := by upd
  simp only [Ex.eval, e4, e5]
  split_ifs
  · rw [eval_cwE (by omega) (by upd; exact hlσ) (by upd; exact hcσ) (by upd; exact h0) (by upd; exact h1), e4, e5]
  · rfl

/-- The width function of a line pair. -/
def cwF (tr : Bool) (g lam cc n n' : ℕ) (i i' : ℕ) : ℕ := cX tr lam (phiD (tB lam) cc (qIdx tr g n n' i i'))

theorem eval_offE (hvl : P.vl < P.u) (hvc : P.vc < P.u) {σ' : ℕ → ℕ} (hl : σ' P.vl = lam) (hc : σ' P.vc = cc) {n n' k : ℕ}
    (h0 : σ' P.u = n) (h1 : σ' (P.u + 1) = n') (h4 : σ' (P.u + 4) = k) :
    eval σ' A (offE P tr) = offC (cwF tr P.g lam cc n n') P.g k := by
  unfold offE offC
  rw [eval_nsum, show eval σ' A (.var (P.u + 4)) = k from h4]
  refine sum_congr rfl fun j _ => ?_
  simp only [Ex.eval]
  upd
  split_ifs
  · rw [eval_cwE (by omega) (by upd; exact hl) (by upd; exact hc) (by upd; exact h0) (by upd; exact h1)]
    upd
    rfl
  · rfl

theorem ZR_F (H : GridHyp m BT B σ₀ A P lam cc Tab) (hσ : Ag B σ₀ σ) {n0 n1 n Q Q' : ℕ} (nE fac : Ex)
    (h0 : σ P.u = n0) (h1 : σ (P.u + 1) = n1) (h2 : σ (P.u + 2) = Q) (h3 : σ (P.u + 3) = Q')
    (hn : ∀ σ', (∀ y, y < P.u + 2 → σ' y = σ y) → eval σ' A nE = n)
    (fN : ℕ → ℕ → ℕ → ℕ → ℕ) (hlt : ∀ a b c d, fN a b c d < m)
    (hfac : ∀ σ', σ' P.vm = m → σ' P.vl = lam →
      eval σ' A fac = fN (σ' (P.u + 10)) (σ' (P.u + 11)) (σ' (P.u + 12)) (σ' (P.u + 13))) :
    ZR m (eval σ A (F P tr nE fac))
      (lineF (fun i i' X Y Q'' => (fN (phiD (tB lam) cc (qIdx tr P.g n0 n1 i i')) X Y Q'' : ZMod m))
        (cwF tr P.g lam cc n0 n1) tr P.g lam Q n Q') := by
  have hu := H.hu; have hl := H.hl; have hc := H.hc; have hvm := H.hvm; have hBT := H.hBT
  have hmσ : σ P.vm = m := by rw [hσ _ (by omega), H.vm]
  have hlσ : σ P.vl = lam := by rw [hσ _ hl, H.vl]
  have hcσ : σ P.vc = cc := by rw [hσ _ hc, H.vc]
  unfold F lineF
  refine ZR_zmul hmσ (by have := H.hm; omega) ?_ ?_
  · refine ZR_zprod hmσ H.hm (P.u + 4) (by rfl) _ fun i _ => ?_
    have hn1 : eval (Function.update σ (P.u + 4) i) A nE = n := hn _ fun y hy => by upd
    rw [eval_ifEq, eval_slcE (by upd; exact hlσ), eval_ptIE, hn1]
    simp only [Ex.eval, eval_p2]
    have e2 : Function.update σ (P.u + 4) i (P.u + 2) = Q := by upd; exact h2
    have e3 : Function.update σ (P.u + 4) i (P.u + 3) = Q' := by upd; exact h3
    have e4 : Function.update σ (P.u + 4) i (P.u + 4) = i := by upd
    have el : Function.update σ (P.u + 4) i P.vl = lam := by upd; exact hlσ
    simp only [e2, e3, e4, el]
    exact ZR_ite (ZR_one H.hm) (ZR_zero (by have := H.hm; omega))
  · refine ZR_zprod hmσ H.hm (P.u + 4) (by rfl) _ fun k _ => ?_
    simp only [Ex.eval]
    upd
    by_cases hk : k / P.g % P.g < k % P.g
    · rw [if_pos hk, if_pos hk]
      rw [hfac _ (by upd; exact hmσ) (by upd; exact hlσ)]
      simp only [Ex.eval, eval_p2]
      upd
      rw [eval_phiDE (by upd; exact hlσ) (by upd; exact hcσ) (by omega), eval_qIdxE,
        eval_slcE (by upd; exact hlσ), eval_slcE (by upd; exact hlσ), eval_ptIE, eval_ptIE,
        eval_offE (tr := tr) (k := k) (by omega) (by omega) (by upd; exact hlσ) (by upd; exact hcσ) (by upd; exact h0)
          (by upd; exact h1) (by upd)]
      simp only [Ex.eval]
      upd
      rw [hn _ (fun y hy => by upd), hn _ (fun y hy => by upd)]
      simp only [h0, h1, h2, h3, hlσ]
      exact ⟨hlt _ _ _ _, rfl⟩
    · rw [if_neg hk, if_neg hk]
      exact ZR_one H.hm

theorem lineF_congr {f f' : ℕ → ℕ → ℕ → ℕ → ℕ → ZMod m}
    (h : ∀ i i' X Y Q'', X < 2 ^ lam → Y < 2 ^ lam → f i i' X Y Q'' = f' i i' X Y Q'')
    (cw : ℕ → ℕ → ℕ) (tr : Bool) (g Q n Q' : ℕ) : lineF f cw tr g lam Q n Q' = lineF f' cw tr g lam Q n Q' := by
  unfold lineF
  congr 1
  refine prod_congr rfl fun k _ => ?_
  split_ifs
  · exact h _ _ _ _ _ (slc_lt _ _ _ _ _) (slc_lt _ _ _ _ _)
  · rfl

theorem cwF_row (g lam cc n n' : ℕ) :
    cwF false g lam cc n n' = fun i i' => cRow lam (phiD (tB lam) cc (qIdx false g n n' i i')) := rfl

theorem cwF_col (g lam cc n n' : ℕ) :
    cwF true g lam cc n n' = fun i i' => cCol lam (phiD (tB lam) cc (qIdx true g n n' i i')) := rfl

/-- The common part of the two representations. -/
theorem lineRep_sz (H : GridHyp m BT B σ₀ A P lam cc Tab) (hσ : Ag B σ₀ σ) :
    eval σ A (sz P) = 2 ^ (lam * (P.g * (P.g * P.g))) := by
  simp only [sz, eval_p2, Ex.eval, hσ _ H.hl, H.vl]

/-- **The row network of a level, as expressions.** -/
theorem row_rep (H : GridHyp m BT B σ₀ A P lam cc Tab) (hcc : cc < (tB lam + 1) ^ (P.g * P.g * (P.g * P.g))) :
    NRep m P.vm B σ₀ A (NVars.std P.u) (nex P false)
      (rowNet (toGrid Tab) (restrictC ((phiEquiv P.g (tB lam)).symm ⟨cc, hcc⟩))) (rowCoding _ _) where
  hm := H.vm
  sz σ hσ a _ := lineRep_sz H hσ
  W σ hσ a z ha hz := by
    have e := (lineEquiv P.g lam).symm_apply_apply z
    have hz' : σ (P.u + 2) = (lineEquiv P.g lam z : ℕ) := hz
    rw [← e, rowNet_W_code]
    exact ZR_W H hσ a.2 ha hz'
  c σ hσ a b hab ha hb := by
    rw [rowNet_c_code _ _ a b hab]
    exact eval_c H hσ ha hb
  l σ hσ a b hab z q ha hb hz hq := by
    have hu := H.hu; have hl := H.hl; have hvm := H.hvm; have hBT := H.hBT
    have e := (lineEquiv P.g lam).symm_apply_apply z
    have hz' : σ (P.u + 2) = (lineEquiv P.g lam z : ℕ) := hz
    rw [← e, rowNet_l_code _ _ H.hg a b hab]
    have := ZR_F (tr := false) (n := (b : ℕ)) H hσ (.var (P.u + 1)) (facLE false (P.u + 20) P.vm P.vl (P.u + 10) (P.u + 11) (P.u + 12) (P.u + 13))
      ha hb hz' hq (fun σ' h' => by simp only [Ex.eval]; rw [h' _ (by omega)]; exact hb)
      (facLN false m lam) (fun _ _ _ _ => facLN_lt H.hm _ _ _ _ _)
      (fun σ' hm' hl' => eval_facLE false (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hm' hl')
    rw [lineF_congr (f' := fun i i' X Y Q'' => facRL m lam (phiD (tB lam) cc (qIdx false P.g a b i i')) X Y Q'')
      (fun i i' X Y Q'' hX hY => facLN_row (by have := H.hm; omega) _ _ _ _ hX hY), cwF_row] at this
    exact this
  r σ hσ a b hab z q ha hb hz hq := by
    have hu := H.hu; have hl := H.hl; have hvm := H.hvm; have hBT := H.hBT
    have e := (lineEquiv P.g lam).symm_apply_apply z
    have hz' : σ (P.u + 2) = (lineEquiv P.g lam z : ℕ) := hz
    rw [← e, rowNet_r_code _ _ H.hg a b hab]
    have := ZR_F (tr := false) (n := (a : ℕ)) H hσ (.var P.u) (facRE false (P.u + 20) P.vm P.vl (P.u + 10) (P.u + 11) (P.u + 12) (P.u + 13))
      ha hb hz' hq (fun σ' h' => by simp only [Ex.eval]; rw [h' _ (by omega)]; exact ha)
      (facRN false m lam) (fun _ _ _ _ => facRN_lt H.hm _ _ _ _ _)
      (fun σ' hm' hl' => eval_facRE false (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hm' hl')
    rw [lineF_congr (f' := fun i i' X Y Q'' => facRR m lam (phiD (tB lam) cc (qIdx false P.g a b i i')) X Y Q'')
      (fun i i' X Y Q'' hX hY => facRN_row (by have := H.hm; omega) _ _ _ _ hX hY), cwF_row] at this
    exact this

/-- **The column network of a level, as expressions.** -/
theorem col_rep (H : GridHyp m BT B σ₀ A P lam cc Tab) (hcc : cc < (tB lam + 1) ^ (P.g * P.g * (P.g * P.g))) :
    NRep m P.vm B σ₀ A (NVars.std P.u) (nex P true)
      (colNet (toGrid Tab) (restrictC ((phiEquiv P.g (tB lam)).symm ⟨cc, hcc⟩))) (colCoding _ _) where
  hm := H.vm
  sz σ hσ a _ := lineRep_sz H hσ
  W σ hσ a z ha hz := by
    have e := (lineEquiv P.g lam).symm_apply_apply z
    have hz' : σ (P.u + 2) = (lineEquiv P.g lam z : ℕ) := hz
    rw [← e, colNet_W_code]
    exact ZR_W H hσ a.2 ha hz'
  c σ hσ a b hab ha hb := by
    rw [colNet_c_code _ _ a b hab]
    exact eval_c H hσ ha hb
  l σ hσ a b hab z q ha hb hz hq := by
    have hu := H.hu; have hl := H.hl; have hvm := H.hvm; have hBT := H.hBT
    have e := (lineEquiv P.g lam).symm_apply_apply z
    have hz' : σ (P.u + 2) = (lineEquiv P.g lam z : ℕ) := hz
    rw [← e, colNet_l_code _ _ H.hg a b hab]
    have := ZR_F (tr := true) (n := (b : ℕ)) H hσ (.var (P.u + 1)) (facLE true (P.u + 20) P.vm P.vl (P.u + 10) (P.u + 11) (P.u + 12) (P.u + 13))
      ha hb hz' hq (fun σ' h' => by simp only [Ex.eval]; rw [h' _ (by omega)]; exact hb)
      (facLN true m lam) (fun _ _ _ _ => facLN_lt H.hm _ _ _ _ _)
      (fun σ' hm' hl' => eval_facLE true (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hm' hl')
    rw [lineF_congr (f' := fun i i' X Y Q'' => facCL m lam (phiD (tB lam) cc (qIdx true P.g a b i i')) X Y Q'')
      (fun i i' X Y Q'' hX hY => facLN_col (by have := H.hm; omega) _ _ _ _ hX hY), cwF_col] at this
    exact this
  r σ hσ a b hab z q ha hb hz hq := by
    have hu := H.hu; have hl := H.hl; have hvm := H.hvm; have hBT := H.hBT
    have e := (lineEquiv P.g lam).symm_apply_apply z
    have hz' : σ (P.u + 2) = (lineEquiv P.g lam z : ℕ) := hz
    rw [← e, colNet_r_code _ _ H.hg a b hab]
    have := ZR_F (tr := true) (n := (a : ℕ)) H hσ (.var P.u) (facRE true (P.u + 20) P.vm P.vl (P.u + 10) (P.u + 11) (P.u + 12) (P.u + 13))
      ha hb hz' hq (fun σ' h' => by simp only [Ex.eval]; rw [h' _ (by omega)]; exact ha)
      (facRN true m lam) (fun _ _ _ _ => facRN_lt H.hm _ _ _ _ _)
      (fun σ' hm' hl' => eval_facRE true (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hm' hl')
    rw [lineF_congr (f' := fun i i' X Y Q'' => facCR m lam (phiD (tB lam) cc (qIdx true P.g a b i i')) X Y Q'')
      (fun i i' X Y Q'' hX hY => facRN_col (by have := H.hm; omega) _ _ _ _ hX hY), cwF_col] at this
    exact this

end GridEx




end Factoring.Aux
