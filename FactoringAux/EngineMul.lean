/-
The multiplication network (`mulNet`, `MulNet.lean`) as expressions, with a coding.

* Codes of the gate settings (`gcode`): input gates in mixed radix `2^L` (`dCode`), a family of `A` residues of
  `ZMod M` in mixed radix `M` (`zCode`), `MID` gates as a pair of such codes, carries as `c + 2^fw · y`.
  `mulSz`, `mulCoding`.
* `MulEx.*`: the expressions.  `N` and `x` are read bit by bit only (`Ex.nBit`, `Ex.xBit`); every value met is
  below `2^(16 L A)` (`mulV`).  The ring `ZMod M` of the transform is computed with residues modulo `M` (an
  expression), the ring `ZMod m` of the network only meets the values `0`, `1`.
* **`mul_rep`**: the expressions represent `(mulNet, mulCoding)`; **`mul_bdd`**, `mul_vb`, `mul_fv`.

Not an audit surface.
-/
module

public import FactoringAux.MulNet
public import FactoringAux.EngineIn
public import FactoringAux.EngineBlk
public import FactoringAux.EngineCoarsenEx

@[expose] public section

namespace Factoring.Aux

open Finset Ex

/-! ### The coding -/

/-- `ZMod M ≃ Fin M` by values. -/
def zmEquiv (M : ℕ) [NeZero M] : ZMod M ≃ Fin M where
  toFun x := ⟨x.val, ZMod.val_lt x⟩
  invFun i := (i.val : ZMod M)
  left_inv x := ZMod.natCast_zmod_val x
  right_inv i := Fin.ext (ZMod.val_cast_of_lt i.2)

/-- The node count of the multiplication network. -/
def mulNodes (s : ℕ) : ℕ := pA s + (pA s + (pA s + (pA s + pA s * pA s)))

/-- `M^A`: codes of `A` residues. -/
def pZ (s : ℕ) : ℕ := pp (fun _ => pM s) (pA s)

/-- `(2^L)^h`: codes of the digits of an input gate. -/
def pD (s : ℕ) : ℕ := pp (fun _ => 2 ^ pL s) (ph s)

theorem pZ_pos (s : ℕ) : 0 < pZ s := pp_pos fun _ _ => by positivity
theorem pD_pos (s : ℕ) : 0 < pD s := pp_pos fun _ _ => by positivity

/-- Codes of a family of `A` residues. -/
def zCode (s : ℕ) : (Fin (pA s) → ZMod (pM s)) ≃ Fin (pZ s) :=
  (Equiv.arrowCongr (Equiv.refl _) (zmEquiv (pM s))).trans
    (codeEquiv (fun _ => pM s) (pA s) (fun _ _ => by positivity))

/-- Codes of the digits of an input gate. -/
def dCode (s : ℕ) : (Fin (ph s) → Fin (2 ^ pL s)) ≃ Fin (pD s) :=
  codeEquiv (fun _ => 2 ^ pL s) (ph s) (fun _ _ => by positivity)

/-- The number of settings of a gate. -/
def gsz (s : ℕ) : MG (pA s) → ℕ
  | .faP _ => pD s
  | .faQ _ => pD s
  | .mid _ => pZ s * pZ s
  | .ib _ => pZ s
  | .carry _ => pM s * 2 ^ fw s

theorem gsz_pos (s : ℕ) (i : MG (pA s)) : 0 < gsz s i := by
  have := pZ_pos s; have := pD_pos s
  cases i <;> simp only [gsz] <;> positivity

/-- The codes of the settings of a gate. -/
def gcode (s : ℕ) : ∀ i : MG (pA s), mS s i ≃ Fin (gsz s i)
  | .faP _ => dCode s
  | .faQ _ => dCode s
  | .mid _ => (Equiv.prodCongr (zCode s) (zCode s)).trans finProdFinEquiv
  | .ib _ => zCode s
  | .carry _ => (Equiv.prodCongr (zmEquiv (pM s)) (Equiv.refl _)).trans finProdFinEquiv

/-- **The sizes, by node index.** -/
def mulSz (s a : ℕ) : ℕ := if h : a < mulNodes s then gsz s ((MG.enum (pA s)).symm ⟨a, h⟩) else 1

theorem mulSz_pos (s a : ℕ) : 0 < mulSz s a := by
  unfold mulSz; split_ifs
  · exact gsz_pos _ _
  · exact Nat.one_pos

theorem mulSz_fin (s : ℕ) (a : Fin (mulNodes s)) : mulSz s a = gsz s ((MG.enum (pA s)).symm a) := by
  unfold mulSz; rw [dif_pos a.2]; rfl

/-- **The coding of the multiplication network.** -/
def mulCoding (s m N k x : ℕ) : Coding (mulNet s (ZMod m) N k x) where
  s := mulSz s
  pos _ := mulSz_pos _ _
  e a := (gcode s ((MG.enum (pA s)).symm a)).trans (finCongr (mulSz_fin s a).symm)

theorem mulCoding_e (s m N k x : ℕ) (a : Fin (mulNodes s)) (z : (mulNet s (ZMod m) N k x).S a) :
    ((mulCoding s m N k x).e a z : ℕ) = (gcode s ((MG.enum (pA s)).symm a) z : ℕ) := rfl

/-! ### Decoding -/

theorem dCode_dig (s : ℕ) (u : Fin (ph s) → Fin (2 ^ pL s)) (i : Fin (ph s)) :
    ((u i : Fin (2 ^ pL s)) : ℕ) = (dCode s u : ℕ) / pp (fun _ => 2 ^ pL s) i % 2 ^ pL s := by
  conv_lhs => rw [← (dCode s).symm_apply_apply u]
  rfl

theorem zCode_dig (s : ℕ) (y : Fin (pA s) → ZMod (pM s)) (r : Fin (pA s)) :
    (y r).val = (zCode s y : ℕ) / pp (fun _ => pM s) r % pM s := by
  conv_lhs => rw [← (zCode s).symm_apply_apply y]
  show (((dgx (fun _ => pM s) (zCode s y) r : ℕ) : ZMod (pM s))).val = _
  rw [ZMod.val_cast_of_lt (dgx_lt (n := fun _ => pM s) (by positivity) _)]
  rfl

theorem mid_code (s : ℕ) (k : Fin (pA s)) (z : mS s (.mid k)) :
    (gcode s (.mid k) z : ℕ) = (zCode s z.2 : ℕ) + pZ s * (zCode s z.1 : ℕ) := rfl

theorem mid_dig1 (s : ℕ) (k : Fin (pA s)) (z : mS s (.mid k)) :
    (gcode s (.mid k) z : ℕ) / pZ s % pZ s = zCode s z.1 := by
  rw [mid_code, Nat.add_mul_div_left _ _ (pZ_pos s), Nat.div_eq_of_lt (zCode s z.2).2, zero_add,
    Nat.mod_eq_of_lt (zCode s z.1).2]

theorem mid_dig2 (s : ℕ) (k : Fin (pA s)) (z : mS s (.mid k)) :
    (gcode s (.mid k) z : ℕ) % pZ s = zCode s z.2 := by
  rw [mid_code, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (zCode s z.2).2]

theorem carry_code (s : ℕ) (j : Fin (pA s * pA s)) (z : mS s (.carry j)) :
    (gcode s (.carry j) z : ℕ) = (z.2 : ℕ) + 2 ^ fw s * z.1.val := rfl

theorem carry_y (s : ℕ) (j : Fin (pA s * pA s)) (z : mS s (.carry j)) :
    (gcode s (.carry j) z : ℕ) / 2 ^ fw s % pM s = z.1.val := by
  rw [carry_code, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt z.2.2, zero_add,
    Nat.mod_eq_of_lt (ZMod.val_lt _)]

theorem carry_c (s : ℕ) (j : Fin (pA s * pA s)) (z : mS s (.carry j)) :
    (gcode s (.carry j) z : ℕ) % 2 ^ fw s = z.2 := by
  rw [carry_code, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt z.2.2]

/-! ### The expressions -/

namespace MulEx

variable (u vs : ℕ)

/-- `h = 2^s`. -/
def hE : Ex := pow2 (u + 4) (.var vs)
/-- `A = 2^(s+1)`. -/
def AE : Ex := pow2 (u + 4) (.add (.var vs) (.lit 1))
/-- `L = 2^(2s+1)`. -/
def LLE : Ex := pow2 (u + 4) (.add (.mul (.lit 2) (.var vs)) (.lit 1))
/-- `fw = 4L + 1`. -/
def fwE : Ex := .add (.mul (.lit 4) (LLE u vs)) (.lit 1)
/-- `M = 2^(4L) + 1`. -/
def ME : Ex := .add (pow2 (u + 4) (.mul (.lit 4) (LLE u vs))) (.lit 1)
/-- `2^L`. -/
def TLE : Ex := pow2 (u + 4) (LLE u vs)
/-- `2^fw`. -/
def PfE : Ex := pow2 (u + 4) (fwE u vs)
/-- `M^A`. -/
def PZE : Ex := nprod (u + 4) (AE u vs) (ME u vs)
/-- `(2^L)^h`. -/
def PDE : Ex := nprod (u + 4) (hE u vs) (TLE u vs)
/-- `c · A`. -/
def kA (c : ℕ) : Ex := .mul (.lit c) (AE u vs)

/-- Dispatch on the layer of the node in variable `v`. -/
def sel (v : ℕ) (e0 e1 e2 e3 e4 : Ex) : Ex :=
  .ifLt (.var v) (kA u vs 1) e0 (.ifLt (.var v) (kA u vs 2) e1
    (.ifLt (.var v) (kA u vs 3) e2 (.ifLt (.var v) (kA u vs 4) e3 e4)))

/-- `e · f mod M`. -/
def mM (e f : Ex) : Ex := .mod (.mul e f) (ME u vs)
/-- `∑_{x<n} b mod M`. -/
def sM (x : ℕ) (n b : Ex) : Ex := .sum x n (ME u vs) b
/-- `b^e mod M`. -/
def pw (b : ℕ) (e : Ex) : Ex := .prod (u + 4) e (ME u vs) (.lit b)
/-- `ω'^e = 16^((A·A − 1) e) mod M`. -/
def pwi (e : Ex) : Ex := pw u vs 16 (.mul (.sub (.mul (AE u vs) (AE u vs)) (.lit 1)) e)
/-- `T⁻¹ = 2^((2m − 1)(2s + 2)) mod M`. -/
def tE : Ex := pw u vs 2 (.mul (.sub (.mul (.lit 2) (.mul (.lit 4) (LLE u vs))) (.lit 1))
  (.add (.mul (.lit 2) (.var vs)) (.lit 2)))

/-- Digit `i` of an input-gate code `z`. -/
def dD (z i : Ex) : Ex := .mod (.div z (nprod (u + 4) i (TLE u vs))) (TLE u vs)
/-- Residue `i` of a residue-family code `z`. -/
def dZ (z i : Ex) : Ex := .mod (.div z (nprod (u + 4) i (ME u vs))) (ME u vs)

/-- The setting code. -/
def zv : Ex := .var (u + 2)
/-- The first family of a `MID` code. -/
def z1E : Ex := .mod (.div (zv u) (PZE u vs)) (PZE u vs)
/-- The second family of a `MID` code. -/
def z2E : Ex := .mod (zv u) (PZE u vs)
/-- The residue of a carry code. -/
def cyE : Ex := .mod (.div (zv u) (PfE u vs)) (ME u vs)
/-- The incoming carry of a carry code. -/
def ccE : Ex := .mod (zv u) (PfE u vs)

/-- `FA[r] → MID[k]` (`r = a mod A`, `k = b − 2A`). -/
def faMsg (va vb : ℕ) : Ex :=
  mM u vs (pw u vs 16 (.mul (.mod (.var va) (AE u vs)) (.sub (.var vb) (kA u vs 2))))
    (sM u vs (u + 5) (AE u vs) (mM u vs
      (.ifLt (.var (u + 5)) (hE u vs) (dD u vs (zv u) (.var (u + 5))) (.lit 0))
      (pw u vs 16 (.mul (.mul (AE u vs) (.var (u + 5))) (.sub (.var vb) (kA u vs 2))))))

/-- Stage 2 of a forward transform of the family coded by `z`, at `i`. -/
def hat (z i : Ex) : Ex :=
  sM u vs (u + 6) (AE u vs) (mM u vs (dZ u vs z (.var (u + 6))) (pw u vs 16 (.mul (.mul (AE u vs) (.var (u + 6))) i)))

/-- `MID[k] → IB[j]` (`k = a − 2A`, `j = b − 3A`). -/
def midMsg (va vb : ℕ) : Ex :=
  mM u vs (pwi u vs (.mul (.sub (.var va) (kA u vs 2)) (.sub (.var vb) (kA u vs 3))))
    (sM u vs (u + 5) (AE u vs) (mM u vs
      (mM u vs (hat u vs (z1E u vs) (.var (u + 5))) (hat u vs (z2E u vs) (.var (u + 5))))
      (pwi u vs (.mul (.mul (AE u vs) (.var (u + 5))) (.sub (.var vb) (kA u vs 3))))))

/-- `IB → CARRY[j]`, output `j₂` (`j₂ = j / A`). -/
def ibMsg (j2 : Ex) : Ex :=
  mM u vs (tE u vs) (sM u vs (u + 6) (AE u vs)
    (mM u vs (dZ u vs (zv u) (.var (u + 6))) (pwi u vs (.mul (.mul (AE u vs) (.var (u + 6))) j2))))

/-- **The message from node `va` to node `vb`** at the setting code `u + 2`. -/
def msg (va vb : ℕ) : Ex :=
  sel u vs va
    (sel u vs vb (.lit 0) (.lit 0) (faMsg u vs va vb) (.lit 0) (.lit 0))
    (sel u vs vb (.lit 0) (.lit 0) (faMsg u vs va vb) (.lit 0) (.lit 0))
    (sel u vs vb (dZ u vs (z1E u vs) (.var vb)) (dZ u vs (z2E u vs) (.sub (.var vb) (kA u vs 1))) (.lit 0)
      (midMsg u vs va vb) (.lit 0))
    (sel u vs vb (.lit 0) (.lit 0) (dZ u vs (zv u) (.sub (.var vb) (kA u vs 2))) (.lit 0)
      (ifEq (.mod (.sub (.var vb) (kA u vs 4)) (AE u vs)) (.sub (.var va) (kA u vs 3))
        (ibMsg u vs (.div (.sub (.var vb) (kA u vs 4)) (AE u vs))) (.lit 0)))
    (sel u vs vb (.lit 0) (.lit 0) (.lit 0)
      (ifEq (.mod (.sub (.var va) (kA u vs 4)) (AE u vs)) (.sub (.var vb) (kA u vs 3)) (cyE u vs) (.lit 0))
      (ifEq (.sub (.var vb) (kA u vs 4)) (.add (.sub (.var va) (kA u vs 4)) (.lit 1))
        (.div (.add (ccE u vs) (cyE u vs)) (TLE u vs))
        (ifEq (.sub (.var va) (kA u vs 4)) (.add (.sub (.var vb) (kA u vs 4)) (.lit 1)) (ccE u vs) (.lit 0))))

/-- `1` if nodes `u`, `u + 1` talk, else `0`. -/
def lnk : Ex :=
  sel u vs u
    (sel u vs (u + 1) (.lit 0) (.lit 0) (.lit 1) (.lit 0) (.lit 0))
    (sel u vs (u + 1) (.lit 0) (.lit 0) (.lit 1) (.lit 0) (.lit 0))
    (sel u vs (u + 1) (.lit 1) (.lit 1) (.lit 0) (.lit 1) (.lit 0))
    (sel u vs (u + 1) (.lit 0) (.lit 0) (.lit 1) (.lit 0)
      (eqE (.mod (.sub (.var (u + 1)) (kA u vs 4)) (AE u vs)) (.sub (.var u) (kA u vs 3))))
    (sel u vs (u + 1) (.lit 0) (.lit 0) (.lit 0)
      (eqE (.mod (.sub (.var u) (kA u vs 4)) (AE u vs)) (.sub (.var (u + 1)) (kA u vs 3)))
      (ifEq (.sub (.var (u + 1)) (kA u vs 4)) (.add (.sub (.var u) (kA u vs 4)) (.lit 1)) (.lit 1)
        (eqE (.sub (.var u) (kA u vs 4)) (.add (.sub (.var (u + 1)) (kA u vs 4)) (.lit 1)))))

/-- The width of the pair `u, u + 1`. -/
def cE : Ex := .mul (lnk u vs) (fwE u vs)

/-- The position `L (a + A i') + t` (`i' = u + 5`, `t = u + 6`). -/
def posE : Ex := .add (.mul (LLE u vs) (.add (.var u) (.mul (AE u vs) (.var (u + 5))))) (.var (u + 6))

/-- The weight of an input gate `faP`. -/
def faW : Ex :=
  nprod (u + 5) (hE u vs) (nprod (u + 6) (LLE u vs)
    (.ifLt (posE u vs) (.var 2) (.lit 1)
      (eqE (.mod (.div (dD u vs (zv u) (.var (u + 5))) (pow2 (u + 4) (.var (u + 6)))) (.lit 2))
        (xBit (.sub (posE u vs) (.var 2))))))

/-- The carry index `j = a − 4A`. -/
def jE : Ex := .sub (.var u) (kA u vs 4)

/-- Digit `j` of `N`, read bit by bit. -/
def dgE : Ex :=
  nsum (u + 5) (LLE u vs) (.mul (nBit (.add (.mul (LLE u vs) (jE u vs)) (.var (u + 5)))) (pow2 (u + 4) (.var (u + 5))))

/-- The weight of a carry gate. -/
def cW : Ex :=
  .mul (eqE (.mod (.add (ccE u vs) (cyE u vs)) (TLE u vs)) (dgE u vs))
    (.mul (ifEq (jE u vs) (.lit 0) (eqE (ccE u vs) (.lit 0)) (.lit 1))
      (ifEq (.add (jE u vs) (.lit 1)) (.mul (AE u vs) (AE u vs))
        (eqE (.div (.add (ccE u vs) (cyE u vs)) (TLE u vs)) (.lit 0)) (.lit 1)))

end MulEx

open MulEx in
/-- **The expressions of the multiplication network.** -/
def mulNEx (u _vm vs : ℕ) : NEx where
  sz := sel u vs u (PDE u vs) (PDE u vs) (.mul (PZE u vs) (PZE u vs)) (PZE u vs) (.mul (ME u vs) (PfE u vs))
  W := sel u vs u (faW u vs) (.lit 1) (.lit 1) (.lit 1) (cW u vs)
  c := cE u vs
  l := eqE (msg u vs u (u + 1)) (.mod (.var (u + 3)) (pow2 (u + 4) (cE u vs)))
  r := eqE (msg u vs (u + 1) u) (.mod (.var (u + 3)) (pow2 (u + 4) (cE u vs)))

end Factoring.Aux
