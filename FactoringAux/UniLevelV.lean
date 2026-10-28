/-
The level builders with their `K`/`G` literals read from variables.

Copies of `GridEx.nex` (`GridV`, data `GPv`: the grid side `g`, `g²`, `g³` in variables `vg`, `vgg`, `vggg`), of the
group step (`GroupV`, data `GSv`: `K`, `g`, `2g+1`, `K^g` in variables `vK`, `vg`, `v2g`, `vKg`) and of one level
(`LevelV`, data `LPv`: the literal variables are the block `p, p+1, …, p+11`, holding `lvlVals K G`):

  `p` K, `p+1` G, `p+2` G·G, `p+3` G·(G·G), `p+4` 2G+1, `p+5` K^G, `p+6` 12G³, `p+7` 11G⁴, `p+8` 24G⁴, `p+9` G·G³,
  `p+10` K³, `p+11` G·G·(G·G)  (the last one is not used by the copies: it is the number of choice codes of a level,
  `(tB λ + 1)^(G·G·(G·G))`, for the engine).

Literals that are fixed numbers stay. The coarsening and clique builders take their sizes as expressions, so they are
not copied. No builder depends on `K` or `G` other than through literals.

* `GridV.grid_LS` (from `sz_LS`, `W_LS`, `c_LS`, `F_LS`; `facLE_LS`, `facRE_LS` by `LSB.refl_ge`), `GroupV.coarsen_LS'`, `GroupV.searchE_LS`, `GroupV.tab_LS` (generic in `ok`, `nb`).
* `lvlVals`, `blockOk`, `lvlOk`; **`LevelV.LnE_LS`**, **`LevelV.searchE_LS`**, **`LevelV.nextTE_LS`**,
  **`LevelV.pre_LS`** (`LS (lvlOk p P.K P.G) (LevelEx.X P) (LevelV.X (LPv.of P p TE'))`), and their `LSB` forms.
* **`LevelV.nextTE_vb`**, **`LevelV.pre_vb`**, **`LevelV.searchE_vb`**, `LevelV.LnE_vb`: variable bounds of the copies.

Not an audit surface.
-/
module

public import FactoringAux.UniLS

@[expose] public section

namespace Factoring.Aux

open Ex

/-! ### Literal variables in a block -/

/-- `v` is variable `p + i` and the `i`-th value is `k`. -/
def blockOk (p : ℕ) (vals : List ℕ) (v k : ℕ) : Prop := p ≤ v ∧ vals[v - p]? = some k

theorem blockOk_lt {p : ℕ} {vals : List ℕ} {v k : ℕ} (h : blockOk p vals v k) : v < p + vals.length := by
  obtain ⟨h1, h2⟩ := h
  have : v - p < vals.length := by
    by_contra hc; rw [List.getElem?_eq_none (by omega)] at h2; exact absurd h2 (by simp)
  omega

theorem blockOk_ge {p : ℕ} {vals : List ℕ} {v k : ℕ} (h : blockOk p vals v k) : p ≤ v := h.1

theorem blockOk_at {p : ℕ} {vals : List ℕ} {i k : ℕ} : blockOk p vals (p + i) k ↔ vals[i]? = some k := by
  simp [blockOk]

/-- If the block holds the values, every literal variable holds its literal. -/
theorem blockOk_holds {p : ℕ} {vals : List ℕ} {σ : ℕ → ℕ} (h : ∀ i (hi : i < vals.length), σ (p + i) = vals[i]) :
    ∀ v k, blockOk p vals v k → σ v = k := by
  intro v k hv
  have hl := blockOk_lt hv
  obtain ⟨h1, h2⟩ := hv
  have e : v = p + (v - p) := by omega
  rw [List.getElem?_eq_some_iff] at h2
  obtain ⟨hi, h2⟩ := h2
  rw [e, h _ hi, h2]

/-- The values of a level's literal variables (`G = 3 K^8` in the engine). -/
def lvlVals (K G : ℕ) : List ℕ :=
  [K, G, G * G, G * (G * G), 2 * G + 1, K ^ G, 12 * G ^ 3, 11 * G ^ 4, 24 * G ^ 4, G * G ^ 3, K ^ 3, G * G * (G * G)]

theorem lvlVals_length (K G : ℕ) : (lvlVals K G).length = 12 := rfl

/-- The level's literal variables `p … p+11`. -/
def lvlOk (p K G : ℕ) : ℕ → ℕ → Prop := blockOk p (lvlVals K G)

theorem lvlOk_lt {p K G v k : ℕ} (h : lvlOk p K G v k) : v < p + 12 := blockOk_lt h

/-- No variable from `p + 12` on is a literal variable. -/
theorem lvlOk_nb {p K G x : ℕ} (hx : p + 12 ≤ x) : ∀ k, ¬ lvlOk p K G x k := fun _ h => by
  have := lvlOk_lt h; omega

/-! ### The line networks -/

/-- The data of the line expressions with the grid side's literals in variables. -/
structure GPv where
  u : ℕ
  vm : ℕ
  vl : ℕ
  vc : ℕ
  vγ : ℕ
  vΘ : ℕ
  /-- The variables holding `g`, `g * g`, `g * (g * g)`. -/
  vg : ℕ
  vgg : ℕ
  vggg : ℕ
  TE : Ex

/-- The copy's data of `P`. -/
def GPv.of (P : GP) (vg vgg vggg : ℕ) (TE : Ex) : GPv := ⟨P.u, P.vm, P.vl, P.vc, P.vγ, P.vΘ, vg, vgg, vggg, TE⟩

namespace GridV

variable (P : GPv) (tr : Bool)

def p2 (e : Ex) : Ex := pow2 (P.u + 19) e
def powE (base e : Ex) : Ex := .prod (P.u + 18) e (.lit 0) base
def slcE (Q i w : Ex) : Ex :=
  .mod (.div Q (p2 P (.mul (.var P.vl) (.add w (.mul (.var P.vgg) i))))) (p2 P (.var P.vl))
def ptIE (n i : Ex) : Ex := if tr then .add n (.mul (.var P.vg) i) else .add i (.mul (.var P.vg) n)
def phiDE (q : Ex) : Ex := .mod (.div (.var P.vc) (powE P (.add (tBE P.vl) (.lit 1)) q)) (.add (tBE P.vl) (.lit 1))
def qIdxE (n n' i i' : Ex) : Ex :=
  if tr then .add (.add n' (.mul (.var P.vg) n)) (.mul (.var P.vgg) (.add i' (.mul (.var P.vg) i)))
  else .add (.add i' (.mul (.var P.vg) i)) (.mul (.var P.vgg) (.add n' (.mul (.var P.vg) n)))
def minE (a b : Ex) : Ex := .ifLt a b a b
def cXE (i : Ex) : Ex :=
  if tr then minE (.mul (.lit 2) (.var P.vl)) (.add (.mul (.lit 4) (tBE P.vl)) (.mul (.lit 3) (.sub (tBE P.vl) i)))
  else minE (.mul (.lit 2) (.var P.vl)) (.add (.mul (.lit 4) (tBE P.vl)) (.mul (.lit 3) i))

def cwE (x y : ℕ) : Ex := cXE P tr (phiDE P (qIdxE P tr (.var P.u) (.var (P.u + 1)) (.var x) (.var y)))

def sz : Ex := p2 P (.mul (.var P.vl) (.var P.vggg))

def W : Ex :=
  zmul P.vm
    (zprod (P.u + 4) (.var P.vg) P.vm
      (ifEq (slcE P (.var (P.u + 2)) (.var (P.u + 4)) (ptIE P tr (.var P.u) (.var (P.u + 4)))) (.lit 0)
        (.lett P.vγ (ptIE P tr (.var P.u) (.var (P.u + 4)))
          (.lett P.vΘ (.div (.var (P.u + 2)) (p2 P (.mul (.var P.vl) (.mul (.var P.vgg) (.var (P.u + 4))))))
            P.TE))
        (.lit 0)))
    (zprod (P.u + 4) (.var P.vg) P.vm (zprod (P.u + 5) (.var P.vg) P.vm
      (.ifLt (.var (P.u + 4)) (.var (P.u + 5))
        (ifEq (slcE P (.var (P.u + 2)) (.var (P.u + 4)) (ptIE P tr (.var P.u) (.var (P.u + 5))))
          (slcE P (.var (P.u + 2)) (.var (P.u + 5)) (ptIE P tr (.var P.u) (.var (P.u + 4)))) (.lit 1) (.lit 0))
        (.lit 1))))

def c : Ex :=
  .add (.mul (.var P.vg) (.var P.vl)) (nsum (P.u + 4) (.var P.vg) (nsum (P.u + 5) (.var P.vg)
    (.ifLt (.var (P.u + 4)) (.var (P.u + 5)) (cwE P tr (P.u + 4) (P.u + 5)) (.lit 0))))

def offE : Ex :=
  nsum (P.u + 7) (.var (P.u + 4)) (.lett (P.u + 8) (.mod (.div (.var (P.u + 7)) (.var P.vg)) (.var P.vg))
    (.lett (P.u + 9) (.mod (.var (P.u + 7)) (.var P.vg))
      (.ifLt (.var (P.u + 8)) (.var (P.u + 9)) (cwE P tr (P.u + 8) (P.u + 9)) (.lit 0))))

def F (nE fac : Ex) : Ex :=
  zmul P.vm
    (zprod (P.u + 4) (.var P.vg) P.vm
      (ifEq (slcE P (.var (P.u + 2)) (.var (P.u + 4)) (ptIE P tr nE (.var (P.u + 4))))
        (.mod (.div (.var (P.u + 3)) (p2 P (.mul (.var P.vl) (.var (P.u + 4))))) (p2 P (.var P.vl))) (.lit 1) (.lit 0)))
    (zprod (P.u + 4) (.var P.vgg) P.vm
      (.lett (P.u + 5) (.mod (.div (.var (P.u + 4)) (.var P.vg)) (.var P.vg))
        (.lett (P.u + 6) (.mod (.var (P.u + 4)) (.var P.vg))
          (.ifLt (.var (P.u + 5)) (.var (P.u + 6))
            (.lett (P.u + 10) (phiDE P (qIdxE P tr (.var P.u) (.var (P.u + 1)) (.var (P.u + 5)) (.var (P.u + 6))))
              (.lett (P.u + 11) (slcE P (.var (P.u + 2)) (.var (P.u + 5)) (ptIE P tr nE (.var (P.u + 6))))
                (.lett (P.u + 12) (slcE P (.var (P.u + 2)) (.var (P.u + 6)) (ptIE P tr nE (.var (P.u + 5))))
                  (.lett (P.u + 13) (.div (.div (.var (P.u + 3)) (p2 P (.mul (.var P.vg) (.var P.vl))))
                      (p2 P (offE P tr)))
                    fac))))
            (.lit 1)))))

/-- The line network's expressions (the rectangle factors `facLE`, `facRE` have no `g` literal and are shared). -/
def nex : NEx :=
  ⟨sz P, W P tr, c P tr,
    F P tr (.var (P.u + 1)) (facLE tr (P.u + 20) P.vm P.vl (P.u + 10) (P.u + 11) (P.u + 12) (P.u + 13)),
    F P tr (.var P.u) (facRE tr (P.u + 20) P.vm P.vl (P.u + 10) (P.u + 11) (P.u + 12) (P.u + 13))⟩

section LS

variable {ok : ℕ → ℕ → Prop} {nb : ℕ → Prop} (P : GP) (tr : Bool) {vg vgg vggg : ℕ} {TE' : Ex}

/-- The rectangle factors have no `g` literal: they are related to themselves. -/
theorem facLE_LS (b vm vl vi vX vY vQ : ℕ) (hnb : ∀ x, b ≤ x → nb x) :
    LSB ok nb (facLE tr b vm vl vi vX vY vQ) (facLE tr b vm vl vi vX vY vQ) :=
  LSB.refl_ge hnb _ (by
    cases tr <;>
    simp only [Ex.BGe, facLE, jOf, decLE, decE, tBE, blkAt, cvPE, evLE, psiE, sgnE, phiE, par3E, bitE, eqE, ifEq,
      pow2, Bool.false_eq_true, ↓reduceIte, and_true, true_and, and_self] <;> omega)

theorem facRE_LS (b vm vl vi vU vV vQ : ℕ) (hnb : ∀ x, b ≤ x → nb x) :
    LSB ok nb (facRE tr b vm vl vi vU vV vQ) (facRE tr b vm vl vi vU vV vQ) :=
  LSB.refl_ge hnb _ (by
    cases tr <;>
    simp only [Ex.BGe, facRE, jOf, pieceE, decLE, decRRE, decCRE, decE, tBE, blkAt, cvPE, evLE, cvRE, evRRE, evCRE,
      psiE, sgnE, phiE, par3E, par4E, bitE, RxE, CxE, eqE, ifEq, pow2, zsum, zmul, Bool.false_eq_true, ↓reduceIte,
      and_true, true_and, and_self] <;> omega)

theorem sz_LS (hggg : ok vggg (P.g * (P.g * P.g))) (hnb : ∀ x, P.u ≤ x → nb x) :
    LSB ok nb (GridEx.sz P) (sz (GPv.of P vg vgg vggg TE')) := by
  simp only [GridEx.sz, sz, GridEx.p2, p2, GPv.of, pow2]
  repeat ls_step

theorem W_LS (hT : LSB ok nb P.TE TE') (hg : ok vg P.g) (hgg : ok vgg (P.g * P.g)) (hγ : nb P.vγ)
    (hΘ : nb P.vΘ) (hnb : ∀ x, P.u ≤ x → nb x) :
    LSB ok nb (GridEx.W P tr) (W (GPv.of P vg vgg vggg TE') tr) := by
  cases tr <;>
    simp only [GridEx.W, W, GridEx.p2, p2, GridEx.slcE, slcE, GridEx.ptIE, ptIE, GPv.of, ifEq, pow2, zmul, zprod,
      Bool.false_eq_true, ↓reduceIte] <;>
    repeat ls_step

theorem cwE_LS (hg : ok vg P.g) (hgg : ok vgg (P.g * P.g)) (hnb : ∀ x, P.u ≤ x → nb x) (x y : ℕ) :
    LSB ok nb (GridEx.cwE P tr x y) (cwE (GPv.of P vg vgg vggg TE') tr x y) := by
  cases tr <;>
    simp only [GridEx.cwE, cwE, GridEx.cXE, cXE, GridEx.minE, minE, GridEx.phiDE, phiDE, GridEx.powE, powE,
      GridEx.qIdxE, qIdxE, GPv.of, tBE, Bool.false_eq_true, ↓reduceIte] <;>
    repeat ls_step

theorem c_LS (hg : ok vg P.g) (hgg : ok vgg (P.g * P.g)) (hnb : ∀ x, P.u ≤ x → nb x) :
    LSB ok nb (GridEx.c P tr) (c (GPv.of P vg vgg vggg TE') tr) := by
  have h := cwE_LS (TE' := TE') (vggg := vggg) P tr hg hgg hnb (P.u + 4) (P.u + 5)
  simp only [GridEx.c, c, nsum] at h ⊢
  repeat ls_step

theorem offE_LS (hg : ok vg P.g) (hgg : ok vgg (P.g * P.g)) (hnb : ∀ x, P.u ≤ x → nb x) :
    LSB ok nb (GridEx.offE P tr) (offE (GPv.of P vg vgg vggg TE') tr) := by
  have h := cwE_LS (TE' := TE') (vggg := vggg) P tr hg hgg hnb (P.u + 8) (P.u + 9)
  simp only [GridEx.offE, offE, nsum] at h ⊢
  repeat ls_step

theorem F_LS (hg : ok vg P.g) (hgg : ok vgg (P.g * P.g)) (hnb : ∀ x, P.u ≤ x → nb x) {nE nE' fac fac' : Ex}
    (hn : LSB ok nb nE nE') (hf : LSB ok nb fac fac') :
    LSB ok nb (GridEx.F P tr nE fac) (F (GPv.of P vg vgg vggg TE') tr nE' fac') := by
  have ho := offE_LS (TE' := TE') (vggg := vggg) P tr hg hgg hnb
  cases tr <;>
    simp only [GridEx.F, F, GridEx.p2, p2, GridEx.slcE, slcE, GridEx.ptIE, ptIE, GridEx.phiDE, phiDE, GridEx.powE,
      powE, GridEx.qIdxE, qIdxE, tBE, GPv.of, ifEq, pow2, zmul, zprod, Bool.false_eq_true, ↓reduceIte] at ho ⊢ <;>
    repeat ls_step

/-- **The line network's copy is related to the original.** -/
theorem grid_LS (hT : LSB ok nb P.TE TE') (hg : ok vg P.g) (hgg : ok vgg (P.g * P.g))
    (hggg : ok vggg (P.g * (P.g * P.g))) (hγ : nb P.vγ) (hΘ : nb P.vΘ) (hnb : ∀ x, P.u ≤ x → nb x) :
    NLS ok nb (GridEx.nex P tr) (nex (GPv.of P vg vgg vggg TE') tr) :=
  ⟨sz_LS P hggg hnb, W_LS P tr hT hg hgg hγ hΘ hnb, c_LS P tr hg hgg hnb,
    F_LS P tr hg hgg hnb (LSB.var _) (facLE_LS tr _ _ _ _ _ _ _ fun x hx => hnb x (by omega)),
    F_LS P tr hg hgg hnb (LSB.var _) (facRE_LS tr _ _ _ _ _ _ _ fun x hx => hnb x (by omega))⟩

end LS

end GridV

/-! ### The group step -/

/-- The data of a group step with `K`, `g`, `2g+1`, `K^g` in variables. -/
structure GSv where
  u : ℕ
  vm : ℕ
  vχ : ℕ
  vL : ℕ
  /-- The variables holding `K`, `g`, `2 * g + 1`, `K ^ g`. -/
  vK : ℕ
  vg : ℕ
  v2g : ℕ
  vKg : ℕ
  E : NEx

/-- The copy's data of `S`. -/
def GSv.of (S : GS) (vK vg v2g vKg : ℕ) (E : NEx) : GSv := ⟨S.u, S.vm, S.vχ, S.vL, vK, vg, v2g, vKg, E⟩

namespace GroupV

variable (S : GSv)

def chiE : Ex := .mod (.div (.var S.vχ) (.prod (S.u + 45) (.var S.u) (.lit 0) (.var S.vK))) (.var S.vK)

def Pc : CP := ⟨S.u, S.u + 46, S.vm, S.E, .var S.vg, chiE S⟩

def Pk : KP := ⟨S.u + 46, S.u + 56, S.vm, CoarsenEx.nex (Pc S), .var S.vK, .var S.vL⟩

def okE : Ex :=
  .mul (nprod (S.u + 54) (.var S.vK)
      (.ifLt (.mul (.var S.vK) (nsum S.u (.var S.vg) (ifEq (chiE S) (.var (S.u + 54)) (.lit 1) (.lit 0))))
        (.var S.v2g) (.lit 1) (.lit 0)))
    (nprod (S.u + 46) (.var S.vK) (nprod (S.u + 47) (.var S.vK)
      (.ifLt (.var (S.u + 46)) (.var (S.u + 47))
        (.ifLt (CoarsenEx.c (Pc S)) (.add (.var S.vL) (.lit 1)) (.lit 1) (.lit 0)) (.lit 1))))

def searchE (vx vs : ℕ) : Ex :=
  .iter vx vs (.var S.vKg) (.var S.vKg)
    (ifEq (.var vs) (.var S.vKg) (.lett S.vχ (.var vx) (ifEq (okE S) (.lit 1) (.var vx) (.var vs))) (.var vs))

def tab : Ex := CliqueEx.tab (Pk S)

variable {ok : ℕ → ℕ → Prop} {nb : ℕ → Prop}

theorem chiE_LS (S : GS) {vK vg v2g vKg : ℕ} {E' : NEx} (hK : ok vK S.K) (hnb : ∀ x, S.u ≤ x → nb x) :
    LSB ok nb (GroupEx.chiE S) (chiE (GSv.of S vK vg v2g vKg E')) := by
  simp only [GroupEx.chiE, chiE, GSv.of]
  repeat ls_step

theorem coarsen_LS' (S : GS) {vK vg v2g vKg : ℕ} {E' : NEx} (hE : NLS ok nb S.E E') (hK : ok vK S.K)
    (hg : ok vg S.g) (hnb : ∀ x, S.u ≤ x → nb x) :
    NLS ok nb (CoarsenEx.nex (GroupEx.Pc S)) (CoarsenEx.nex (Pc (GSv.of S vK vg v2g vKg E'))) :=
  coarsen_LS S.u (S.u + 46) S.vm hE (LSB.lv hg) (chiE_LS S hK hnb) hnb (fun x hx => hnb x (by omega))

theorem searchE_LS (S : GS) {vK vg v2g vKg : ℕ} {E' : NEx} (hE : NLS ok nb S.E E') (hK : ok vK S.K)
    (hg : ok vg S.g) (h2g : ok v2g (2 * S.g + 1)) (hKg : ok vKg (S.K ^ S.g)) (hnb : ∀ x, S.u ≤ x → nb x)
    (hχ : nb S.vχ) {vx vs : ℕ} (hx : nb vx) (hs : nb vs) :
    LSB ok nb (GroupEx.searchE S vx vs) (searchE (GSv.of S vK vg v2g vKg E') vx vs) := by
  have hc : LSB ok nb (CoarsenEx.c (GroupEx.Pc S)) (CoarsenEx.c (Pc (GSv.of S vK vg v2g vKg E'))) :=
    (coarsen_LS' S hE hK hg hnb).2.2.1
  have hch := chiE_LS (vg := vg) (v2g := v2g) (vKg := vKg) (E' := E') S hK hnb
  simp only [GroupEx.searchE, searchE, GroupEx.okE, okE, ifEq, nsum, nprod] at hc hch ⊢
  repeat ls_step

theorem tab_LS (S : GS) {vK vg v2g vKg : ℕ} {E' : NEx} (hE : NLS ok nb S.E E') (hK : ok vK S.K)
    (hg : ok vg S.g) (hnb : ∀ x, S.u ≤ x → nb x) :
    LSB ok nb (GroupEx.tab S) (tab (GSv.of S vK vg v2g vKg E')) :=
  clique_LS (S.u + 46) (S.u + 56) S.vm (coarsen_LS' S hE hK hg hnb) (LSB.lv hK) (LSB.var _)
    (fun x hx => hnb x (by omega)) (fun x hx => hnb x (by omega))

end GroupV

/-! ### One level -/

/-- The data of a level with its literals in the variables `p … p+11`. -/
structure LPv where
  b : ℕ
  vm : ℕ
  vl : ℕ
  vγ : ℕ
  vΘ : ℕ
  /-- The first literal variable. -/
  p : ℕ
  TE : Ex

/-- The copy's data of `P`. -/
def LPv.of (P : LP) (p : ℕ) (TE : Ex) : LPv := ⟨P.b, P.vm, P.vl, P.vγ, P.vΘ, p, TE⟩

namespace LevelV

variable (Q : LPv)

def gp : GPv := ⟨Q.b + 6, Q.vm, Q.vl, Q.b, Q.vγ, Q.vΘ, Q.p + 1, Q.p + 2, Q.p + 3, Q.TE⟩

def gs (tr : Bool) : GSv :=
  ⟨Q.b + 6, Q.vm, if tr then Q.b + 5 else Q.b + 4, Q.b + 1, Q.p, Q.p + 1, Q.p + 4, Q.p + 5, GridV.nex (gp Q) tr⟩

def UE (tr : Bool) : Ex :=
  nsum (Q.b + 6) (.var (Q.p + 1)) (nsum (Q.b + 7) (.var (Q.p + 1))
    (.ifLt (.var (Q.b + 6)) (.var (Q.b + 7)) (GridV.c (gp Q) tr) (.lit 0)))

/-- The next table. -/
def nextTE : Ex := .ifLt (UE Q false) (.add (UE Q true) (.lit 1)) (GroupV.tab (gs Q false)) (GroupV.tab (gs Q true))

/-- `Lnext K G λ`. -/
def LnE : Ex :=
  .div (.add (.mul (.var Q.p) (.div (.add (.add (.mul (.var (Q.p + 6)) (.var Q.vl))
      (.mul (.var (Q.p + 7)) (.var Q.vl))) (.var (Q.p + 8))) (.lit 12)))
    (.mul (.var (Q.p + 9)) (.var Q.vl))) (.var (Q.p + 10))

/-- The search for the first good code of the row (`false`) or column (`true`) network. -/
def searchE (tr : Bool) (vx vs : ℕ) : Ex := GroupV.searchE (gs Q tr) vx vs

/-- The `lett`s of a level before its body. -/
def pre (body : Ex) : Ex :=
  .lett (Q.b + 1) (LnE Q) (.lett (Q.b + 4) (searchE Q false (Q.b + 2) (Q.b + 3))
    (.lett (Q.b + 5) (searchE Q true (Q.b + 2) (Q.b + 3)) body))

section LS

variable {nb : ℕ → Prop} (P : LP) (p : ℕ) {TE' : Ex}

theorem ok0 : lvlOk p P.K P.G p P.K := ⟨le_rfl, by simp [lvlVals]⟩
theorem okAt {i k : ℕ} (h : (lvlVals P.K P.G)[i]? = some k) : lvlOk p P.K P.G (p + i) k := blockOk_at.mpr h

theorem grid_LS' (hT : LSB (lvlOk p P.K P.G) nb P.TE TE') (hγ : nb P.vγ) (hΘ : nb P.vΘ)
    (hnb : ∀ x, P.b ≤ x → nb x) (tr : Bool) :
    NLS (lvlOk p P.K P.G) nb (GridEx.nex (LevelEx.gp P) tr) (GridV.nex (gp (LPv.of P p TE')) tr) :=
  GridV.grid_LS (LevelEx.gp P) tr hT (okAt P p (i := 1) rfl) (okAt P p (i := 2) rfl) (okAt P p (i := 3) rfl)
    hγ hΘ (fun x hx => hnb x (by simp only [LevelEx.gp] at hx; omega))

theorem LnE_LSB : LSB (lvlOk p P.K P.G) nb (LevelEx.LnE P) (LnE (LPv.of P p TE')) := by
  have h0 := ok0 P p
  have h6 := okAt P p (i := 6) rfl
  have h7 := okAt P p (i := 7) rfl
  have h8 := okAt P p (i := 8) rfl
  have h9 := okAt P p (i := 9) rfl
  have h10 := okAt P p (i := 10) rfl
  simp only [LevelEx.LnE, LnE, LPv.of]
  repeat ls_step

theorem searchE_LSB (hT : LSB (lvlOk p P.K P.G) nb P.TE TE') (hγ : nb P.vγ) (hΘ : nb P.vΘ)
    (hnb : ∀ x, P.b ≤ x → nb x) (tr : Bool) {vx vs : ℕ} (hx : nb vx) (hs : nb vs) :
    LSB (lvlOk p P.K P.G) nb (GroupEx.searchE (LevelEx.gs P tr) vx vs) (searchE (LPv.of P p TE') tr vx vs) :=
  GroupV.searchE_LS (LevelEx.gs P tr) (grid_LS' P p hT hγ hΘ hnb tr) (ok0 P p) (okAt P p (i := 1) rfl)
    (okAt P p (i := 4) rfl) (okAt P p (i := 5) rfl) (fun x hx => hnb x (by simp only [LevelEx.gs] at hx; omega))
    (hnb _ (by cases tr <;> simp [LevelEx.gs])) hx hs

theorem nextTE_LSB (hT : LSB (lvlOk p P.K P.G) nb P.TE TE') (hγ : nb P.vγ) (hΘ : nb P.vΘ)
    (hnb : ∀ x, P.b ≤ x → nb x) :
    LSB (lvlOk p P.K P.G) nb (LevelEx.nextTE P) (nextTE (LPv.of P p TE')) := by
  have h1 := okAt P p (i := 1) rfl
  have ht : ∀ tr, LSB (lvlOk p P.K P.G) nb (GroupEx.tab (LevelEx.gs P tr)) (GroupV.tab (gs (LPv.of P p TE') tr)) :=
    fun tr => GroupV.tab_LS (LevelEx.gs P tr) (grid_LS' P p hT hγ hΘ hnb tr) (ok0 P p) h1
      (fun x hx => hnb x (by simp only [LevelEx.gs] at hx; omega))
  have hc : ∀ tr, LSB (lvlOk p P.K P.G) nb (GridEx.c (LevelEx.gp P) tr) (GridV.c (gp (LPv.of P p TE')) tr) :=
    fun tr => (grid_LS' P p hT hγ hΘ hnb tr).2.2.1
  have hc0 := hc false
  have hc1 := hc true
  have ht0 := ht false
  have ht1 := ht true
  have hnb' : ∀ x, P.b ≤ x → nb x := hnb
  simp only [LevelEx.nextTE, nextTE, LevelEx.UE, UE, nsum]
  repeat ls_step

theorem pre_LSB (hT : LSB (lvlOk p P.K P.G) nb P.TE TE') (hγ : nb P.vγ) (hΘ : nb P.vΘ)
    (hnb : ∀ x, P.b ≤ x → nb x) {body body' : Ex} (hB : LSB (lvlOk p P.K P.G) nb body body') :
    LSB (lvlOk p P.K P.G) nb (LevelEx.pre P body) (pre (LPv.of P p TE') body') := by
  have hL := LnE_LSB (nb := nb) (TE' := TE') P p
  have hs0 := searchE_LSB P p hT hγ hΘ hnb false (vx := P.b + 2) (vs := P.b + 3) (hnb _ (by omega)) (hnb _ (by omega))
  have hs1 := searchE_LSB P p hT hγ hΘ hnb true (vx := P.b + 2) (vs := P.b + 3) (hnb _ (by omega)) (hnb _ (by omega))
  simp only [LevelEx.pre, pre]
  repeat ls_step

/-! #### The relation `LS` (no binder is a literal variable) -/

theorem nb_of (hγ : p + 12 ≤ P.vγ) (hΘ : p + 12 ≤ P.vΘ) (hb : p + 12 ≤ P.b) :
    (∀ k, ¬ lvlOk p P.K P.G P.vγ k) ∧ (∀ k, ¬ lvlOk p P.K P.G P.vΘ k) ∧
      ∀ x, P.b ≤ x → ∀ k, ¬ lvlOk p P.K P.G x k :=
  ⟨lvlOk_nb hγ, lvlOk_nb hΘ, fun _ hx => lvlOk_nb (by omega)⟩

/-- **`Lnext` with its literals in variables.** -/
theorem LnE_LS : LS (lvlOk p P.K P.G) (LevelEx.LnE P) (LnE (LPv.of P p TE')) := LnE_LSB P p

/-- **The searches with their literals in variables** (`TE'` related to the table `P.TE`, the literal variables below
`vγ`, `vΘ`, `b`, `vx`, `vs`). -/
theorem searchE_LS (hT : LS (lvlOk p P.K P.G) P.TE TE') (hγ : p + 12 ≤ P.vγ) (hΘ : p + 12 ≤ P.vΘ)
    (hb : p + 12 ≤ P.b) (tr : Bool) {vx vs : ℕ} (hx : p + 12 ≤ vx) (hs : p + 12 ≤ vs) :
    LS (lvlOk p P.K P.G) (GroupEx.searchE (LevelEx.gs P tr) vx vs) (searchE (LPv.of P p TE') tr vx vs) :=
  let h := nb_of P p hγ hΘ hb
  searchE_LSB P p hT h.1 h.2.1 h.2.2 tr (lvlOk_nb hx) (lvlOk_nb hs)

/-- **The next table with its literals in variables.** -/
theorem nextTE_LS (hT : LS (lvlOk p P.K P.G) P.TE TE') (hγ : p + 12 ≤ P.vγ) (hΘ : p + 12 ≤ P.vΘ)
    (hb : p + 12 ≤ P.b) : LS (lvlOk p P.K P.G) (LevelEx.nextTE P) (nextTE (LPv.of P p TE')) :=
  let h := nb_of P p hγ hΘ hb
  nextTE_LSB P p hT h.1 h.2.1 h.2.2

/-- **The `lett`s of a level with their literals in variables.** -/
theorem pre_LS (hT : LS (lvlOk p P.K P.G) P.TE TE') (hγ : p + 12 ≤ P.vγ) (hΘ : p + 12 ≤ P.vΘ)
    (hb : p + 12 ≤ P.b) {body body' : Ex} (hB : LS (lvlOk p P.K P.G) body body') :
    LS (lvlOk p P.K P.G) (LevelEx.pre P body) (pre (LPv.of P p TE') body') :=
  let h := nb_of P p hγ hΘ hb
  pre_LSB P p hT h.1 h.2.1 h.2.2 hB

end LS

/-! #### Variable bounds of the copies -/

section VB

variable {t : ℕ}

/-- Any copy's data comes from an original (with `K = G = 0`, the table being the copy's). -/
def toLP : LP := ⟨Q.b, Q.vm, Q.vl, Q.vγ, Q.vΘ, 0, 0, Q.TE⟩

theorem of_toLP : LPv.of (toLP Q) Q.p Q.TE = Q := rfl

theorem lvlOk_lt' {v k : ℕ} (h : lvlOk Q.p (toLP Q).K (toLP Q).G v k) {t : ℕ} (hp : Q.p + 12 ≤ t) : v < t := by
  have := lvlOk_lt h; omega

theorem LnE_vb (hvl : Q.vl < t) (hp : Q.p + 12 ≤ t) : VB t (LnE Q) := by
  have h := LnE_LSB (nb := fun _ => True) (TE' := Q.TE) (toLP Q) Q.p
  rw [of_toLP] at h
  exact LSB.VB h (fun _ _ hv => lvlOk_lt' Q hv hp)
    (by simp only [LevelEx.LnE, toLP, VB, and_true, true_and, and_self]; exact hvl)

theorem nextTE_vb (hT : VB t Q.TE) (hvm : Q.vm < t) (hvl : Q.vl < t) (hγ : Q.vγ < t) (hΘ : Q.vΘ < t)
    (hb : Q.b + 65 ≤ t) (hp : Q.p + 12 ≤ t) : VB t (nextTE Q) := by
  have h := nextTE_LSB (nb := fun _ => True) (toLP Q) Q.p (LSB.refl_true Q.TE) trivial trivial (fun _ _ => trivial)
  rw [of_toLP] at h
  exact LSB.VB h (fun _ _ hv => lvlOk_lt' Q hv hp) (level_nextTE_vb (P := toLP Q) hT hvm hvl hγ hΘ hb)

theorem searchE_vb (hT : VB t Q.TE) (hvm : Q.vm < t) (hvl : Q.vl < t) (hγ : Q.vγ < t) (hΘ : Q.vΘ < t)
    (hb : Q.b + 65 ≤ t) (hp : Q.p + 12 ≤ t) (tr : Bool) {vx vs : ℕ} (hx : vx < t) (hs : vs < t) :
    VB t (searchE Q tr vx vs) := by
  have h := searchE_LSB (nb := fun _ => True) (toLP Q) Q.p (LSB.refl_true Q.TE) trivial trivial (fun _ _ => trivial)
    tr (vx := vx) (vs := vs) trivial trivial
  rw [of_toLP] at h
  have hg : (GridEx.nex (LevelEx.gp (toLP Q)) tr).VB t :=
    grid_vb (P := LevelEx.gp (toLP Q)) tr hT hvm hvl (by simp only [LevelEx.gp, toLP]; omega) hγ hΘ
      (by simp only [LevelEx.gp, toLP]; omega)
  exact LSB.VB h (fun _ _ hv => lvlOk_lt' Q hv hp)
    (group_search_vb (S := LevelEx.gs (toLP Q) tr) hg hvm
      (by cases tr <;> simp only [LevelEx.gs, toLP] <;> simp <;> omega)
      (by simp only [LevelEx.gs, toLP]; omega) (by simp only [LevelEx.gs, toLP]; omega) hx hs)

theorem pre_vb (hT : VB t Q.TE) (hvm : Q.vm < t) (hvl : Q.vl < t) (hγ : Q.vγ < t) (hΘ : Q.vΘ < t)
    (hb : Q.b + 65 ≤ t) (hp : Q.p + 12 ≤ t) {body : Ex} (hB : VB t body) : VB t (pre Q body) := by
  have h := pre_LSB (nb := fun _ => True) (toLP Q) Q.p (LSB.refl_true Q.TE) trivial trivial (fun _ _ => trivial)
    (LSB.refl_true body)
  rw [of_toLP] at h
  exact LSB.VB h (fun _ _ hv => lvlOk_lt' Q hv hp) (level_pre_vb (P := toLP Q) hT hvm hvl hγ hΘ hb hB)

end VB

end LevelV

end Factoring.Aux
