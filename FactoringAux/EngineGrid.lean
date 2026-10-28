/-
The row and column networks of one level (`rowNet`, `colNet` of `toGrid T`) at codes.

* `blkEquiv`: `M` strings of `L` bits as one number (block `i` at bit `L i`); `lineEquiv`: a line setting
  (`LineS g λ`, slot `i`, grid point `w`) as one number, block `w + g² i` (`w` row-major); `lineCoding`.
* Choices by codes: `Quad g` (all quadruples), `restrictC φ` (the choice of `φ` on the rectangles), `phiEquiv`
  (radix `t + 1`); **`sum_restrict`**: summing over all `φ` multiplies (34) by `(t+1)^(#non-rectangles)`.
* Generic code formulas with a transpose flag `tr` (`false`: rows, `true`: columns): `slc` (a string of a line
  code), `ptI` (the grid index of slot `i` of line `n`), `lineW` (the weight), `lineC` (the width), `lineL`/`lineR`
  (the factor functions, given the rectangle factors `fL`, `fR`).
* **`rowNet_W_code`, `colNet_W_code`, `rowNet_c_code`, `colNet_c_code`, `rowNet_l_code`, …**: the networks at codes.

Not an audit surface.
-/
module

public import FactoringAux.EngineCliqueEx
public import FactoringAux.EngineRowFac
public import FactoringAux.Level

@[expose] public section

namespace Factoring.Aux

open Finset

/-! ### Block codes -/

theorem bitsEquiv_symm (c q : ℕ) (hq : q < 2 ^ c) : (bitsEquiv c).symm ⟨q, hq⟩ = bdec c q := by
  apply (bitsEquiv c).injective
  rw [Equiv.apply_symm_apply]
  exact Fin.ext (bnum_bdec hq).symm

/-- `M` strings of `L` bits, block `i` at bit `L i`. -/
def blkEquiv (L M : ℕ) : (Fin M → Bits L) ≃ Fin (2 ^ (L * M)) :=
  ((Equiv.arrowCongr (Equiv.refl (Fin M)) (bitsEquiv L)).trans finFunctionFinEquiv).trans
    (finCongr (pow_mul 2 L M).symm)

theorem blkEquiv_symm (L M : ℕ) (q : Fin (2 ^ (L * M))) (i : Fin M) :
    (blkEquiv L M).symm q i = bdec L (q / 2 ^ (L * i)) := by
  simp only [blkEquiv, Equiv.symm_trans_apply, Equiv.arrowCongr_symm, Equiv.arrowCongr_apply,
    Function.comp_apply, Equiv.refl_symm, Equiv.refl_apply]
  set q' := (finCongr (pow_mul 2 L M).symm).symm q
  have hv : (finFunctionFinEquiv.symm q' i : ℕ) = q / 2 ^ (L * i) % 2 ^ L := by
    rw [finFunctionFinEquiv_symm_apply_val, show ((2 : ℕ) ^ L) ^ (i : ℕ) = 2 ^ (L * i) from (pow_mul 2 L i).symm]
    rfl
  have : finFunctionFinEquiv.symm q' i = ⟨q / 2 ^ (L * i) % 2 ^ L, Nat.mod_lt _ (by positivity)⟩ := Fin.ext hv
  rw [this, bitsEquiv_symm, bdec_mod]

/-! ### Line settings -/

variable {g lam : ℕ}

/-- Slot `j` and point `w` of a line, numbered `w + g² j` (`w` row-major). -/
def lineIdx (g : ℕ) : Fin g × Pt g ≃ Fin (g * (g * g)) :=
  (Equiv.prodCongr (Equiv.refl _) (gidx g)).trans finProdFinEquiv

theorem lineIdx_val (j : Fin g) (w : Pt g) : (lineIdx g (j, w) : ℕ) = w.2 + g * w.1 + g * g * j := by
  simp [lineIdx, gidx, finProdFinEquiv_apply_val]

/-- A line setting as one number. -/
def lineEquiv (g lam : ℕ) : LineS g lam ≃ Fin (2 ^ (lam * (g * (g * g)))) :=
  (Equiv.curry (Fin g) (Pt g) (Bits lam)).symm.trans
    ((Equiv.arrowCongr (lineIdx g) (Equiv.refl _)).trans (blkEquiv lam (g * (g * g))))

/-- The string at slot `i`, grid index `w`, of a line code. -/
def slc (lam g Q i w : ℕ) : ℕ := Q / 2 ^ (lam * (w + g * g * i)) % 2 ^ lam

theorem lineEquiv_symm (Q : Fin (2 ^ (lam * (g * (g * g))))) (j : Fin g) (w : Pt g) :
    (lineEquiv g lam).symm Q j w = bdec lam (Q / 2 ^ (lam * (w.2 + g * w.1 + g * g * j))) := by
  show (blkEquiv lam (g * (g * g))).symm Q (lineIdx g (j, w)) = _
  rw [blkEquiv_symm, lineIdx_val]

theorem lineEquiv_symm_slc (Q : Fin (2 ^ (lam * (g * (g * g))))) (j : Fin g) (w : Pt g) :
    (lineEquiv g lam).symm Q j w = bdec lam (slc lam g Q j (w.2 + g * w.1)) := by
  rw [lineEquiv_symm, slc, bdec_mod]

theorem bdec_eq_iff (L X Y : ℕ) : bdec L X = bdec L Y ↔ X % 2 ^ L = Y % 2 ^ L := by
  constructor
  · intro h
    rw [← bnum_bdec (Nat.mod_lt X (by positivity) : X % 2 ^ L < 2 ^ L),
      ← bnum_bdec (Nat.mod_lt Y (by positivity) : Y % 2 ^ L < 2 ^ L), bdec_mod, bdec_mod, h]
  · intro h
    rw [← bdec_mod L X, h, bdec_mod]

theorem slc_lt (lam g Q i w : ℕ) : slc lam g Q i w < 2 ^ lam := Nat.mod_lt _ (by positivity)

/-! ### Choices by codes -/

/-- All quadruples `((a, a'), (j, j'))`. -/
abbrev Quad (g : ℕ) := (Fin g × Fin g) × (Fin g × Fin g)

/-- The choice of `φ` on the rectangles. -/
def restrictC (φ : Quad g → Fin (tB lam + 1)) : Choice g lam := fun r => φ r.1

theorem ιf_restrictC (φ : Quad g → Fin (tB lam + 1)) (r : Quad g) :
    ιf (restrictC φ) r = if r ∈ rects g then (φ r : ℕ) else 0 := by
  unfold ιf restrictC; split_ifs <;> rfl

/-- The number of quadruples that are not rectangles. -/
def nonRects (g : ℕ) : ℕ := (univ.filter (fun r : Quad g => r ∉ rects g)).card

section Restrict

variable {R : Type*} [CommRing R]

/-- **Summing over all `φ`**: (34) with the multiplier `(t+1)^(#non-rectangles)`. -/
theorem sum_restrict (T : GridClique R g lam) :
    ∑ φ : Quad g → Fin (tB lam + 1), Zι T (restrictC φ) =
      ((tB lam + 1 : R) ^ nonRects g * 2 ^ (tB lam * (rects g).card)) * gridZ T := by
  unfold Zι gridZ
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun Θ _ => ?_
  rw [← Finset.mul_sum]
  set E : Quad g → R := fun r => eqI Θ (r.1.1, r.2.1) (r.1.2, r.2.2) * eqI Θ (r.1.1, r.2.2) (r.1.2, r.2.1)
  set h : Quad g → Fin (tB lam + 1) → R := fun r i => if r ∈ rects g then
    (pieceA lam i (rx Θ r) (ry Θ r) (ru Θ r) (rv Θ r) : R) else 1
  have h1 : ∀ φ : Quad g → Fin (tB lam + 1), ∏ r ∈ rects g, rectA (restrictC φ) Θ r = ∏ r, h r (φ r) := by
    intro φ
    rw [← prod_ite_mem_eq]
    refine Finset.prod_congr rfl fun r _ => ?_
    simp only [h]
    split_ifs with hr
    · simp [rectA, ιf_restrictC, hr]
    · rfl
  simp_rw [h1]
  rw [← Fintype.prod_sum]
  have h2 : ∀ r, ∑ i, h r i = if r ∈ rects g then (2 : R) ^ tB lam * E r else (tB lam + 1 : R) := by
    intro r
    simp only [h]
    split_ifs with hr
    · exact sum_rectA Θ r
    · simp
  simp_rw [h2]
  rw [Finset.prod_ite, Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_const]
  have hf : (univ.filter (fun r : Quad g => r ∈ rects g)) = rects g := by ext r; simp
  rw [hf, ← pow_mul, show (univ.filter (fun r : Quad g => ¬ r ∈ rects g)).card = nonRects g from rfl]
  simp only [E]
  ring

end Restrict

/-- Quadruples numbered `j' + g j + g² (a' + g a)`. -/
def quadEquiv (g : ℕ) : Quad g ≃ Fin (g * g * (g * g)) :=
  (Equiv.prodCongr finProdFinEquiv finProdFinEquiv).trans finProdFinEquiv

theorem quadEquiv_val (r : Quad g) :
    (quadEquiv g r : ℕ) = r.2.2 + g * r.2.1 + g * g * (r.1.2 + g * r.1.1) := by
  simp [quadEquiv, finProdFinEquiv_apply_val]

/-- Choice functions on all quadruples as numbers in radix `t + 1`. -/
def phiEquiv (g t : ℕ) : (Quad g → Fin (t + 1)) ≃ Fin ((t + 1) ^ (g * g * (g * g))) :=
  (Equiv.arrowCongr (quadEquiv g) (Equiv.refl _)).trans finFunctionFinEquiv

theorem phiEquiv_symm (t : ℕ) (c : Fin ((t + 1) ^ (g * g * (g * g)))) (r : Quad g) :
    ((phiEquiv g t).symm c r : ℕ) = c / (t + 1) ^ (quadEquiv g r : ℕ) % (t + 1) := by
  show (finFunctionFinEquiv.symm c (quadEquiv g r) : ℕ) = _
  rw [finFunctionFinEquiv_symm_apply_val]

/-! ### Line networks at codes -/

/-- The grid index of slot `i` of line `n`: `(n, i)` for rows, `(i, n)` for columns. -/
def ptI (tr : Bool) (g n i : ℕ) : ℕ := if tr then n + g * i else i + g * n

variable {m : ℕ}

/-- The table of a clique on `g²` nodes, read at a node index and a block code. -/
def tabAt (T : Clique (ZMod m) (g * g) lam) (γ Q : ℕ) : ZMod m :=
  if h : γ < g * g then T ⟨γ, h⟩ (thetaOf lam Q) else 0

/-- The weight of line `n` at code `Q`. -/
def lineW (T : ℕ → ℕ → ZMod m) (tr : Bool) (g lam Q n : ℕ) : ZMod m :=
  (∏ i ∈ range g, if slc lam g Q i (ptI tr g n i) = 0 then T (ptI tr g n i) (Q / 2 ^ (lam * (g * g * i))) else 0) *
    ∏ i ∈ range g, ∏ i' ∈ range g, if i < i' then
      (if slc lam g Q i (ptI tr g n i') = slc lam g Q i' (ptI tr g n i) then 1 else 0) else 1

/-- The offset of rectangle factor `k` (pairs `k = i g + i'`, `i < i'`). -/
def offC (cw : ℕ → ℕ → ℕ) (g k : ℕ) : ℕ := ∑ j ∈ range k, if j / g % g < j % g then cw (j / g % g) (j % g) else 0

/-- A factor function of a line network at codes (left: the other line `n'`; right: the line `n`), given the
rectangle factors `f i i' X Y Q''` and their widths `cw i i'`. -/
def lineF (f : ℕ → ℕ → ℕ → ℕ → ℕ → ZMod m) (cw : ℕ → ℕ → ℕ) (tr : Bool) (g lam Q n Q' : ℕ) : ZMod m :=
  (∏ i ∈ range g, if slc lam g Q i (ptI tr g n i) = Q' / 2 ^ (lam * i) % 2 ^ lam then 1 else 0) *
    ∏ k ∈ range (g * g), if k / g % g < k % g then
      f (k / g % g) (k % g) (slc lam g Q (k / g % g) (ptI tr g n (k % g)))
        (slc lam g Q (k % g) (ptI tr g n (k / g % g))) (Q' / 2 ^ (g * lam) / 2 ^ offC cw g k) else 1

theorem slc_bdec_zero (Q i w : ℕ) : bdec lam (slc lam g Q i w) = zeroBits lam ↔ slc lam g Q i w = 0 := by
  rw [Fac.bdec_eq_zero, Nat.mod_eq_of_lt (slc_lt _ _ _ _ _)]

theorem slc_bdec_eq (Q i w i' w' : ℕ) :
    bdec lam (slc lam g Q i w) = bdec lam (slc lam g Q i' w') ↔ slc lam g Q i w = slc lam g Q i' w' := by
  rw [bdec_eq_iff, Nat.mod_eq_of_lt (slc_lt _ _ _ _ _), Nat.mod_eq_of_lt (slc_lt _ _ _ _ _)]

theorem slc_bdec_eq' (Q i w X : ℕ) :
    bdec lam (slc lam g Q i w) = bdec lam X ↔ slc lam g Q i w = X % 2 ^ lam := by
  rw [bdec_eq_iff, Nat.mod_eq_of_lt (slc_lt _ _ _ _ _)]

theorem gidx_val (w : Pt g) : (gidx g w : ℕ) = w.2 + g * w.1 := finProdFinEquiv_apply_val w

/-- The table of `toGrid` at point `(a, j)`, for the strings of slot `i` of a line code. -/
theorem toGrid_at (T : Clique (ZMod m) (g * g) lam) (Q : Fin (2 ^ (lam * (g * (g * g))))) (i a j : Fin g) :
    toGrid T (a, j) ((lineEquiv g lam).symm Q i) = tabAt T (j + g * a) (Q / 2 ^ (lam * (g * g * i))) := by
  have hlt : (j : ℕ) + g * a < g * g := by
    have := (gidx g (a, j)).2; rw [gidx_val] at this; exact this
  unfold toGrid tabAt
  rw [dif_pos hlt]
  have e1 : gidx g (a, j) = ⟨_, hlt⟩ := Fin.ext (gidx_val _)
  rw [e1]
  congr 1
  funext γ
  rw [lineEquiv_symm]
  have hγ : (((gidx g).symm γ).2 : ℕ) + g * ((gidx g).symm γ).1 = γ := by
    rw [← gidx_val, Equiv.apply_symm_apply]
  rw [hγ, thetaOf, Nat.div_div_eq_div_mul, ← pow_add, mul_add, add_comm (lam * γ)]

/-- Products over a list with constant widths. -/
theorem plA_const {R X Y ι : Type*} [CommSemiring R] (w : ℕ) (F : ι → Fac R X Y w) (x : X) :
    ∀ (L : List ι) (f : ℕ → ι), (∀ k (h : k < L.length), L[k] = f k) → ∀ q, Fac.plA (fun _ => w) F x L q =
      ∏ k ∈ range L.length, (F (f k)).l x (bdec w (q / 2 ^ (w * k)))
  | [], _, _, _ => by simp [Fac.plA]
  | i :: L, f, hf, q => by
      have h0 : i = f 0 := hf 0 (by simp)
      have hf' : ∀ k (h : k < L.length), L[k] = f (k + 1) := fun k h => hf (k + 1) (by simp; omega)
      rw [Fac.plA, plA_const w F x L _ hf', List.length_cons, prod_range_succ', h0, mul_comm]
      congr 1
      · refine prod_congr rfl fun k _ => ?_
        rw [Nat.div_div_eq_div_mul, ← pow_add]
        congr 4; ring
      · simp

theorem plA_finRange {R X Y : Type*} [CommSemiring R] (w : ℕ) (hg : 0 < g) (F : Fin g → Fac R X Y w) (x : X)
    (q : ℕ) : Fac.plA (fun _ => w) F x (List.finRange g) q =
      ∏ k ∈ range g, (F ⟨k % g, Nat.mod_lt _ hg⟩).l x (bdec w (q / 2 ^ (w * k))) := by
  rw [plA_const w F x (List.finRange g) (fun k => ⟨k % g, Nat.mod_lt _ hg⟩), List.length_finRange]
  intro k hk
  rw [List.length_finRange] at hk
  simp [List.getElem_finRange, Nat.mod_eq_of_lt hk]

/-- Products over a list with constant widths, right side. -/
theorem plB_const {R X Y ι : Type*} [CommSemiring R] (w : ℕ) (F : ι → Fac R X Y w) (x : Y) :
    ∀ (L : List ι) (f : ℕ → ι), (∀ k (h : k < L.length), L[k] = f k) → ∀ q, Fac.plB (fun _ => w) F x L q =
      ∏ k ∈ range L.length, (F (f k)).r x (bdec w (q / 2 ^ (w * k)))
  | [], _, _, _ => by simp [Fac.plB]
  | i :: L, f, hf, q => by
      have h0 : i = f 0 := hf 0 (by simp)
      have hf' : ∀ k (h : k < L.length), L[k] = f (k + 1) := fun k h => hf (k + 1) (by simp; omega)
      rw [Fac.plB, plB_const w F x L _ hf', List.length_cons, prod_range_succ', h0, mul_comm]
      congr 1
      · refine prod_congr rfl fun k _ => ?_
        rw [Nat.div_div_eq_div_mul, ← pow_add]
        congr 4; ring
      · simp

theorem plB_finRange {R X Y : Type*} [CommSemiring R] (w : ℕ) (hg : 0 < g) (F : Fin g → Fac R X Y w) (x : Y)
    (q : ℕ) : Fac.plB (fun _ => w) F x (List.finRange g) q =
      ∏ k ∈ range g, (F ⟨k % g, Nat.mod_lt _ hg⟩).r x (bdec w (q / 2 ^ (w * k))) := by
  rw [plB_const w F x (List.finRange g) (fun k => ⟨k % g, Nat.mod_lt _ hg⟩), List.length_finRange]
  intro k hk
  rw [List.length_finRange] at hk
  simp [List.getElem_finRange, Nat.mod_eq_of_lt hk]

/-- Digit `q` of a choice code (radix `t + 1`). -/
def phiD (t c q : ℕ) : ℕ := c / (t + 1) ^ q % (t + 1)

/-- The number of the quadruple of lines `n < n'` and slots `i < i'` (rows: `((n, n'), (i, i'))`; columns:
`((i, i'), (n, n'))`). -/
def qIdx (tr : Bool) (g n n' i i' : ℕ) : ℕ :=
  if tr then n' + g * n + g * g * (i' + g * i) else i' + g * i + g * g * (n' + g * n)

/-- The width of the line pair `n < n'`. -/
def lineC (cX : ℕ → ℕ) (tr : Bool) (g lam t c n n' : ℕ) : ℕ :=
  g * lam + ∑ i ∈ range g, ∑ i' ∈ range g, if i < i' then cX (phiD t c (qIdx tr g n n' i i')) else 0

/-- The rectangle factors at codes, as elements of `ZMod m`. -/
def facRL (m lam i X Y Q : ℕ) : ZMod m := (((rowFac lam i).l (bdec lam X, bdec lam Y) (bdec (cRow lam i) Q) : ℤ) : ZMod m)
def facRR (m lam i X Y Q : ℕ) : ZMod m := (((rowFac lam i).r (bdec lam X, bdec lam Y) (bdec (cRow lam i) Q) : ℤ) : ZMod m)
def facCL (m lam i X Y Q : ℕ) : ZMod m := (((colFac lam i).l (bdec lam X, bdec lam Y) (bdec (cCol lam i) Q) : ℤ) : ZMod m)
def facCR (m lam i X Y Q : ℕ) : ZMod m := (((colFac lam i).r (bdec lam X, bdec lam Y) (bdec (cCol lam i) Q) : ℤ) : ZMod m)

section Codes

variable (T : Clique (ZMod m) (g * g) lam) (c : Fin ((tB lam + 1) ^ (g * g * (g * g))))

theorem restrict_at (a a' i i' : Fin g) (ha : a < a') (hi : i < i') :
    ιf (restrictC ((phiEquiv g (tB lam)).symm c)) ((a, a'), (i, i')) = phiD (tB lam) c (qIdx false g a a' i i') := by
  rw [ιf_restrictC, if_pos (by simp [rects, ha, hi]), phiEquiv_symm, quadEquiv_val]
  rfl

theorem restrict_at' (a a' i i' : Fin g) (ha : a < a') (hi : i < i') :
    ιf (restrictC ((phiEquiv g (tB lam)).symm c)) ((i, i'), (a, a')) = phiD (tB lam) c (qIdx true g a a' i i') := by
  rw [ιf_restrictC, if_pos (by simp [rects, ha, hi]), phiEquiv_symm, quadEquiv_val]
  rfl

theorem rowNet_W_code (ι : Choice g lam) (a : Fin g) (Q : Fin (2 ^ (lam * (g * (g * g))))) :
    (rowNet (toGrid T) ι).W a ((lineEquiv g lam).symm Q) = lineW (tabAt T) false g lam Q a := by
  show (∏ j, if (lineEquiv g lam).symm Q j (a, j) = zeroBits lam then
      toGrid T (a, j) ((lineEquiv g lam).symm Q j) else 0) *
    ∏ q ∈ pairs g, (if (lineEquiv g lam).symm Q q.1 (a, q.2) = (lineEquiv g lam).symm Q q.2 (a, q.1)
      then 1 else 0) = _
  unfold lineW
  congr 1
  · rw [prod_fin_range]
    refine prod_congr rfl fun j hj => ?_
    rw [dif_pos (mem_range.mp hj), toGrid_at]
    simp only [lineEquiv_symm_slc, slc_bdec_zero]
    rfl
  · rw [prod_pairs_range]
    refine prod_congr rfl fun i hi => prod_congr rfl fun i' hi' => ?_
    rw [dif_pos ⟨mem_range.mp hi, mem_range.mp hi'⟩]
    simp only [lineEquiv_symm_slc, slc_bdec_eq]
    rfl

theorem colNet_W_code (ι : Choice g lam) (j : Fin g) (Q : Fin (2 ^ (lam * (g * (g * g))))) :
    (colNet (toGrid T) ι).W j ((lineEquiv g lam).symm Q) = lineW (tabAt T) true g lam Q j := by
  show (∏ a, if (lineEquiv g lam).symm Q a (a, j) = zeroBits lam then
      toGrid T (a, j) ((lineEquiv g lam).symm Q a) else 0) *
    ∏ p ∈ pairs g, (if (lineEquiv g lam).symm Q p.1 (p.2, j) = (lineEquiv g lam).symm Q p.2 (p.1, j)
      then 1 else 0) = _
  unfold lineW
  congr 1
  · rw [prod_fin_range]
    refine prod_congr rfl fun a ha => ?_
    rw [dif_pos (mem_range.mp ha), toGrid_at]
    simp only [lineEquiv_symm_slc, slc_bdec_zero]
    rfl
  · rw [prod_pairs_range]
    refine prod_congr rfl fun i hi => prod_congr rfl fun i' hi' => ?_
    rw [dif_pos ⟨mem_range.mp hi, mem_range.mp hi'⟩]
    simp only [lineEquiv_symm_slc, slc_bdec_eq]
    rfl

theorem rowNet_c_code (a a' : Fin g) (ha : a < a') :
    (rowNet (toGrid T) (restrictC ((phiEquiv g (tB lam)).symm c))).c a a' =
      lineC (cRow lam) false g lam (tB lam) c a a' := by
  show ((List.finRange g).map fun _ => lam).sum +
    ((pairsList g).map fun q => cRow lam (ιf (restrictC ((phiEquiv g (tB lam)).symm c)) ((a, a'), q))).sum = _
  rw [sum_finRange_const, sum_pairsList, sum_pairs_range, lineC]
  congr 1
  refine sum_congr rfl fun i hi => sum_congr rfl fun i' hi' => ?_
  rw [dif_pos ⟨mem_range.mp hi, mem_range.mp hi'⟩]
  split_ifs with h
  · rw [restrict_at c a a' _ _ ha h]
  · rfl

theorem colNet_c_code (j j' : Fin g) (hj : j < j') :
    (colNet (toGrid T) (restrictC ((phiEquiv g (tB lam)).symm c))).c j j' =
      lineC (cCol lam) true g lam (tB lam) c j j' := by
  show ((List.finRange g).map fun _ => lam).sum +
    ((pairsList g).map fun p => cCol lam (ιf (restrictC ((phiEquiv g (tB lam)).symm c)) (p, (j, j')))).sum = _
  rw [sum_finRange_const, sum_pairsList, sum_pairs_range, lineC]
  congr 1
  refine sum_congr rfl fun i hi => sum_congr rfl fun i' hi' => ?_
  rw [dif_pos ⟨mem_range.mp hi, mem_range.mp hi'⟩]
  split_ifs with h
  · rw [restrict_at' c j j' _ _ hj h]
  · rfl

theorem pairOf_lt (hg : 0 < g) (k : ℕ) : (Net.pairOf g hg k).1 < (Net.pairOf g hg k).2 ↔ k / g % g < k % g := by
  simp [Net.pairOf, Fin.lt_def]

theorem offR_row (hg : 0 < g) (a a' : Fin g) (ha : a < a') (k : ℕ) :
    offR (fun q => cRow lam (ιf (restrictC ((phiEquiv g (tB lam)).symm c)) ((a, a'), q)))
        (fun p : Fin g × Fin g => p.1 < p.2) (Net.pairOf g hg) k =
      offC (fun i i' => cRow lam (phiD (tB lam) c (qIdx false g a a' i i'))) g k := by
  unfold offR offC
  refine sum_congr rfl fun j _ => ?_
  by_cases h : (Net.pairOf g hg j).1 < (Net.pairOf g hg j).2
  · rw [if_pos h, if_pos ((pairOf_lt hg j).mp h)]
    show cRow lam (ιf _ ((a, a'), ((Net.pairOf g hg j).1, (Net.pairOf g hg j).2))) = _
    rw [restrict_at c a a' _ _ ha h]; rfl
  · rw [if_neg h, if_neg (fun h' => h ((pairOf_lt hg j).mpr h'))]

theorem offR_col (hg : 0 < g) (j j' : Fin g) (hj : j < j') (k : ℕ) :
    offR (fun p => cCol lam (ιf (restrictC ((phiEquiv g (tB lam)).symm c)) (p, (j, j'))))
        (fun p : Fin g × Fin g => p.1 < p.2) (Net.pairOf g hg) k =
      offC (fun i i' => cCol lam (phiD (tB lam) c (qIdx true g j j' i i'))) g k := by
  unfold offR offC
  refine sum_congr rfl fun i _ => ?_
  by_cases h : (Net.pairOf g hg i).1 < (Net.pairOf g hg i).2
  · rw [if_pos h, if_pos ((pairOf_lt hg i).mp h)]
    show cCol lam (ιf _ (((Net.pairOf g hg i).1, (Net.pairOf g hg i).2), (j, j'))) = _
    rw [restrict_at' c j j' _ _ hj h]; rfl
  · rw [if_neg h, if_neg (fun h' => h ((pairOf_lt hg i).mpr h'))]

theorem rowNet_l_code (hg : 0 < g) (a a' : Fin g) (ha : a < a') (Q : Fin (2 ^ (lam * (g * (g * g))))) (Q' : ℕ) :
    ((rowNet (toGrid T) (restrictC ((phiEquiv g (tB lam)).symm c))).F a a').l ((lineEquiv g lam).symm Q)
        (bdec _ Q') =
      lineF (fun i i' X Y Q'' => facRL m lam (phiD (tB lam) c (qIdx false g a a' i i')) X Y Q'')
        (fun i i' => cRow lam (phiD (tB lam) c (qIdx false g a a' i i'))) false g lam Q a' Q' := by
  set ι := restrictC ((phiEquiv g (tB lam)).symm c)
  show ((Fac.prodList (fun _ => lam) (fun j => vertTest a a' j) (List.finRange g)).mul
    (Fac.prodList (fun q => cRow lam (ιf ι ((a, a'), q))) (fun q => rowRect ι a a' q) (pairsList g))).l
      ((lineEquiv g lam).symm Q) (bdec _ Q') = _
  rw [Fac.l_mul_bdec, Fac.prodList_l, plA_finRange lam hg, sum_finRange_const]
  unfold lineF
  congr 1
  · refine prod_congr rfl fun k hk => ?_
    have hk' := mem_range.mp hk
    simp only [vertTest, Fac.eqTest, Nat.mod_eq_of_lt hk', lineEquiv_symm_slc, slc_bdec_eq']
    rfl
  · erw [Fac.prodList_filter_l]
    rw [plL_eq_range _ _ _ _ _ (Net.pairOf g hg) (Net.pairOf_get g hg), List.length_product,
      List.length_finRange]
    refine prod_congr rfl fun k _ => ?_
    by_cases h : (Net.pairOf g hg k).1 < (Net.pairOf g hg k).2
    · rw [if_pos h, if_pos ((pairOf_lt hg k).mp h), offR_row c hg a a' ha]
      simp only [rowRect, Fac.comp, Fac.mapInt, lineEquiv_symm_slc]
      rw [restrict_at c a a' _ _ ha h]
      rfl
    · rw [if_neg h, if_neg (fun h' => h ((pairOf_lt hg k).mpr h'))]

theorem rowNet_r_code (hg : 0 < g) (a a' : Fin g) (ha : a < a') (Q : Fin (2 ^ (lam * (g * (g * g))))) (Q' : ℕ) :
    ((rowNet (toGrid T) (restrictC ((phiEquiv g (tB lam)).symm c))).F a a').r ((lineEquiv g lam).symm Q)
        (bdec _ Q') =
      lineF (fun i i' X Y Q'' => facRR m lam (phiD (tB lam) c (qIdx false g a a' i i')) X Y Q'')
        (fun i i' => cRow lam (phiD (tB lam) c (qIdx false g a a' i i'))) false g lam Q a Q' := by
  set ι := restrictC ((phiEquiv g (tB lam)).symm c)
  show ((Fac.prodList (fun _ => lam) (fun j => vertTest a a' j) (List.finRange g)).mul
    (Fac.prodList (fun q => cRow lam (ιf ι ((a, a'), q))) (fun q => rowRect ι a a' q) (pairsList g))).r
      ((lineEquiv g lam).symm Q) (bdec _ Q') = _
  rw [Fac.r_mul_bdec, Fac.prodList_r, plB_finRange lam hg, sum_finRange_const]
  unfold lineF
  congr 1
  · refine prod_congr rfl fun k hk => ?_
    have hk' := mem_range.mp hk
    simp only [vertTest, Fac.eqTest, Nat.mod_eq_of_lt hk', lineEquiv_symm_slc, slc_bdec_eq']
    rfl
  · erw [Fac.prodList_filter_r]
    rw [plR_eq_range _ _ _ _ _ (Net.pairOf g hg) (Net.pairOf_get g hg), List.length_product,
      List.length_finRange]
    refine prod_congr rfl fun k _ => ?_
    by_cases h : (Net.pairOf g hg k).1 < (Net.pairOf g hg k).2
    · rw [if_pos h, if_pos ((pairOf_lt hg k).mp h), offR_row c hg a a' ha]
      simp only [rowRect, Fac.comp, Fac.mapInt, lineEquiv_symm_slc]
      rw [restrict_at c a a' _ _ ha h]
      rfl
    · rw [if_neg h, if_neg (fun h' => h ((pairOf_lt hg k).mpr h'))]

theorem colNet_l_code (hg : 0 < g) (j j' : Fin g) (hj : j < j') (Q : Fin (2 ^ (lam * (g * (g * g))))) (Q' : ℕ) :
    ((colNet (toGrid T) (restrictC ((phiEquiv g (tB lam)).symm c))).F j j').l ((lineEquiv g lam).symm Q)
        (bdec _ Q') =
      lineF (fun i i' X Y Q'' => facCL m lam (phiD (tB lam) c (qIdx true g j j' i i')) X Y Q'')
        (fun i i' => cCol lam (phiD (tB lam) c (qIdx true g j j' i i'))) true g lam Q j' Q' := by
  set ι := restrictC ((phiEquiv g (tB lam)).symm c)
  show ((Fac.prodList (fun _ => lam) (fun a => horizTest (R := ZMod m) j j' a) (List.finRange g)).mul
    (Fac.prodList (fun p => cCol lam (ιf ι (p, (j, j')))) (fun p => colRect (R := ZMod m) ι j j' p) (pairsList g))).l
      ((lineEquiv g lam).symm Q) (bdec _ Q') = _
  rw [Fac.l_mul_bdec, Fac.prodList_l, plA_finRange lam hg, sum_finRange_const]
  unfold lineF
  congr 1
  · refine prod_congr rfl fun k hk => ?_
    have hk' := mem_range.mp hk
    simp only [horizTest, Fac.eqTest, Nat.mod_eq_of_lt hk', lineEquiv_symm_slc, slc_bdec_eq']
    rfl
  · erw [Fac.prodList_filter_l]
    rw [plL_eq_range _ _ _ _ _ (Net.pairOf g hg) (Net.pairOf_get g hg), List.length_product,
      List.length_finRange]
    refine prod_congr rfl fun k _ => ?_
    by_cases h : (Net.pairOf g hg k).1 < (Net.pairOf g hg k).2
    · rw [if_pos h, if_pos ((pairOf_lt hg k).mp h), offR_col c hg j j' hj]
      simp only [colRect, Fac.comp, Fac.mapInt, lineEquiv_symm_slc]
      rw [restrict_at' c j j' _ _ hj h]
      rfl
    · rw [if_neg h, if_neg (fun h' => h ((pairOf_lt hg k).mpr h'))]

theorem colNet_r_code (hg : 0 < g) (j j' : Fin g) (hj : j < j') (Q : Fin (2 ^ (lam * (g * (g * g))))) (Q' : ℕ) :
    ((colNet (toGrid T) (restrictC ((phiEquiv g (tB lam)).symm c))).F j j').r ((lineEquiv g lam).symm Q)
        (bdec _ Q') =
      lineF (fun i i' X Y Q'' => facCR m lam (phiD (tB lam) c (qIdx true g j j' i i')) X Y Q'')
        (fun i i' => cCol lam (phiD (tB lam) c (qIdx true g j j' i i'))) true g lam Q j Q' := by
  set ι := restrictC ((phiEquiv g (tB lam)).symm c)
  show ((Fac.prodList (fun _ => lam) (fun a => horizTest (R := ZMod m) j j' a) (List.finRange g)).mul
    (Fac.prodList (fun p => cCol lam (ιf ι (p, (j, j')))) (fun p => colRect (R := ZMod m) ι j j' p) (pairsList g))).r
      ((lineEquiv g lam).symm Q) (bdec _ Q') = _
  rw [Fac.r_mul_bdec, Fac.prodList_r, plB_finRange lam hg, sum_finRange_const]
  unfold lineF
  congr 1
  · refine prod_congr rfl fun k hk => ?_
    have hk' := mem_range.mp hk
    simp only [horizTest, Fac.eqTest, Nat.mod_eq_of_lt hk', lineEquiv_symm_slc, slc_bdec_eq']
    rfl
  · erw [Fac.prodList_filter_r]
    rw [plR_eq_range _ _ _ _ _ (Net.pairOf g hg) (Net.pairOf_get g hg), List.length_product,
      List.length_finRange]
    refine prod_congr rfl fun k _ => ?_
    by_cases h : (Net.pairOf g hg k).1 < (Net.pairOf g hg k).2
    · rw [if_pos h, if_pos ((pairOf_lt hg k).mp h), offR_col c hg j j' hj]
      simp only [colRect, Fac.comp, Fac.mapInt, lineEquiv_symm_slc]
      rw [restrict_at' c j j' _ _ hj h]
      rfl
    · rw [if_neg h, if_neg (fun h' => h ((pairOf_lt hg k).mpr h'))]

end Codes

/-! ### The rectangle factors at codes, as numbers -/

/-- A decoder run of `coefFac`, from `j m + 1` (`EnginePieces.lean`). -/
def decN (m Q : ℕ) (cv ev : ℕ → ℕ → ℕ) (t j : ℕ) : ℕ := cfOut m (cfRun m Q cv ev t (j * m + 1 % m))

/-- The left decoder of `rowFacB`/`colFacB` at codes `X, Y`. -/
def decL (m lam X Y j Q : ℕ) : ℕ := decN m Q (cvP m X Y) (evL X Y) (tB lam) j
/-- The right decoder of `rowFacB` at codes `U, V`. -/
def decRR (m lam U V j Q : ℕ) : ℕ :=
  decN m Q (fun s Qs => psiN m Qs (V / 2 ^ (3 * s)) (U / 2 ^ (3 * s))) (evRowR m U V) (tB lam) j
/-- The right decoder of `colFacB` at codes `U, V`. -/
def decCR (m lam U V j Q : ℕ) : ℕ :=
  decN m Q (fun s Qs => psiN m Qs (V / 2 ^ (3 * s)) (U / 2 ^ (3 * s))) (evColR m U V) (tB lam) j

/-- `A_i(x, y, u, v)` at codes, through `rowFacB`. -/
def pieceN (m lam i X Y U V : ℕ) : ℕ :=
  (∑ q ∈ range (2 ^ (4 * tB lam + 3 * i)), decL m lam X Y i q * decRR m lam U V i q) % m

/-- The left rectangle factor at codes (`tr = false`: `rowFac`; `true`: `colFac`). -/
def facLN (tr : Bool) (m lam i X Y Q : ℕ) : ℕ :=
  let j := if tr then tB lam - i else i
  if 4 * tB lam + 3 * j ≤ 2 * lam then decL m lam X Y j Q
  else if Q % 2 ^ (lam + lam) = X + 2 ^ lam * Y then 1 else 0

/-- The right rectangle factor at codes. -/
def facRN (tr : Bool) (m lam i U V Q : ℕ) : ℕ :=
  let j := if tr then tB lam - i else i
  if 4 * tB lam + 3 * j ≤ 2 * lam then (if tr then decCR m lam U V j Q else decRR m lam U V j Q)
  else if tr then pieceN m lam i (Q % 2 ^ lam) U (Q / 2 ^ lam % 2 ^ lam) V
  else pieceN m lam i (Q % 2 ^ lam) (Q / 2 ^ lam % 2 ^ lam) U V

section FacCodes

variable {m lam : ℕ}

theorem cfOut_lt (hm : 0 < m) (st : ℕ) : cfOut m st < m := by
  unfold cfOut; split_ifs
  · exact Nat.mod_lt _ hm
  · exact hm

theorem pieceN_cast (hm : 0 < m) (i X Y U V : ℕ) (hX : X < 2 ^ lam) (hY : Y < 2 ^ lam) (hU : U < 2 ^ lam)
    (hV : V < 2 ^ lam) :
    ((pieceN m lam i X Y U V : ℕ) : ZMod m) =
      ((pieceA lam i (bdec lam X) (bdec lam Y) (bdec lam U) (bdec lam V) : ℤ) : ZMod m) := by
  rw [← eval_rowFacB lam i (bdec lam X, bdec lam Y) (bdec lam U, bdec lam V)]
  unfold pieceN Fac.eval
  rw [sum_bits_eq, ZMod.natCast_mod, Nat.cast_sum, Int.cast_sum]
  refine sum_congr rfl fun q _ => ?_
  rw [Nat.cast_mul, Int.cast_mul, decL, decN, rowFacB_l_code hm i hX hY, decRR, decN, rowFacB_r_code hm i hU hV]

theorem facLN_row (hm : 0 < m) (i X Y Q : ℕ) (hX : X < 2 ^ lam) (hY : Y < 2 ^ lam) :
    ((facLN false m lam i X Y Q : ℕ) : ZMod m) = facRL m lam i X Y Q := by
  unfold facLN facRL rowFac
  simp only [Bool.false_eq_true, if_false]
  split_ifs with h h2
  · rw [Fac.l_cast, Fac.bdec_cast, decL, decN, rowFacB_l_code hm i hX hY]
  · rw [Fac.l_cast, Fac.bdec_cast]
    have hk : strPairEquiv lam (bdec lam X, bdec lam Y) = bdec (lam + lam) Q :=
      (append_bdec_iff lam lam X Y Q hX hY).mpr h2
    simp only [Fac.ofEquiv]
    rw [if_pos hk]
    simp
  · rw [Fac.l_cast, Fac.bdec_cast]
    have hk : ¬ strPairEquiv lam (bdec lam X, bdec lam Y) = bdec (lam + lam) Q :=
      fun h' => h2 ((append_bdec_iff lam lam X Y Q hX hY).mp h')
    simp only [Fac.ofEquiv]
    rw [if_neg hk]
    simp

theorem facLN_col (hm : 0 < m) (i X Y Q : ℕ) (hX : X < 2 ^ lam) (hY : Y < 2 ^ lam) :
    ((facLN true m lam i X Y Q : ℕ) : ZMod m) = facCL m lam i X Y Q := by
  unfold facLN facCL colFac
  simp only [if_true]
  split_ifs with h h2
  · rw [Fac.l_cast, Fac.bdec_cast, decL, decN, colFacB_l_code hm _ hX hY]
  · rw [Fac.l_cast, Fac.bdec_cast]
    have hk : strPairEquiv lam (bdec lam X, bdec lam Y) = bdec (lam + lam) Q :=
      (append_bdec_iff lam lam X Y Q hX hY).mpr h2
    simp only [Fac.ofEquiv]
    rw [if_pos hk]
    simp
  · rw [Fac.l_cast, Fac.bdec_cast]
    have hk : ¬ strPairEquiv lam (bdec lam X, bdec lam Y) = bdec (lam + lam) Q :=
      fun h' => h2 ((append_bdec_iff lam lam X Y Q hX hY).mp h')
    simp only [Fac.ofEquiv]
    rw [if_neg hk]
    simp

theorem facRN_row (hm : 0 < m) (i U V Q : ℕ) (hU : U < 2 ^ lam) (hV : V < 2 ^ lam) :
    ((facRN false m lam i U V Q : ℕ) : ZMod m) = facRR m lam i U V Q := by
  unfold facRN facRR rowFac
  simp only [Bool.false_eq_true, if_false]
  split_ifs with h
  · rw [Fac.r_cast, Fac.bdec_cast, decRR, decN, rowFacB_r_code hm i hU hV]
  · rw [Fac.r_cast, Fac.bdec_cast]
    simp only [Fac.ofEquiv]
    rw [show (strPairEquiv lam).symm (bdec (lam + lam) Q) = (bdec lam Q, bdec lam (Q / 2 ^ lam)) from
      appendEquiv_symm_bdec lam lam Q, pieceN_cast hm _ _ _ _ _ (Nat.mod_lt _ (by positivity))
      (Nat.mod_lt _ (by positivity)) hU hV, bdec_mod, bdec_mod]

theorem facRN_col (hm : 0 < m) (i U V Q : ℕ) (hU : U < 2 ^ lam) (hV : V < 2 ^ lam) :
    ((facRN true m lam i U V Q : ℕ) : ZMod m) = facCR m lam i U V Q := by
  unfold facRN facCR colFac
  simp only [if_true]
  split_ifs with h
  · rw [Fac.r_cast, Fac.bdec_cast, decCR, decN, colFacB_r_code hm _ hU hV]
  · rw [Fac.r_cast, Fac.bdec_cast]
    simp only [Fac.ofEquiv]
    rw [show (strPairEquiv lam).symm (bdec (lam + lam) Q) = (bdec lam Q, bdec lam (Q / 2 ^ lam)) from
      appendEquiv_symm_bdec lam lam Q, pieceN_cast hm _ _ _ _ _ (Nat.mod_lt _ (by positivity)) hU
      (Nat.mod_lt _ (by positivity)) hV, bdec_mod, bdec_mod]

theorem facLN_lt (hm : 1 < m) (tr : Bool) (i X Y Q : ℕ) : facLN tr m lam i X Y Q < m := by
  unfold facLN decL decN; dsimp only
  split_ifs <;> first | exact cfOut_lt (by omega) _ | omega

theorem facRN_lt (hm : 1 < m) (tr : Bool) (i U V Q : ℕ) : facRN tr m lam i U V Q < m := by
  unfold facRN pieceN decCR decRR decN; dsimp only
  split_ifs <;> first | exact cfOut_lt (by omega) _ | exact Nat.mod_lt _ (by omega)

end FacCodes

/-- The coding of a line network: every node codes its settings by `lineEquiv`. -/
def lineCoding {R : Type*} [CommRing R] (N : Net R g) (hS : ∀ a, N.S a = LineS g lam) : Coding N where
  s _ := 2 ^ (lam * (g * (g * g)))
  pos _ := by positivity
  e a := (Equiv.cast (hS a)).trans (lineEquiv g lam)

theorem lineCoding_symm {R : Type*} [CommRing R] (N : Net R g) (hS : ∀ a, N.S a = LineS g lam) (a : Fin g)
    (Q : Fin (2 ^ (lam * (g * (g * g))))) :
    ((lineCoding N hS).e a).symm Q = cast (hS a).symm ((lineEquiv g lam).symm Q) := rfl

/-- The coding of the row network. -/
def rowCoding {R : Type*} [CommRing R] (T : GridClique R g lam) (ι : Choice g lam) : Coding (rowNet T ι) :=
  lineCoding (rowNet T ι) fun _ => rfl

/-- The coding of the column network. -/
def colCoding {R : Type*} [CommRing R] (T : GridClique R g lam) (ι : Choice g lam) : Coding (colNet T ι) :=
  lineCoding (colNet T ι) fun _ => rfl

end Factoring.Aux
