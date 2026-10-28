/-
One level of the recursion (the paper's Proposition 3), as mathematics: the expansion (34) and the two networks.

A `(g², λ)`-clique is taken on the grid `Pt g = Fin g × Fin g` (row, column): node `w` holds `Θ w : Pt g → Bits λ`.
Its value `gridZ T` sums over all `Θ` the tables (own coordinate `0`), the equality tests of the straight edges
(inside a row: `horizP`; inside a column: `vertP`) and of the two diagonals of every rectangle
`r = ((a, a'), (j, j'))`, `a < a'`, `j < j'` (`rects g = pairs g ×ˢ pairs g`).  The rectangle's four strings (33) are
`rx, ry, ru, rv`; its diagonals test `[x = v]` and `[y = u]`.

* (34) `sum_Zι`: `2^(t|R|) · gridZ T = ∑_ι Z_ι`, over `ι : R → {0, …, t}`, where `Z_ι` replaces each rectangle's two
  diagonal tests by the piece `A_{ι(r)}` (Lemma 2(a)).
* The row network `rowNet T ι` on `Fin g` (a setting of row `a` is the `g` arrays of its points) and the column
  network `colNet T ι`; `value_rowNet`, `value_colNet`: both have value `Z_ι`.  Their pair factorizations are the
  vertical (horizontal) equality tests through `λ` bits each and the pieces' row (column) factorizations of Lemma 2(b).
* (35) `rowNet_c_le`, `colNet_c_le`: two rows (columns) share at most `g²λ` bits; `rowNet_fits`, `colNet_fits`: every
  node shares at most `P = g³λ` bits.  (36) `min_total`: `12 min(U_row, U_col) ≤ 12g³λ + 11g⁴λ + 24g⁴`.

Not an audit surface.
-/
module

public import FactoringAux.Lemma1
public import FactoringAux.Pieces

@[expose] public section

namespace Factoring.Aux

open Finset

namespace Fac

variable {R : Type*} [CommRing R] {X Y : Type*}

/-- Push an integer factorization into a ring. -/
def mapInt {c : ℕ} (f : Fac ℤ X Y c) : Fac R X Y c := ⟨fun x θ => (f.l x θ : R), fun y θ => (f.r y θ : R)⟩

@[simp] theorem eval_mapInt {c : ℕ} (f : Fac ℤ X Y c) (x : X) (y : Y) :
    (f.mapInt : Fac R X Y c).eval x y = (f.eval x y : R) := by
  simp [eval, mapInt]

/-- The equality test `[π x = π' y]` through `L` bits (observation (b) after Definition 1). -/
def eqTest {L : ℕ} (π : X → Bits L) (π' : Y → Bits L) : Fac R X Y L :=
  ⟨fun x θ => if π x = θ then 1 else 0, fun y θ => if π' y = θ then 1 else 0⟩

@[simp] theorem eval_eqTest {L : ℕ} (π : X → Bits L) (π' : Y → Bits L) (x : X) (y : Y) :
    (eqTest π π' : Fac R X Y L).eval x y = if π x = π' y then 1 else 0 := by
  simp only [eval, eqTest, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp [eq_comm]

end Fac

variable {R : Type*} [CommRing R] {g lam : ℕ}

/-- Grid points: (row, column). -/
abbrev Pt (g : ℕ) := Fin g × Fin g

/-- Rectangles: two rows `a < a'` and two columns `j < j'`. -/
def rects (g : ℕ) : Finset ((Fin g × Fin g) × (Fin g × Fin g)) := pairs g ×ˢ pairs g

/-- A clique on the grid, with written-out tables. -/
abbrev GridClique (R : Type*) (g lam : ℕ) := Pt g → (Pt g → Bits lam) → R

/-- The equality test of the edge `{w, w'}`: the two copies agree. -/
def eqI (Θ : Pt g → Pt g → Bits lam) (w w' : Pt g) : R := if Θ w w' = Θ w' w then 1 else 0

/-- The tables, each with its own coordinate `0`. -/
def diagW (T : GridClique R g lam) (Θ : Pt g → Pt g → Bits lam) : R :=
  ∏ w, if Θ w w = zeroBits lam then T w (Θ w) else 0

/-- The straight edges inside rows. -/
def horizP (Θ : Pt g → Pt g → Bits lam) : R := ∏ a, ∏ q ∈ pairs g, eqI Θ (a, q.1) (a, q.2)

/-- The straight edges inside columns. -/
def vertP (Θ : Pt g → Pt g → Bits lam) : R := ∏ p ∈ pairs g, ∏ j, eqI Θ (p.1, j) (p.2, j)

/-- The four strings of rectangle `r = ((a, a'), (j, j'))`, eq. (33). -/
def rx (Θ : Pt g → Pt g → Bits lam) (r : (Fin g × Fin g) × (Fin g × Fin g)) : Bits lam :=
  Θ (r.1.1, r.2.1) (r.1.2, r.2.2)
def ry (Θ : Pt g → Pt g → Bits lam) (r : (Fin g × Fin g) × (Fin g × Fin g)) : Bits lam :=
  Θ (r.1.1, r.2.2) (r.1.2, r.2.1)
def ru (Θ : Pt g → Pt g → Bits lam) (r : (Fin g × Fin g) × (Fin g × Fin g)) : Bits lam :=
  Θ (r.1.2, r.2.1) (r.1.1, r.2.2)
def rv (Θ : Pt g → Pt g → Bits lam) (r : (Fin g × Fin g) × (Fin g × Fin g)) : Bits lam :=
  Θ (r.1.2, r.2.2) (r.1.1, r.2.1)

/-- The value of a grid clique: every edge is straight or a diagonal of exactly one rectangle. -/
def gridZ (T : GridClique R g lam) : R :=
  ∑ Θ : Pt g → Pt g → Bits lam, diagW T Θ * horizP Θ * vertP Θ *
    ∏ r ∈ rects g, (eqI Θ (r.1.1, r.2.1) (r.1.2, r.2.2) * eqI Θ (r.1.1, r.2.2) (r.1.2, r.2.1))

/-- A choice of one piece per rectangle. -/
abbrev Choice (g lam : ℕ) := {r // r ∈ rects g} → Fin (tB lam + 1)

/-- The piece index of a rectangle (`0` off the rectangles). -/
def ιf (ι : Choice g lam) (r : (Fin g × Fin g) × (Fin g × Fin g)) : ℕ :=
  if h : r ∈ rects g then (ι ⟨r, h⟩ : ℕ) else 0

theorem ιf_le (ι : Choice g lam) (r : (Fin g × Fin g) × (Fin g × Fin g)) : ιf ι r ≤ tB lam := by
  unfold ιf; split
  · exact Nat.lt_succ_iff.mp (ι _).2
  · exact Nat.zero_le _

/-- The piece of rectangle `r` under the choice `ι`. -/
def rectA (ι : Choice g lam) (Θ : Pt g → Pt g → Bits lam) (r : (Fin g × Fin g) × (Fin g × Fin g)) : R :=
  (pieceA lam (ιf ι r) (rx Θ r) (ry Θ r) (ru Θ r) (rv Θ r) : R)

/-- `Z_ι` of (34). -/
def Zι (T : GridClique R g lam) (ι : Choice g lam) : R :=
  ∑ Θ : Pt g → Pt g → Bits lam, diagW T Θ * horizP Θ * vertP Θ * ∏ r ∈ rects g, rectA ι Θ r

/-- Lemma 2(a) at one rectangle. -/
theorem sum_rectA (Θ : Pt g → Pt g → Bits lam) (r : (Fin g × Fin g) × (Fin g × Fin g)) :
    ∑ i : Fin (tB lam + 1), (pieceA lam i (rx Θ r) (ry Θ r) (ru Θ r) (rv Θ r) : R) =
      (2 : R) ^ tB lam * (eqI Θ (r.1.1, r.2.1) (r.1.2, r.2.2) * eqI Θ (r.1.1, r.2.2) (r.1.2, r.2.1)) := by
  have h := sum_pieceA lam (rx Θ r) (ry Θ r) (ru Θ r) (rv Θ r)
  rw [← Fin.sum_univ_eq_sum_range] at h
  have h' := congrArg (fun z : ℤ => (z : R)) h
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_ofNat] at h'
  rw [h']
  unfold eqI rx ry ru rv
  by_cases h1 : Θ (r.1.1, r.2.1) (r.1.2, r.2.2) = Θ (r.1.2, r.2.2) (r.1.1, r.2.1) <;>
    by_cases h2 : Θ (r.1.1, r.2.2) (r.1.2, r.2.1) = Θ (r.1.2, r.2.1) (r.1.1, r.2.2) <;> simp [h1, h2]

/-- Eq. (34): `2^(t|R|) Z = ∑_ι Z_ι`. -/
theorem sum_Zι (T : GridClique R g lam) :
    (2 : R) ^ (tB lam * (rects g).card) * gridZ T = ∑ ι : Choice g lam, Zι T ι := by
  unfold gridZ Zι
  rw [Finset.mul_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun Θ _ => ?_
  rw [← Finset.mul_sum]
  have : (2 : R) ^ (tB lam * (rects g).card) *
      ∏ r ∈ rects g, (eqI Θ (r.1.1, r.2.1) (r.1.2, r.2.2) * eqI Θ (r.1.1, r.2.2) (r.1.2, r.2.1)) =
      ∑ ι : Choice g lam, ∏ r ∈ rects g, rectA ι Θ r := by
    rw [pow_mul, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    rw [← Finset.prod_coe_sort (rects g)]
    simp only [← sum_rectA]
    rw [Fintype.prod_sum]
    refine Finset.sum_congr rfl fun ι _ => ?_
    rw [← Finset.prod_coe_sort (rects g)]
    refine Finset.prod_congr rfl fun r _ => ?_
    simp [rectA, ιf, r.2]
  rw [← this]
  ring

/-! ### The row network -/

/-- A setting of a row (or of a column): the arrays of its `g` points. -/
abbrev LineS (g lam : ℕ) := Fin g → (Pt g → Bits lam)

/-- The pieces of the rectangles between rows `a, a'`, row-wise. -/
def rowRect (ι : Choice g lam) (a a' : Fin g) (q : Fin g × Fin g) :
    Fac R (LineS g lam) (LineS g lam) (cRow lam (ιf ι ((a, a'), q))) :=
  (rowFac lam (ιf ι ((a, a'), q))).mapInt.comp
    (fun s => (s q.1 (a', q.2), s q.2 (a', q.1))) (fun s' => (s' q.1 (a, q.2), s' q.2 (a, q.1)))

/-- The vertical test in column `j` between rows `a, a'`. -/
def vertTest (a a' j : Fin g) : Fac R (LineS g lam) (LineS g lam) lam :=
  Fac.eqTest (fun s => s j (a', j)) (fun s' => s' j (a, j))

/-- The row network for the choice `ι`. -/
def rowNet (T : GridClique R g lam) (ι : Choice g lam) : Net R g where
  S _ := LineS g lam
  fS _ := inferInstance
  dS _ := inferInstance
  W a s := (∏ j, if s j (a, j) = zeroBits lam then T (a, j) (s j) else 0) *
    ∏ q ∈ pairs g, (if s q.1 (a, q.2) = s q.2 (a, q.1) then 1 else 0)
  c a a' := ((List.finRange g).map fun _ => lam).sum +
    ((pairsList g).map fun q => cRow lam (ιf ι ((a, a'), q))).sum
  F a a' := (Fac.prodList (fun _ => lam) (fun j => vertTest a a' j) (List.finRange g)).mul
    (Fac.prodList (fun q => cRow lam (ιf ι ((a, a'), q))) (fun q => rowRect ι a a' q) (pairsList g))

/-- Products over the list of pairs are products over `pairs g`. -/
theorem prod_pairsList {M : Type*} [CommMonoid M] (f : Fin g × Fin g → M) :
    ((pairsList g).map f).prod = ∏ q ∈ pairs g, f q := by
  rw [← List.prod_toFinset f (pairsList_nodup g)]
  congr 1
  ext q; simp [mem_pairsList]

theorem prod_finRange {M : Type*} [CommMonoid M] (f : Fin g → M) :
    ((List.finRange g).map f).prod = ∏ j, f j := by
  rw [← List.prod_toFinset f (List.nodup_finRange g)]
  congr 1
  ext j; simp

/-- The row network has value `Z_ι`. -/
theorem value_rowNet (T : GridClique R g lam) (ι : Choice g lam) : (rowNet T ι).value = Zι T ι := by
  have hv : (rowNet T ι).value = ∑ s : Fin g → LineS g lam, (∏ a, (rowNet T ι).W a (s a)) *
      ∏ p ∈ pairs g, (rowNet T ι).Ψ p.1 p.2 (s p.1) (s p.2) := rfl
  rw [hv, Zι, ← (Equiv.curry (Fin g) (Fin g) (Pt g → Bits lam)).symm.sum_comp]
  refine Finset.sum_congr rfl fun s _ => ?_
  -- weights
  have hW : ∏ a, (rowNet T ι).W a (s a) = diagW T ((Equiv.curry _ _ _).symm s) *
      horizP ((Equiv.curry _ _ _).symm s) := by
    simp only [rowNet, Finset.prod_mul_distrib, diagW, horizP, eqI, Fintype.prod_prod_type,
      Equiv.curry_symm_apply, Function.uncurry_apply_pair]
    rfl
  -- pair factors
  have hΨ : ∏ p ∈ pairs g, (rowNet T ι).Ψ p.1 p.2 (s p.1) (s p.2) =
      vertP ((Equiv.curry _ _ _).symm s) * ∏ r ∈ rects g, rectA ι ((Equiv.curry _ _ _).symm s) r := by
    simp only [Net.Ψ, rowNet, Fac.eval_mul, Fac.eval_prodList, prod_finRange, prod_pairsList]
    rw [Finset.prod_mul_distrib, rects, Finset.prod_product]
    congr 1
    · refine Finset.prod_congr rfl fun p _ => Finset.prod_congr rfl fun j _ => ?_
      simp [vertTest, eqI, Equiv.curry_symm_apply]
    · refine Finset.prod_congr rfl fun p _ => Finset.prod_congr rfl fun q _ => ?_
      simp only [rowRect, Fac.eval_comp, Fac.eval_mapInt, eval_rowFac, rectA, rx, ry, ru, rv,
        Equiv.curry_symm_apply, Function.uncurry_apply_pair]
  show (∏ a, (rowNet T ι).W a (s a)) * ∏ p ∈ pairs g, (rowNet T ι).Ψ p.1 p.2 (s p.1) (s p.2) = _
  rw [hW, hΨ]
  ring

/-! ### The column network -/

/-- The pieces of the rectangles between columns `j, j'`, column-wise. -/
def colRect (ι : Choice g lam) (j j' : Fin g) (p : Fin g × Fin g) :
    Fac R (LineS g lam) (LineS g lam) (cCol lam (ιf ι (p, (j, j')))) :=
  (colFac lam (ιf ι (p, (j, j')))).mapInt.comp
    (fun s => (s p.1 (p.2, j'), s p.2 (p.1, j'))) (fun s' => (s' p.1 (p.2, j), s' p.2 (p.1, j)))

/-- The horizontal test in row `a` between columns `j, j'`. -/
def horizTest (j j' a : Fin g) : Fac R (LineS g lam) (LineS g lam) lam :=
  Fac.eqTest (fun s => s a (a, j')) (fun s' => s' a (a, j))

/-- The column network for the choice `ι` (a setting of column `j` is indexed by rows: `s a = Θ (a, j)`). -/
def colNet (T : GridClique R g lam) (ι : Choice g lam) : Net R g where
  S _ := LineS g lam
  fS _ := inferInstance
  dS _ := inferInstance
  W j s := (∏ a, if s a (a, j) = zeroBits lam then T (a, j) (s a) else 0) *
    ∏ p ∈ pairs g, (if s p.1 (p.2, j) = s p.2 (p.1, j) then 1 else 0)
  c j j' := ((List.finRange g).map fun _ => lam).sum +
    ((pairsList g).map fun p => cCol lam (ιf ι (p, (j, j')))).sum
  F j j' := (Fac.prodList (fun _ => lam) (fun a => horizTest j j' a) (List.finRange g)).mul
    (Fac.prodList (fun p => cCol lam (ιf ι (p, (j, j')))) (fun p => colRect ι j j' p) (pairsList g))

/-- The column network has value `Z_ι`. -/
theorem value_colNet (T : GridClique R g lam) (ι : Choice g lam) : (colNet T ι).value = Zι T ι := by
  have hv : (colNet T ι).value = ∑ s : Fin g → LineS g lam, (∏ a, (colNet T ι).W a (s a)) *
      ∏ p ∈ pairs g, (colNet T ι).Ψ p.1 p.2 (s p.1) (s p.2) := rfl
  rw [hv, Zι]
  -- a column setting `s j` is indexed by rows: `Θ (a, j) = s j a`
  let e : (Fin g → LineS g lam) ≃ (Pt g → Pt g → Bits lam) :=
    { toFun := fun s w => s w.2 w.1
      invFun := fun Θ j a => Θ (a, j)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← e.symm.sum_comp]
  refine Finset.sum_congr rfl fun Θ _ => ?_
  have hW : ∏ j, (colNet T ι).W j (e.symm Θ j) = diagW T Θ * vertP Θ := by
    simp only [colNet, Finset.prod_mul_distrib, diagW, vertP, eqI, e, Equiv.coe_fn_symm_mk]
    congr 1
    · rw [Fintype.prod_prod_type, Finset.prod_comm]
    · rw [Finset.prod_comm]
  have hΨ : ∏ q ∈ pairs g, (colNet T ι).Ψ q.1 q.2 (e.symm Θ q.1) (e.symm Θ q.2) =
      horizP Θ * ∏ r ∈ rects g, rectA ι Θ r := by
    simp only [Net.Ψ, colNet, Fac.eval_mul, Fac.eval_prodList, prod_finRange, prod_pairsList]
    rw [Finset.prod_mul_distrib, rects, Finset.prod_product_right]
    congr 1
    · rw [horizP, Finset.prod_comm]
      refine Finset.prod_congr rfl fun q _ => Finset.prod_congr rfl fun a _ => ?_
      simp [horizTest, eqI, e]
    · refine Finset.prod_congr rfl fun q _ => Finset.prod_congr rfl fun p _ => ?_
      simp only [colRect, Fac.eval_comp, Fac.eval_mapInt, eval_colFac _ _ (ιf_le ι _), rectA, rx, ry, ru, rv, e,
        Equiv.coe_fn_symm_mk]
  show (∏ j, (colNet T ι).W j (e.symm Θ j)) *
      ∏ q ∈ pairs g, (colNet T ι).Ψ q.1 q.2 (e.symm Θ q.1) (e.symm Θ q.2) = _
  rw [hW, hΨ]
  ring

/-! ### Shared bits: (35) and (36) -/

theorem card_pairs (g : ℕ) : 2 * (pairs g).card = g * (g - 1) := by
  have h1 := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin g × Fin g))) (fun q => q.1 < q.2)
  have h2 := Finset.card_filter_add_card_filter_not
    (s := (univ : Finset (Fin g × Fin g)).filter (fun q => ¬ q.1 < q.2)) (fun q => q.2 < q.1)
  have hswap : ((univ.filter (fun q : Fin g × Fin g => ¬ q.1 < q.2)).filter (fun q => q.2 < q.1)).card =
      (pairs g).card := by
    refine Finset.card_bij (fun q _ => q.swap) (fun q hq => ?_) (fun q _ q' _ h => ?_) (fun q hq => ?_)
    · simp only [Finset.mem_filter, mem_univ, true_and] at hq; simpa [pairs] using hq.2
    · simpa using congrArg Prod.swap h
    · refine ⟨q.swap, ?_, by simp⟩
      have := mem_pairs.mp hq
      simp [this, this.le]
  have hdiag : ((univ.filter (fun q : Fin g × Fin g => ¬ q.1 < q.2)).filter (fun q => ¬ q.2 < q.1)).card = g := by
    rw [show (univ.filter (fun q : Fin g × Fin g => ¬ q.1 < q.2)).filter (fun q => ¬ q.2 < q.1) =
        univ.image (fun a => (a, a)) by
      ext q; simp only [Finset.mem_filter, mem_univ, true_and, Finset.mem_image]
      constructor
      · intro h; exact ⟨q.1, Prod.ext rfl (le_antisymm (not_lt.mp h.2) (not_lt.mp h.1))⟩
      · rintro ⟨a, rfl⟩; simp]
    rw [Finset.card_image_of_injective _ (fun a b h => (Prod.ext_iff.mp h).1), card_univ, Fintype.card_fin]
  rw [card_univ, Fintype.card_prod, Fintype.card_fin] at h1
  rw [hswap, hdiag] at h2
  have hp : (univ.filter (fun q : Fin g × Fin g => q.1 < q.2)) = pairs g := rfl
  rw [hp] at h1
  rw [Nat.mul_sub_one]
  omega

theorem sum_pairsList {M : Type*} [AddCommMonoid M] (f : Fin g × Fin g → M) :
    ((pairsList g).map f).sum = ∑ q ∈ pairs g, f q := by
  rw [← List.sum_toFinset f (pairsList_nodup g)]
  congr 1
  ext q; simp [mem_pairsList]

theorem sum_finRange_const (k : ℕ) : ((List.finRange g).map fun _ => k).sum = g * k := by
  simp [List.map_const', List.sum_replicate]

/-- The total of a network is twice the sum over pairs. -/
theorem Net.total_eq {g : ℕ} (N : Net R g) : N.total = 2 * ∑ p ∈ pairs g, N.c p.1 p.2 := by
  unfold Net.total Net.cc
  rw [← Fintype.sum_prod_type' (fun a b => if a < b then N.c a b else if b < a then N.c b a else 0)]
  have : ∀ q : Fin g × Fin g, (if q.1 < q.2 then N.c q.1 q.2 else if q.2 < q.1 then N.c q.2 q.1 else 0) =
      (if q.1 < q.2 then N.c q.1 q.2 else 0) + (if q.2 < q.1 then N.c q.2 q.1 else 0) := by
    intro q
    rcases lt_trichotomy q.1 q.2 with h | h | h
    · simp [h, not_lt.mpr h.le]
    · simp [h]
    · simp [h, not_lt.mpr h.le]
  rw [Finset.sum_congr rfl fun q _ => this q, Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_filter]
  have hs : ∑ q ∈ univ.filter (fun q : Fin g × Fin g => q.2 < q.1), N.c q.2 q.1 =
      ∑ q ∈ pairs g, N.c q.1 q.2 := by
    refine Finset.sum_bij (fun q _ => q.swap) (fun q hq => ?_) (fun q _ q' _ h => ?_) (fun q hq => ?_)
      (fun q _ => rfl)
    · simpa [pairs] using hq
    · simpa using congrArg Prod.swap h
    · exact ⟨q.swap, by simpa [pairs] using hq, by simp⟩
  rw [hs]
  show ∑ q ∈ pairs g, N.c q.1 q.2 + _ = _
  ring

theorem rowNet_c (T : GridClique R g lam) (ι : Choice g lam) (a a' : Fin g) :
    (rowNet T ι).c a a' = g * lam + ∑ q ∈ pairs g, cRow lam (ιf ι ((a, a'), q)) := by
  show ((List.finRange g).map fun _ => lam).sum +
    ((pairsList g).map fun q => cRow lam (ιf ι ((a, a'), q))).sum = _
  rw [sum_finRange_const, sum_pairsList]

theorem colNet_c (T : GridClique R g lam) (ι : Choice g lam) (j j' : Fin g) :
    (colNet T ι).c j j' = g * lam + ∑ p ∈ pairs g, cCol lam (ιf ι (p, (j, j'))) := by
  show ((List.finRange g).map fun _ => lam).sum +
    ((pairsList g).map fun p => cCol lam (ιf ι (p, (j, j')))).sum = _
  rw [sum_finRange_const, sum_pairsList]

/-- (35): two rows share at most `g²λ` bits. -/
theorem rowNet_c_le (T : GridClique R g lam) (ι : Choice g lam) (a a' : Fin g) :
    (rowNet T ι).c a a' ≤ g ^ 2 * lam := by
  rw [rowNet_c]
  have h1 : ∑ q ∈ pairs g, cRow lam (ιf ι ((a, a'), q)) ≤ (pairs g).card * (2 * lam) :=
    Finset.sum_le_card_nsmul _ _ _ (fun q _ => cRow_le _ _) |>.trans (by simp)
  have h2 := card_pairs g
  have h3 : (pairs g).card * (2 * lam) = g * (g - 1) * lam := by rw [← h2]; ring
  rcases g with _ | g
  · simp
  · rw [Nat.add_sub_cancel] at h3
    nlinarith

/-- (35), columns. -/
theorem colNet_c_le (T : GridClique R g lam) (ι : Choice g lam) (j j' : Fin g) :
    (colNet T ι).c j j' ≤ g ^ 2 * lam := by
  rw [colNet_c]
  have h1 : ∑ p ∈ pairs g, cCol lam (ιf ι (p, (j, j'))) ≤ (pairs g).card * (2 * lam) :=
    Finset.sum_le_card_nsmul _ _ _ (fun q _ => cCol_le _ _) |>.trans (by simp)
  have h2 := card_pairs g
  have h3 : (pairs g).card * (2 * lam) = g * (g - 1) * lam := by rw [← h2]; ring
  rcases g with _ | g
  · simp
  · rw [Nat.add_sub_cancel] at h3
    nlinarith

theorem fits_of_c_le {g : ℕ} (N : Net R g) (B : ℕ) (h : ∀ a b, N.c a b ≤ B) : N.Fits (g * B) := by
  intro a
  calc ∑ b, N.cc a b ≤ ∑ _b : Fin g, B := Finset.sum_le_sum fun b _ => by
        unfold Net.cc; split_ifs
        · exact h _ _
        · exact h _ _
        · exact Nat.zero_le _
    _ = g * B := by simp

/-- Both networks fit `P = g³λ`. -/
theorem rowNet_fits (T : GridClique R g lam) (ι : Choice g lam) : (rowNet T ι).Fits (g ^ 3 * lam) := by
  have := fits_of_c_le (rowNet T ι) (g ^ 2 * lam) (rowNet_c_le T ι)
  rwa [show g * (g ^ 2 * lam) = g ^ 3 * lam by ring] at this

theorem colNet_fits (T : GridClique R g lam) (ι : Choice g lam) : (colNet T ι).Fits (g ^ 3 * lam) := by
  have := fits_of_c_le (colNet T ι) (g ^ 2 * lam) (colNet_c_le T ι)
  rwa [show g * (g ^ 2 * lam) = g ^ 3 * lam by ring] at this

/-- (36): the smaller total, `12 min(U_row, U_col) ≤ 12 g³λ + 11 g⁴λ + 24 g⁴`. -/
theorem min_total (T : GridClique R g lam) (ι : Choice g lam) :
    12 * min (rowNet T ι).total (colNet T ι).total ≤ 12 * g ^ 3 * lam + 11 * g ^ 4 * lam + 24 * g ^ 4 := by
  have hr : (rowNet T ι).total = 2 * ((pairs g).card * (g * lam)) +
      2 * ∑ r ∈ rects g, cRow lam (ιf ι r) := by
    rw [Net.total_eq]
    simp only [rowNet_c, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, rects, Finset.sum_product]
    ring
  have hc : (colNet T ι).total = 2 * ((pairs g).card * (g * lam)) +
      2 * ∑ r ∈ rects g, cCol lam (ιf ι r) := by
    rw [Net.total_eq]
    simp only [colNet_c, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, rects,
      Finset.sum_product_right]
    ring
  have hpieces : 12 * ∑ r ∈ rects g, (cRow lam (ιf ι r) + cCol lam (ιf ι r)) ≤
      (rects g).card * (4 * (11 * lam + 24)) := by
    rw [Finset.mul_sum]
    refine (Finset.sum_le_card_nsmul (rects g) _ (4 * (11 * lam + 24)) fun r _ => ?_).trans
      (le_of_eq (smul_eq_mul _ _))
    have := cRow_add_cCol lam (ιf ι r) (ιf_le ι r)
    omega
  have hR : (rects g).card = (pairs g).card * (pairs g).card := by simp [rects]
  have hp := card_pairs g
  have hmin : 2 * min (rowNet T ι).total (colNet T ι).total ≤ (rowNet T ι).total + (colNet T ι).total := by
    omega
  rw [Finset.sum_add_distrib] at hpieces
  -- 4|R| = (g(g−1))² ≤ g⁴ and 2|pairs| g = g²(g−1) ≤ g³
  have h4R : 4 * (rects g).card ≤ g ^ 4 := by
    rw [hR]
    have : 4 * ((pairs g).card * (pairs g).card) = (g * (g - 1)) * (g * (g - 1)) := by rw [← hp]; ring
    rw [this]
    have : g * (g - 1) ≤ g * g := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    calc g * (g - 1) * (g * (g - 1)) ≤ (g * g) * (g * g) := Nat.mul_le_mul this this
      _ = g ^ 4 := by ring
  have h2p : 2 * (pairs g).card * g ≤ g ^ 3 := by
    rw [hp]
    have : g * (g - 1) ≤ g * g := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    calc g * (g - 1) * g ≤ g * g * g := Nat.mul_le_mul_right _ this
      _ = g ^ 3 := by ring
  have h5 : (rects g).card * (4 * (11 * lam + 24)) ≤ g ^ 4 * (11 * lam + 24) := by
    calc (rects g).card * (4 * (11 * lam + 24)) = 4 * (rects g).card * (11 * lam + 24) := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ h4R
  have h6 : 12 * (2 * ((pairs g).card * (g * lam))) ≤ 12 * g ^ 3 * lam := by
    calc 12 * (2 * ((pairs g).card * (g * lam))) = 12 * (2 * (pairs g).card * g) * lam := by ring
      _ ≤ 12 * g ^ 3 * lam := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h2p)
  nlinarith

/-! ### From a clique on `Fin (g*g)` to the grid -/

/-- Grid points numbered row by row. -/
def gidx (g : ℕ) : Pt g ≃ Fin (g * g) := finProdFinEquiv

theorem gidx_lt {w w' : Pt g} : gidx g w < gidx g w' ↔ w.1 < w'.1 ∨ (w.1 = w'.1 ∧ w.2 < w'.2) := by
  rcases w with ⟨⟨a, ha⟩, ⟨j, hj⟩⟩
  rcases w' with ⟨⟨a', ha'⟩, ⟨j', hj'⟩⟩
  simp only [gidx, Fin.lt_def, finProdFinEquiv, Equiv.coe_fn_mk, Fin.mk.injEq]
  constructor
  · intro h
    rcases lt_trichotomy a a' with h1 | h1 | h1
    · exact Or.inl h1
    · subst h1; exact Or.inr ⟨rfl, by omega⟩
    · exfalso
      have h2 : g * (a' + 1) ≤ g * a := Nat.mul_le_mul_left g h1
      rw [Nat.mul_succ] at h2
      omega
  · rintro (h1 | ⟨rfl, h1⟩)
    · have h2 : g * (a + 1) ≤ g * a' := Nat.mul_le_mul_left g h1
      rw [Nat.mul_succ] at h2
      omega
    · omega

/-- The pairs of the clique on `Fin (g*g)` are the straight edges and the two diagonals of every rectangle. -/
theorem prod_pairs_grid {M : Type*} [CommMonoid M] (f : Pt g → Pt g → M) :
    ∏ q ∈ pairs (g * g), f ((gidx g).symm q.1) ((gidx g).symm q.2) =
      (∏ a, ∏ q ∈ pairs g, f (a, q.1) (a, q.2)) * (∏ p ∈ pairs g, ∏ j, f (p.1, j) (p.2, j)) *
        ∏ r ∈ rects g, (f (r.1.1, r.2.1) (r.1.2, r.2.2) * f (r.1.1, r.2.2) (r.1.2, r.2.1)) := by
  -- pairs of `Fin (g*g)` = pairs of grid points in row-major order
  have h1 : ∏ q ∈ pairs (g * g), f ((gidx g).symm q.1) ((gidx g).symm q.2) =
      ∏ p ∈ univ.filter (fun p : Pt g × Pt g => gidx g p.1 < gidx g p.2), f p.1 p.2 := by
    refine Finset.prod_nbij' (fun q => ((gidx g).symm q.1, (gidx g).symm q.2)) (fun p => (gidx g p.1, gidx g p.2)) ?_ ?_ ?_ ?_ ?_
    · intro q hq; simpa [pairs] using hq
    · intro p hp; simpa [pairs] using hp
    · intro q _; simp
    · intro p _; simp
    · intro q _; rfl
  rw [h1, Finset.prod_filter]
  -- four disjoint kinds
  have hsplit : ∀ p : Pt g × Pt g, (if gidx g p.1 < gidx g p.2 then f p.1 p.2 else 1) =
      (if p.1.1 = p.2.1 ∧ p.1.2 < p.2.2 then f p.1 p.2 else 1) *
      (if p.1.1 < p.2.1 ∧ p.1.2 = p.2.2 then f p.1 p.2 else 1) *
      (if p.1.1 < p.2.1 ∧ p.1.2 < p.2.2 then f p.1 p.2 else 1) *
      (if p.1.1 < p.2.1 ∧ p.2.2 < p.1.2 then f p.1 p.2 else 1) := by
    intro p
    simp only [gidx_lt]
    split_ifs <;> (try simp) <;> omega
  simp only [hsplit, Finset.prod_mul_distrib]
  -- each kind
  have k1 : ∏ p : Pt g × Pt g, (if p.1.1 = p.2.1 ∧ p.1.2 < p.2.2 then f p.1 p.2 else 1) =
      ∏ a, ∏ q ∈ pairs g, f (a, q.1) (a, q.2) := by
    rw [← Finset.prod_filter, ← Finset.prod_product']
    refine Finset.prod_nbij' (fun p => (p.1.1, (p.1.2, p.2.2))) (fun x => ((x.1, x.2.1), (x.1, x.2.2)))
      ?_ ?_ ?_ ?_ ?_
    · intro p hp; simp only [Finset.mem_filter, mem_univ, true_and] at hp; simpa [pairs] using hp.2
    · intro x hx; simp only [Finset.mem_product, mem_univ, true_and] at hx; simpa [pairs] using hx
    · intro p hp; simp only [Finset.mem_filter, mem_univ, true_and] at hp
      obtain ⟨⟨a, j⟩, ⟨a', j'⟩⟩ := p; simp only at hp ⊢; rw [hp.1]
    · intro x _; rfl
    · intro p hp; simp only [Finset.mem_filter, mem_univ, true_and] at hp
      obtain ⟨⟨a, j⟩, ⟨a', j'⟩⟩ := p; simp only at hp ⊢; rw [hp.1]
  have k2 : ∏ p : Pt g × Pt g, (if p.1.1 < p.2.1 ∧ p.1.2 = p.2.2 then f p.1 p.2 else 1) =
      ∏ p ∈ pairs g, ∏ j, f (p.1, j) (p.2, j) := by
    rw [← Finset.prod_filter, ← Finset.prod_product']
    refine Finset.prod_nbij' (fun p => ((p.1.1, p.2.1), p.1.2)) (fun x => ((x.1.1, x.2), (x.1.2, x.2)))
      ?_ ?_ ?_ ?_ ?_
    · intro p hp; simp only [Finset.mem_filter, mem_univ, true_and] at hp; simpa [pairs] using hp.1
    · intro x hx; simp only [Finset.mem_product, mem_univ, and_true] at hx; simpa [pairs] using hx
    · intro p hp; simp only [Finset.mem_filter, mem_univ, true_and] at hp
      obtain ⟨⟨a, j⟩, ⟨a', j'⟩⟩ := p; simp only at hp ⊢; rw [hp.2]
    · intro x _; rfl
    · intro p hp; simp only [Finset.mem_filter, mem_univ, true_and] at hp
      obtain ⟨⟨a, j⟩, ⟨a', j'⟩⟩ := p; simp only at hp ⊢; rw [hp.2]
  have k3 : ∏ p : Pt g × Pt g, (if p.1.1 < p.2.1 ∧ p.1.2 < p.2.2 then f p.1 p.2 else 1) =
      ∏ r ∈ rects g, f (r.1.1, r.2.1) (r.1.2, r.2.2) := by
    rw [← Finset.prod_filter]
    refine Finset.prod_nbij' (fun p => ((p.1.1, p.2.1), (p.1.2, p.2.2)))
      (fun r => ((r.1.1, r.2.1), (r.1.2, r.2.2))) ?_ ?_ ?_ ?_ ?_
    · intro p hp; simp only [Finset.mem_filter, mem_univ, true_and] at hp; simpa [rects, pairs] using hp
    · intro r hr; simp only [rects, Finset.mem_product, mem_pairs] at hr; simpa using hr
    · intro p _; rfl
    · intro r _; rfl
    · intro p _; rfl
  have k4 : ∏ p : Pt g × Pt g, (if p.1.1 < p.2.1 ∧ p.2.2 < p.1.2 then f p.1 p.2 else 1) =
      ∏ r ∈ rects g, f (r.1.1, r.2.2) (r.1.2, r.2.1) := by
    rw [← Finset.prod_filter]
    refine Finset.prod_nbij' (fun p => ((p.1.1, p.2.1), (p.2.2, p.1.2)))
      (fun r => ((r.1.1, r.2.2), (r.1.2, r.2.1))) ?_ ?_ ?_ ?_ ?_
    · intro p hp; simp only [Finset.mem_filter, mem_univ, true_and] at hp; simpa [rects, pairs] using hp
    · intro r hr; simp only [rects, Finset.mem_product, mem_pairs] at hr; simpa using hr
    · intro p _; rfl
    · intro r _; rfl
    · intro p _; rfl
  rw [k1, k2, k3, k4, mul_assoc]

/-- The grid clique of a clique on `Fin (g*g)`. -/
def toGrid (T : Clique R (g * g) lam) : GridClique R g lam :=
  fun w Θ => T (gidx g w) (fun γ => Θ ((gidx g).symm γ))

/-- Relabelling the nodes as grid points keeps the value. -/
theorem value_toGrid (T : Clique R (g * g) lam) : T.value = gridZ (toGrid T) := by
  unfold Clique.value gridZ
  let Φ : (Pt g → Pt g → Bits lam) ≃ (Fin (g * g) → Fin (g * g) → Bits lam) :=
    (gidx g).arrowCongr ((gidx g).arrowCongr (Equiv.refl _))
  rw [← Φ.sum_comp]
  refine Finset.sum_congr rfl fun Θ _ => ?_
  have hd : (∏ γ, if Φ Θ γ γ = zeroBits lam then T γ (Φ Θ γ) else 0) = diagW (toGrid T) Θ := by
    unfold diagW toGrid
    rw [← (gidx g).prod_comp]
    refine Finset.prod_congr rfl fun w _ => ?_
    simp only [Φ, Equiv.arrowCongr_apply, Function.comp_def, Equiv.symm_apply_apply, Equiv.refl_apply]
    rfl
  have hp := prod_pairs_grid (g := g) (M := R) (fun w w' => if Θ w w' = Θ w' w then (1 : R) else 0)
  have hp' : ∏ q ∈ pairs (g * g), (if Φ Θ q.1 q.2 = Φ Θ q.2 q.1 then (1 : R) else 0) =
      ∏ q ∈ pairs (g * g), (fun w w' => if Θ w w' = Θ w' w then (1 : R) else 0)
        ((gidx g).symm q.1) ((gidx g).symm q.2) := by
    refine Finset.prod_congr rfl fun q _ => ?_
    simp only [Φ, Equiv.arrowCongr_apply, Function.comp_def, Equiv.refl_apply]
  rw [hd, hp', hp]
  simp only [horizP, vertP, eqI]
  ring

/-- **Proposition 3, the value**: for a `(g², λ)`-clique `T`, `2^(t|R|) Z` is the sum over the choices `ι` of the
values of the row networks, and also of the column networks; each fits `P = g³λ`, and the smaller total obeys (36). -/
theorem level_value (T : Clique R (g * g) lam) :
    (2 : R) ^ (tB lam * (rects g).card) * T.value = ∑ ι : Choice g lam, (rowNet (toGrid T) ι).value ∧
    (2 : R) ^ (tB lam * (rects g).card) * T.value = ∑ ι : Choice g lam, (colNet (toGrid T) ι).value := by
  rw [value_toGrid, sum_Zι]
  exact ⟨Finset.sum_congr rfl fun ι _ => (value_rowNet _ ι).symm,
    Finset.sum_congr rfl fun ι _ => (value_colNet _ ι).symm⟩

end Factoring.Aux
