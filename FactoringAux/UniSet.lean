/-
Setting the literal variables.

* `setBlock p es`: the `Cmd` writing the values of the expressions `es` into the scalars `p, p+1, …` (each compiled by
  `Ex.comp _ _ 1000`). **`setBlock_spec`**: if every expression's value is fixed by the scalar `q` (outside the block),
  the block holds the values, every other scalar below `1000` and every array is kept, and the cost is at most
  `length · (C + 2) + 1` for a per-expression cost bound `C`.
* `GEx q` (`3 K^8` for `K` in `q`), `lvlExs q`, **`lvlSet p q := setBlock p (lvlExs q)`**; **`lvlSet_spec`**: with `K` in
  scalar `q`, the block `p … p+11` holds `lvlVals K (3 K^8)` (so every literal variable of `lvlOk p K (3 K^8)` holds its
  literal), the other scalars below `1000` and the arrays are kept, and the cost is at most
  `12 · ((64 (V+1)^3)^5 + 2) + 1` for `V = lvlV K = (K+2)^(3K^8+50)`.

Values are bounded with `Bdd` and the cost with `cost_le_of_Bdd` (`EngineBound.lean`).

Not an audit surface.
-/
module

public import FactoringAux.UniLevelV

@[expose] public section

namespace Factoring.Aux

open Ex Finset Factoring.Aux.Copied Factoring.Aux.Copied.PLib

/-! ### Writing a list of values -/

/-- Writes the value of the `i`-th expression into scalar `p + i` (scratch from `1000`). -/
def setBlock : ℕ → List Ex → Cmd
  | _, [] => .skip
  | p, e :: es => .seq (Ex.comp e p 1000) (setBlock (p + 1) es)

/-- **The block holds the values**, the rest is kept, at a cost linear in the number of values. -/
theorem setBlock_spec (q K C : ℕ) : ∀ (es : List Ex) (vs : List ℕ) (p : ℕ) (st : St),
    es.length = vs.length → p + es.length ≤ 1000 → (q < p ∨ p + es.length ≤ q) → q < 1000 → st.sc q = K →
    (∀ i (hi : i < es.length) (hi' : i < vs.length), VB 1000 es[i] ∧ ∀ (σ : ℕ → ℕ) (A : ℕ → ℕ → ℕ), σ q = K →
        eval σ A es[i] = vs[i] ∧ cost σ A es[i] ≤ C) →
    (∀ i (hi : i < vs.length), (Cmd.run (setBlock p es) st).1.sc (p + i) = vs[i]) ∧
      (∀ y < 1000, (y < p ∨ p + es.length ≤ y) → (Cmd.run (setBlock p es) st).1.sc y = st.sc y) ∧
      (Cmd.run (setBlock p es) st).1.ar = st.ar ∧ (Cmd.run (setBlock p es) st).2 ≤ es.length * (C + 2) + 1
  | [], vs, p, st, hl, _, _, _, _, _ => by
      have : vs = [] := List.eq_nil_of_length_eq_zero hl.symm
      subst this
      exact ⟨fun i hi => absurd hi (by simp), fun _ _ _ => rfl, rfl, by simp [setBlock, Cmd.run_skip]⟩
  | e :: es, vs, p, st, hl, hp, hq, hq1, hK, h => by
      obtain ⟨v, vs', rfl⟩ : ∃ v vs', vs = v :: vs' := by
        cases vs with
        | nil => simp at hl
        | cons v vs' => exact ⟨v, vs', rfl⟩
      simp only [List.length_cons, add_left_inj] at hl hp hq ⊢
      obtain ⟨hvb, hev⟩ := h 0 (by simp) (by simp)
      simp only [List.getElem_cons_zero] at hvb hev
      have w := comp_spec e p 1000 st hvb (by omega)
      obtain ⟨w1, w2, w3, w4⟩ := w
      set st1 := (Cmd.run (Ex.comp e p 1000) st).1
      have hK1 : st1.sc q = K := by rw [w2 q hq1 (by omega), hK]
      have ih := setBlock_spec q K C es vs' (p + 1) st1 hl (by omega) (by omega) hq1 hK1
        (fun i hi hi' => by
          have := h (i + 1) (by simp; omega) (by simp; omega)
          simpa only [List.getElem_cons_succ] using this)
      obtain ⟨i1, i2, i3, i4⟩ := ih
      have hv : st1.sc p = v := by rw [w1, (hev st.sc st.ar hK).1]
      simp only [setBlock, Cmd.run_seq]
      refine ⟨fun i hi => ?_, fun y hy hy' => ?_, by rw [i3, w3], ?_⟩
      · rcases i with _ | i
        · simp only [add_zero, List.getElem_cons_zero]
          rw [i2 p (by omega) (by omega), hv]
        · simp only [List.getElem_cons_succ]
          rw [show p + (i + 1) = p + 1 + i by omega]
          exact i1 i (by simp at hi; omega)
      · rw [i2 y hy (by omega), w2 y hy (by omega)]
      · have hc := (hev st.sc st.ar hK).2
        have : (Cmd.run (Ex.comp e p 1000) st).2 ≤ C := w4.trans hc
        nlinarith

/-! ### Value bounds -/

section Bdd

variable {V : ℕ} {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ}

theorem pow_le_of_le {c N V : ℕ} (h : c ^ N ≤ V) (h1 : 1 ≤ V) : ∀ j ≤ N, c ^ j ≤ V := by
  intro j hj
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · rcases Nat.eq_zero_or_pos j with rfl | hj0
    · simpa using h1
    · rw [zero_pow (by omega)]; omega
  · exact (Nat.pow_le_pow_right hc hj).trans h

/-- A product of a constant. -/
theorem eval_nprod_const {x : ℕ} {n b : Ex} {c : ℕ} (hc : ∀ j, eval (Function.update σ x j) A b = c) :
    eval σ A (nprod x n b) = c ^ eval σ A n := by
  rw [eval_nprod, pp_congr (f' := fun _ => c) (fun i _ => hc i), pp_const]

theorem bdd_nprod_const {x : ℕ} {n b : Ex} {c : ℕ} (hn : Bdd V σ A n) (hb : ∀ j, Bdd V (Function.update σ x j) A b)
    (hc : ∀ j, eval (Function.update σ x j) A b = c) (hV : ∀ j ≤ eval σ A n, c ^ j ≤ V) :
    Bdd V σ A (nprod x n b) := by
  refine ⟨hn, Nat.zero_le _, fun j _ => hb j, fun j hj => ?_⟩
  show foldProd _ 0 j ≤ V
  rw [foldProd_zero, pp_congr (f' := fun _ => c) (fun i _ => hc i), pp_const]
  exact hV j hj

end Bdd

/-! ### The level's values from `K` -/

/-- `3 K^8` for `K` in scalar `q` (product variable `999`). -/
def GEx (q : ℕ) : Ex := .mul (.lit 3) (nprod 999 (.lit 8) (.var q))

/-- The expressions of `lvlVals K (3 K^8)` from `K` in scalar `q`. -/
def lvlExs (q : ℕ) : List Ex :=
  [.var q, GEx q, .mul (GEx q) (GEx q), .mul (GEx q) (.mul (GEx q) (GEx q)), .add (.mul (.lit 2) (GEx q)) (.lit 1),
    nprod 999 (GEx q) (.var q), .mul (.lit 12) (nprod 999 (.lit 3) (GEx q)), .mul (.lit 11) (nprod 999 (.lit 4) (GEx q)),
    .mul (.lit 24) (nprod 999 (.lit 4) (GEx q)), .mul (GEx q) (nprod 999 (.lit 3) (GEx q)), nprod 999 (.lit 3) (.var q),
    .mul (.mul (GEx q) (GEx q)) (.mul (GEx q) (GEx q))]

/-- **Sets the level's literal variables `p … p+11`** from `K` in scalar `q`. -/
def lvlSet (p q : ℕ) : Cmd := setBlock p (lvlExs q)

/-- The value bound of `lvlSet`. -/
def lvlV (K : ℕ) : ℕ := (K + 2) ^ (3 * K ^ 8 + 50)

section Vals

variable {q K : ℕ} {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ}

theorem upd_q (hq : q ≠ 999) (hσ : σ q = K) (j : ℕ) : Function.update σ 999 j q = K := by
  rw [Function.update_of_ne hq, hσ]

theorem eval_GEx (hq : q ≠ 999) (hσ : σ q = K) : eval σ A (GEx q) = 3 * K ^ 8 := by
  simp only [GEx, eval]
  rw [eval_nprod_const (c := K) (fun j => by simp only [eval]; exact upd_q hq hσ j)]
  rfl

/-- The facts on `V` used by the value bounds. -/
structure VFacts (K V : ℕ) : Prop where
  pK : ∀ j ≤ 3 * K ^ 8 + 50, K ^ j ≤ V
  pG : 24 * (3 * K ^ 8 + 1) ^ 4 ≤ V

theorem VFacts.one {K V : ℕ} (h : VFacts K V) : 1 ≤ V := by have := h.pK 0 (by omega); simpa using this

theorem VFacts.cG {K V : ℕ} (h : VFacts K V) {c k : ℕ} (hc : c ≤ 24) (hk : k ≤ 4) : c * (3 * K ^ 8) ^ k ≤ V := by
  refine le_trans ?_ h.pG
  have h1 : (3 * K ^ 8) ^ k ≤ (3 * K ^ 8 + 1) ^ 4 :=
    (Nat.pow_le_pow_left (by omega) k).trans (Nat.pow_le_pow_right (by omega) hk)
  exact Nat.mul_le_mul hc h1

theorem lvlV_facts (K : ℕ) : VFacts K (lvlV K) where
  pK j hj := (Nat.pow_le_pow_left (by omega) j).trans (Nat.pow_le_pow_right (by omega) hj)
  pG := by
    unfold lvlV
    have h2 : 2 ≤ K + 2 := by omega
    have hG : 3 * K ^ 8 + 1 ≤ (K + 2) ^ 10 := by
      have a : K ^ 8 ≤ (K + 2) ^ 8 := Nat.pow_le_pow_left (by omega) 8
      have b : 4 ≤ (K + 2) ^ 2 := by nlinarith
      have c : 1 ≤ (K + 2) ^ 8 := Nat.one_le_pow _ _ (by omega)
      have : (K + 2) ^ 10 = (K + 2) ^ 2 * (K + 2) ^ 8 := by ring
      nlinarith
    have h24 : 24 ≤ (K + 2) ^ 5 := le_trans (by norm_num) (Nat.pow_le_pow_left h2 5)
    calc 24 * (3 * K ^ 8 + 1) ^ 4 ≤ (K + 2) ^ 5 * ((K + 2) ^ 10) ^ 4 :=
          Nat.mul_le_mul h24 (Nat.pow_le_pow_left hG 4)
      _ = (K + 2) ^ 45 := by ring
      _ ≤ (K + 2) ^ (3 * K ^ 8 + 50) := Nat.pow_le_pow_right (by omega) (by omega)

variable {V : ℕ}

theorem bdd_GEx (hV : VFacts K V) (hq : q ≠ 999) (hσ : σ q = K) : Bdd V σ A (GEx q) := by
  have l : ∀ c ≤ 24, c ≤ V := fun c hc => by simpa using hV.cG (c := c) (k := 0) hc (by omega)
  have hK1 : K ≤ V := by simpa using hV.pK 1 (by omega)
  have hn : Bdd V σ A (nprod 999 (.lit 8) (.var q)) :=
    bdd_nprod_const (c := K) (l 8 (by omega)) (fun j => by show _ ≤ V; rw [upd_q hq hσ j]; exact hK1)
      (fun j => by simp only [eval]; exact upd_q hq hσ j) (fun j hj => hV.pK j (by simp only [eval] at hj; omega))
  refine ⟨l 3 (by omega), hn, ?_⟩
  show 3 * eval σ A (nprod 999 (.lit 8) (.var q)) ≤ V
  rw [eval_nprod_const (c := K) (fun j => by simp only [eval]; exact upd_q hq hσ j)]
  simp only [eval]
  simpa using hV.cG (c := 1) (k := 1) (by omega) (by omega)

/-- Products of constants `G = 3 K^8`. -/
theorem bdd_nprodG (hV : VFacts K V) (hq : q ≠ 999) (hσ : σ q = K) (k : ℕ) (hk : k ≤ 4) :
    Bdd V σ A (nprod 999 (.lit k) (GEx q)) :=
  bdd_nprod_const (c := 3 * K ^ 8) (show k ≤ V by simpa using hV.cG (c := k) (k := 0) (by omega) (by omega))
    (fun j => bdd_GEx hV hq (upd_q hq hσ j)) (fun j => eval_GEx hq (upd_q hq hσ j))
    (fun j hj => by simpa using hV.cG (c := 1) (k := j) (by omega) (by simp only [eval] at hj; omega))

theorem eval_nprodG (hq : q ≠ 999) (hσ : σ q = K) (k : ℕ) :
    eval σ A (nprod 999 (.lit k) (GEx q)) = (3 * K ^ 8) ^ k := by
  rw [eval_nprod_const (c := 3 * K ^ 8) (fun j => eval_GEx hq (upd_q hq hσ j))]; rfl

theorem eval_nprodVq (hq : q ≠ 999) (hσ : σ q = K) (n : Ex) :
    eval σ A (nprod 999 n (.var q)) = K ^ eval σ A n :=
  eval_nprod_const (c := K) (fun j => by simp only [eval]; exact upd_q hq hσ j)

end Vals

/-- The value and the value bound of each of `lvlExs`. -/
theorem lvlExs_spec {q K V : ℕ} (hV : VFacts K V) (hq : q ≠ 999) :
    ∀ i (hi : i < (lvlExs q).length) (hi' : i < (lvlVals K (3 * K ^ 8)).length) (σ : ℕ → ℕ) (A : ℕ → ℕ → ℕ),
      σ q = K → eval σ A (lvlExs q)[i] = (lvlVals K (3 * K ^ 8))[i] ∧ Bdd V σ A (lvlExs q)[i] := by
  intro i hi _ σ A hσ
  have eG := eval_GEx (A := A) hq hσ
  have bG := bdd_GEx (A := A) hV hq hσ
  have l : ∀ c ≤ 24, c ≤ V := fun c hc => by simpa using hV.cG (c := c) (k := 0) hc (by omega)
  have hK1 : K ≤ V := by simpa using hV.pK 1 (by omega)
  have bq : ∀ j, Bdd V (Function.update σ 999 j) A (.var q) := fun j => by
    show _ ≤ V; rw [upd_q hq hσ j]; exact hK1
  have eq' : ∀ j, eval (Function.update σ 999 j) A (.var q) = K := fun j => by
    simp only [eval]; exact upd_q hq hσ j
  have c2 := hV.cG (c := 1) (k := 2) (by omega) (by omega)
  have c3 := hV.cG (c := 1) (k := 3) (by omega) (by omega)
  have c4 := hV.cG (c := 1) (k := 4) (by omega) (by omega)
  have g3 := hV.cG (c := 3) (k := 1) (by omega) (by omega)
  simp only [one_mul, pow_one] at c2 c3 c4 g3
  have one := hV.one
  set G := 3 * K ^ 8 with hG
  have sq : G * G = G ^ 2 := by ring
  have cu : G * (G * G) = G ^ 3 := by ring
  have qu : G * G * (G * G) = G ^ 4 := by ring
  have qu' : G * G ^ 3 = G ^ 4 := by ring
  have bGG : Bdd V σ A (.mul (GEx q) (GEx q)) :=
    ⟨bG, bG, by show eval σ A (GEx q) * eval σ A (GEx q) ≤ V; rw [eG, sq]; exact c2⟩
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | i
  · exact ⟨hσ, by show σ q ≤ V; rw [hσ]; exact hK1⟩
  · exact ⟨eG, bG⟩
  · exact ⟨by show eval σ A (GEx q) * eval σ A (GEx q) = _; rw [eG]; rfl, bGG⟩
  · refine ⟨by show eval σ A (GEx q) * (eval σ A (GEx q) * eval σ A (GEx q)) = _; rw [eG]; rfl, bG, bGG, ?_⟩
    show eval σ A (GEx q) * (eval σ A (GEx q) * eval σ A (GEx q)) ≤ V; rw [eG, cu]; exact c3
  · refine ⟨by show 2 * eval σ A (GEx q) + 1 = _; rw [eG]; rfl, ⟨l 2 (by omega), bG, ?_⟩, l 1 (by omega), ?_⟩
    · show 2 * eval σ A (GEx q) ≤ V; rw [eG]; omega
    · show 2 * eval σ A (GEx q) + 1 ≤ V; rw [eG]; omega
  · refine ⟨by show eval σ A (nprod 999 (GEx q) (.var q)) = _; rw [eval_nprodVq hq hσ, eG]; rfl,
      bdd_nprod_const (c := K) bG bq eq' (fun j hj => hV.pK j (by rw [eG] at hj; omega))⟩
  · refine ⟨by show 12 * eval σ A (nprod 999 (.lit 3) (GEx q)) = _; rw [eval_nprodG hq hσ]; rfl,
      l 12 (by omega), bdd_nprodG hV hq hσ 3 (by omega), ?_⟩
    show 12 * eval σ A (nprod 999 (.lit 3) (GEx q)) ≤ V; rw [eval_nprodG hq hσ]; exact hV.cG (by omega) (by omega)
  · refine ⟨by show 11 * eval σ A (nprod 999 (.lit 4) (GEx q)) = _; rw [eval_nprodG hq hσ]; rfl,
      l 11 (by omega), bdd_nprodG hV hq hσ 4 (by omega), ?_⟩
    show 11 * eval σ A (nprod 999 (.lit 4) (GEx q)) ≤ V; rw [eval_nprodG hq hσ]; exact hV.cG (by omega) (by omega)
  · refine ⟨by show 24 * eval σ A (nprod 999 (.lit 4) (GEx q)) = _; rw [eval_nprodG hq hσ]; rfl,
      l 24 (by omega), bdd_nprodG hV hq hσ 4 (by omega), ?_⟩
    show 24 * eval σ A (nprod 999 (.lit 4) (GEx q)) ≤ V; rw [eval_nprodG hq hσ]; exact hV.cG (by omega) (by omega)
  · refine ⟨by show eval σ A (GEx q) * eval σ A (nprod 999 (.lit 3) (GEx q)) = _; rw [eval_nprodG hq hσ, eG]; rfl,
      bG, bdd_nprodG hV hq hσ 3 (by omega), ?_⟩
    show eval σ A (GEx q) * eval σ A (nprod 999 (.lit 3) (GEx q)) ≤ V; rw [eval_nprodG hq hσ, eG, qu']; exact c4
  · refine ⟨by show eval σ A (nprod 999 (.lit 3) (.var q)) = _; rw [eval_nprodVq hq hσ]; rfl,
      bdd_nprod_const (c := K) (l 3 (by omega)) bq eq' (fun j hj => hV.pK j (by simp only [eval] at hj; omega))⟩
  · refine ⟨by
      show eval σ A (GEx q) * eval σ A (GEx q) * (eval σ A (GEx q) * eval σ A (GEx q)) = _; rw [eG]; rfl,
      bGG, bGG, ?_⟩
    show eval σ A (GEx q) * eval σ A (GEx q) * (eval σ A (GEx q) * eval σ A (GEx q)) ≤ V; rw [eG, qu]; exact c4
  · exact absurd hi (by simp [lvlExs])

theorem lvlExs_vb (q : ℕ) (hq : q < 999) : ∀ e ∈ lvlExs q, VB 1000 e := by
  intro e he
  simp only [lvlExs, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [GEx, nprod, VB, and_true, true_and, and_self] <;> omega

theorem lvlExs_dp (q : ℕ) : ∀ e ∈ lvlExs q, Ex.dp e ≤ 5 := by
  intro e he
  simp only [lvlExs, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [GEx, nprod, Ex.dp]

/-- The cost of one expression with all values at most `V` and depth at most `5`. -/
theorem cost_le5 {V : ℕ} {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ} {e : Ex} (hb : Bdd V σ A e) (hd : Ex.dp e ≤ 5) :
    cost σ A e ≤ (64 * (V + 1) ^ 3) ^ 5 :=
  (cost_le_of_Bdd A e σ hb).trans (Nat.pow_le_pow_right (by have := Nat.one_le_pow 3 (V + 1) (by omega); omega) hd)

/-- **`lvlSet`**: with `K` in scalar `q` (outside the block, below `999`), the block `p … p+11` holds
`lvlVals K (3 K^8)`, every other scalar below `1000` and every array is kept, and the cost is at most
`12 · ((64 (lvlV K + 1)^3)^5 + 2) + 1`. -/
theorem lvlSet_spec {p q K : ℕ} (st : St) (hK : st.sc q = K) (hp : p + 12 ≤ 1000) (hq : q < p ∨ p + 12 ≤ q)
    (hq9 : q < 999) :
    (∀ i (hi : i < 12), (Cmd.run (lvlSet p q) st).1.sc (p + i) = (lvlVals K (3 * K ^ 8))[i]) ∧
      (∀ v k, lvlOk p K (3 * K ^ 8) v k → (Cmd.run (lvlSet p q) st).1.sc v = k) ∧
      (∀ y < 1000, (y < p ∨ p + 12 ≤ y) → (Cmd.run (lvlSet p q) st).1.sc y = st.sc y) ∧
      (Cmd.run (lvlSet p q) st).1.ar = st.ar ∧
      (Cmd.run (lvlSet p q) st).2 ≤ 12 * ((64 * (lvlV K + 1) ^ 3) ^ 5 + 2) + 1 := by
  have hV := lvlV_facts K
  have h := setBlock_spec q K ((64 * (lvlV K + 1) ^ 3) ^ 5) (lvlExs q) (lvlVals K (3 * K ^ 8)) p st rfl hp hq (by omega) hK
    (fun i hi hi' => ⟨lvlExs_vb q hq9 _ (List.getElem_mem hi), fun σ A hσ => by
      obtain ⟨e1, b1⟩ := lvlExs_spec hV (by omega) i hi hi' σ A hσ
      exact ⟨e1, cost_le5 b1 (lvlExs_dp q _ (List.getElem_mem hi))⟩⟩)
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨fun i hi => h1 i hi, blockOk_holds (fun i hi => h1 i hi), h2, h3, h4⟩

end Factoring.Aux
