/-
The uniform engine: writing a table into array `3` (memoisation).

A table with entries `i < n` is written at the cells `3 i + par` of array `3` (`par < 3`, the slot: the top table at slot `2`, the levels alternate
between slots `0` and `1`, so that a level can read the previous table while it writes its own).  Entry `i` is the value of an expression
`f` with `vγ := i % K`, `vΘ := i / K`; `f` may read array `3`, but only cells of the other slots (`AgP`).

* `AgP` (arrays equal except at the cells of slot `par` of array `3`), `fillC`, **`fill_spec`**;
* `cset` (`Ex.comp e d 1000`) and `cset_spec`.

Not an audit surface.
-/
module

public import FactoringAux.EngineGridEx

@[expose] public section

namespace Factoring.Aux

open Factoring.Aux.Copied Factoring.Aux.Copied.PLib Finset Ex

/-- `A'` equals `A` except at the cells of slot `par` of array `3`. -/
def AgP (A A' : ℕ → ℕ → ℕ) (par : ℕ) : Prop :=
  (∀ a, a ≠ 3 → A' a = A a) ∧ ∀ x, x % 3 ≠ par → A' 3 x = A 3 x

theorem AgP.refl (A : ℕ → ℕ → ℕ) (par : ℕ) : AgP A A par := ⟨fun _ _ => rfl, fun _ _ => rfl⟩

theorem AgP.trans {A A' A'' : ℕ → ℕ → ℕ} {par : ℕ} (h1 : AgP A A' par) (h2 : AgP A' A'' par) : AgP A A'' par :=
  ⟨fun a ha => (h2.1 a ha).trans (h1.1 a ha), fun x hx => (h2.2 x hx).trans (h1.2 x hx)⟩

/-- `e` into scalar `d`, scratch from `1000`. -/
def cset (e : Ex) (d : ℕ) : Cmd := Ex.comp e d 1000

theorem cset_spec (e : Ex) (d : ℕ) (st : St) (hv : VB 1000 e) (hd : d < 1000) :
    (Cmd.run (cset e d) st).1.sc d = eval st.sc st.ar e ∧
      (∀ y < 1000, y ≠ d → (Cmd.run (cset e d) st).1.sc y = st.sc y) ∧
      (Cmd.run (cset e d) st).1.ar = st.ar ∧ (Cmd.run (cset e d) st).2 ≤ cost st.sc st.ar e :=
  Ex.comp_spec e d 1000 st hv hd

/-- The entry expression of `fillC`. -/
def fillE (f : Ex) (vi vK vγ vΘ : ℕ) : Ex :=
  .lett vγ (.mod (.var vi) (.var vK)) (.lett vΘ (.div (.var vi) (.var vK)) f)

/-- The cell of entry `var vi`. -/
def cellE (vi vpar : ℕ) : Ex := .add (.mul (.lit 3) (.var vi)) (.var vpar)

/-- Write entries `i < var vn` (`f` at `vγ := i % K`, `vΘ := i / K`) into the cells `3 i + par` of array `3`.
Scratch scalars `990`, `991`. -/
def fillC (f : Ex) (vn vi vK vγ vΘ vpar : ℕ) : Cmd :=
  .loop vn vi (.seq (cset (fillE f vi vK vγ vΘ) 990) (.seq (cset (cellE vi vpar) 991) (.wr 3 991 0 990)))

/-- The environment of entry `i`. -/
def fillEnv (σ : ℕ → ℕ) (vi vK vγ vΘ i : ℕ) : ℕ → ℕ :=
  Function.update (Function.update (Function.update σ vi i) vγ (i % σ vK)) vΘ (i / σ vK)

/-- The array after the first `j` entries. -/
def filled (A : ℕ → ℕ → ℕ) (v : ℕ → ℕ) (par j : ℕ) : ℕ → ℕ → ℕ :=
  Function.update A 3 (fun x => if x % 3 = par ∧ x / 3 < j then v (x / 3) else A 3 x)

theorem filled_agP (A : ℕ → ℕ → ℕ) (v : ℕ → ℕ) (par j : ℕ) : AgP A (filled A v par j) par := by
  refine ⟨fun a ha => by simp [filled, ha], fun x hx => ?_⟩
  simp [filled, hx]

/-- The body of `fillC`. -/
def fillBody (f : Ex) (vi vK vγ vΘ vpar : ℕ) : Cmd :=
  .seq (cset (fillE f vi vK vγ vΘ) 990) (.seq (cset (cellE vi vpar) 991) (.wr 3 991 0 990))

/-- The invariant of `fillC` after `j` entries. -/
def FillInv (st : St) (v : ℕ → ℕ) (vi par j : ℕ) (s : St) : Prop :=
  s.ar = filled st.ar v par j ∧ ∀ y < 990, y ≠ vi → s.sc y = st.sc y

/-- One entry. -/
theorem fill_step (f : Ex) {vi vK vγ vΘ vpar : ℕ} (hvi : vi < 990) (hvK : vK < 990) (hvγ : vγ < 990)
    (hvΘ : vΘ < 990) (hvp : vpar < 990) (h1 : vi ≠ vK) (h2 : vi ≠ vpar) (h3 : vγ ≠ vi)
    (h4 : vγ ≠ vK) (hf : VB 990 f) (st : St) (hpar : st.sc vpar < 3) (v : ℕ → ℕ) (n : ℕ)
    (hval : ∀ i < n, ∀ A', AgP st.ar A' (st.sc vpar) → eval (fillEnv st.sc vi vK vγ vΘ i) A' f = v i)
    (j : ℕ) (s : St) (hj : j < n) (hs : FillInv st v vi (st.sc vpar) j s) :
    FillInv st v vi (st.sc vpar) (j + 1) (Cmd.run (fillBody f vi vK vγ vΘ vpar) (s.setSc vi j)).1 ∧
      AgP st.ar s.ar (st.sc vpar) ∧
      (Cmd.run (fillBody f vi vK vγ vΘ vpar) (s.setSc vi j)).2 ≤
        cost (fillEnv st.sc vi vK vγ vΘ j) s.ar f + 40 * n + 200 := by
    set par := st.sc vpar
    set body := fillBody f vi vK vγ vΘ vpar
    obtain ⟨hA, hS⟩ := hs
    set s1 := s.setSc vi j
    have vb1 : VB 1000 (fillE f vi vK vγ vΘ) :=
      ⟨by omega, ⟨by show vi < 1000; omega, by show vK < 1000; omega⟩, by omega,
        ⟨by show vi < 1000; omega, by show vK < 1000; omega⟩, VB_mono (by omega) f hf⟩
    obtain ⟨a1, a2, a3, a4⟩ := cset_spec (fillE f vi vK vγ vΘ) 990 s1 vb1 (by omega)
    have hK1 : s1.sc vK = st.sc vK := by
      simp only [s1, St.setSc_sc]; rw [Function.update_of_ne (Ne.symm h1)]; exact hS vK hvK (Ne.symm h1)
    have hi1 : s1.sc vi = j := by simp [s1]
    -- the entry's value and cost
    have hag : ∀ y < 990, Function.update (Function.update s1.sc vγ (j % st.sc vK)) vΘ (j / st.sc vK) y =
        fillEnv st.sc vi vK vγ vΘ j y := by
      intro y hy
      simp only [fillEnv, s1, St.setSc_sc]
      by_cases e1 : y = vΘ
      · subst e1; simp
      by_cases e2 : y = vγ
      · subst e2; simp [e1]
      by_cases e3 : y = vi
      · subst e3; simp [e1, e2]
      simp only [Function.update_of_ne e1, Function.update_of_ne e2, Function.update_of_ne e3]
      exact hS y hy e3
    have hAg : AgP st.ar s1.ar par := by
      rw [show s1.ar = s.ar from rfl, hA]; exact filled_agP _ _ _ _
    have hv1 := hval j hj s1.ar hAg
    have ev : eval s1.sc s1.ar (fillE f vi vK vγ vΘ) = v j ∧ cost s1.sc s1.ar (fillE f vi vK vγ vΘ) ≤
        cost (fillEnv st.sc vi vK vγ vΘ j) s1.ar f + 14 * j + 60 := by
      obtain ⟨c1, c2⟩ := Ex.congr s1.ar f _ _ hag hf
      have u1 : Function.update s1.sc vγ (j % st.sc vK) vi = j := by
        rw [Function.update_of_ne (Ne.symm h3), hi1]
      have u2 : Function.update s1.sc vγ (j % st.sc vK) vK = st.sc vK := by
        rw [Function.update_of_ne (Ne.symm h4), hK1]
      simp only [fillE, Ex.eval, Ex.cost, hi1, hK1, u1, u2]
      constructor
      · rw [c1, hv1]
      · rw [c2]; have : j / st.sc vK ≤ j := Nat.div_le_self _ _; omega
    -- the cell
    set s2 := (Cmd.run (cset (fillE f vi vK vγ vΘ) 990) s1).1
    have vb2 : VB 1000 (cellE vi vpar) := ⟨⟨trivial, by show vi < 1000; omega⟩, by show vpar < 1000; omega⟩
    obtain ⟨b1, b2, b3, b4⟩ := cset_spec (cellE vi vpar) 991 s2 vb2 (by omega)
    have s2i : s2.sc vi = j := by rw [a2 vi (by omega) (by omega), hi1]
    have s2p : s2.sc vpar = par := by
      rw [a2 vpar (by omega) (by omega)]; simp only [s1, St.setSc_sc]
      rw [Function.update_of_ne (Ne.symm h2)]; exact hS vpar hvp (Ne.symm h2)
    set s3 := (Cmd.run (cset (cellE vi vpar) 991) s2).1
    have hcell : s3.sc 991 = 3 * j + par := by rw [b1]; simp [cellE, Ex.eval, s2i, s2p]
    have hval3 : s3.sc 990 = v j := by rw [b2 990 (by omega) (by omega), a1, ev.1]
    have hcc : cost s2.sc s2.ar (cellE vi vpar) ≤ 12 * j + 2 * par + 40 := by
      simp only [cellE, Ex.cost, Ex.eval, s2i, s2p]; omega
    simp only [body, fillBody, Cmd.run_seq, Cmd.run_wr]
    refine ⟨⟨?_, fun y hy hyi => ?_⟩, hAg, ?_⟩
    · rw [St.setAr_ar, b3, a3, show s1.ar = s.ar from rfl, hA, hcell, hval3]
      funext a x
      simp only [filled, Function.update_apply]
      by_cases ha : a = 3
      · subst ha
        simp only [if_true, add_zero]
        by_cases hx : x = 3 * j + par
        · subst hx
          have e1 : (3 * j + par) % 3 = par := by omega
          have e2 : (3 * j + par) / 3 = j := by omega
          simp [e1, e2]
        · rw [Function.update_of_ne hx]
          by_cases hxp : x % 3 = par
          · have : x / 3 < j + 1 ↔ x / 3 < j := by omega
            simp only [hxp, true_and, this]
          · simp [hxp]
      · simp [ha]
    · simp only [St.setAr_sc]
      rw [b2 y (by omega) (by omega), a2 y (by omega) (by omega)]
      simp only [s1, St.setSc_sc, Function.update_apply, if_neg hyi]
      exact hS y hy hyi
    · have hpar' : par ≤ 2 := by omega
      have hjn : j ≤ n := hj.le
      have e4 : (Cmd.run (cset (fillE f vi vK vγ vΘ) 990) s1).2 ≤
          cost (fillEnv st.sc vi vK vγ vΘ j) s.ar f + 14 * j + 60 := le_trans a4 ev.2
      have e5 := le_trans b4 hcc
      change (Cmd.run (cset (fillE f vi vK vγ vΘ) 990) s1).2 + ((Cmd.run (cset (cellE vi vpar) 991) s2).2 + 1 + 1)
        + 1 ≤ _
      omega
theorem fillInv_zero (st : St) (v : ℕ → ℕ) (vi par : ℕ) : FillInv st v vi par 0 st := ⟨by
    funext a x
    simp only [filled, Function.update_apply]
    split_ifs with ha
    · subst ha; simp
    · rfl, fun _ _ _ => rfl⟩

/-- **Writing a table**: the values. -/
theorem fill_val (f : Ex) {vn vi vK vγ vΘ vpar : ℕ} (hvi : vi < 990) (hvK : vK < 990) (hvγ : vγ < 990)
    (hvΘ : vΘ < 990) (hvp : vpar < 990) (h1 : vi ≠ vK) (h2 : vi ≠ vpar) (h3 : vγ ≠ vi)
    (h4 : vγ ≠ vK) (hf : VB 990 f) (st : St) (hpar : st.sc vpar < 3) (v : ℕ → ℕ)
    (hval : ∀ i < st.sc vn, ∀ A', AgP st.ar A' (st.sc vpar) → eval (fillEnv st.sc vi vK vγ vΘ i) A' f = v i) :
    (Cmd.run (fillC f vn vi vK vγ vΘ vpar) st).1.ar = filled st.ar v (st.sc vpar) (st.sc vn) ∧
      (∀ y < 990, y ≠ vi → (Cmd.run (fillC f vn vi vK vγ vΘ vpar) st).1.sc y = st.sc y) :=
  Cmd.loop_inv (b := vn) (c := vi) (body := fillBody f vi vK vγ vΘ vpar) (FillInv st v vi (st.sc vpar))
    (fillInv_zero st v vi _) (fun j s hj hs =>
      (fill_step f hvi hvK hvγ hvΘ hvp h1 h2 h3 h4 hf st hpar v (st.sc vn) hval j s hj hs).1)

/-- **Writing a table**: the values and the cost. -/
theorem fill_spec (f : Ex) {vn vi vK vγ vΘ vpar : ℕ} (hvi : vi < 990) (hvK : vK < 990) (hvγ : vγ < 990)
    (hvΘ : vΘ < 990) (hvp : vpar < 990) (h1 : vi ≠ vK) (h2 : vi ≠ vpar) (h3 : vγ ≠ vi)
    (h4 : vγ ≠ vK) (hf : VB 990 f) (st : St) (hpar : st.sc vpar < 3) (v : ℕ → ℕ) (C : ℕ)
    (hval : ∀ i < st.sc vn, ∀ A', AgP st.ar A' (st.sc vpar) → eval (fillEnv st.sc vi vK vγ vΘ i) A' f = v i)
    (hcost : ∀ i < st.sc vn, ∀ A', AgP st.ar A' (st.sc vpar) → cost (fillEnv st.sc vi vK vγ vΘ i) A' f ≤ C) :
    (Cmd.run (fillC f vn vi vK vγ vΘ vpar) st).2 ≤ st.sc vn * (C + 40 * st.sc vn + 201) + 1 := by
  have step := fill_step f hvi hvK hvγ hvΘ hvp h1 h2 h3 h4 hf st hpar v (st.sc vn) hval
  exact Cmd.loop_cost_le (b := vn) (c := vi) (body := fillBody f vi vK vγ vΘ vpar) (FillInv st v vi (st.sc vpar))
    (C + 40 * st.sc vn + 200) (fillInv_zero st v vi _) (fun j s hj hs => (step j s hj hs).1)
    (fun j s hj hs => le_trans (step j s hj hs).2.2 (by
      have := hcost j hj s.ar (step j s hj hs).2.1; omega))

end Factoring.Aux
