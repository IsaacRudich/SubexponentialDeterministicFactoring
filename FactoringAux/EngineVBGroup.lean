/-
Free variables and variable bounds of the group steps (`GroupEx`) and of one level (`LevelEx`).

* `GroupEx`: **`group_tab_fvw`** (arguments `u+56`, `u+57`), **`group_search_fvw`**, **`group_tab_vb`**,
  **`group_search_vb`** (every variable below `t` if `u + 59 ≤ t`).
* `LevelEx`: **`level_nextTE_fvw`** (arguments `b+62`, `b+63`; the context holds `vm`, `vl`, `b`, `b+1`, `b+4`,
  `b+5`), **`level_pre_fvw`**, **`level_nextTE_vb`**, **`level_pre_vb`** (below `t` if `b + 65 ≤ t`).

Not an audit surface.
-/
module

public import FactoringAux.EngineVBGrid
public import FactoringAux.EngineLevelEx

@[expose] public section

namespace Factoring.Aux

open Ex

set_option linter.unusedSimpArgs false

theorem Ex.FVw.mono {s s' : ℕ → Prop} {vs vs' : List ℕ} {e : Ex} (h : FVw s vs e) (h1 : ∀ y, s y → s' y)
    (h2 : ∀ v ∈ vs, s' v ∨ v ∈ vs') : FVw s' vs' e := fun s'' hs hv =>
  h s'' (fun y hy => hs y (h1 y hy)) (fun v hv' => (h2 v hv').elim (hs v) (hv v))

theorem NEx.FVw.mono {s s' : ℕ → Prop} {v : NVars} {E : NEx} (h : E.FVw s v) (h1 : ∀ y, s y → s' y) :
    E.FVw s' v :=
  ⟨h.1.mono h1 (fun _ hv => Or.inr hv), h.2.1.mono h1 (fun _ hv => Or.inr hv),
    h.2.2.1.mono h1 (fun _ hv => Or.inr hv), h.2.2.2.1.mono h1 (fun _ hv => Or.inr hv),
    h.2.2.2.2.mono h1 (fun _ hv => Or.inr hv)⟩

section Group

open GroupEx

variable {s : ℕ → Prop} {S : GS}

theorem group_chi_fvw (hχ : s S.vχ) : FVw s [S.u] (chiE S) := by
  intro s' hs hv
  simp only [List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true, and_true] at hv
  simp (config := {contextual := true}) only [chiE, FV, true_or, or_true, and_true, true_and, and_self, hs, hχ,
    hv]

/-- **The free variables of a group step's table.** -/
theorem group_tab_fvw (hvm : s S.vm) (hχ : s S.vχ) (hL : s S.vL) (hE : S.E.FVw s (NVars.std S.u)) :
    FVw s [S.u + 56, S.u + 57] (tab S) := by
  have hc := coarsen_fvw (P := Pc S) hvm hE (fun _ _ _ => trivial) (group_chi_fvw hχ)
  exact clique_fvw (P := Pk S) hvm hc (fun _ _ _ => trivial) (fun _ hs _ => hs _ hL)

theorem group_okE_fvw (hχ : s S.vχ) (hL : s S.vL) (hE : S.E.FVw s (NVars.std S.u)) : FVw s [] (okE S) := by
  have hc : FVw s [S.u + 46, S.u + 47] (CoarsenEx.c (Pc S)) :=
    coarsen_c_fvw (P := Pc S) hE (fun _ _ _ => trivial) (group_chi_fvw hχ)
  have hc' := group_chi_fvw (S := S) hχ
  intro s' hs _
  simp only [FVw, List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true, and_true, and_imp] at hc hc'
  simp (config := {contextual := true}) only [okE, ifEq, nsum, nprod, FV, true_or, or_true, and_true, true_and,
    and_self, implies_true, hs, hL, hc, hc', Nat.add_assoc, Nat.reduceAdd]

/-- **The free variables of a group step's search.** -/
theorem group_search_fvw (hL : s S.vL) (hE : S.E.FVw s (NVars.std S.u)) (vx vs : ℕ) :
    FVw s [] (searchE S vx vs) := by
  have h := group_okE_fvw (S := S) (s := fun y => s y ∨ y = S.vχ) (Or.inr rfl) (Or.inl hL)
    (hE.mono fun y hy => Or.inl hy)
  have h' : ∀ s'' : ℕ → Prop, (∀ y, s y → s'' y) → s'' S.vχ → FV s'' (okE S) := fun s'' h1 h2 =>
    h s'' (fun y hy => hy.elim (h1 y) (fun e => e ▸ h2)) (by simp)
  intro s' hs _
  simp (config := {contextual := true}) only [searchE, ifEq, FV, true_or, or_true, and_true, true_and,
    and_self, implies_true, hs, hL, h']

theorem group_tab_vb {t : ℕ} (hE : S.E.VB t) (hvm : S.vm < t) (hχ : S.vχ < t) (hL : S.vL < t)
    (hu : S.u + 59 ≤ t) : VB t (tab S) := by
  have hc := coarsen_vb (P := Pc S) hE trivial (by simp only [Pc, chiE, VB, and_true, true_and]; omega) hvm (by simp [Pc])
    (by simp only [Pc]; omega)
  exact clique_vb (P := Pk S) hc trivial hL hvm (by simp [Pk]) (by simp only [Pk]; omega)

theorem group_search_vb {t : ℕ} (hE : S.E.VB t) (hvm : S.vm < t) (hχ : S.vχ < t) (hL : S.vL < t)
    (hu : S.u + 59 ≤ t) {vx vs : ℕ} (hx : vx < t) (hs : vs < t) : VB t (searchE S vx vs) := by
  have hc := coarsen_vb (P := Pc S) hE trivial (by simp only [Pc, chiE, VB, and_true, true_and]; omega) hvm (by simp [Pc])
    (by simp only [Pc]; omega)
  obtain ⟨-, -, hc3, -, -⟩ := hc
  simp only [CoarsenEx.nex] at hc3
  simp only [searchE, okE, chiE, ifEq, nsum, nprod, VB, hc3, and_true, true_and, and_self]
  omega

end Group

section Level

open LevelEx

variable {s : ℕ → Prop} {P : LP}

theorem level_grid_fvw (hvm : s P.vm) (hvl : s P.vl) (hb : s P.b) (hT : FVw s [P.vγ, P.vΘ] P.TE) (tr : Bool) :
    (GridEx.nex (gp P) tr).FVw s (NVars.std (P.b + 6)) :=
  grid_fvw (P := gp P) tr hvm hvl hb hT

theorem level_UE_fvw (hvm : s P.vm) (hvl : s P.vl) (hb : s P.b) (hT : FVw s [P.vγ, P.vΘ] P.TE) (tr : Bool) :
    FVw s [] (UE P tr) := by
  have hc : FVw s [P.b + 6, P.b + 7] (GridEx.c (gp P) tr) := (level_grid_fvw hvm hvl hb hT tr).2.2.1
  intro s' hs _
  simp only [FVw, List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true, and_true, and_imp] at hc
  simp (config := {contextual := true}) only [UE, nsum, FV, true_or, or_true, and_true, true_and, and_self,
    implies_true, hs, hc]

theorem level_tab_fvw (hvm : s P.vm) (hvl : s P.vl) (hb : s P.b) (hb1 : s (P.b + 1)) (hb4 : s (P.b + 4))
    (hb5 : s (P.b + 5)) (hT : FVw s [P.vγ, P.vΘ] P.TE) (tr : Bool) :
    FVw s [P.b + 62, P.b + 63] (GroupEx.tab (gs P tr)) :=
  group_tab_fvw (S := gs P tr) hvm (by cases tr <;> simpa [gs]) hb1 (level_grid_fvw hvm hvl hb hT tr)

/-- **The free variables of the next table** (its arguments `b+62`, `b+63`). -/
theorem level_nextTE_fvw (hvm : s P.vm) (hvl : s P.vl) (hb : s P.b) (hb1 : s (P.b + 1)) (hb4 : s (P.b + 4))
    (hb5 : s (P.b + 5)) (hT : FVw s [P.vγ, P.vΘ] P.TE) : FVw s [P.b + 62, P.b + 63] (nextTE P) := by
  intro s' hs hv
  exact ⟨level_UE_fvw hvm hvl hb hT false s' hs (by simp), ⟨level_UE_fvw hvm hvl hb hT true s' hs (by simp), trivial⟩,
    level_tab_fvw hvm hvl hb hb1 hb4 hb5 hT false s' hs hv, level_tab_fvw hvm hvl hb hb1 hb4 hb5 hT true s' hs hv⟩

/-- **The free variables of a level's `lett`s around a body.** -/
theorem level_pre_fvw (hvm : s P.vm) (hvl : s P.vl) (hb : s P.b) (hT : FVw s [P.vγ, P.vΘ] P.TE) {body : Ex}
    (hB : FVw s [P.b + 1, P.b + 4, P.b + 5] body) : FVw s [] (pre P body) := by
  intro s' hs _
  have g1 : ∀ y, s y → s' y ∨ y = P.b + 1 := fun y hy => Or.inl (hs y hy)
  have g4 : ∀ y, s y → (s' y ∨ y = P.b + 1) ∨ y = P.b + 4 := fun y hy => Or.inl (g1 y hy)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [LnE, FV, and_true, true_and, and_self]; exact hs _ hvl
  · exact group_search_fvw (S := gs P false) (s := fun y => s' y ∨ y = P.b + 1) (Or.inr rfl)
      ((level_grid_fvw hvm hvl hb hT false).mono g1) _ _ _ (fun _ h => h) (by simp)
  · exact group_search_fvw (S := gs P true) (s := fun y => (s' y ∨ y = P.b + 1) ∨ y = P.b + 4)
      (Or.inl (Or.inr rfl)) ((level_grid_fvw hvm hvl hb hT true).mono g4) _ _ _ (fun _ h => h) (by simp)
  · exact hB _ (fun y hy => Or.inl (g4 y hy)) (by simp)

theorem level_nextTE_vb {t : ℕ} (hT : VB t P.TE) (hvm : P.vm < t) (hvl : P.vl < t) (hγ : P.vγ < t)
    (hΘ : P.vΘ < t) (hb : P.b + 65 ≤ t) : VB t (nextTE P) := by
  have hg : ∀ tr, (GridEx.nex (gp P) tr).VB t := fun tr =>
    grid_vb (P := gp P) tr hT hvm hvl (by simp only [gp]; omega) hγ hΘ (by simp only [gp]; omega)
  have ht : ∀ tr, VB t (GroupEx.tab (gs P tr)) := fun tr =>
    group_tab_vb (S := gs P tr) (hg tr) hvm (by cases tr <;> simp only [gs] <;> simp <;> omega)
      (by simp only [gs]; omega) (by simp only [gs]; omega)
  have hc : ∀ tr, VB t (GridEx.c (gp P) tr) := fun tr => (hg tr).2.2.1
  simp only [nextTE, UE, nsum, VB, ht, hc, and_true, true_and, and_self]
  omega

theorem level_pre_vb {t : ℕ} (hT : VB t P.TE) (hvm : P.vm < t) (hvl : P.vl < t) (hγ : P.vγ < t)
    (hΘ : P.vΘ < t) (hb : P.b + 65 ≤ t) {body : Ex} (hB : VB t body) : VB t (pre P body) := by
  have hg : ∀ tr, (GridEx.nex (gp P) tr).VB t := fun tr =>
    grid_vb (P := gp P) tr hT hvm hvl (by simp only [gp]; omega) hγ hΘ (by simp only [gp]; omega)
  have hs : ∀ tr, VB t (GroupEx.searchE (gs P tr) (P.b + 2) (P.b + 3)) := fun tr =>
    group_search_vb (S := gs P tr) (hg tr) hvm (by cases tr <;> simp only [gs] <;> simp <;> omega)
      (by simp only [gs]; omega) (by simp only [gs]; omega) (by omega) (by omega)
  simp only [pre, LnE, VB, hs, hB, and_true, true_and, and_self]
  omega

end Level

end Factoring.Aux
