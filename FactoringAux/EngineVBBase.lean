/-
Free variables and variable bounds of the engine's expressions: the predicates and the coarsening and
clique builders.

* `Ex.FVw s vs e`: the free variables of `e` satisfy `s` or are in the list `vs` (stated for every larger predicate,
  so that it composes under binders); `NEx.FVw` for the five expressions of a network.
* Coarsening (`CoarsenEx.nex`): **`coarsen_fvw`**, **`coarsen_vb`**.  Clique (`CliqueEx.tab`): **`clique_fvw`**,
  **`clique_vb`**.

Not an audit surface.
-/
module

public import FactoringAux.EngineCliqueEx

@[expose] public section

namespace Factoring.Aux

open Ex

set_option linter.unusedSimpArgs false

namespace Ex

/-- The free variables of `e` satisfy `s` or are among `vs`. -/
def FVw (s : ℕ → Prop) (vs : List ℕ) (e : Ex) : Prop :=
  ∀ s' : ℕ → Prop, (∀ y, s y → s' y) → (∀ v ∈ vs, s' v) → FV s' e

theorem FVw.fv {s : ℕ → Prop} {vs : List ℕ} {e : Ex} (h : FVw s vs e) : FV (fun y => s y ∨ y ∈ vs) e :=
  h _ (fun _ hy => Or.inl hy) (fun _ hv => Or.inr hv)

theorem FVw.of_fv {s : ℕ → Prop} {vs : List ℕ} {e : Ex} (h : FV (fun y => s y ∨ y ∈ vs) e) : FVw s vs e :=
  fun _ hs hv => FV_mono (fun y hy => hy.elim (hs y) (hv y)) e h

end Ex

/-- The five expressions of a network have their free variables in `s` or among their arguments `v` (the size reads
`a`; the weight `a, z`; the width `a, b`; the factor functions `a, b, z, q`). -/
def NEx.FVw (s : ℕ → Prop) (v : NVars) (E : NEx) : Prop :=
  Ex.FVw s [v.a] E.sz ∧ Ex.FVw s [v.a, v.z] E.W ∧ Ex.FVw s [v.a, v.b] E.c ∧ Ex.FVw s [v.a, v.b, v.z, v.q] E.l ∧
    Ex.FVw s [v.a, v.b, v.z, v.q] E.r

/-- Every variable of the five expressions is below `t`. -/
def NEx.VB (t : ℕ) (E : NEx) : Prop :=
  Ex.VB t E.sz ∧ Ex.VB t E.W ∧ Ex.VB t E.c ∧ Ex.VB t E.l ∧ Ex.VB t E.r

section Coarsen

open CoarsenEx

variable {s : ℕ → Prop} {P : CP}

theorem coarsen_sz_fvw (hE : P.E.FVw s (NVars.std P.u)) (hg : FVw s [] P.gE)
    (hχ : FVw s [P.u] P.χE) : FVw s [P.w] (sz P) := by
  intro s' hs hv
  simp only [FVw, NEx.FVw, NVars.std, List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true,
    and_true, and_imp] at hv hE hg hχ
  obtain ⟨hE1, hE2, hE3, hE4, hE5⟩ := hE
  simp (config := {contextual := true}) only [sz, sgE, nprod, ifEq, FV, true_or, or_true, and_true, true_and,
    and_self, implies_true, hs, hv, hE1, hg, hχ]

theorem coarsen_W_fvw (hvm : s P.vm) (hE : P.E.FVw s (NVars.std P.u)) (hg : FVw s [] P.gE)
    (hχ : FVw s [P.u] P.χE) : FVw s [P.w, P.w + 2] (W P) := by
  intro s' hs hv
  simp only [FVw, NEx.FVw, NVars.std, List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true,
    and_true, and_imp] at hv hE hg hχ
  obtain ⟨hE1, hE2, hE3, hE4, hE5⟩ := hE
  obtain ⟨hv0, hv2⟩ := hv
  simp (config := {contextual := true}) only [W, sgE, ppE, digE, digB, chiB, zmul, zprod, zsum, pow2, nprod, ifEq,
    FV, true_or, or_true, and_true, true_and, and_self, implies_true, hs, hvm, hv0, hv2, hE1, hE2, hE3, hE4, hE5,
    hg, hχ]

theorem coarsen_c_fvw (hE : P.E.FVw s (NVars.std P.u)) (hg : FVw s [] P.gE)
    (hχ : FVw s [P.u] P.χE) : FVw s [P.w, P.w + 1] (c P) := by
  intro s' hs hv
  simp only [FVw, NEx.FVw, NVars.std, List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true,
    and_true, and_imp] at hv hE hg hχ
  obtain ⟨hE1, hE2, hE3, hE4, hE5⟩ := hE
  obtain ⟨hv0, hv1⟩ := hv
  simp (config := {contextual := true}) only [c, atPair, usedE, crossE, chiB, nsum, ifEq,
    FV, true_or, or_true, and_true, true_and, and_self, implies_true, hs, hv0, hv1, hE1, hE2, hE3, hE4, hE5,
    hg, hχ]

theorem coarsen_l_fvw (hvm : s P.vm) (hE : P.E.FVw s (NVars.std P.u)) (hg : FVw s [] P.gE)
    (hχ : FVw s [P.u] P.χE) : FVw s [P.w, P.w + 1, P.w + 2, P.w + 3] (l P) := by
  intro s' hs hv
  simp only [FVw, NEx.FVw, NVars.std, List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true,
    and_true, and_imp] at hv hE hg hχ
  obtain ⟨hE1, hE2, hE3, hE4, hE5⟩ := hE
  obtain ⟨hv0, hv1, hv2, hv3⟩ := hv
  simp (config := {contextual := true}) only [l, offE, sgE, ppE, digE, digB, chiB, atPair, usedE, crossE, zmul,
    zprod, nsum, pow2, nprod, ifEq, FV, true_or, or_true, and_true, true_and, and_self, implies_true, hs, hvm, hv0,
    hv1, hv2, hv3, hE1, hE2, hE3, hE4, hE5, hg, hχ]

theorem coarsen_r_fvw (hvm : s P.vm) (hE : P.E.FVw s (NVars.std P.u)) (hg : FVw s [] P.gE)
    (hχ : FVw s [P.u] P.χE) : FVw s [P.w, P.w + 1, P.w + 2, P.w + 3] (r P) := by
  intro s' hs hv
  simp only [FVw, NEx.FVw, NVars.std, List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true,
    and_true, and_imp] at hv hE hg hχ
  obtain ⟨hE1, hE2, hE3, hE4, hE5⟩ := hE
  obtain ⟨hv0, hv1, hv2, hv3⟩ := hv
  simp (config := {contextual := true}) only [r, offE, sgE, ppE, digE, digB, chiB, atPair, usedE, crossE, zmul,
    zprod, nsum, pow2, nprod, ifEq, FV, true_or, or_true, and_true, true_and, and_self, implies_true, hs, hvm, hv0,
    hv1, hv2, hv3, hE1, hE2, hE3, hE4, hE5, hg, hχ]

/-- **The free variables of the coarsened network's expressions.** -/
theorem coarsen_fvw (hvm : s P.vm) (hE : P.E.FVw s (NVars.std P.u)) (hg : FVw s [] P.gE)
    (hχ : FVw s [P.u] P.χE) : (nex P).FVw s (NVars.std P.w) :=
  ⟨coarsen_sz_fvw hE hg hχ, coarsen_W_fvw hvm hE hg hχ, coarsen_c_fvw hE hg hχ, coarsen_l_fvw hvm hE hg hχ,
    coarsen_r_fvw hvm hE hg hχ⟩

/-- **Every variable of the coarsened network's expressions is below `t`.** -/
theorem coarsen_vb {t : ℕ} (hE : P.E.VB t) (hg : VB t P.gE) (hχ : VB t P.χE) (hvm : P.vm < t)
    (hu : P.u + 4 ≤ P.w) (hw : P.w + 7 ≤ t) : (nex P).VB t := by
  obtain ⟨hE1, hE2, hE3, hE4, hE5⟩ := hE
  simp only [NEx.VB, nex, sz, W, c, l, r, offE, sgE, ppE, digE, digB, chiB, atPair, usedE, crossE, zmul, zprod,
    zsum, nsum, pow2, nprod, ifEq, VB, hE1, hE2, hE3, hE4, hE5, hg, hχ, and_true, true_and, and_self]
  omega

end Coarsen

section Clique

open CliqueEx

variable {s : ℕ → Prop} {P : KP}

/-- **The free variables of the clique table.** -/
theorem clique_fvw (hvm : s P.vm) (hE : P.E.FVw s (NVars.std P.u)) (hk : FVw s [] P.kE) (hL : FVw s [] P.LE) :
    FVw s [P.w, P.w + 1] (tab P) := by
  intro s' hs hv
  simp only [FVw, NEx.FVw, NVars.std, List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true,
    and_true, and_imp] at hv hE hk hL
  obtain ⟨hE1, hE2, hE3, hE4, hE5⟩ := hE
  obtain ⟨hv0, hv1⟩ := hv
  simp (config := {contextual := true}) only [tab, padL, padR, unitE, blkQ, zmul, zprod, zsum, pow2, nprod, ifEq,
    FV, true_or, or_true, and_true, true_and, and_self, implies_true, hs, hvm, hv0, hv1, hE1, hE2, hE3, hE4, hE5,
    hk, hL]

/-- **Every variable of the clique table is below `t`.** -/
theorem clique_vb {t : ℕ} (hE : P.E.VB t) (hk : VB t P.kE) (hL : VB t P.LE) (hvm : P.vm < t)
    (hu : P.u + 4 ≤ P.w) (hw : P.w + 3 ≤ t) : VB t (tab P) := by
  obtain ⟨hE1, hE2, hE3, hE4, hE5⟩ := hE
  simp only [tab, padL, padR, unitE, blkQ, zmul, zprod, zsum, pow2, nprod, ifEq, VB, hE1, hE2, hE3, hE4, hE5, hk,
    hL, and_true, true_and, and_self]
  omega

end Clique

end Factoring.Aux
