/-
Free variables and variable bounds of the whole counting expression `Ex.topE`.

* `mulNEx_fvw`: the multiplication network's expressions read `0`, `2`, `vs` and their arguments (per field).
* `deep_fvw`, `deep_vb`: the chain `deepEx` (by induction on the depth; its base moves by `100` per level).
* **`topE_fv`**: the free variables of `topE K0 ℓ` are among `0`, `2`, `10`;
  **`topE_vb`**: every variable of `topE K0 ℓ` is below `100 ℓ + 165`.

Not an audit surface.
-/
module

public import FactoringAux.EngineVBGroup
public import FactoringAux.EngineTop

@[expose] public section

namespace Factoring.Aux

open Ex MulEx

set_option linter.unusedSimpArgs false

/-- The free variables of the multiplication network's expressions, field by field. -/
theorem mulNEx_fvw {s : ℕ → Prop} {u vm vs : ℕ} (h0 : s 0) (h2 : s 2) (hvs : s vs) :
    (mulNEx u vm vs).FVw s (NVars.std u) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intro s' hs hv <;>
    simp only [NVars.std, List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true, and_true] at hv <;>
    simp (config := {contextual := true}) only [mulNEx, msg, sel, kA, AE, hE, LLE, fwE, ME, TLE, PfE, PZE, PDE, mM,
      sM, pw, pwi, tE, dD, dZ, zv, z1E, z2E, cyE, ccE, faMsg, hat, midMsg, ibMsg, lnk, cE, posE, faW, jE, dgE, cW,
      xBit, nBit, bitRd, ifEq, eqE, pow2, nprod, nsum, FV, true_or, or_true, and_true, true_and, and_self,
      implies_true, hs, h0, h2, hvs, hv]

/-- **The free variables of the chain.** -/
theorem deep_fvw (K0 : ℕ) : ∀ (d b vm vl vγ vΘ : ℕ) (TE : Ex) (s : ℕ → Prop), s vm → s vl →
    FVw s [vγ, vΘ] TE → FVw s [] (deepEx K0 d b vm vl vγ vΘ TE)
  | 0, b, vm, vl, vγ, vΘ, TE, s, hvm, hvl, hT => by
      intro s' hs _
      simp only [FVw, List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true, and_true,
        and_imp] at hT
      simp (config := {contextual := true}) only [deepEx, bruteE, blkKE, zsum, zmul, zprod, pow2, ifEq, FV,
        true_or, or_true, and_true, true_and, and_self, implies_true, hs, hvm, hvl, hT]
  | d + 1, b, vm, vl, vγ, vΘ, TE, s, hvm, hvl, hT => by
      intro s' hs _
      have hB : FVw (fun y => s' y ∨ y = b) [b + 1, b + 4, b + 5]
          (deepEx K0 d (b + 100) vm (b + 1) (b + 62) (b + 63)
            (LevelEx.nextTE ⟨b, vm, vl, vγ, vΘ, Kb K0 d, Gs K0 d, TE⟩)) := by
        intro s2 hs2 hv2
        simp only [List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true, and_true] at hv2
        obtain ⟨h1, h4, h5⟩ := hv2
        have g : ∀ y, s y → s2 y := fun y hy => hs2 y (Or.inl (hs y hy))
        refine deep_fvw K0 d (b + 100) vm (b + 1) (b + 62) (b + 63) _ s2 (g _ hvm) h1 ?_ s2 (fun _ h => h)
          (by simp)
        exact level_nextTE_fvw (P := ⟨b, vm, vl, vγ, vΘ, Kb K0 d, Gs K0 d, TE⟩) (s := s2) (g _ hvm) (g _ hvl)
          (hs2 _ (Or.inr rfl)) h1 h4 h5 (hT.mono g (fun _ hv => Or.inr hv))
      simp only [deepEx, zsum, FV]
      refine ⟨?_, hs _ hvm, ?_⟩
      · simp only [tBE, FV, and_true, true_and]; exact Or.inl (hs _ hvl)
      · exact level_pre_fvw (P := ⟨b, vm, vl, vγ, vΘ, Kb K0 d, Gs K0 d, TE⟩) (s := fun y => s' y ∨ y = b)
          (Or.inl (hs _ hvm)) (Or.inl (hs _ hvl)) (Or.inr rfl) (hT.mono (fun y hy => Or.inl (hs y hy))
            (fun _ hv => Or.inr hv)) hB _ (fun _ h => h) (by simp)

/-- **Every variable of the chain is below `t`** if `b + 100 d + 65 ≤ t`. -/
theorem deep_vb (K0 : ℕ) : ∀ (d b vm vl vγ vΘ : ℕ) (TE : Ex) (t : ℕ), vm < t → vl < t → vγ < t → vΘ < t →
    VB t TE → b + 100 * d + 65 ≤ t → VB t (deepEx K0 d b vm vl vγ vΘ TE)
  | 0, b, vm, vl, vγ, vΘ, TE, t, hvm, hvl, hγ, hΘ, hT, hb => by
      simp only [deepEx, bruteE, blkKE, zsum, zmul, zprod, pow2, ifEq, VB, hT, and_true, true_and, and_self]
      omega
  | d + 1, b, vm, vl, vγ, vΘ, TE, t, hvm, hvl, hγ, hΘ, hT, hb => by
      have hN := level_nextTE_vb (P := ⟨b, vm, vl, vγ, vΘ, Kb K0 d, Gs K0 d, TE⟩) hT hvm hvl hγ hΘ (by dsimp only; omega)
      have hD := deep_vb K0 d (b + 100) vm (b + 1) (b + 62) (b + 63) _ t hvm (by omega) (by omega) (by omega) hN
        (by omega)
      have hP := level_pre_vb (P := ⟨b, vm, vl, vγ, vΘ, Kb K0 d, Gs K0 d, TE⟩) hT hvm hvl hγ hΘ (by dsimp only; omega) hD
      simp only [deepEx, zsum, tBE, VB, hP, and_true, true_and, and_self]
      omega

/-- The top coarsening's expressions. -/
theorem top_coarsen_fvw {s : ℕ → Prop} (g : ℕ) (h0 : s 0) (h2 : s 2) (h10 : s 10) (h11 : s 11) :
    (CoarsenEx.nex (clPc g)).FVw s (NVars.std 26) := by
  refine coarsen_fvw (P := clPc g) h10 (mulNEx_fvw (vm := 10) h0 h2 h11) ?_ ?_
  · intro s' hs _
    simp only [clPc, nodesE, AE, pow2, FV, true_and, and_true, and_self]; exact hs _ h11
  · intro s' hs hv
    simp only [clPc, List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true, and_true] at hv
    simp (config := {contextual := true}) only [clPc, clχE, sel, kA, AE, pow2, FV, true_or, or_true, and_true,
      true_and, and_self, implies_true, hs, h11, hv]

/-- **The free variables of the whole counting expression are among `0`, `2`, `10`.** -/
theorem topE_fv (K0 ℓ : ℕ) : Ex.FV (fun y => y = 0 ∨ y = 2 ∨ y = 10) (Ex.topE K0 ℓ) := by
  set s0 : ℕ → Prop := fun y => y = 0 ∨ y = 2 ∨ y = 10
  have hS : FVw (fun y => ((s0 y ∨ y = 11) ∨ y = 12) ∨ y = 15) [82, 83] (GroupEx.tab (gsTop (Kb K0 ℓ) (Gs K0 ℓ))) :=
    group_tab_fvw (S := gsTop (Kb K0 ℓ) (Gs K0 ℓ)) (by simp [s0, gsTop]) (Or.inr rfl) (Or.inl (Or.inr rfl))
      (top_coarsen_fvw _ (by simp [s0]) (by simp [s0]) (by simp [s0]) (by simp))
  simp only [topE, FV]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [sE, pow2, FV, s0]
  · simp [L0E, clPE, AE, fwE, LLE, pow2, FV, s0]
  · exact group_search_fvw (S := gsTop (Kb K0 ℓ) (Gs K0 ℓ)) (s := fun y => (s0 y ∨ y = 11) ∨ y = 12)
      (Or.inr rfl) (top_coarsen_fvw _ (by simp [s0]) (by simp [s0]) (by simp [s0]) (by simp)) _ _ _
      (fun _ h => h) (by simp)
  · exact deep_fvw K0 ℓ 100 10 12 82 83 _ _ (by simp [s0]) (by simp) hS _ (fun _ h => h) (by simp)

/-- **Every variable of the whole counting expression is below `100 ℓ + 165`.** -/
theorem topE_vb (K0 ℓ : ℕ) : Ex.VB (100 * ℓ + 165) (Ex.topE K0 ℓ) := by
  set t := 100 * ℓ + 165 with ht
  have hm := mul_vb (u := 16) (vm := 10) (vs := 11) (by omega) (by omega) (by omega)
  have hM : (mulNEx 16 10 11).VB t :=
    ⟨VB_mono (by omega) _ hm.1, VB_mono (by omega) _ hm.2.1, VB_mono (by omega) _ hm.2.2.1,
      VB_mono (by omega) _ hm.2.2.2.1, VB_mono (by omega) _ hm.2.2.2.2⟩
  have hC : (CoarsenEx.nex (clPc (Gs K0 ℓ))).VB t :=
    coarsen_vb (P := clPc (Gs K0 ℓ)) hM
      (by simp only [clPc, nodesE, AE, pow2, VB, and_true, true_and, and_self]; omega)
      (by simp only [clPc, clχE, sel, kA, AE, pow2, VB, and_true, true_and, and_self]; omega)
      (by simp only [clPc]; omega) (by simp only [clPc]; omega) (by simp only [clPc]; omega)
  have hS := group_search_vb (S := gsTop (Kb K0 ℓ) (Gs K0 ℓ)) (t := t) hC (by simp only [gsTop]; omega)
    (by simp only [gsTop]; omega) (by simp only [gsTop]; omega) (by simp only [gsTop]; omega)
    (vx := 13) (vs := 14) (by omega) (by omega)
  have hT := group_tab_vb (S := gsTop (Kb K0 ℓ) (Gs K0 ℓ)) (t := t) hC (by simp only [gsTop]; omega)
    (by simp only [gsTop]; omega) (by simp only [gsTop]; omega) (by simp only [gsTop]; omega)
  have hD := deep_vb K0 ℓ 100 10 12 82 83 _ t (by omega) (by omega) (by omega) (by omega) hT (by omega)
  simp only [topE, sE, L0E, clPE, AE, fwE, LLE, pow2, VB, hS, hD, and_true, true_and, and_self]
  omega

end Factoring.Aux
