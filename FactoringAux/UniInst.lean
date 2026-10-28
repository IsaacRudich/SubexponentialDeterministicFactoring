/-
The uniform engine: the literal-free copies plugged in (`UP`), and their specification (**`UP_ok`**).

Not an audit surface.
-/
module

public import FactoringAux.UniLevelSpec
public import FactoringAux.UniLevelV
public import FactoringAux.UniSet
public import FactoringAux.UniTopV

@[expose] public section

namespace Factoring.Aux

open Factoring.Aux.Copied Factoring.Aux.Copied.PLib Ex Uni MulEx

namespace Uni

/-- The level data with its literals in variables `20 … 31`. -/
def lvQ : LPv := ⟨100, 10, 40, 60, 61, 20, rdT⟩

theorem lvQ_eq (K : ℕ) : LPv.of (lvP K) 20 rdT = lvQ := rfl

end Uni

/-- **The engine's parts.** -/
def UP : UParts where
  lset := lvlSet 20 43
  lnE := LevelV.LnE lvQ
  srE := fun tr => LevelV.searchE lvQ tr 102 103
  nxE := LevelV.nextTE lvQ
  tset := topSet 43
  l0E := TopV.L0E
  tsE := TopV.searchE
  ttE := TopV.tab

/-- Level literal variables. -/
def lokU (K : ℕ) : ℕ → ℕ → Prop := lvlOk 20 K (3 * K ^ 8)
/-- Top literal variables. -/
def tokU (K : ℕ) : ℕ → ℕ → Prop := topOk K (3 * K ^ 8)

theorem bge_rdT : Ex.BGe 32 rdT := by simp [Ex.BGe, rdT, rdTE, pow2]

theorem rdT_LS (K : ℕ) : LS (lokU K) rdT rdT :=
  LSB.refl_ge (t := 32) (fun _ hx => lvlOk_nb hx) rdT bge_rdT

theorem vb_rdT990 : VB 990 rdT := by simp [rdT, rdTE, pow2, VB]

theorem coarsen_vb990 : (CoarsenEx.nex (Ex.clPc 0)).VB 990 := by
  have hm := mul_vb (u := 16) (vm := 10) (vs := 11) (by omega) (by omega) (by omega)
  have hM : (mulNEx 16 10 11).VB 990 :=
    ⟨VB_mono (by omega) _ hm.1, VB_mono (by omega) _ hm.2.1, VB_mono (by omega) _ hm.2.2.1,
      VB_mono (by omega) _ hm.2.2.2.1, VB_mono (by omega) _ hm.2.2.2.2⟩
  exact coarsen_vb (P := Ex.clPc 0) hM
    (by simp only [Ex.clPc, nodesE, AE, pow2, VB, and_true, true_and, and_self]; omega)
    (by simp only [Ex.clPc, Ex.clχE, sel, kA, AE, pow2, VB, and_true, true_and, and_self]; omega)
    (by simp only [Ex.clPc]; omega) (by simp only [Ex.clPc]; omega) (by simp only [Ex.clPc]; omega)

theorem tab_vb990 : VB 990 TopV.tab :=
  LS.VB (TopV.tab_LS (K := 0) (g := 0))
    (group_tab_vb (S := gsTop 0 0) (t := 990) coarsen_vb990 (by simp only [gsTop]; omega)
      (by simp only [gsTop]; omega) (by simp only [gsTop]; omega) (by simp only [gsTop]; omega))
    (fun _ _ h => by have := topOk_lt h; omega)

/-- **The copies meet their specification.** -/
theorem UP_ok : UOK UP lokU tokU where
  lvar K v k h := ⟨h.1, by have := lvlOk_lt h; omega⟩
  tvar K v k h := Or.inr (Or.inr ⟨h.1, by have := topOk_lt h; omega⟩)
  lset st := by
    rw [show UP.lset = lvlSet 20 43 from rfl]
    obtain ⟨-, h1, h2, h3, -⟩ := lvlSet_spec (p := 20) (q := 43) st rfl (by norm_num) (Or.inr (by norm_num)) (by norm_num)
    refine ⟨fun v k hv => h1 v k hv, fun y hy h => h2 y hy ?_, h3⟩
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (le_trans (by norm_num) h)
  tset st := by
    rw [show UP.tset = topSet 43 from rfl]
    obtain ⟨-, h1, h2, h3, -⟩ := topSet_spec (q := 43) st rfl (Or.inr (by norm_num)) (by norm_num)
    refine ⟨fun v k hv => h1 v k hv, fun y hy _ _ h => h2 y hy ?_, h3⟩
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr h
  lnE K σ A h := by
    have := LevelV.LnE_LS (P := lvP K) (p := 20) (TE' := rdT)
    exact LS.eval_cost this h
  srE K tr σ A h := by
    have := LevelV.searchE_LS (P := lvP K) (p := 20) (TE' := rdT) (rdT_LS K) (by simp [lvP]) (by simp [lvP])
      (by simp [lvP]) tr (vx := 102) (vs := 103) (by norm_num) (by norm_num)
    exact LS.eval_cost this h
  nxE K σ A h := by
    have := LevelV.nextTE_LS (P := lvP K) (p := 20) (TE' := rdT) (rdT_LS K) (by simp [lvP]) (by simp [lvP])
      (by simp [lvP])
    exact LS.eval_cost this h
  l0E K σ A h := LS.eval_cost (TopV.L0E_LS (K := K) (g := 3 * K ^ 8)) h
  tsE K σ A h := LS.eval_cost (TopV.searchE_LS (K := K) (g := 3 * K ^ 8)) h
  ttE K σ A h := LS.eval_cost (TopV.tab_LS (K := K) (g := 3 * K ^ 8)) h
  vlnE := LevelV.LnE_vb lvQ (by simp [lvQ]) (by simp [lvQ])
  vsrE tr := LevelV.searchE_vb lvQ (VB_mono (by norm_num) _ vb_rdT990) (by simp [lvQ]) (by simp [lvQ])
    (by simp [lvQ]) (by simp [lvQ]) (by simp [lvQ]) (by simp [lvQ]) tr (by norm_num) (by norm_num)
  vnxE := LevelV.nextTE_vb lvQ vb_rdT990 (by simp [lvQ]) (by simp [lvQ]) (by simp [lvQ]) (by simp [lvQ])
    (by simp [lvQ]) (by simp [lvQ])
  vl0E := TopV.L0E_vb
  vtsE := TopV.searchE_vb
  vttE := tab_vb990

end Factoring.Aux
