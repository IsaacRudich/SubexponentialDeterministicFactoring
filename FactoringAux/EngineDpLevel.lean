/-
Nesting depth of the engine's expressions, part 2: a group step (`dpT_group_tab`, `dpT_group_search`),
one level (`dpT_nextTE`: `dp (nextTE P) ≤ max (dp P.TE + 20) 75`; `dpT_pre`), the brute force and the chain of
levels (`dpT_deepEx`: `dp (deepEx K0 d … TE) ≤ max (dp TE) 55 + 24 d + 8`).

Not an audit surface.
-/
module

public import FactoringAux.EngineDpBase

@[expose] public section

set_option linter.unusedSectionVars false

namespace Factoring.Aux

open Ex

theorem dpT_key {x k n : ℕ} (h : x ≤ n - k) (hk : k ≤ n) : x + k ≤ n := by omega

macro "dpc" : tactic => `(tactic| ((try simp only [GroupEx.Pc, GroupEx.Pk, GroupEx.chiE, Ex.dp]) <;> omega))

/-! ### A group step -/

theorem dpT_group_tab {S : GS} {n : ℕ} (h0 : 39 ≤ n) (hs : dp S.E.sz + 29 ≤ n) (hW : dp S.E.W + 12 ≤ n)
    (hc : dp S.E.c + 25 ≤ n) (hl : dp S.E.l + 22 ≤ n) (hr : dp S.E.r + 23 ≤ n) : dp (GroupEx.tab S) ≤ n := by
  unfold GroupEx.tab
  apply dpT_clique_tab
  · exact dpT_key (dpT_coarsen_sz (by dpc) (by dpc) (by dpc)) (by omega)
  · exact dpT_key (dpT_coarsen_W (by dpc) (by dpc) (by dpc) (by dpc) (by dpc) (by dpc) (by dpc)) (by omega)
  · exact dpT_key (dpT_coarsen_c (by dpc) (by dpc) (by dpc)) (by omega)
  · exact dpT_key (dpT_coarsen_l (by dpc) (by dpc) (by dpc) (by dpc) (by dpc) (by dpc)) (by omega)
  · exact dpT_key (dpT_coarsen_r (by dpc) (by dpc) (by dpc) (by dpc) (by dpc) (by dpc)) (by omega)
  · dpc
  · dpc

theorem dpT_group_search {S : GS} {n : ℕ} (vx vs : ℕ) (h0 : 30 ≤ n) (hc : dp S.E.c + 16 ≤ n) :
    dp (GroupEx.searchE S vx vs) ≤ n := by
  have hcc : dp (CoarsenEx.c (GroupEx.Pc S)) + 11 ≤ n :=
    dpT_key (dpT_coarsen_c (P := GroupEx.Pc S) (by dpc) (by dpc) (by dpc)) (by omega)
  dp_tac [GroupEx.searchE, GroupEx.okE, GroupEx.chiE, ifEq, nprod, nsum]

/-! ### One level -/

section Level

variable (P : LP)

theorem dpT_level_tab (tr : Bool) : dp (GroupEx.tab (LevelEx.gs P tr)) ≤ max (dp P.TE + 19) 74 := by
  have hs := dpT_grid_sz (LevelEx.gp P) tr
  have hW := dpT_grid_W (LevelEx.gp P) tr
  have hc := dpT_grid_c (LevelEx.gp P) tr
  have hl := dpT_grid_l (LevelEx.gp P) tr
  have hr := dpT_grid_r (LevelEx.gp P) tr
  have hT : (LevelEx.gp P).TE = P.TE := rfl
  rw [hT] at hW
  apply dpT_group_tab <;> (try simp only [LevelEx.gs]) <;> omega

theorem dpT_level_search (tr : Bool) (vx vs : ℕ) : dp (GroupEx.searchE (LevelEx.gs P tr) vx vs) ≤ 32 := by
  have hc := dpT_grid_c (LevelEx.gp P) tr
  apply dpT_group_search <;> (try simp only [LevelEx.gs]) <;> omega

theorem dpT_UE (tr : Bool) : dp (LevelEx.UE P tr) ≤ 19 := by
  have h : dp (GridEx.c (LevelEx.gp P) tr) ≤ 16 := dpT_grid_c (LevelEx.gp P) tr
  dp_tac [LevelEx.UE, nsum]

/-- **The next table** is at most `20` deeper than the table (or `75` deep). -/
theorem dpT_nextTE : dp (LevelEx.nextTE P) ≤ max (dp P.TE + 20) 75 := by
  have h1 := dpT_level_tab P false
  have h2 := dpT_level_tab P true
  have h3 := dpT_UE P false
  have h4 := dpT_UE P true
  simp only [LevelEx.nextTE, Ex.dp]
  omega

theorem dpT_LnE : dp (LevelEx.LnE P) ≤ 8 := by
  dp_tac [LevelEx.LnE]

theorem dpT_pre (body : Ex) : dp (LevelEx.pre P body) ≤ max (dp body + 3) 35 := by
  have h1 := dpT_level_search P false (P.b + 2) (P.b + 3)
  have h2 := dpT_level_search P true (P.b + 2) (P.b + 3)
  have h3 := dpT_LnE P
  simp only [LevelEx.pre, Ex.dp]
  omega

end Level

/-! ### The chain of levels -/

theorem dpT_bruteE (b vm vL vγ vΘ K : ℕ) (TE : Ex) : dp (bruteE b vm vL vγ vΘ K TE) ≤ max (dp TE + 8) 15 := by
  dp_tac [bruteE, blkKE, zsum, zmul, zprod, ifEq, pow2]

/-- **The chain from depth `d`** adds `24` per level. -/
theorem dpT_deepEx (K0 : ℕ) : ∀ d b vm vl vγ vΘ TE,
    dp (deepEx K0 d b vm vl vγ vΘ TE) ≤ max (dp TE) 55 + 24 * d + 8
  | 0, b, vm, vl, vγ, vΘ, TE => by
      have := dpT_bruteE b vm vl vγ vΘ (Kb K0 0) TE
      simp only [deepEx]
      omega
  | d + 1, b, vm, vl, vγ, vΘ, TE => by
      have ih := dpT_deepEx K0 d (b + 100) vm (b + 1) (b + 62) (b + 63)
        (LevelEx.nextTE ⟨b, vm, vl, vγ, vΘ, Kb K0 d, Gs K0 d, TE⟩)
      have hn := dpT_nextTE ⟨b, vm, vl, vγ, vΘ, Kb K0 d, Gs K0 d, TE⟩
      have hp := dpT_pre ⟨b, vm, vl, vγ, vΘ, Kb K0 d, Gs K0 d, TE⟩
        (deepEx K0 d (b + 100) vm (b + 1) (b + 62) (b + 63) (LevelEx.nextTE ⟨b, vm, vl, vγ, vΘ, Kb K0 d, Gs K0 d, TE⟩))
      dsimp only at hn
      simp only [deepEx, zsum, tBE, Ex.dp]
      omega

end Factoring.Aux
