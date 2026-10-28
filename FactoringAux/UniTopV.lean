/-
The top builders with their `K`/`g` literals read from variables.

Copies of `L0E K g`, `GroupEx.searchE (gsTop K g) 13 14`, `GroupEx.tab (gsTop K g)` (with `clPc g`, `clχE g`,
`clPE g`). The literal variables are `5 … 9`, holding `topVals K g`:

  `5` K, `6` g, `7` K³, `8` 2g+1, `9` K^g.

Every binder of the top expressions is at least `10` (`pow2` scratch `13`, `20`; searches `13`, `14`, `15`;
multiplication network `16 …`; clusters `26 …`; group step `26 + 45 …`; table arguments `82`, `83`, `84`), so none
is a literal variable. The multiplication network (`mulNEx`) and the node count (`nodesE`) have no `K`/`g` literal
and are shared.

* `topVals`, `topOk`; **`TopV.L0E_LS`**, **`TopV.searchE_LS`**, **`TopV.tab_LS`** (`LS (topOk K g) original copy`),
  `TopV.clχE_LS`, `TopV.coarsen_LS`.
* **`TopV.L0E_vb`**, **`TopV.searchE_vb`**, **`TopV.tab_vb`**: every variable below `1000`.
* `topExs q`, **`topSet q := setBlock 5 (topExs q)`**; **`topSet_spec`**: with `K` in scalar `q` (`q < 5` or `10 ≤ q`,
  `q < 999`), the scalars `5 … 9` hold `topVals K (3 K^8)`, every other scalar below `1000` and every array is kept,
  and the cost is at most `5 · ((64 (lvlV K + 1)^3)^5 + 2) + 1`.

Not an audit surface.
-/
module

public import FactoringAux.UniSet
public import FactoringAux.EngineVBTop

@[expose] public section

namespace Factoring.Aux

open Ex MulEx Factoring.Aux.Copied Factoring.Aux.Copied.PLib

/-- The values of the top's literal variables `5 … 9` (`g = 3 K^8` in the engine). -/
def topVals (K g : ℕ) : List ℕ := [K, g, K ^ 3, 2 * g + 1, K ^ g]

/-- The top's literal variables `5 … 9`. -/
def topOk (K g : ℕ) : ℕ → ℕ → Prop := blockOk 5 (topVals K g)

theorem topOk_lt {K g v k : ℕ} (h : topOk K g v k) : v < 10 := blockOk_lt h

theorem topOk_nb {K g x : ℕ} (hx : 10 ≤ x) : ∀ k, ¬ topOk K g x k := fun _ h => by
  have := topOk_lt h; omega

namespace TopV

/-- The cluster of node `var 16`, `g` in `var 6`. -/
def clχE : Ex :=
  sel 16 11 16 (.div (.mul (.var 16) (.var 6)) (AE 16 11))
    (.div (.mul (.sub (.var 16) (kA 16 11 1)) (.var 6)) (AE 16 11))
    (.div (.mul (.sub (.var 16) (kA 16 11 2)) (.var 6)) (AE 16 11))
    (.div (.mul (.sub (.var 16) (kA 16 11 3)) (.var 6)) (AE 16 11))
    (.div (.mul (.sub (.var 16) (kA 16 11 4)) (.var 6)) (.mul (AE 16 11) (AE 16 11)))

/-- The clustering data. -/
def clPc : CP := ⟨16, 26, 10, mulNEx 16 10 11, nodesE, clχE⟩

/-- The top group step: `K` in `5`, `g` in `6`, `2g+1` in `8`, `K^g` in `9`. -/
def gs : GSv := ⟨26, 10, 15, 12, 5, 6, 8, 9, CoarsenEx.nex clPc⟩

/-- `clP s g`. -/
def clPE : Ex :=
  .add (.mul (.mul (.mul (.lit 7) (.add (.div (AE 9 11) (.var 6)) (.lit 2))) (AE 9 11)) (fwE 9 11))
    (.mul (.mul (.lit 3) (.add (.div (.mul (AE 9 11) (AE 9 11)) (.var 6)) (.lit 2))) (fwE 9 11))

/-- The top width `(K · 10A²fw + g · clP) / K³`. -/
def L0E : Ex :=
  .div (.add (.mul (.var 5) (.mul (.mul (.lit 10) (.mul (AE 9 11) (AE 9 11))) (fwE 9 11))) (.mul (.var 6) clPE))
    (.var 7)

/-- The top search (candidate `13`, state `14`). -/
def searchE : Ex := GroupV.searchE gs 13 14

/-- The top table (arguments `82`, `83`). -/
def tab : Ex := GroupV.tab gs

/-! ### The relation -/

variable {K g : ℕ}

theorem ok5 : topOk K g 5 K := ⟨le_rfl, rfl⟩
theorem ok6 : topOk K g 6 g := ⟨by omega, rfl⟩
theorem ok7 : topOk K g 7 (K ^ 3) := ⟨by omega, rfl⟩
theorem ok8 : topOk K g 8 (2 * g + 1) := ⟨by omega, rfl⟩
theorem ok9 : topOk K g 9 (K ^ g) := ⟨by omega, rfl⟩

theorem nodesE_bge : BGe 10 nodesE := by
  simp only [nodesE, AE, pow2, BGe, and_true, true_and, and_self]; omega

theorem msg_bge {va vb : ℕ} : BGe 16 (msg 16 11 va vb) := by
  simp only [msg, sel, kA, AE, hE, LLE, fwE, ME, TLE, PfE, PZE, PDE, mM, sM, pw, pwi, tE, dD, dZ, zv, z1E, z2E, cyE,
    ccE, midMsg, faMsg, hat, ibMsg, ifEq, eqE, pow2, nprod, nsum, BGe, and_true, true_and, and_self] <;> omega

theorem mul_LS : NLS (topOk K g) (fun x => ∀ k, ¬ topOk K g x k) (mulNEx 16 10 11) (mulNEx 16 10 11) := by
  have hnb : ∀ x, 16 ≤ x → ∀ k, ¬ topOk K g x k := fun x hx => topOk_nb (by omega)
  have m1 : BGe 16 (msg 16 11 16 17) := msg_bge
  have m2 : BGe 16 (msg 16 11 17 16) := msg_bge
  refine ⟨LSB.refl_ge hnb _ ?_, LSB.refl_ge hnb _ ?_, LSB.refl_ge hnb _ ?_, LSB.refl_ge hnb _ ?_,
    LSB.refl_ge hnb _ ?_⟩ <;>
  simp only [mulNEx, sel, kA, AE, hE, LLE, fwE, ME, TLE, PfE, PZE, PDE, mM, sM, pw, pwi, tE, dD, dZ, zv, z1E, z2E,
    cyE, ccE, lnk, cE, posE, faW, jE, dgE, cW, xBit, nBit, bitRd, ifEq, eqE, pow2, nprod, nsum, BGe, m1, m2,
    and_true, true_and, and_self] <;> omega

/-- The clusters with `g` in variable `6`. -/
theorem clχE_LS : LS (topOk K g) (Ex.clχE g) clχE := by
  have h6 : topOk K g 6 g := ok6
  have hnb : ∀ x, 10 ≤ x → ∀ k, ¬ topOk K g x k := fun x hx => topOk_nb hx
  simp only [Ex.clχE, clχE, sel, kA, AE, pow2]
  repeat ls_step

theorem coarsen_LS : NLS (topOk K g) (fun x => ∀ k, ¬ topOk K g x k) (CoarsenEx.nex (Ex.clPc g))
    (CoarsenEx.nex clPc) :=
  _root_.Factoring.Aux.coarsen_LS 16 26 10 mul_LS (LSB.refl_ge (fun x hx => topOk_nb hx) _ nodesE_bge) clχE_LS
    (fun x hx => topOk_nb (by omega)) (fun x hx => topOk_nb (by omega))

/-- **The top width with its literals in variables.** -/
theorem L0E_LS : LS (topOk K g) (Ex.L0E K g) L0E := by
  have h5 : topOk K g 5 K := ok5
  have h6 : topOk K g 6 g := ok6
  have h7 : topOk K g 7 (K ^ 3) := ok7
  have hnb : ∀ x, 10 ≤ x → ∀ k, ¬ topOk K g x k := fun x hx => topOk_nb hx
  simp only [Ex.L0E, L0E, Ex.clPE, clPE, AE, fwE, LLE, pow2]
  repeat ls_step

/-- **The top search with its literals in variables.** -/
theorem searchE_LS : LS (topOk K g) (GroupEx.searchE (gsTop K g) 13 14) searchE :=
  GroupV.searchE_LS (gsTop K g) (E' := CoarsenEx.nex clPc) coarsen_LS ok5 ok6 ok8 ok9
    (fun x hx => topOk_nb (by simp only [gsTop] at hx; omega)) (topOk_nb (by simp only [gsTop]; omega))
    (topOk_nb (by omega)) (topOk_nb (by omega))

/-- **The top table with its literals in variables.** -/
theorem tab_LS : LS (topOk K g) (GroupEx.tab (gsTop K g)) tab :=
  GroupV.tab_LS (gsTop K g) (E' := CoarsenEx.nex clPc) coarsen_LS ok5 ok6
    (fun x hx => topOk_nb (by simp only [gsTop] at hx; omega))

/-! ### Variable bounds -/

theorem coarsen_vb1000 : (CoarsenEx.nex (Ex.clPc 0)).VB 1000 := by
  have hm := mul_vb (u := 16) (vm := 10) (vs := 11) (by omega) (by omega) (by omega)
  have hM : (mulNEx 16 10 11).VB 1000 :=
    ⟨VB_mono (by omega) _ hm.1, VB_mono (by omega) _ hm.2.1, VB_mono (by omega) _ hm.2.2.1,
      VB_mono (by omega) _ hm.2.2.2.1, VB_mono (by omega) _ hm.2.2.2.2⟩
  exact coarsen_vb (P := Ex.clPc 0) hM
    (by simp only [Ex.clPc, nodesE, AE, pow2, VB, and_true, true_and, and_self]; omega)
    (by simp only [Ex.clPc, Ex.clχE, sel, kA, AE, pow2, VB, and_true, true_and, and_self]; omega)
    (by simp only [Ex.clPc]; omega) (by simp only [Ex.clPc]; omega) (by simp only [Ex.clPc]; omega)

theorem searchE_vb : VB 1000 searchE :=
  LS.VB (searchE_LS (K := 0) (g := 0))
    (group_search_vb (S := gsTop 0 0) (t := 1000) coarsen_vb1000 (by simp only [gsTop]; omega)
      (by simp only [gsTop]; omega) (by simp only [gsTop]; omega) (by simp only [gsTop]; omega)
      (vx := 13) (vs := 14) (by omega) (by omega))
    (fun _ _ h => by have := topOk_lt h; omega)

theorem tab_vb : VB 1000 tab :=
  LS.VB (tab_LS (K := 0) (g := 0))
    (group_tab_vb (S := gsTop 0 0) (t := 1000) coarsen_vb1000 (by simp only [gsTop]; omega)
      (by simp only [gsTop]; omega) (by simp only [gsTop]; omega) (by simp only [gsTop]; omega))
    (fun _ _ h => by have := topOk_lt h; omega)

theorem L0E_vb : VB 1000 L0E := by
  simp only [L0E, clPE, AE, fwE, LLE, pow2, VB, and_true, true_and, and_self]; omega

end TopV

/-! ### Setting the top's literal variables -/

/-- The expressions of `topVals K (3 K^8)` from `K` in scalar `q` (entries `0, 1, 10, 4, 5` of `lvlExs q`). -/
def topExs (q : ℕ) : List Ex :=
  [.var q, GEx q, nprod 999 (.lit 3) (.var q), .add (.mul (.lit 2) (GEx q)) (.lit 1), nprod 999 (GEx q) (.var q)]

/-- **Sets the top's literal variables `5 … 9`** from `K` in scalar `q`. -/
def topSet (q : ℕ) : Cmd := setBlock 5 (topExs q)

theorem topExs_spec {q K V : ℕ} (hV : VFacts K V) (hq : q ≠ 999) :
    ∀ i (hi : i < (topExs q).length) (hi' : i < (topVals K (3 * K ^ 8)).length) (σ : ℕ → ℕ) (A : ℕ → ℕ → ℕ),
      σ q = K → eval σ A (topExs q)[i] = (topVals K (3 * K ^ 8))[i] ∧ Bdd V σ A (topExs q)[i] := by
  intro i hi _ σ A hσ
  rcases i with _ | _ | _ | _ | _ | i
  · exact lvlExs_spec hV hq 0 (by simp [lvlExs]) (by simp [lvlVals]) σ A hσ
  · exact lvlExs_spec hV hq 1 (by simp [lvlExs]) (by simp [lvlVals]) σ A hσ
  · exact lvlExs_spec hV hq 10 (by simp [lvlExs]) (by simp [lvlVals]) σ A hσ
  · exact lvlExs_spec hV hq 4 (by simp [lvlExs]) (by simp [lvlVals]) σ A hσ
  · exact lvlExs_spec hV hq 5 (by simp [lvlExs]) (by simp [lvlVals]) σ A hσ
  · exact absurd hi (by simp [topExs])

/-- **`topSet`**: with `K` in scalar `q` (`q < 5` or `10 ≤ q`, `q < 999`), the scalars `5 … 9` hold
`topVals K (3 K^8)`, every other scalar below `1000` and every array is kept, and the cost is at most
`5 · ((64 (lvlV K + 1)^3)^5 + 2) + 1`. -/
theorem topSet_spec {q K : ℕ} (st : St) (hK : st.sc q = K) (hq : q < 5 ∨ 10 ≤ q) (hq9 : q < 999) :
    (∀ i (hi : i < 5), (Cmd.run (topSet q) st).1.sc (5 + i) = (topVals K (3 * K ^ 8))[i]) ∧
      (∀ v k, topOk K (3 * K ^ 8) v k → (Cmd.run (topSet q) st).1.sc v = k) ∧
      (∀ y < 1000, (y < 5 ∨ 10 ≤ y) → (Cmd.run (topSet q) st).1.sc y = st.sc y) ∧
      (Cmd.run (topSet q) st).1.ar = st.ar ∧
      (Cmd.run (topSet q) st).2 ≤ 5 * ((64 * (lvlV K + 1) ^ 3) ^ 5 + 2) + 1 := by
  have hV := lvlV_facts K
  have hvb : ∀ e ∈ topExs q, VB 1000 e ∧ Ex.dp e ≤ 5 := by
    intro e he
    have hl : ∀ e ∈ topExs q, e ∈ lvlExs q := by
      intro e he; simp only [topExs, lvlExs, List.mem_cons, List.not_mem_nil, or_false] at he ⊢; tauto
    exact ⟨lvlExs_vb q hq9 e (hl e he), lvlExs_dp q e (hl e he)⟩
  have h := setBlock_spec q K ((64 * (lvlV K + 1) ^ 3) ^ 5) (topExs q) (topVals K (3 * K ^ 8)) 5 st rfl
    (by simp [topExs]) (by simpa [topExs] using hq) (by omega) hK
    (fun i hi hi' => ⟨(hvb _ (List.getElem_mem hi)).1, fun σ A hσ => by
      obtain ⟨e1, b1⟩ := topExs_spec hV (by omega) i hi hi' σ A hσ
      exact ⟨e1, cost_le5 b1 (hvb _ (List.getElem_mem hi)).2⟩⟩)
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨fun i hi => h1 i hi, blockOk_holds (fun i hi => h1 i hi), fun y hy hy' => h2 y hy (by simpa [topExs] using hy'),
    h3, h4⟩

end Factoring.Aux
