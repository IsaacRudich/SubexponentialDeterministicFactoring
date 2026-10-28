/-
The top of the chain: the multiplication network (`mul_rep`), its clusters (`clusterNet`, by `coarsen_rep`),
the grouping into the top clique (`group_rep`), and the whole chain below it (`deep_rep`).

Variables: `0` = n, `2` = k (the driver's); `10` the modulus, `11` = s, `12` the top width, `13, 14` search
variables, `15` the top grouping code, `16 …` the multiplication network's arguments, `26 …` the clusters'
arguments, `82, 83` the top table's arguments, `100 …` the chain.

* `sOf n` (the parameter `s` of the multiplication network, `n ≤ pL s · pL s`), `sE`;
* `clχE` (the clusters as an expression), `topE`; **`top_rep`**: `topE` represents
  `deepMult · #{d ∣ N : d / 2^k = x}`.

Not an audit surface.
-/
module

public import FactoringAux.EngineDeepEx
public import FactoringAux.EngineMulVar
public import FactoringAux.Cluster

@[expose] public section

namespace Factoring.Aux

open Finset Ex MulEx

/-! ### The parameter `s` -/

/-- One step of the search for `s`. -/
def sStep (n : ℕ) (_ s : ℕ) : ℕ := if 2 ^ (4 * s + 2) < n then s + 1 else s

/-- The least `s` with `n ≤ 2^(4s+2) = pL s · pL s` (found in `n` steps). -/
def sOf (n : ℕ) : ℕ := iterF (sStep n) 0 n

theorem pL_sq (s : ℕ) : pL s * pL s = 2 ^ (4 * s + 2) := by
  unfold pL; rw [← pow_add]; congr 1; ring

theorem sOf_inv (n : ℕ) : ∀ j, n ≤ 2 ^ (4 * iterF (sStep n) 0 j + 2) ∨ iterF (sStep n) 0 j = j
  | 0 => Or.inr rfl
  | j + 1 => by
      have ih := sOf_inv n j
      show n ≤ 2 ^ (4 * sStep n j (iterF (sStep n) 0 j) + 2) ∨ sStep n j (iterF (sStep n) 0 j) = j + 1
      generalize iterF (sStep n) 0 j = X at ih ⊢
      unfold sStep
      split_ifs with h' <;> omega

theorem sOf_spec (n : ℕ) : n ≤ pL (sOf n) * pL (sOf n) := by
  rw [pL_sq]
  rcases sOf_inv n n with h | h
  · exact h
  · unfold sOf; rw [h]
    calc n ≤ 2 ^ n := (Nat.lt_two_pow_self).le
      _ ≤ 2 ^ (4 * n + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)

namespace Ex

/-- `sOf n` (`n = var 0`), with loop variables `13`, `14`, `15`. -/
def sE : Ex := .iter 13 14 (.var 0) (.lit 0)
  (.ifLt (pow2 15 (.add (.mul (.lit 4) (.var 14)) (.lit 2))) (.var 0) (.add (.var 14) (.lit 1)) (.var 14))

end Ex

theorem eval_sE {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ} : eval σ A sE = sOf (σ 0) := by
  rw [sE, eval_iter]
  show iterF _ 0 (σ 0) = _
  unfold sOf
  congr 1
  funext j s
  rw [eval_ifLt', eval_pow2]
  simp only [Ex.eval]
  have e14 : Function.update (Function.update σ 13 j) 14 s 14 = s := by simp
  have e0 : Function.update (Function.update σ 13 j) 14 s 0 = σ 0 := by simp
  simp only [e14, e0]
  rfl

/-! ### The clusters -/

theorem enum_faP {A : ℕ} (r : Fin A) : (MG.enum A (.faP r) : ℕ) = r := by
  simp [MG.enum, MG.sumEquiv, MG.toSum]
theorem enum_faQ {A : ℕ} (r : Fin A) : (MG.enum A (.faQ r) : ℕ) = A + r := by
  simp [MG.enum, MG.sumEquiv, MG.toSum]
theorem enum_mid {A : ℕ} (r : Fin A) : (MG.enum A (.mid r) : ℕ) = A + (A + r) := by
  simp [MG.enum, MG.sumEquiv, MG.toSum]
theorem enum_ib {A : ℕ} (r : Fin A) : (MG.enum A (.ib r) : ℕ) = A + (A + (A + r)) := by
  simp [MG.enum, MG.sumEquiv, MG.toSum]
theorem enum_carry {A : ℕ} (r : Fin (A * A)) : (MG.enum A (.carry r) : ℕ) = A + (A + (A + (A + r))) := by
  simp [MG.enum, MG.sumEquiv, MG.toSum]

namespace Ex

/-- The cluster of node `var 16` (the multiplication network's nodes; `s` in `var 11`). -/
def clχE (g : ℕ) : Ex :=
  sel 16 11 16 (.div (.mul (.var 16) (.lit g)) (AE 16 11))
    (.div (.mul (.sub (.var 16) (kA 16 11 1)) (.lit g)) (AE 16 11))
    (.div (.mul (.sub (.var 16) (kA 16 11 2)) (.lit g)) (AE 16 11))
    (.div (.mul (.sub (.var 16) (kA 16 11 3)) (.lit g)) (AE 16 11))
    (.div (.mul (.sub (.var 16) (kA 16 11 4)) (.lit g)) (.mul (AE 16 11) (AE 16 11)))

/-- The number of nodes of the multiplication network. -/
def nodesE : Ex := .add (AE 16 11) (.add (AE 16 11) (.add (AE 16 11) (.add (AE 16 11) (.mul (AE 16 11) (AE 16 11)))))

/-- The clustering data. -/
def clPc (g : ℕ) : CP := ⟨16, 26, 10, mulNEx 16 10 11, nodesE, clχE g⟩

/-- The top group step. -/
def gsTop (K g : ℕ) : GS := ⟨26, 10, 15, 12, g, K, CoarsenEx.nex (clPc g)⟩

/-- `clP s g`. -/
def clPE (g : ℕ) : Ex :=
  .add (.mul (.mul (.mul (.lit 7) (.add (.div (AE 9 11) (.lit g)) (.lit 2))) (AE 9 11)) (fwE 9 11))
    (.mul (.mul (.lit 3) (.add (.div (.mul (AE 9 11) (AE 9 11)) (.lit g)) (.lit 2))) (fwE 9 11))

/-- The top width `(K · 10A²fw + g · clP) / K³`. -/
def L0E (K g : ℕ) : Ex :=
  .div (.add (.mul (.lit K) (.mul (.mul (.lit 10) (.mul (AE 9 11) (AE 9 11))) (fwE 9 11))) (.mul (.lit g) (clPE g)))
    (.lit (K ^ 3))

/-- The whole count modulo the modulus in `var 10`. -/
def topE (K0 ℓ : ℕ) : Ex :=
  .lett 11 sE (.lett 12 (L0E (Kb K0 ℓ) (Gs K0 ℓ))
    (.lett 15 (GroupEx.searchE (gsTop (Kb K0 ℓ) (Gs K0 ℓ)) 13 14)
      (deepEx K0 ℓ 100 10 12 82 83 (GroupEx.tab (gsTop (Kb K0 ℓ) (Gs K0 ℓ))))))

end Ex

/-- The top width. -/
def Ltop (K g s : ℕ) : ℕ := (K * (10 * (pA s * pA s) * fw s) + g * clP s g) / K ^ 3

variable {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ}

theorem eval_L0E {K g s : ℕ} (h : σ 11 = s) : eval σ A (L0E K g) = Ltop K g s := by
  simp only [L0E, clPE, Ex.eval, eval_AE h, eval_fwE h, Ltop, clP]

theorem eval_nodesE {s : ℕ} (h : σ 11 = s) : eval σ A nodesE = mulNodes s := by
  simp only [nodesE, Ex.eval, eval_AE h, mulNodes]

/-- The clusters' hypotheses. -/
theorem clusterHyp {m s n k g : ℕ} {σ₀ : ℕ → ℕ} (hm : 1 < m) (hg : 0 < g) (h0 : σ₀ 10 = m) (hs : σ₀ 11 = s)
    (hn : σ₀ 0 = n) (hk : σ₀ 2 = k) (hkn : k ≤ n) (hnL : n ≤ pL s * pL s) :
    CoarsenHyp m 13 σ₀ A (clPc g) (mulNet s (ZMod m) (numCells (A 0) 1 n) k (numCells (A 1) k (n - k)))
      (mulCoding s m (numCells (A 0) 1 n) k (numCells (A 1) k (n - k)))
      (fun a => clMG s g hg ((MG.enum (pA s)).symm a)) where
  rep := mul_rep hm h0 hs hn hk hkn hnL (show 10 < 13 by norm_num) (show 11 < 13 by norm_num) (by norm_num)
    (show 13 ≤ 16 by norm_num)
  hg := by have := pA_pos s; show 0 < pA s + _; omega
  gE σ hσ := eval_nodesE (by rw [hσ 11 (by norm_num), hs])
  χE σ hσ a ha := by
    have h11 : σ 11 = s := by rw [hσ 11 (by norm_num), hs]
    show eval σ A (clχE g) = _
    obtain ⟨i, rfl⟩ := (MG.enum (pA s)).surjective a
    rw [Equiv.symm_apply_apply]
    replace ha : σ 16 = MG.enum (pA s) i := ha
    cases i with
    | faP r =>
        rw [clχE, eval_sel_faP h11 r.2 (by rw [ha, enum_faP])]
        simp only [Ex.eval, eval_AE h11, ha, enum_faP, clMG]
    | faQ r =>
        rw [clχE, eval_sel_faQ h11 r.2 (by rw [ha, enum_faQ])]
        simp only [Ex.eval, eval_AE h11, eval_kA h11, ha, enum_faQ, clMG]; congr 2; omega
    | mid r =>
        rw [clχE, eval_sel_mid h11 r.2 (by rw [ha, enum_mid])]
        simp only [Ex.eval, eval_AE h11, eval_kA h11, ha, enum_mid, clMG]; congr 2; omega
    | ib r =>
        rw [clχE, eval_sel_ib h11 r.2 (by rw [ha, enum_ib])]
        simp only [Ex.eval, eval_AE h11, eval_kA h11, ha, enum_ib, clMG]; congr 2; omega
    | carry r =>
        rw [clχE, eval_sel_carry h11 (by rw [ha, enum_carry])]
        simp only [Ex.eval, eval_AE h11, eval_kA h11, ha, enum_carry, clMG]; congr 2; omega
  hu := by show 13 ≤ 16; norm_num
  hw := by show 16 + 4 ≤ 26; norm_num
  hm := hm

/-- **The whole count**: `topE` represents `deepMult · #{d ∣ N : d / 2^k = x}` modulo `m` (in `var 10`). -/
theorem top_rep (K0 ℓ : ℕ) (hK : 2 ≤ K0) {m n k : ℕ} (hm : 1 < m) (h10 : σ 10 = m) (hn : σ 0 = n) (hk : σ 2 = k)
    (hkn : k ≤ n) (hN1 : 1 ≤ numCells (A 0) 1 n) :
    ZR m (eval σ A (topE K0 ℓ))
      ((deepMult K0 ℓ (Ltop (Kb K0 ℓ) (Gs K0 ℓ) (sOf n)) : ZMod m) *
        (((numCells (A 0) 1 n).divisors.filter (fun d => d / 2 ^ k = numCells (A 1) k (n - k))).card : ZMod m)) := by
  set K := Kb K0 ℓ
  set g := Gs K0 ℓ
  set s := sOf n
  set L := Ltop K g s
  set N := numCells (A 0) 1 n
  set x := numCells (A 1) k (n - k)
  have hK2 : 2 ≤ K := Kb_ge K0 hK ℓ
  have hK0 : 0 < K := by omega
  have hg : 0 < g := by show 0 < 3 * K ^ 8; positivity
  have hnL : n ≤ pL s * pL s := sOf_spec n
  rw [topE, eval_lett, eval_sE, hn]
  set σ1 := Function.update σ 11 s
  rw [eval_lett, eval_L0E (s := s) (by simp [σ1])]
  set σ2 := Function.update σ1 12 L
  have H2 := clusterHyp (A := A) (σ₀ := σ2) hm hg (by simp [σ2, σ1, h10]) (by simp [σ2, σ1]) (by simp [σ2, σ1, hn])
    (by simp [σ2, σ1, hk]) hkn hnL
  have hr2 := coarsen_rep H2 (show 10 < 13 by norm_num)
  set CN := clusterNet s (ZMod m) N k x g hg
  rw [eval_lett, GroupEx.eval_searchE (S := gsTop K g) (L := L) hK0 hg hm hr2 (show 10 < 13 by norm_num)
    (show 12 < 13 by norm_num) (show 13 ≤ 13 by norm_num) (show 13 ≤ 14 by norm_num) (show 13 ≤ 15 by norm_num)
    (show (13 : ℕ) ≠ 14 by norm_num) (show (13 : ℕ) ≠ 15 by norm_num) (show (14 : ℕ) ≠ 15 by norm_num)
    (show 13 < 26 by norm_num) (show 14 < 26 by norm_num) (show 15 < 26 by norm_num) (show σ2 12 = L by simp [σ2])
    (Ag.refl _ _)]
  set xf := firstGood (okG CN K L hK0) (K ^ g) (K ^ g)
  set σ3 := Function.update σ2 15 xf
  have a3 : Ag 13 σ2 σ3 := (Ag.refl 13 σ2).upd (by norm_num) xf
  have H3 := clusterHyp (A := A) (σ₀ := σ3) hm hg (by simp [σ3, σ2, σ1, h10]) (by simp [σ3, σ2, σ1])
    (by simp [σ3, σ2, σ1, hn]) (by simp [σ3, σ2, σ1, hk]) hkn hnL
  have hr3 := (coarsen_rep H3 (show 10 < 13 by norm_num)).mono (show 13 ≤ 16 by norm_num)
  have hT := GroupEx.group_rep (S := gsTop K g) (x := xf) (L := L) hK0 hg hm hr3 (show 10 < 16 by norm_num)
    (show 15 < 16 by norm_num) (show 12 < 16 by norm_num) (show 16 ≤ 26 by norm_num) (show σ3 15 = xf by simp [σ3])
    (show σ3 12 = L by simp [σ3, σ2])
  set Ttop : Clique (ZMod m) (Kb K0 ℓ) L := (CN.coarsen (chiOf K g xf hK0)).toClique L
  have hd : ZR m (eval σ3 A (deepEx K0 ℓ 100 10 12 82 83 (GroupEx.tab (gsTop K g)))) (deepVal K0 hK ℓ L Ttop) :=
    deep_rep K0 hK hm ℓ 100 16 10 12 82 83 _ L Ttop σ3 hT (by simp [σ3, σ2, σ1, h10]) (by simp [σ3, σ2])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) σ3 (Ag.refl _ _)
  rw [deepVal_eq K0 hK ℓ L Ttop] at hd
  -- the value of the top clique
  obtain ⟨x0, hx0, hok⟩ := good_exists CN (clP s g) (10 * (pA s * pA s) * fw s) (clusterNet_fits s _ N k x g hg)
    (clusterNet_total_le s _ N k x g hg) hK2 rfl
  have hspec := firstGood_spec (okG CN K L hK0) (le_refl (K ^ g)) ⟨x0, hx0, hok⟩
  have hNlt : N < 2 ^ (pL s * pL s) :=
    lt_of_lt_of_le (numCells_lt _ _ _) (Nat.pow_le_pow_right (by norm_num) hnL)
  rw [okG_value CN hK0 hspec.2, clusterNet_value s _ N k x g hg hN1 hNlt] at hd
  exact hd

end Factoring.Aux
