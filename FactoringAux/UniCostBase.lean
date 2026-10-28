/-
The cost of the uniform counting command: generic tools.

* `Bdd_mono`: value bounds are monotone in the bound; `DecV.mono`, `LevelReq.mono`, `BruteReq.mono`,
  `DeepReq.mono`, `TopReq.mono`: so are the requirements.
* `Wv V = 4 V²` (the bound used for every expression: table indices `3 K 2^(L K)` and table sizes `K 2^(L K)` exceed
  `V`), `PB V = (64 (Wv V + 1)^3)^100` (the cost of one expression of depth `≤ 100`), `YB V = (Wv V + 1) · PB V`;
  **`cost_le_PB`**.
* `seq_cost`: the cost of a `seq`.

Not an audit surface.
-/
module

public import FactoringAux.UniValSpec
public import FactoringAux.EngineCostMain
public import FactoringAux.EngineCostRate
public import FactoringAux.EngineVBRd

@[expose] public section

namespace Factoring.Aux

open Factoring.Aux.Copied Factoring.Aux.Copied.PLib Ex Uni Finset SB

namespace UCost

/-! ### Monotonicity -/

theorem Bdd_mono {V W : ℕ} (hVW : V ≤ W) (A : ℕ → ℕ → ℕ) : ∀ (e : Ex) (σ : ℕ → ℕ), Bdd V σ A e → Bdd W σ A e
  | .lit _, _, h => le_trans h hVW
  | .var _, _, h => le_trans h hVW
  | .rd _ i, σ, h => ⟨Bdd_mono hVW A i σ h.1, le_trans h.2 hVW⟩
  | .add e f, σ, h => ⟨Bdd_mono hVW A e σ h.1, Bdd_mono hVW A f σ h.2.1, le_trans h.2.2 hVW⟩
  | .sub e f, σ, h => ⟨Bdd_mono hVW A e σ h.1, Bdd_mono hVW A f σ h.2⟩
  | .mul e f, σ, h => ⟨Bdd_mono hVW A e σ h.1, Bdd_mono hVW A f σ h.2.1, le_trans h.2.2 hVW⟩
  | .div e f, σ, h => ⟨Bdd_mono hVW A e σ h.1, Bdd_mono hVW A f σ h.2⟩
  | .mod e f, σ, h => ⟨Bdd_mono hVW A e σ h.1, Bdd_mono hVW A f σ h.2⟩
  | .ifLt e f u v, σ, h => by
      obtain ⟨h1, h2, h3⟩ := h
      refine ⟨Bdd_mono hVW A e σ h1, Bdd_mono hVW A f σ h2, ?_⟩
      split_ifs at h3 ⊢
      · exact Bdd_mono hVW A u σ h3
      · exact Bdd_mono hVW A v σ h3
  | .lett _ e b, σ, h => ⟨Bdd_mono hVW A e σ h.1, Bdd_mono hVW A b _ h.2⟩
  | .sum _ n m b, σ, h => ⟨Bdd_mono hVW A n σ h.1, Bdd_mono hVW A m σ h.2.1,
      fun j hj => Bdd_mono hVW A b _ (h.2.2.1 j hj), fun j hj => le_trans (h.2.2.2 j hj) hVW⟩
  | .prod _ n m b, σ, h => ⟨Bdd_mono hVW A n σ h.1, Bdd_mono hVW A m σ h.2.1,
      fun j hj => Bdd_mono hVW A b _ (h.2.2.1 j hj), fun j hj => le_trans (h.2.2.2 j hj) hVW⟩
  | .blk _ e, σ, h => Bdd_mono hVW A e σ h
  | .iter _ _ n i b, σ, h => ⟨Bdd_mono hVW A n σ h.1, Bdd_mono hVW A i σ h.2.1,
      fun j hj => Bdd_mono hVW A b _ (h.2.2 j hj)⟩

theorem TBdd_mono {V W B : ℕ} {σ₀ : ℕ → ℕ} {A : ℕ → ℕ → ℕ} {vγ vΘ : ℕ} {T : Ex} {K : ℕ} (hVW : V ≤ W)
    (h : ∀ σ, Ag B σ₀ σ → σ vγ < K → σ vΘ ≤ W → Bdd V σ A T) : TBdd W B σ₀ A vγ vΘ T K :=
  fun σ hσ hγ hΘ => Bdd_mono hVW A T σ (h σ hσ hγ hΘ)

theorem DecV.mono {V W m lam : ℕ} (h : DecV V m lam) (hVW : V ≤ W) : DecV W m lam :=
  ⟨h.hm, h.hD.trans hVW, h.hjm.trans hVW, h.hmm.trans hVW, h.h64.trans hVW⟩

theorem LevelReq.mono {V W m K G lam : ℕ} (h : LevelReq V m K G lam) (hVW : V ≤ W) : LevelReq W m K G lam :=
  ⟨DecV.mono h.dec hVW, h.hS.trans hVW, h.hW.trans hVW, h.hC.trans hVW, h.hg4.trans hVW, h.hKg.trans hVW,
    h.hKG.trans hVW, h.hg1.trans hVW, h.hgrp.trans hVW, h.hLK.trans hVW, h.htot.trans hVW, h.hUE.trans hVW,
    h.hLn.trans hVW, h.hmult.trans hVW⟩

theorem BruteReq.mono {V W m K L : ℕ} (h : BruteReq V m K L) (hVW : V ≤ W) : BruteReq W m K L :=
  ⟨h.hm, h.mm.trans hVW, h.hK, h.KK.trans hVW, h.hLK.trans hVW, h.two.trans hVW⟩

theorem DeepReq.mono {V W m K0 : ℕ} (hVW : V ≤ W) : ∀ d L, DeepReq V m K0 d L → DeepReq W m K0 d L
  | 0, _, h => BruteReq.mono h hVW
  | d + 1, _, h => ⟨LevelReq.mono h.1 hVW, DeepReq.mono hVW d _ h.2⟩

theorem TopReq.mono {V W m K0 ℓ n : ℕ} (h : TopReq V m K0 ℓ n) (hVW : V ≤ W) : TopReq W m K0 ℓ n :=
  ⟨h.hm, h.mul.trans hVW, h.mm.trans hVW, h.hn.trans hVW, h.hL0.trans hVW, h.hKg.trans hVW, h.hKG.trans hVW,
    h.hgg.trans hVW, h.hg1.trans hVW, h.hgN.trans hVW, h.hWc.trans hVW, h.hclP.trans hVW, h.hgrp.trans hVW,
    h.hLK.trans hVW, DeepReq.mono hVW _ _ h.deep⟩

/-! ### The bounds -/

/-- The value bound of every expression. -/
def Wv (V : ℕ) : ℕ := 4 * V * V

/-- The cost bound of one expression. -/
def PB (V : ℕ) : ℕ := (64 * (Wv V + 1) ^ 3) ^ 100

/-- The unit of the cost bounds. -/
def YB (V : ℕ) : ℕ := (Wv V + 1) * PB V

theorem le_Wv {V : ℕ} : V ≤ Wv V := by
  unfold Wv; rcases Nat.eq_zero_or_pos V with h | h
  · subst h; rfl
  · nlinarith

theorem sq_le_Wv {V : ℕ} : V * V ≤ Wv V := by unfold Wv; nlinarith

theorem X_ge (V : ℕ) : 64 * (Wv V + 1) ^ 3 ≥ 64 * (Wv V + 1) := by
  have := Nat.le_self_pow (n := 3) (by norm_num) (Wv V + 1); omega

theorem PB_ge (V : ℕ) : 64 * (Wv V + 1) ^ 3 ≤ PB V := by
  unfold PB
  exact Nat.le_self_pow (by norm_num) _

theorem PB_ge' (V : ℕ) : 64 * (Wv V + 1) ≤ PB V := le_trans (X_ge V) (PB_ge V)

theorem PB_ge2 (V : ℕ) : 4096 * (Wv V + 1) ≤ PB V := by
  have hX := X_ge V
  have h1 : (64 * (Wv V + 1) ^ 3) ^ 2 ≤ PB V := by
    unfold PB; exact Nat.pow_le_pow_right (by omega) (by norm_num)
  have h2 : 4096 * (Wv V + 1) ≤ (64 * (Wv V + 1)) ^ 2 := by nlinarith
  exact le_trans h2 (le_trans (Nat.pow_le_pow_left hX 2) h1)

theorem PB_le_YB (V : ℕ) : PB V ≤ YB V := by unfold YB; exact Nat.le_mul_of_pos_left _ (by omega)

theorem W_le_YB (V : ℕ) : Wv V + 1 ≤ YB V := by
  unfold YB; exact Nat.le_mul_of_pos_right _ (by have := PB_ge' V; omega)

theorem YB_ge (V : ℕ) : 64 ≤ YB V := le_trans (by have := PB_ge' V; omega) (PB_le_YB V)

/-- **The cost of one expression** (values `≤ Wv V`, depth `≤ 100`). -/
theorem cost_le_PB {V : ℕ} {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ} {e : Ex} (hb : Bdd (Wv V) σ A e) (hd : Ex.dp e ≤ 100) :
    cost σ A e ≤ PB V :=
  (cost_le_of_Bdd A e σ hb).trans (Nat.pow_le_pow_right (by have := Nat.one_le_pow 3 (Wv V + 1) (by omega); omega) hd)

/-- The cost of the literal-setting commands. -/
theorem set_le_PB {V K : ℕ} (h : lvlV K ≤ Wv V) : 12 * ((64 * (lvlV K + 1) ^ 3) ^ 5 + 2) + 1 ≤ 15 * PB V := by
  have h1 : (64 * (lvlV K + 1) ^ 3) ^ 5 ≤ PB V := by
    unfold PB
    calc (64 * (lvlV K + 1) ^ 3) ^ 5 ≤ (64 * (Wv V + 1) ^ 3) ^ 5 :=
          Nat.pow_le_pow_left (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3)) 5
      _ ≤ _ := Nat.pow_le_pow_right (by have := Nat.one_le_pow 3 (Wv V + 1) (by omega); omega) (by norm_num)
  have := PB_ge' V
  omega

/-- The cost of a table fill. -/
theorem fill_le {V n C : ℕ} (hn : n ≤ Wv V) (hC : C ≤ PB V) : n * (C + 40 * n + 201) + 1 ≤ 3 * YB V := by
  have h1 : C + 40 * n + 201 ≤ 2 * PB V := by have := PB_ge2 V; omega
  have h2 : n * (C + 40 * n + 201) ≤ (Wv V + 1) * (2 * PB V) := Nat.mul_le_mul (by omega) h1
  have h3 : (Wv V + 1) * (2 * PB V) = 2 * YB V := by unfold YB; ring
  have := YB_ge V
  omega

/-- A loop of at most `Wv V` turns, each costing at most `k · YB^e`. -/
theorem loop_le {V b k e : ℕ} (hb : b ≤ Wv V) : b * (k * YB V ^ e + 1) + 1 ≤ (k + 2) * YB V ^ (e + 1) := by
  have hY := YB_ge V
  have hW := W_le_YB V
  have h1 : 1 ≤ YB V ^ e := Nat.one_le_pow _ _ (by omega)
  have h2 : b * (k * YB V ^ e + 1) ≤ YB V * ((k + 1) * YB V ^ e) :=
    Nat.mul_le_mul (by omega) (by nlinarith)
  have h3 : YB V * ((k + 1) * YB V ^ e) = (k + 1) * YB V ^ (e + 1) := by ring
  have h4 : 1 ≤ YB V ^ (e + 1) := Nat.one_le_pow _ _ (by omega)
  nlinarith

/-! ### Commands -/

theorem seq_cost (s t : Cmd) (st : St) :
    (Cmd.run (.seq s t) st).2 = (Cmd.run s st).2 + (Cmd.run t (Cmd.run s st).1).2 + 1 := rfl

theorem seq_le {s t : Cmd} {st : St} {a b : ℕ} (ha : (Cmd.run s st).2 ≤ a) (hb : (Cmd.run t (Cmd.run s st).1).2 ≤ b) :
    (Cmd.run (.seq s t) st).2 ≤ a + b + 1 := by rw [seq_cost]; omega

end UCost

end Factoring.Aux
