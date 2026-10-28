/-
Value bounds (`Ex.Bdd`) for the engine's builders: the predicates and generic lemmas.

* **`NBdd V B σ₀ A v E g`**: every value met by the five expressions of a network is at most `V`, for arguments
  `a < g` (size), `a < g`, `z ≤ V` (weight), `a < b < g` (width), `a < b < g`, `z, q ≤ V` (factor functions).
  Each expression only needs the arguments it reads.
* **`TBdd V B σ₀ A vγ vΘ T K`**: the same for a table expression, at `γ < K`, `Θ ≤ V`.
* `NBdd.mono`, `NBdd.congr`, `TBdd.mono`, `TBdd.congr`: changing the context.
* Generic lemmas in namespace `SB` (`B_add`, `B_zmul`, `B_zprod`, `B_zsum`, `lt_zprod`, …) and values below `m` from a
  representation (`NRep.W_lt`, `NRep.l_lt`, `NRep.r_lt`).

Not an audit surface.
-/
module

public import FactoringAux.EngineGroupEx
public import FactoringAux.EngineMulBdd

@[expose] public section

namespace Factoring.Aux

open Finset Ex

/-- **Value bounds of a network's expressions** (each at the arguments it reads). -/
structure NBdd (V B : ℕ) (σ₀ : ℕ → ℕ) (A : ℕ → ℕ → ℕ) (v : NVars) (E : NEx) (g : ℕ) : Prop where
  sz : ∀ σ, Ag B σ₀ σ → σ v.a < g → Ex.Bdd V σ A E.sz
  W : ∀ σ, Ag B σ₀ σ → σ v.a < g → σ v.z ≤ V → Ex.Bdd V σ A E.W
  c : ∀ σ, Ag B σ₀ σ → σ v.a < σ v.b → σ v.b < g → Ex.Bdd V σ A E.c
  l : ∀ σ, Ag B σ₀ σ → σ v.a < σ v.b → σ v.b < g → σ v.z ≤ V → σ v.q ≤ V → Ex.Bdd V σ A E.l
  r : ∀ σ, Ag B σ₀ σ → σ v.a < σ v.b → σ v.b < g → σ v.z ≤ V → σ v.q ≤ V → Ex.Bdd V σ A E.r

/-- **Value bounds of a table expression.** -/
def TBdd (V B : ℕ) (σ₀ : ℕ → ℕ) (A : ℕ → ℕ → ℕ) (vγ vΘ : ℕ) (T : Ex) (K : ℕ) : Prop :=
  ∀ σ, Ag B σ₀ σ → σ vγ < K → σ vΘ ≤ V → Ex.Bdd V σ A T

theorem NBdd.mono {V B B' : ℕ} {σ₀ : ℕ → ℕ} {A : ℕ → ℕ → ℕ} {v : NVars} {E : NEx} {g : ℕ}
    (h : NBdd V B σ₀ A v E g) (hB : B ≤ B') : NBdd V B' σ₀ A v E g where
  sz σ hσ := h.sz σ (hσ.mono hB)
  W σ hσ := h.W σ (hσ.mono hB)
  c σ hσ := h.c σ (hσ.mono hB)
  l σ hσ := h.l σ (hσ.mono hB)
  r σ hσ := h.r σ (hσ.mono hB)

theorem NBdd.congr {V B : ℕ} {σ₀ σ₀' : ℕ → ℕ} {A : ℕ → ℕ → ℕ} {v : NVars} {E : NEx} {g : ℕ}
    (h : NBdd V B σ₀ A v E g) (hσ : Ag B σ₀ σ₀') : NBdd V B σ₀' A v E g where
  sz σ h' := h.sz σ fun y hy => (h' y hy).trans (hσ y hy)
  W σ h' := h.W σ fun y hy => (h' y hy).trans (hσ y hy)
  c σ h' := h.c σ fun y hy => (h' y hy).trans (hσ y hy)
  l σ h' := h.l σ fun y hy => (h' y hy).trans (hσ y hy)
  r σ h' := h.r σ fun y hy => (h' y hy).trans (hσ y hy)

theorem TBdd.mono {V B B' : ℕ} {σ₀ : ℕ → ℕ} {A : ℕ → ℕ → ℕ} {vγ vΘ : ℕ} {T : Ex} {K : ℕ}
    (h : TBdd V B σ₀ A vγ vΘ T K) (hB : B ≤ B') : TBdd V B' σ₀ A vγ vΘ T K :=
  fun σ hσ => h σ (hσ.mono hB)

theorem TBdd.congr {V B : ℕ} {σ₀ σ₀' : ℕ → ℕ} {A : ℕ → ℕ → ℕ} {vγ vΘ : ℕ} {T : Ex} {K : ℕ}
    (h : TBdd V B σ₀ A vγ vΘ T K) (hσ : Ag B σ₀ σ₀') : TBdd V B σ₀' A vγ vΘ T K :=
  fun σ h' => h σ fun y hy => (h' y hy).trans (hσ y hy)

/-! ### Values below `m` from a representation -/

section RepLt

variable {m vm B : ℕ} {σ₀ σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ} {v : NVars} {E : NEx} {g : ℕ}
  {N : Net (ZMod m) g} {κ : Coding N}

theorem NRep.W_lt (h : NRep m vm B σ₀ A v E N κ) (hσ : Ag B σ₀ σ) (a : Fin g) (ha : σ v.a = a)
    (hz : σ v.z < κ.s a) : Ex.eval σ A E.W < m :=
  (h.W σ hσ a ((κ.e a).symm ⟨σ v.z, hz⟩) ha (by simp)).1

theorem NRep.l_lt (h : NRep m vm B σ₀ A v E N κ) (hσ : Ag B σ₀ σ) (a b : Fin g) (hab : a < b) (ha : σ v.a = a)
    (hb : σ v.b = b) (hz : σ v.z < κ.s a) : Ex.eval σ A E.l < m :=
  (h.l σ hσ a b hab ((κ.e a).symm ⟨σ v.z, hz⟩) (σ v.q) ha hb (by simp) rfl).1

theorem NRep.r_lt (h : NRep m vm B σ₀ A v E N κ) (hσ : Ag B σ₀ σ) (a b : Fin g) (hab : a < b) (ha : σ v.a = a)
    (hb : σ v.b = b) (hz : σ v.z < κ.s b) : Ex.eval σ A E.r < m :=
  (h.r σ hσ a b hab ((κ.e b).symm ⟨σ v.z, hz⟩) (σ v.q) ha hb (by simp) rfl).1

end RepLt

/-! ### Generic lemmas -/

namespace SB

variable {V : ℕ} {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ}

theorem B_lit {k : ℕ} (h : k ≤ V) : Bdd V σ A (.lit k) := h
theorem B_var {x : ℕ} (h : σ x ≤ V) : Bdd V σ A (.var x) := h

theorem B_add {e f : Ex} (h1 : Bdd V σ A e) (h2 : Bdd V σ A f) (h3 : eval σ A e + eval σ A f ≤ V) :
    Bdd V σ A (.add e f) := ⟨h1, h2, h3⟩
theorem B_mul {e f : Ex} (h1 : Bdd V σ A e) (h2 : Bdd V σ A f) (h3 : eval σ A e * eval σ A f ≤ V) :
    Bdd V σ A (.mul e f) := ⟨h1, h2, h3⟩
theorem B_sub {e f : Ex} (h1 : Bdd V σ A e) (h2 : Bdd V σ A f) : Bdd V σ A (.sub e f) := ⟨h1, h2⟩
theorem B_div {e f : Ex} (h1 : Bdd V σ A e) (h2 : Bdd V σ A f) : Bdd V σ A (.div e f) := ⟨h1, h2⟩
theorem B_mod {e f : Ex} (h1 : Bdd V σ A e) (h2 : Bdd V σ A f) : Bdd V σ A (.mod e f) := ⟨h1, h2⟩
theorem B_lett {x : ℕ} {e b : Ex} (h1 : Bdd V σ A e) (h2 : Bdd V (Function.update σ x (eval σ A e)) A b) :
    Bdd V σ A (.lett x e b) := ⟨h1, h2⟩

theorem le_of_B {e : Ex} (h : Bdd V σ A e) : eval σ A e ≤ V := eval_le_of_Bdd A e σ h

theorem B_zmul {vm : ℕ} {e f : Ex} (h1 : Bdd V σ A e) (h2 : Bdd V σ A f) (hm : σ vm ≤ V)
    (h3 : eval σ A e * eval σ A f ≤ V) : Bdd V σ A (zmul vm e f) := ⟨⟨h1, h2, h3⟩, hm⟩

theorem B_zprod {vm x : ℕ} {n b : Ex} (hm : 0 < σ vm) (hmV : σ vm ≤ V) (h1 : 1 ≤ V) (hn : Bdd V σ A n)
    (hb : ∀ j < eval σ A n, Bdd V (Function.update σ x j) A b) : Bdd V σ A (zprod x n vm b) :=
  B_prod_mod hn hmV hm hmV h1 hb

theorem B_zsum {vm x : ℕ} {n b : Ex} (hm : 0 < σ vm) (hmV : σ vm ≤ V) (hn : Bdd V σ A n)
    (hb : ∀ j < eval σ A n, Bdd V (Function.update σ x j) A b) : Bdd V σ A (zsum x n vm b) :=
  B_sum_mod hn hmV hm hmV hb

theorem lt_zmul {vm : ℕ} {e f : Ex} (hm : 0 < σ vm) : eval σ A (zmul vm e f) < σ vm := by
  simp only [zmul, Ex.eval]; exact Nat.mod_lt _ hm

theorem lt_zsum {vm x : ℕ} {n b : Ex} (hm : 0 < σ vm) : eval σ A (zsum x n vm b) < σ vm := by
  simp only [zsum, Ex.eval, foldSum_eq]; exact Nat.mod_lt _ hm

theorem lt_zprod {vm x : ℕ} {n b : Ex} (hm : 1 < σ vm) : eval σ A (zprod x n vm b) < σ vm := by
  simp only [zprod, Ex.eval]
  rcases Nat.eq_zero_or_pos (eval σ A n) with h0 | h0
  · rw [h0]; exact hm
  · rw [foldProd_eq _ _ _ h0]; exact Nat.mod_lt _ (by omega)

theorem B_ifLt' {e f a b : Ex} (h1 : Bdd V σ A e) (h2 : Bdd V σ A f) (h3 : eval σ A e < eval σ A f → Bdd V σ A a)
    (h4 : eval σ A f ≤ eval σ A e → Bdd V σ A b) : Bdd V σ A (.ifLt e f a b) :=
  B_ifLt h1 h2 h3 fun h => h4 (by omega)

theorem B_ifEq' {e f a b : Ex} (h1 : Bdd V σ A e) (h2 : Bdd V σ A f) (h3 : eval σ A e = eval σ A f → Bdd V σ A a)
    (h4 : eval σ A e ≠ eval σ A f → Bdd V σ A b) : Bdd V σ A (ifEq e f a b) :=
  B_ifLt h1 h2 (fun h => h4 (by omega)) (fun h => B_ifLt h2 h1 (fun h' => h4 (by omega)) (fun h' => h3 (by omega)))

theorem B_nsum' {x : ℕ} {n b : Ex} {c : ℕ} (hn : Bdd V σ A n)
    (hb : ∀ j < eval σ A n, Bdd V (Function.update σ x j) A b ∧ eval (Function.update σ x j) A b ≤ c)
    (hV : eval σ A n * c ≤ V) : Bdd V σ A (nsum x n b) :=
  B_nsum hn (fun j hj => (hb j hj).1)
    (le_trans (Ex.sum_le_card_mul fun j hj => (hb j hj).2) hV)

theorem ifEq_le {e f a b : Ex} {c : ℕ} (ha : eval σ A a ≤ c) (hb : eval σ A b ≤ c) :
    eval σ A (ifEq e f a b) ≤ c := by
  rw [eval_ifEq]; split_ifs <;> assumption

theorem ifLt_le {e f a b : Ex} {c : ℕ} (ha : eval σ A a ≤ c) (hb : eval σ A b ≤ c) :
    eval σ A (.ifLt e f a b) ≤ c := by
  rw [eval_ifLt']; split_ifs <;> assumption

end SB

end Factoring.Aux
