/-
The uniform engine: a clique table held in array `3`, and the expression reading it.

Entry `(γ, Q)` of a `(K, L)`-clique table (`γ < K`, `Q < 2^(L·K)` the code of the other strings) is held, as the
residue `val`, at cell `3 (γ + K Q) + par` of array `3`.  `rdTE` reads it back for any `Q` (reduced modulo
`2^(L·K)`: the table only looks at the low `L·K` bits), so it represents the table (`TRep`).

* `Holds`, `thetaOf_mod`, `rdTE`, **`rdTE_rep`**.

Not an audit surface.
-/
module

public import FactoringAux.UniFill
public import FactoringAux.EngineDeepEx

@[expose] public section

namespace Factoring.Aux

open Finset Ex

/-- Array `3` holds the table `T` at slot `par`. -/
def Holds {m K L : ℕ} (A : ℕ → ℕ → ℕ) (par : ℕ) (T : Clique (ZMod m) K L) : Prop :=
  ∀ γ < K, ∀ Q < 2 ^ (L * K), A 3 (3 * (γ + K * Q) + par) = (tabK T γ Q).val

theorem Holds.congr {m K L par : ℕ} {A A' : ℕ → ℕ → ℕ} {T : Clique (ZMod m) K L} (h : Holds A par T)
    (hA : ∀ x, x % 3 = par → A' 3 x = A 3 x) (hpar : par < 3) : Holds A' par T := fun γ hγ Q hQ => by
  rw [hA _ (by omega), h γ hγ Q hQ]

theorem thetaOf_mod (L K Q : ℕ) : (thetaOf L (Q % 2 ^ (L * K)) : Fin K → Bits L) = thetaOf L Q := by
  funext γ'
  simp only [thetaOf]
  rw [← bdec_mod L (Q % 2 ^ (L * K) / 2 ^ (L * γ')), ← bdec_mod L (Q / 2 ^ (L * γ'))]
  congr 1
  have hK : L * K = L * γ' + L * (K - γ') := by
    rw [← mul_add]; congr 1; have := γ'.2; omega
  rw [hK, pow_add, Nat.mod_mul_right_div_self]
  refine Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 ?_)
  have : 1 ≤ K - γ' := by have := γ'.2; omega
  nlinarith

/-- The table in array `3` read at `(var vγ, var vΘ)` (node count in `vK`, width in `vL`, slot in `vpar`;
`x` the scratch of the power). -/
def rdTE (vK vL vpar vγ vΘ x : ℕ) : Ex :=
  .rd 3 (.add (.mul (.lit 3) (.add (.var vγ) (.mul (.var vK)
    (.mod (.var vΘ) (pow2 x (.mul (.var vL) (.var vK))))))) (.var vpar))

theorem eval_rdTE {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ} (vK vL vpar vγ vΘ x : ℕ) :
    eval σ A (rdTE vK vL vpar vγ vΘ x) =
      A 3 (3 * (σ vγ + σ vK * (σ vΘ % 2 ^ (σ vL * σ vK))) + σ vpar) := by
  simp only [rdTE, Ex.eval, eval_pow2]

/-- **The table read back** represents the clique. -/
theorem rdTE_rep {m K L par BT vK vL vpar vγ vΘ x : ℕ} (hm : 1 < m) {T : Clique (ZMod m) K L}
    {A : ℕ → ℕ → ℕ} (hH : Holds A par T) {σ₀ : ℕ → ℕ} (hK : σ₀ vK = K) (hL : σ₀ vL = L) (hp : σ₀ vpar = par)
    (h1 : vK < BT) (h2 : vL < BT) (h3 : vpar < BT) :
    TRep m BT σ₀ A vγ vΘ (rdTE vK vL vpar vγ vΘ x) T := by
  intro σ hσ γ Q hγ hQ
  have : NeZero m := ⟨by omega⟩
  rw [eval_rdTE, hσ vK h1, hσ vL h2, hσ vpar h3, hK, hL, hp, hγ, hQ]
  have hlt : Q % 2 ^ (L * K) < 2 ^ (L * K) := Nat.mod_lt _ (by positivity)
  rw [hH γ γ.2 _ hlt, tabK, dif_pos γ.2, thetaOf_mod]
  exact ⟨ZMod.val_lt _, ZMod.natCast_zmod_val _⟩

end Factoring.Aux
