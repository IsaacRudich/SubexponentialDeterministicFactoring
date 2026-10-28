/-
Groupings by codes, the first good grouping, and the chain of levels (mathematics for the counting expression).

* `chiOf K g x`: the grouping of code `x` (radix `K`); `okG`: a code is good ((G1) group sizes, every pair of groups
  sharing at most `L` bits); `firstGood`: the first good code (a fold); **`firstGood_spec`**; **`good_exists`**
  (Lemma 1); `okG_value`: a good grouping keeps the value.
* One level: `Umax`, `Lnext`, **`nextT`** (the smaller of the row and column networks, grouped by its first good
  code, written out), **`value_nextT`**, **`sum_nextT`** (`∑_c value = mult · value`).
* The chain: `Kb` (group counts from the bottom, `Kb (d+1) = (3 Kb(d)^8)²`), **`deepVal`** (the nested sums),
  **`deepVal_eq`**: `deepVal d L T = deepMult d L · T.value`.

Not an audit surface.
-/
module

public import FactoringAux.EngineGrid
public import FactoringAux.Lemma1

@[expose] public section

namespace Factoring.Aux

open Finset

variable {R : Type*} [CommRing R] {g K : ℕ}

/-- The grouping of a code (radix `K`). -/
def chiOf (K g x : ℕ) (hK : 0 < K) : Fin g → Fin K := fun a => ⟨x / K ^ (a : ℕ) % K, Nat.mod_lt _ hK⟩

theorem chiOf_code (hK : 0 < K) (χ : Fin g → Fin K) : chiOf K g (finFunctionFinEquiv χ) hK = χ := by
  funext a
  apply Fin.ext
  have := finFunctionFinEquiv_symm_apply_val (finFunctionFinEquiv χ) a
  rw [Equiv.symm_apply_apply] at this
  exact this.symm

/-- A good code: (G1) and every pair of groups sharing at most `L` bits. -/
def okG (N : Net R g) (K L : ℕ) (hK : 0 < K) (x : ℕ) : Prop :=
  (∀ γ : Fin K, K * (univ.filter (fun a => chiOf K g x hK a = γ)).card ≤ 2 * g) ∧
    ∀ γ γ' : Fin K, γ < γ' → (N.coarsen (chiOf K g x hK)).c γ γ' ≤ L

instance (N : Net R g) (K L : ℕ) (hK : 0 < K) : DecidablePred (okG N K L hK) := fun _ => by
  unfold okG; infer_instance

/-- One step of the search for the first good code (`S`: not found yet). -/
def fgStep (ok : ℕ → Prop) [DecidablePred ok] (S x s : ℕ) : ℕ := if s = S ∧ ok x then x else s

/-- The first good code below `n`, or `S` if none. -/
def firstGood (ok : ℕ → Prop) [DecidablePred ok] (S n : ℕ) : ℕ := iterF (fun x s => fgStep ok S x s) S n

theorem firstGood_inv (ok : ℕ → Prop) [DecidablePred ok] (S : ℕ) :
    ∀ k, k ≤ S → (firstGood ok S k = S ∧ ∀ x < k, ¬ ok x) ∨ (firstGood ok S k < k ∧ ok (firstGood ok S k))
  | 0, _ => Or.inl ⟨rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | k + 1, hk => by
      have ih := firstGood_inv ok S k (by omega)
      have hs : firstGood ok S (k + 1) = fgStep ok S k (firstGood ok S k) := rfl
      rw [hs]
      unfold fgStep
      rcases ih with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · by_cases hk' : ok k
        · rw [if_pos ⟨h1, hk'⟩]; exact Or.inr ⟨by omega, hk'⟩
        · rw [if_neg (fun h => hk' h.2)]
          exact Or.inl ⟨h1, fun x hx => by
            rcases Nat.lt_succ_iff_lt_or_eq.mp hx with hx | rfl
            · exact h2 x hx
            · exact hk'⟩
      · rw [if_neg (fun h => by omega)]
        exact Or.inr ⟨by omega, h2⟩

/-- **The first good code is good**, when some code below `n ≤ S` is. -/
theorem firstGood_spec (ok : ℕ → Prop) [DecidablePred ok] {S n : ℕ} (hn : n ≤ S) (h : ∃ x < n, ok x) :
    firstGood ok S n < n ∧ ok (firstGood ok S n) := by
  rcases firstGood_inv ok S n hn with ⟨_, h2⟩ | h'
  · obtain ⟨x, hx, hok⟩ := h; exact absurd hok (h2 x hx)
  · exact h'

/-- **Lemma 1 by codes**: a good code exists. -/
theorem good_exists (N : Net R g) (P0 U0 : ℕ) (hfit : N.Fits P0) (htot : N.total ≤ U0) (hK : 2 ≤ K)
    (hg : g = 3 * K ^ 8) : ∃ x < K ^ g, okG N K ((K * U0 + g * P0) / K ^ 3) (by omega) x := by
  obtain ⟨χ, h1, h2, -⟩ := Net.lemma1 N P0 hfit hK hg
  refine ⟨finFunctionFinEquiv χ, (finFunctionFinEquiv χ).2, ?_, ?_⟩
  · intro γ; rw [chiOf_code]; exact h1 γ
  · intro γ γ' hlt
    rw [chiOf_code]
    have := h2 γ γ' (ne_of_lt hlt)
    rw [Nat.le_div_iff_mul_le (by positivity)]
    calc (N.coarsen χ).c γ γ' * K ^ 3 = K ^ 3 * (N.coarsen χ).c γ γ' := by ring
      _ ≤ K * N.total + g * P0 := this
      _ ≤ K * U0 + g * P0 := by gcongr

theorem okG_value (N : Net R g) {L : ℕ} (hK : 0 < K) {x : ℕ} (h : okG N K L hK x) :
    ((N.coarsen (chiOf K g x hK)).toClique L).value = N.value :=
  Net.value_group N _ L h.2

/-! ### One level -/

/-- The bound (36) on the smaller total. -/
def Umax (G lam : ℕ) : ℕ := (12 * G ^ 3 * lam + 11 * G ^ 4 * lam + 24 * G ^ 4) / 12

/-- The label width of the next level. -/
def Lnext (K G lam : ℕ) : ℕ := (K * Umax G lam + G * (G ^ 3 * lam)) / K ^ 3

/-- The multiplier of one level. -/
def mult (G lam : ℕ) : ℕ := (tB lam + 1) ^ nonRects G * 2 ^ (tB lam * (rects G).card)

variable {m : ℕ}

/-- The next clique: the smaller of the row and the column network of the choice `c`, grouped by its first good
code, written out. -/
def nextT {G lam : ℕ} (K : ℕ) (hK : 0 < K) (T : Clique (ZMod m) (G * G) lam)
    (c : Fin ((tB lam + 1) ^ (G * G * (G * G)))) : Clique (ZMod m) K (Lnext K G lam) :=
  if (rowNet (toGrid T) (restrictC ((phiEquiv G (tB lam)).symm c))).total ≤
      (colNet (toGrid T) (restrictC ((phiEquiv G (tB lam)).symm c))).total then
    ((rowNet (toGrid T) (restrictC ((phiEquiv G (tB lam)).symm c))).coarsen
      (chiOf K G (firstGood (okG (rowNet (toGrid T) (restrictC ((phiEquiv G (tB lam)).symm c))) K
        (Lnext K G lam) hK) (K ^ G) (K ^ G)) hK)).toClique (Lnext K G lam)
  else
    ((colNet (toGrid T) (restrictC ((phiEquiv G (tB lam)).symm c))).coarsen
      (chiOf K G (firstGood (okG (colNet (toGrid T) (restrictC ((phiEquiv G (tB lam)).symm c))) K
        (Lnext K G lam) hK) (K ^ G) (K ^ G)) hK)).toClique (Lnext K G lam)

theorem total_le_Umax {G lam : ℕ} (T : GridClique (ZMod m) G lam) (ι : Choice G lam) {U : ℕ}
    (hU : U = min (rowNet T ι).total (colNet T ι).total) : U ≤ Umax G lam := by
  have := min_total T ι
  rw [← hU] at this
  unfold Umax
  rw [Nat.le_div_iff_mul_le (by norm_num)]
  linarith

theorem value_nextT {G lam : ℕ} (K : ℕ) (hK2 : 2 ≤ K) (hG : G = 3 * K ^ 8) (T : Clique (ZMod m) (G * G) lam)
    (c : Fin ((tB lam + 1) ^ (G * G * (G * G)))) :
    (nextT K (by omega) T c).value = Zι (toGrid T) (restrictC ((phiEquiv G (tB lam)).symm c)) := by
  set ι := restrictC ((phiEquiv G (tB lam)).symm c)
  unfold nextT
  split_ifs with h
  · have hU : (rowNet (toGrid T) ι).total ≤ Umax G lam :=
      total_le_Umax (toGrid T) ι (U := (rowNet (toGrid T) ι).total) (min_eq_left h).symm
    obtain ⟨x, hx, hok⟩ := good_exists (rowNet (toGrid T) ι) _ _ (rowNet_fits (toGrid T) ι) hU hK2 hG
    have := firstGood_spec (okG (rowNet (toGrid T) ι) K (Lnext K G lam) (by omega)) (le_refl (K ^ G)) ⟨x, hx, hok⟩
    rw [okG_value _ _ this.2, value_rowNet]
  · have hU : (colNet (toGrid T) ι).total ≤ Umax G lam :=
      total_le_Umax (toGrid T) ι (U := (colNet (toGrid T) ι).total) (min_eq_right (le_of_lt (not_le.mp h))).symm
    obtain ⟨x, hx, hok⟩ := good_exists (colNet (toGrid T) ι) _ _ (colNet_fits (toGrid T) ι) hU hK2 hG
    have := firstGood_spec (okG (colNet (toGrid T) ι) K (Lnext K G lam) (by omega)) (le_refl (K ^ G)) ⟨x, hx, hok⟩
    rw [okG_value _ _ this.2, value_colNet]

/-- **One level**: summing the next cliques over all choice codes. -/
theorem sum_nextT {G lam : ℕ} (K : ℕ) (hK2 : 2 ≤ K) (hG : G = 3 * K ^ 8) (T : Clique (ZMod m) (G * G) lam) :
    ∑ c, (nextT K (by omega) T c).value = (mult G lam : ZMod m) * T.value := by
  simp only [value_nextT K hK2 hG T]
  rw [Fintype.sum_equiv (phiEquiv G (tB lam)).symm _ (fun φ => Zι (toGrid T) (restrictC φ)) (fun _ => rfl),
    sum_restrict, ← value_toGrid]
  simp [mult]

/-! ### The chain -/

/-- Group counts from the bottom: `Kb 0 = K0`, `Kb (d+1) = G_d²` with `G_d = 3 Kb(d)^8`. -/
def Kb (K0 : ℕ) : ℕ → ℕ
  | 0 => K0
  | d + 1 => (3 * Kb K0 d ^ 8) * (3 * Kb K0 d ^ 8)

/-- The grid side of the step from depth `d + 1` to depth `d`. -/
def Gs (K0 d : ℕ) : ℕ := 3 * Kb K0 d ^ 8

theorem Kb_ge (K0 : ℕ) (hK : 2 ≤ K0) : ∀ d, 2 ≤ Kb K0 d
  | 0 => hK
  | d + 1 => by
      have := Kb_ge K0 hK d
      show 2 ≤ (3 * Kb K0 d ^ 8) * (3 * Kb K0 d ^ 8)
      have : 1 ≤ Kb K0 d ^ 8 := Nat.one_le_pow _ _ (by omega)
      nlinarith

/-- The nested sums of the chain, from a clique at depth `d`. -/
def deepVal (K0 : ℕ) (hK : 2 ≤ K0) : (d L : ℕ) → Clique (ZMod m) (Kb K0 d) L → ZMod m
  | 0, _, T => T.value
  | d + 1, L, T => ∑ c : Fin ((tB L + 1) ^ (Gs K0 d * Gs K0 d * (Gs K0 d * Gs K0 d))),
      deepVal K0 hK d (Lnext (Kb K0 d) (Gs K0 d) L) (nextT (Kb K0 d) (by have := Kb_ge K0 hK d; omega) T c)

/-- The multiplier of the chain. -/
def deepMult (K0 : ℕ) : (d L : ℕ) → ℕ
  | 0, _ => 1
  | d + 1, L => mult (Gs K0 d) L * deepMult K0 d (Lnext (Kb K0 d) (Gs K0 d) L)

/-- **The chain computes a multiple of the value.** -/
theorem deepVal_eq (K0 : ℕ) (hK : 2 ≤ K0) :
    ∀ (d L : ℕ) (T : Clique (ZMod m) (Kb K0 d) L), deepVal K0 hK d L T = (deepMult K0 d L : ZMod m) * T.value
  | 0, L, T => by simp [deepVal, deepMult]
  | d + 1, L, T => by
      simp only [deepVal, deepMult]
      simp only [deepVal_eq K0 hK d]
      rw [← Finset.mul_sum]
      have h := sum_nextT (m := m) (G := Gs K0 d) (lam := L) (Kb K0 d) (Kb_ge K0 hK d) rfl T
      rw [h]
      show _ = ((mult (Gs K0 d) L * deepMult K0 d (Lnext (Kb K0 d) (Gs K0 d) L) : ℕ) : ZMod m) *
        Clique.value (K := Gs K0 d * Gs K0 d) T
      push_cast; ring

theorem deepMult_pos (K0 : ℕ) : ∀ d L, 0 < deepMult K0 d L
  | 0, _ => by simp [deepMult]
  | d + 1, L => by
      simp only [deepMult]
      exact Nat.mul_pos (Nat.mul_pos (Nat.pow_pos (by omega)) (Nat.pow_pos (by norm_num)))
        (deepMult_pos K0 d _)

end Factoring.Aux
