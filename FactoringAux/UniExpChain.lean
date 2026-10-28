/-
The uniform engine's exponent: the number of levels and the chain.

* `Kb48_ge` (`48 · 2^d ≤ Kb 48 d`), `lt_Kb48`; the number of levels `ellOf n`: `ell_inv`, **`lt_Kb_ellOf`**
  (`n < Kb 48 (ellOf n + 1) ^ 40`), **`Kb_ellOf_le`** (`Kb 48 (ellOf n) ^ 40 ≤ n` when `ellOf n ≥ 1`),
  **`le_ellOf`** (`Kb 48 ℓ₀ ^ 40 ≤ n → ℓ₀ ≤ ellOf n`), `ellOf_le`.
* The chain: `chainMax` (the largest exponent along the chain), `deepE_chainMax`; **`chainMax_le`**: a version of
  `deepE_of` that charges the level at height `d` with `14 N / Kb K0 d` for the actual group count `Kb K0 d` and
  keeps, for each level, both bounds on its bits `N` (`N ≤ W` and `23^(d+1) N ≤ 24^(d+1) W0`);
  **`NPof_le`**: `NPof ≤ (W+1)^(d · G⁴)`.

Not an audit surface.
-/
module

public import FactoringAux.EngineCostFinal
public import FactoringAux.UniParams

@[expose] public section

namespace Factoring.Aux

/-! ### The group counts and the number of levels -/

theorem Kb48_ge (d : ℕ) : 48 * 2 ^ d ≤ Kb K0u d := by
  induction d with
  | zero => show 48 * 1 ≤ 48; norm_num
  | succ d ih =>
      rw [Kb_succ]
      have h : Kb K0u d ≤ Kb K0u d ^ 16 := Nat.le_self_pow (by norm_num) _
      rw [pow_succ]
      omega

theorem lt_Kb48 (d : ℕ) : d < Kb K0u d := by
  have := Kb48_ge d
  have : d < 2 ^ d := Nat.lt_two_pow_self
  omega

theorem Kb48_ge48 (d : ℕ) : 48 ≤ Kb K0u d := le_trans (by have := Nat.one_le_two_pow (n := d); omega) (Kb48_ge d)

theorem Kb48_mono {d d' : ℕ} (h : d ≤ d') : Kb K0u d ≤ Kb K0u d' := Kb_mono K0u (by norm_num) h

theorem ell_inv (n : ℕ) : ∀ j, (iterF (ellStep n) 0 j = 0 ∨ Kb K0u (iterF (ellStep n) 0 j) ^ 40 ≤ n) ∧
    (iterF (ellStep n) 0 j = j ∨ n < Kb K0u (iterF (ellStep n) 0 j + 1) ^ 40)
  | 0 => ⟨Or.inl rfl, Or.inl rfl⟩
  | j + 1 => by
      obtain ⟨h1, h2⟩ := ell_inv n j
      have hs : iterF (ellStep n) 0 (j + 1) = ellStep n j (iterF (ellStep n) 0 j) := rfl
      rw [hs]
      generalize iterF (ellStep n) 0 j = y at h1 h2
      unfold ellStep
      split_ifs with h
      · exact ⟨h1, Or.inr h⟩
      · refine ⟨Or.inr (by omega), Or.inl ?_⟩
        rcases h2 with h2 | h2
        · omega
        · exact absurd h2 h

/-- **Above the number of levels.** -/
theorem lt_Kb_ellOf (n : ℕ) : n < Kb K0u (ellOf n + 1) ^ 40 := by
  rcases (ell_inv n n).2 with h | h
  · have e : ellOf n = n := h
    rw [e]
    have := lt_Kb48 (n + 1)
    have : Kb K0u (n + 1) ≤ Kb K0u (n + 1) ^ 40 := Nat.le_self_pow (by norm_num) _
    omega
  · exact h

/-- **At the number of levels.** -/
theorem Kb_ellOf_le {n : ℕ} (h : 1 ≤ ellOf n) : Kb K0u (ellOf n) ^ 40 ≤ n := by
  rcases (ell_inv n n).1 with h' | h'
  · exact absurd h' (by show ¬ ellOf n = 0; omega)
  · exact h'

/-- **Every admissible number of levels is at most `ellOf n`.** -/
theorem le_ellOf {n ℓ₀ : ℕ} (h : Kb K0u ℓ₀ ^ 40 ≤ n) : ℓ₀ ≤ ellOf n := by
  by_contra hc
  have h1 : Kb K0u (ellOf n + 1) ≤ Kb K0u ℓ₀ := Kb48_mono (by omega)
  have h2 := Nat.pow_le_pow_left h1 40
  have := lt_Kb_ellOf n
  omega

theorem ellOf_le (n : ℕ) : ellOf n ≤ n := by
  rcases Nat.eq_zero_or_pos (ellOf n) with h | h
  · omega
  · have h1 := Kb_ellOf_le h
    have h2 := lt_Kb48 (ellOf n)
    have : Kb K0u (ellOf n) ≤ Kb K0u (ellOf n) ^ 40 := Nat.le_self_pow (by norm_num) _
    omega

/-! ### The chain -/

/-- The largest exponent along the chain (the brute force at the bottom). -/
def chainMax (mb K0 : ℕ) : ℕ → ℕ → ℕ
  | 0, L => eBr (Kb K0 0) L mb
  | d + 1, L => max (eLev (Kb K0 d) (Gs K0 d) L mb) (chainMax mb K0 d (Lnext (Kb K0 d) (Gs K0 d) L))

theorem deepE_chainMax (mb K0 Z : ℕ) : ∀ d L, chainMax mb K0 d L ≤ Z → DeepE Z mb K0 d L
  | 0, _, h => h
  | d + 1, L, h => by
      have h' : max (eLev (Kb K0 d) (Gs K0 d) L mb) (chainMax mb K0 d (Lnext (Kb K0 d) (Gs K0 d) L)) ≤ Z := h
      exact ⟨le_trans (le_max_left _ _) h', deepE_chainMax mb K0 Z d _ (le_trans (le_max_right _ _) h')⟩

/-- **The chain's exponents, level by level**: the level at height `d` costs at most `14 (N + 2G⁴) / Kb K0 d`
plus its polynomial part, where its bits `N` satisfy `N + 2 G⁴ ≤ W` and `23^(d+1) N ≤ 24^(d+1) W0`. -/
theorem chainMax_le (K0 Y mb W W0 Gm : ℕ) (hK : 48 ≤ K0)
    (hLev : ∀ d N, N + 2 * (Gm * Gm * (Gm * Gm)) ≤ W → 23 ^ (d + 1) * N ≤ 24 ^ (d + 1) * W0 →
      14 * (N + 2 * (Gm * Gm * (Gm * Gm))) / Kb K0 d + 7 +
        (Gm * Gm * (Gm * Gm) + 9) * (Nat.log 2 (W + mb + Gm + Gm + 64) + 1) ≤ Y)
    (hBr : W0 + 2 * (Nat.log 2 (mb + K0 + 64) + 1) ≤ Y) :
    ∀ d L, Kb K0 d ≤ Gm → Kb K0 d ^ 2 * L + 2 * d * (Gm * Gm * (Gm * Gm)) ≤ W →
      23 ^ d * (Kb K0 d ^ 2 * L) + 24 ^ d * (2 * d * (Gm * Gm * (Gm * Gm))) ≤ 24 ^ d * W0 →
      chainMax mb K0 d L ≤ Y
  | 0, L, _, _, h2 => by
      show L * (K0 * K0) + 2 * (Nat.log 2 (mb + K0 + 64) + 1) ≤ Y
      have : Kb K0 0 ^ 2 * L = L * (K0 * K0) := by show K0 ^ 2 * L = _; ring
      simp only [pow_zero, one_mul, mul_zero, zero_mul, add_zero, this] at h2
      omega
  | d + 1, L, hGm, h1, h2 => by
      show max (eLev (Kb K0 d) (Gs K0 d) L mb) (chainMax mb K0 d (Lnext (Kb K0 d) (Gs K0 d) L)) ≤ Y
      set K := Kb K0 d
      set G := Gs K0 d
      have hKd : K0 ≤ K := Kb_mono K0 (by omega) (Nat.zero_le d)
      have hKG : K ≤ G := K_le_G K
      have hGGm : G ≤ Gm := le_trans (show G ≤ Kb K0 (d + 1) by
        show G ≤ G * G; exact Nat.le_mul_of_pos_left _ (by have := K_le_G K; omega)) hGm
      have hG4 : G * G * (G * G) ≤ Gm * Gm * (Gm * Gm) :=
        Nat.mul_le_mul (Nat.mul_le_mul hGGm hGGm) (Nat.mul_le_mul hGGm hGGm)
      have eN : Kb K0 (d + 1) ^ 2 * L = G * G * (G * G) * L := by show (G * G) ^ 2 * L = _; ring
      rw [eN] at h1 h2
      set N := G * G * (G * G) * L
      set N' := K ^ 2 * Lnext K G L
      set Gm4 := Gm * Gm * (Gm * Gm)
      have hs := N_step K G L (by omega) hKG
      have hN'N : N' ≤ N + 2 * Gm4 := by omega
      have hN2 : N + 2 * Gm4 ≤ W := by
        have : 2 * (d + 1) * Gm4 = 2 * d * Gm4 + 2 * Gm4 := by ring
        omega
      have h1' : N' + 2 * d * Gm4 ≤ W := by
        have : 2 * (d + 1) * Gm4 = 2 * d * Gm4 + 2 * Gm4 := by ring
        omega
      have h23 : 23 ^ (d + 1) * N ≤ 24 ^ (d + 1) * W0 := by omega
      have hG0 : 0 < G := by omega
      have hl : L ≤ W := by
        have : L ≤ N := Nat.le_mul_of_pos_left _ (Nat.mul_pos (Nat.mul_pos hG0 hG0) (Nat.mul_pos hG0 hG0))
        omega
      refine max_le ?_ ?_
      · refine le_trans (eLev_le K K G L mb (N + 2 * Gm4) (by omega) le_rfl hKG (by omega) hN'N) ?_
        have : ePolyL K G L mb ≤ (Gm4 + 9) * (Nat.log 2 (W + mb + Gm + Gm + 64) + 1) :=
          ePolyL_mono (mb := mb) (le_trans hKG hGGm) hGGm hl
        have h3 : 14 * (N + 2 * Gm4) / K + 7 + (Gm4 + 9) * (Nat.log 2 (W + mb + Gm + Gm + 64) + 1) ≤ Y :=
          hLev d N hN2 h23
        omega
      · refine chainMax_le K0 Y mb W W0 Gm hK hLev hBr d _ (le_trans (le_trans hKG (by
          show G ≤ G * G; exact Nat.le_mul_of_pos_left _ (by omega))) hGm) h1' ?_
        have a1 : 24 * (23 ^ d * N') ≤ 23 ^ (d + 1) * N + 24 ^ (d + 1) * (2 * Gm4) := by
          have b1 : 23 ^ d * (24 * N') ≤ 23 ^ d * (23 * N + 48 * (G * G * (G * G))) := Nat.mul_le_mul_left _ hs
          have b2 : 23 ^ d * (48 * (G * G * (G * G))) ≤ 24 ^ d * (48 * Gm4) :=
            Nat.mul_le_mul (Nat.pow_le_pow_left (by norm_num) d) (Nat.mul_le_mul_left _ hG4)
          have e1 : 24 * (23 ^ d * N') = 23 ^ d * (24 * N') := by ring
          have e2 : 23 ^ d * (23 * N + 48 * (G * G * (G * G))) = 23 ^ (d + 1) * N +
              23 ^ d * (48 * (G * G * (G * G))) := by ring
          have e3 : 24 ^ d * (48 * Gm4) = 24 ^ (d + 1) * (2 * Gm4) := by ring
          omega
        have e4 : 24 ^ (d + 1) * (2 * (d + 1) * Gm4) = 24 ^ (d + 1) * (2 * Gm4) + 24 * (24 ^ d * (2 * d * Gm4)) := by
          ring
        have e5 : 24 ^ (d + 1) * W0 = 24 * (24 ^ d * W0) := by ring
        have : 24 * (23 ^ d * N' + 24 ^ d * (2 * d * Gm4)) ≤ 24 * (24 ^ d * W0) := by
          rw [mul_add]; omega
        exact Nat.le_of_mul_le_mul_left this (by norm_num)

/-- **The number of paths.** -/
theorem NPof_le (K0 W Gm : ℕ) (hK : 48 ≤ K0) :
    ∀ d L, Kb K0 d ≤ Gm → Kb K0 d ^ 2 * L + 2 * d * (Gm * Gm * (Gm * Gm)) ≤ W →
      NPof K0 d L ≤ (W + 1) ^ (d * (Gm * Gm * (Gm * Gm)))
  | 0, _, _, _ => by simp [NPof]
  | d + 1, L, hGm, h1 => by
      show Nc K0 d L * NPof K0 d (Lnext (Kb K0 d) (Gs K0 d) L) ≤ _
      set K := Kb K0 d
      set G := Gs K0 d
      have hKd : K0 ≤ K := Kb_mono K0 (by omega) (Nat.zero_le d)
      have hKG : K ≤ G := K_le_G K
      have hGGm : G ≤ Gm := le_trans (show G ≤ Kb K0 (d + 1) by
        show G ≤ G * G; exact Nat.le_mul_of_pos_left _ (by have := K_le_G K; omega)) hGm
      have hG4 : G * G * (G * G) ≤ Gm * Gm * (Gm * Gm) :=
        Nat.mul_le_mul (Nat.mul_le_mul hGGm hGGm) (Nat.mul_le_mul hGGm hGGm)
      have eN : Kb K0 (d + 1) ^ 2 * L = G * G * (G * G) * L := by show (G * G) ^ 2 * L = _; ring
      rw [eN] at h1
      set N := G * G * (G * G) * L
      set Gm4 := Gm * Gm * (Gm * Gm)
      have hs := N_step K G L (by omega) hKG
      have h1' : K ^ 2 * Lnext K G L + 2 * d * Gm4 ≤ W := by
        have : 2 * (d + 1) * Gm4 = 2 * d * Gm4 + 2 * Gm4 := by ring
        omega
      have hG0 : 0 < G := by omega
      have hl : L ≤ W := by
        have : L ≤ N := Nat.le_mul_of_pos_left _ (Nat.mul_pos (Nat.mul_pos hG0 hG0) (Nat.mul_pos hG0 hG0))
        omega
      have ih := NPof_le K0 W Gm hK d (Lnext K G L) (le_trans (le_trans hKG (by
          show G ≤ G * G; exact Nat.le_mul_of_pos_left _ (by omega))) hGm) h1'
      have hNc : Nc K0 d L ≤ (W + 1) ^ Gm4 := by
        unfold Nc
        calc (tB L + 1) ^ (G * G * (G * G)) ≤ (W + 1) ^ (G * G * (G * G)) :=
              Nat.pow_le_pow_left (by unfold tB; omega) _
          _ ≤ (W + 1) ^ Gm4 := Nat.pow_le_pow_right (by omega) hG4
      calc Nc K0 d L * NPof K0 d (Lnext K G L) ≤ (W + 1) ^ Gm4 * (W + 1) ^ (d * Gm4) := Nat.mul_le_mul hNc ih
        _ = (W + 1) ^ ((d + 1) * Gm4) := by rw [← pow_add]; ring_nf

end Factoring.Aux
