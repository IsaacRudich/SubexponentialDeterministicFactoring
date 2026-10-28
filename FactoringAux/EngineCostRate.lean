/-
The cost of the counting expression: the rate.

With `S = 2^(sOf n)` (so `n ≤ 4 S⁴ ≤ 16 n + 16`):
* the top: `K² · Ltop ≤ 720 S⁴ + 306 g S³` (`Ntop_le`), `K · eTop ≤ 2160 S⁴ + …` (`eTop_le`);
* the chain: `24 N' ≤ 23 N + 48 G⁴` (`N_step`), so every level's bits stay below `W` and the brute force's decay by
  `(23/24)^ℓ` (`deepE_of`);
* absorption of the lower-order terms (`absorb`, `log_le_S`), the choice of `ℓ` and `K0`, and
  **`count_cost`**: the hypothesis of `count_of_mainE`.

Not an audit surface.
-/
module

public import FactoringAux.EngineCostReq
public import FactoringAux.EngineRate

@[expose] public section

namespace Factoring.Aux

open Finset

/-! ### The parameters in `S = 2^s` -/

theorem pA_S (s : ℕ) : pA s = 2 * 2 ^ s := by unfold pA; ring
theorem pL_S (s : ℕ) : pL s = 2 * (2 ^ s) ^ 2 := by unfold pL; ring
theorem fw_S (s : ℕ) : fw s = 8 * (2 ^ s) ^ 2 + 1 := by unfold fw pm; rw [pL_S]; ring

theorem A2fw_le (s : ℕ) : pA s * pA s * fw s ≤ 36 * (2 ^ s) ^ 4 := by
  rw [pA_S, fw_S]; have : (2 ^ s) ^ 2 ≤ (2 ^ s) ^ 4 := Nat.pow_le_pow_right (Nat.one_le_two_pow) (by norm_num)
  nlinarith

theorem Afw_le (s : ℕ) : pA s * fw s ≤ 18 * (2 ^ s) ^ 3 := by
  rw [pA_S, fw_S]; have : 2 ^ s ≤ (2 ^ s) ^ 3 := Nat.le_self_pow (by norm_num) _
  nlinarith

theorem fw_le (s : ℕ) : fw s ≤ 9 * (2 ^ s) ^ 3 := by
  rw [fw_S]; have : 1 ≤ (2 ^ s) ^ 2 := Nat.one_le_pow _ _ (Nat.two_pow_pos s)
  have : (2 ^ s) ^ 2 ≤ (2 ^ s) ^ 3 := Nat.pow_le_pow_right (Nat.one_le_two_pow) (by norm_num)
  omega

theorem n_le_S (n : ℕ) : n ≤ 4 * (2 ^ sOf n) ^ 4 := by
  have := sOf_spec n; rw [pL_S] at this; nlinarith

theorem sIter_min (n : ℕ) : ∀ j X, iterF (sStep n) 0 j = X + 1 → 2 ^ (4 * X + 2) < n
  | 0, X, h => by simp [iterF] at h
  | j + 1, X, h => by
      have ih := sIter_min n j
      change sStep n j (iterF (sStep n) 0 j) = X + 1 at h
      generalize iterF (sStep n) 0 j = Y at ih h
      unfold sStep at h
      split_ifs at h with h1
      · have : Y = X := by omega
        subst this; exact h1
      · exact ih X h

theorem S_le_n (n : ℕ) : (2 ^ sOf n) ^ 4 ≤ 4 * n + 4 := by
  rcases Nat.eq_zero_or_pos (sOf n) with h0 | h0
  · rw [h0]; norm_num
  · obtain ⟨X, hX⟩ : ∃ X, sOf n = X + 1 := ⟨sOf n - 1, by omega⟩
    have := sIter_min n n X hX
    have e : (2 ^ (X + 1)) ^ 4 = 4 * 2 ^ (4 * X + 2) := by
      rw [← pow_mul, show (X + 1) * 4 = (4 * X + 2) + 2 by ring, pow_add]; ring
    rw [hX, e]
    omega

/-! ### The top -/

theorem clP_mul_le (a f g : ℕ) :
    g * (7 * (a / g + 2) * a * f + 3 * (a * a / g + 2) * f) ≤ 10 * (a * a * f) + g * (14 * (a * f) + 6 * f) := by
  have h1 : g * (a / g) ≤ a := Nat.mul_div_le a g
  have h2 : g * (a * a / g) ≤ a * a := Nat.mul_div_le _ g
  have e : g * (7 * (a / g + 2) * a * f + 3 * (a * a / g + 2) * f) =
      7 * ((g * (a / g)) * (a * f)) + 3 * ((g * (a * a / g)) * f) + g * (14 * (a * f) + 6 * f) := by ring
  rw [e]
  have h3 := Nat.mul_le_mul_right (a * f) h1
  have h4 := Nat.mul_le_mul_right f h2
  have e2 : a * (a * f) = a * a * f := by ring
  omega

theorem Wc_mul_le (s g : ℕ) :
    g * Wc s g ≤ 10 * (pA s * pA s * fw s) + g * (16 * (pA s * fw s) + 4 * fw s) := by
  unfold Wc
  set a := pA s
  set f := fw s
  have h1 : g * (a / g) ≤ a := Nat.mul_div_le a g
  have h2 : g * (a * a / g) ≤ a * a := Nat.mul_div_le _ g
  have e : g * (8 * (a / g + 2) * a * f + 2 * (a * a / g + 2) * f) =
      8 * ((g * (a / g)) * (a * f)) + 2 * ((g * (a * a / g)) * f) + g * (16 * (a * f) + 4 * f) := by ring
  rw [e]
  have h3 := Nat.mul_le_mul_right (a * f) h1
  have h4 := Nat.mul_le_mul_right f h2
  have e2 : a * (a * f) = a * a * f := by ring
  omega

/-- **The top clique's bits.** -/
theorem Ntop_le (K g s : ℕ) (hK : 1 ≤ K) :
    K ^ 2 * Ltop K g s ≤ 20 * (pA s * pA s * fw s) + g * (14 * (pA s * fw s) + 6 * fw s) := by
  unfold Ltop
  set X := K * (10 * (pA s * pA s) * fw s) + g * clP s g
  have h1 : K ^ 3 * (X / K ^ 3) ≤ X := Nat.mul_div_le X _
  have h2 : K ^ 2 * (X / K ^ 3) ≤ X / K := by
    rw [Nat.le_div_iff_mul_le (by omega)]
    calc K ^ 2 * (X / K ^ 3) * K = K ^ 3 * (X / K ^ 3) := by ring
      _ ≤ X := h1
  have h3 : X / K ≤ 10 * (pA s * pA s * fw s) + g * clP s g := by
    rw [Nat.div_le_iff_le_mul_add_pred (by omega)]
    have : K * (10 * (pA s * pA s) * fw s) = 10 * (pA s * pA s * fw s) * K := by ring
    have : g * clP s g ≤ g * clP s g * K := Nat.le_mul_of_pos_right _ (by omega)
    show K * (10 * (pA s * pA s) * fw s) + g * clP s g ≤ _
    nlinarith
  have h4 := clP_mul_le (pA s) (fw s) g
  unfold clP at h3
  omega

theorem Ntop_S (K g s : ℕ) (hK : 1 ≤ K) : K ^ 2 * Ltop K g s ≤ 720 * (2 ^ s) ^ 4 + 306 * (g * (2 ^ s) ^ 3) := by
  have h := Ntop_le K g s hK
  have a1 := A2fw_le s
  have a2 := Nat.mul_le_mul_left g (show 14 * (pA s * fw s) + 6 * fw s ≤ 306 * (2 ^ s) ^ 3 by
    have := Afw_le s; have := fw_le s; omega)
  have : g * (306 * (2 ^ s) ^ 3) = 306 * (g * (2 ^ s) ^ 3) := by ring
  omega

/-- **The top's exponents**, times `K`. -/
theorem eTop_le (K0 ℓ n mb : ℕ) (hK : 2 ≤ K0) :
    Kb K0 ℓ * eTop K0 ℓ n mb ≤ 2160 * (2 ^ sOf n) ^ 4 +
      Kb K0 ℓ * (1584 * (Gs K0 ℓ * (2 ^ sOf n) ^ 3) + 78 * (2 ^ sOf n) ^ 3 +
        ePolyT (Kb K0 ℓ) (Gs K0 ℓ) (sOf n) n mb) := by
  set K := Kb K0 ℓ
  set g := Gs K0 ℓ
  set s := sOf n
  have hK2 : 2 ≤ K := Kb_ge K0 hK ℓ
  have hKg : K ≤ g := by
    show K ≤ 3 * K ^ 8
    have : K ≤ K ^ 8 := Nat.le_self_pow (by norm_num) K
    omega
  have a1 := A2fw_le s
  have a2 := Afw_le s
  have a3 := fw_le s
  have hW := Wc_mul_le s g
  have hC := clP_mul_le (pA s) (fw s) g
  have hN := Ntop_le K g s (by omega)
  have p3 : K * Wc s g ≤ 10 * (pA s * pA s * fw s) + g * (16 * (pA s * fw s) + 4 * fw s) :=
    le_trans (Nat.mul_le_mul_right _ hKg) hW
  have p4 : K * clP s g ≤ 10 * (pA s * pA s * fw s) + g * (14 * (pA s * fw s) + 6 * fw s) := by
    unfold clP; exact le_trans (Nat.mul_le_mul_right _ hKg) hC
  have p5 : K * (Wc s g * (2 * g / K)) ≤ 2 * (10 * (pA s * pA s * fw s) + g * (16 * (pA s * fw s) + 4 * fw s)) := by
    calc K * (Wc s g * (2 * g / K)) = Wc s g * (K * (2 * g / K)) := by ring
      _ ≤ Wc s g * (2 * g) := Nat.mul_le_mul_left _ (Nat.mul_div_le _ _)
      _ = 2 * (g * Wc s g) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ hW
  have p1 : pL s * (16 * pA s) = 64 * (2 ^ s) ^ 3 := by rw [pL_S, pA_S]; ring
  have p2 : 7 * pL s ≤ 14 * (2 ^ s) ^ 3 := by
    rw [pL_S]; have : (2 ^ s) ^ 2 ≤ (2 ^ s) ^ 3 := Nat.pow_le_pow_right (Nat.one_le_two_pow) (by norm_num)
    omega
  have hX : 76 * (pA s * fw s) + 24 * fw s ≤ 1584 * (2 ^ s) ^ 3 := by omega
  have hsum : g * (16 * (pA s * fw s) + 4 * fw s) + g * (14 * (pA s * fw s) + 6 * fw s) +
      2 * (g * (16 * (pA s * fw s) + 4 * fw s)) + g * (14 * (pA s * fw s) + 6 * fw s) ≤
      1584 * (g * (2 ^ s) ^ 3) := by
    calc _ = g * (76 * (pA s * fw s) + 24 * fw s) := by ring
      _ ≤ g * (1584 * (2 ^ s) ^ 3) := Nat.mul_le_mul_left _ hX
      _ = 1584 * (g * (2 ^ s) ^ 3) := by ring
  have q1 : K * (64 * (2 ^ s) ^ 3 + 7 * pL s) ≤ K * (78 * (2 ^ s) ^ 3) :=
    Nat.mul_le_mul_left K (show 64 * (2 ^ s) ^ 3 + 7 * pL s ≤ 78 * (2 ^ s) ^ 3 by omega)
  have q2 : 1584 * (g * (2 ^ s) ^ 3) ≤ K * (1584 * (g * (2 ^ s) ^ 3)) := Nat.le_mul_of_pos_left _ (by omega)
  calc K * eTop K0 ℓ n mb = K * (64 * (2 ^ s) ^ 3 + 7 * pL s) + K * Wc s g + K * clP s g +
        K * (Wc s g * (2 * g / K)) + K ^ 2 * Ltop K g s + K * ePolyT K g s n mb := by
          unfold eTop; rw [p1]; ring
    _ ≤ K * (78 * (2 ^ s) ^ 3) + (10 * (pA s * pA s * fw s) + g * (16 * (pA s * fw s) + 4 * fw s)) +
        (10 * (pA s * pA s * fw s) + g * (14 * (pA s * fw s) + 6 * fw s)) +
        2 * (10 * (pA s * pA s * fw s) + g * (16 * (pA s * fw s) + 4 * fw s)) +
        (20 * (pA s * pA s * fw s) + g * (14 * (pA s * fw s) + 6 * fw s)) + K * ePolyT K g s n mb := by
          gcongr
    _ ≤ 2160 * (2 ^ s) ^ 4 + K * (1584 * (g * (2 ^ s) ^ 3) + 78 * (2 ^ s) ^ 3 + ePolyT K g s n mb) := by
          have e : K * (1584 * (g * (2 ^ s) ^ 3) + 78 * (2 ^ s) ^ 3 + ePolyT K g s n mb) =
              K * (1584 * (g * (2 ^ s) ^ 3)) + K * (78 * (2 ^ s) ^ 3) + K * ePolyT K g s n mb := by ring
          rw [e]; omega

/-! ### The chain -/

theorem Kb_le_succ (K0 : ℕ) (hK : 1 ≤ K0) (d : ℕ) : Kb K0 d ≤ Kb K0 (d + 1) := by
  have h1 : 1 ≤ Kb K0 d := by
    induction d with
    | zero => exact hK
    | succ d ih => show 1 ≤ (3 * Kb K0 d ^ 8) * (3 * Kb K0 d ^ 8); have := Nat.one_le_pow 8 _ ih; nlinarith
  show Kb K0 d ≤ (3 * Kb K0 d ^ 8) * (3 * Kb K0 d ^ 8)
  have : Kb K0 d ≤ Kb K0 d ^ 8 := Nat.le_self_pow (by norm_num) _
  have := Nat.one_le_pow 8 _ h1
  nlinarith

theorem Kb_mono (K0 : ℕ) (hK : 1 ≤ K0) {d d' : ℕ} (h : d ≤ d') : Kb K0 d ≤ Kb K0 d' := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact le_trans ih (Kb_le_succ K0 hK _)

theorem Gs_mono (K0 : ℕ) (hK : 1 ≤ K0) {d d' : ℕ} (h : d ≤ d') : Gs K0 d ≤ Gs K0 d' := by
  unfold Gs; exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Kb_mono K0 hK h) 8)

theorem K_le_G (K : ℕ) : K ≤ 3 * K ^ 8 := by
  rcases Nat.eq_zero_or_pos K with h | h
  · simp [h]
  · have : K ≤ K ^ 8 := Nat.le_self_pow (by norm_num) K
    omega

/-- **One level's decay**: `24 N' ≤ 23 N + 48 G⁴` when `K ≥ 48`. -/
theorem N_step (K G lam : ℕ) (hK : 48 ≤ K) (hGK : K ≤ G) :
    24 * (K ^ 2 * Lnext K G lam) ≤ 23 * (G * G * (G * G) * lam) + 48 * (G * G * (G * G)) := by
  have h := N_next K G lam hGK
  have e : G ^ 4 = G * G * (G * G) := by ring
  rw [e] at h
  set N := G * G * (G * G) * lam
  set N' := K ^ 2 * Lnext K G lam
  set G4 := G * G * (G * G)
  have h2 : 48 * N ≤ K * N := Nat.mul_le_mul_right _ hK
  have h3 : K * (24 * N') ≤ K * (23 * N + 48 * G4) := by nlinarith
  exact Nat.le_of_mul_le_mul_left h3 (by omega)

theorem eLev_le (K0 K G lam mb W : ℕ) (hK0 : 1 ≤ K0) (hK : K0 ≤ K) (hKG : K ≤ G)
    (hN : G * G * (G * G) * lam ≤ W) (hN' : K ^ 2 * Lnext K G lam ≤ W) :
    eLev K G lam mb ≤ 14 * W / K0 + 7 + ePolyL K G lam mb := by
  have hK1 : 1 ≤ K := le_trans hK0 hK
  have hG1 : 1 ≤ G := le_trans hK1 hKG
  set N := G * G * (G * G) * lam
  have r1 : K * (lam * (G * (G * G)) * (2 * G / K)) ≤ 2 * N := by
    calc K * (lam * (G * (G * G)) * (2 * G / K)) = lam * (G * (G * G)) * (K * (2 * G / K)) := by ring
      _ ≤ lam * (G * (G * G)) * (2 * G) := Nat.mul_le_mul_left _ (Nat.mul_div_le _ _)
      _ = 2 * N := by ring
  have r2 : K * (lam * (G * (G * G))) ≤ N := by
    calc K * (lam * (G * (G * G))) ≤ G * (lam * (G * (G * G))) := Nat.mul_le_mul_right _ hKG
      _ = N := by ring
  have hGG : lam * (G * G) ≤ lam * (G * (G * G)) := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (by omega))
  have r3 : K * (3 * (lam * (G * G))) ≤ 3 * N := by
    calc K * (3 * (lam * (G * G))) = 3 * (K * (lam * (G * G))) := by ring
      _ ≤ 3 * (K * (lam * (G * (G * G)))) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hGG)
      _ ≤ 3 * N := Nat.mul_le_mul_left _ r2
  have hKl : K * lam ≤ N := by
    have : K * lam ≤ K * (lam * (G * (G * G))) :=
      Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ (by positivity))
    omega
  have r4 : K * (7 * tB lam) ≤ 7 * N + 7 * K := by
    have := Nat.mul_le_mul_left K (tB_le lam)
    have e : K * (lam + 1) = K * lam + K := by ring
    have e2 : K * (7 * tB lam) = 7 * (K * tB lam) := by ring
    omega
  have r5 : K * (Lnext K G lam * K) ≤ W := by
    calc K * (Lnext K G lam * K) = K ^ 2 * Lnext K G lam := by ring
      _ ≤ W := hN'
  set R := lam * (G * (G * G)) * (2 * G / K) + lam * (G * (G * G)) + 3 * (lam * (G * G)) + 7 * tB lam +
    Lnext K G lam * K
  have hR : K * R ≤ 14 * W + 7 * K := by
    have e : K * R = K * (lam * (G * (G * G)) * (2 * G / K)) + K * (lam * (G * (G * G))) +
        K * (3 * (lam * (G * G))) + K * (7 * tB lam) + K * (Lnext K G lam * K) := by simp only [R]; ring
    omega
  have hR' : R ≤ 14 * W / K0 + 7 := by
    have h1 : R ≤ (14 * W + 7 * K) / K := (Nat.le_div_iff_mul_le (by omega)).mpr (by rw [mul_comm]; exact hR)
    rw [Nat.add_mul_div_right _ _ (by omega)] at h1
    exact le_trans h1 (Nat.add_le_add_right (Nat.div_le_div_left hK (by omega)) _)
  show R + ePolyL K G lam mb ≤ _
  omega

theorem ePolyL_mono {K G lam mb W Gm : ℕ} (hK : K ≤ Gm) (hG : G ≤ Gm) (hl : lam ≤ W) :
    ePolyL K G lam mb ≤ (Gm * Gm * (Gm * Gm) + 9) * (Nat.log 2 (W + mb + Gm + Gm + 64) + 1) := by
  unfold ePolyL
  refine Nat.mul_le_mul (Nat.add_le_add_right ?_ _) (Nat.add_le_add_right (Nat.log_mono_right (by omega)) _)
  exact Nat.mul_le_mul (Nat.mul_le_mul hG hG) (Nat.mul_le_mul hG hG)

/-- **The chain's exponents**, from bounds on the bits at the top of the chain. -/
theorem deepE_of (K0 Z mb W W0 Gm : ℕ) (hK : 48 ≤ K0)
    (hLev : 14 * W / K0 + 7 + (Gm * Gm * (Gm * Gm) + 9) * (Nat.log 2 (W + mb + Gm + Gm + 64) + 1) ≤ Z)
    (hBr : W0 + 2 * (Nat.log 2 (mb + K0 + 64) + 1) ≤ Z) :
    ∀ d L, Kb K0 d ≤ Gm → Kb K0 d ^ 2 * L + 2 * d * (Gm * Gm * (Gm * Gm)) ≤ W →
      23 ^ d * (Kb K0 d ^ 2 * L) + 24 ^ d * (2 * d * (Gm * Gm * (Gm * Gm))) ≤ 24 ^ d * W0 →
      DeepE Z mb K0 d L
  | 0, L, _, _, h2 => by
      show L * (K0 * K0) + 2 * (Nat.log 2 (mb + K0 + 64) + 1) ≤ Z
      have : Kb K0 0 ^ 2 * L = L * (K0 * K0) := by show K0 ^ 2 * L = _; ring
      simp only [pow_zero, one_mul, mul_zero, zero_mul, add_zero, mul_one, this] at h2
      omega
  | d + 1, L, hGm, h1, h2 => by
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
      have h1' : N' + 2 * d * Gm4 ≤ W := by
        have : 2 * (d + 1) * Gm4 = 2 * d * Gm4 + 2 * Gm4 := by ring
        omega
      have hG0 : 0 < G := by omega
      have hl : L ≤ W := by
        have : L ≤ N := Nat.le_mul_of_pos_left _ (Nat.mul_pos (Nat.mul_pos hG0 hG0) (Nat.mul_pos hG0 hG0))
        omega
      refine ⟨le_trans (eLev_le K0 K G L mb W (by omega) hKd hKG (by omega) (by omega)) ?_, ?_⟩
      · have : ePolyL K G L mb ≤ (Gm4 + 9) * (Nat.log 2 (W + mb + Gm + Gm + 64) + 1) :=
          ePolyL_mono (mb := mb) (le_trans hKG hGGm) hGGm hl
        omega
      · refine deepE_of K0 Z mb W W0 Gm hK hLev hBr d _ (le_trans (le_trans hKG (by
          show G ≤ G * G; exact Nat.le_mul_of_pos_left _ (by omega))) hGm) h1' ?_
        -- 24 (23^d N' + 24^d · 2d Gm4) ≤ 24 · 24^d W0
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

/-- The multiplier's exponent along the chain. -/
theorem mlogN_le (K0 W Gm : ℕ) (hK : 48 ≤ K0) :
    ∀ d L, Kb K0 d ≤ Gm → Kb K0 d ^ 2 * L + 2 * d * (Gm * Gm * (Gm * Gm)) ≤ W →
      mlogN K0 d L ≤ 2 * d * (Gm * Gm * (Gm * Gm)) * (W + 1)
  | 0, _, _, _ => by simp [mlogN]
  | d + 1, L, hGm, h1 => by
      set K := Kb K0 d
      set G := Gs K0 d
      have hKG : K ≤ G := K_le_G K
      have hKd : K0 ≤ K := Kb_mono K0 (by omega) (Nat.zero_le d)
      have hG0 : 0 < G := by omega
      have hGGm : G ≤ Gm := le_trans (show G ≤ Kb K0 (d + 1) by
        show G ≤ G * G; exact Nat.le_mul_of_pos_left _ hG0) hGm
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
      have ih : mlogN K0 d (Lnext K G L) ≤ 2 * d * Gm4 * (W + 1) := mlogN_le K0 W Gm hK d _ (le_trans (le_trans hKG (by
          show G ≤ G * G; exact Nat.le_mul_of_pos_left _ (by omega))) hGm) h1'
      have hl : L ≤ N := Nat.le_mul_of_pos_left _ (Nat.mul_pos (Nat.mul_pos hG0 hG0) (Nat.mul_pos hG0 hG0))
      have ht : tB L ≤ W + 1 := le_trans (tB_le L) (by omega)
      have e4 : G ^ 4 = G * G * (G * G) := by ring
      show 2 * G ^ 4 * tB L + mlogN K0 d (Lnext K G L) ≤ _
      rw [e4]
      have c1 : 2 * (G * G * (G * G)) * tB L ≤ 2 * Gm4 * (W + 1) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ hG4) ht
      have e5 : 2 * (d + 1) * Gm4 * (W + 1) = 2 * Gm4 * (W + 1) + 2 * d * Gm4 * (W + 1) := by ring
      omega

end Factoring.Aux
