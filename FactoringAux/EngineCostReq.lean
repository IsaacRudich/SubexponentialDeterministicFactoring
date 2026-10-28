/-
The cost of the counting expression: the requirements on `V = 2^Z` from exponents.

* `eLev` (one level), `eBr` (the brute force), `DeepE` (the chain), `eTop`; **`mainReq_of`**: `MainReq (2^Z) K0 ℓ n`
  when `Z` is at least every exponent. Polynomial items are bounded by `B^deg ≤ 2^(deg·(log₂ B + 1))`.

Not an audit surface.
-/
module

public import FactoringAux.EngineCostMain

@[expose] public section

namespace Factoring.Aux

open Finset

/-! ### Generic facts -/

theorem le_two_pow_log (B : ℕ) : B < 2 ^ (Nat.log 2 B + 1) := Nat.lt_pow_succ_log_self (by norm_num) B

theorem pow_le_two_pow_log (B e : ℕ) : B ^ e ≤ 2 ^ (e * (Nat.log 2 B + 1)) := by
  rw [mul_comm, pow_mul]; exact Nat.pow_le_pow_left (le_two_pow_log B).le e

theorem le_pow_of_le {x B i j : ℕ} (hB : 1 ≤ B) (hx : x ≤ B ^ i) (hij : i ≤ j) : x ≤ B ^ j :=
  le_trans hx (Nat.pow_le_pow_right hB hij)

theorem tB_le (lam : ℕ) : tB lam ≤ lam + 1 := by unfold tB; omega

/-! ### One level -/

/-- The polynomial exponent of a level (`B = λ + m + K + G + 64`). -/
def ePolyL (K G lam m : ℕ) : ℕ := (G * G * (G * G) + 9) * (Nat.log 2 (lam + m + K + G + 64) + 1)

/-- All exponents of one level. -/
def eLev (K G lam m : ℕ) : ℕ :=
  lam * (G * (G * G)) * (2 * G / K) + lam * (G * (G * G)) + 3 * (lam * (G * G)) + 7 * tB lam +
    Lnext K G lam * K + ePolyL K G lam m

theorem levelReq_of {V m mb K G lam Z : ℕ} (hm : 1 < m) (hmb : m ≤ mb) (hG : 1 ≤ G) (hZ : eLev K G lam mb ≤ Z)
    (hV : 2 ^ Z ≤ V) : LevelReq V m K G lam := by
  have hZ1 : (G * G * (G * G) + 9) * (Nat.log 2 (lam + mb + K + G + 64) + 1) ≤ Z :=
    le_trans (by unfold eLev ePolyL; omega) hZ
  set B := lam + mb + K + G + 64 with hBdef
  have hB1 : 1 ≤ B := by omega
  set e := G * G * (G * G) + 9
  have hPV : B ^ e ≤ V := le_trans (pow_le_two_pow_log B e)
    (le_trans (Nat.pow_le_pow_right (by norm_num) hZ1) hV)
  have hBe : ∀ x i, x ≤ B ^ i → i ≤ e → x ≤ V := fun x i hx hi => le_trans (le_pow_of_le hB1 hx hi) hPV
  have h2 : ∀ a, a ≤ eLev K G lam mb → 2 ^ a ≤ V := fun a ha =>
    le_trans (Nat.pow_le_pow_right (by norm_num) (le_trans ha hZ)) hV
  have hG4 : 1 ≤ G * G * (G * G) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have ht : tB lam + 1 ≤ B := by have := tB_le lam; omega
  have hmB : mb ≤ B := by omega
  have hKB : K ≤ B := by omega
  have hGB : G ≤ B := by omega
  have hlB : lam + 1 ≤ B := by omega
  have h64 : 64 ≤ B := by omega
  have hB2 : B ^ 2 = B * B := by ring
  have hpow : ∀ i, B ^ i ≤ B ^ (i + 1) := fun i => Nat.pow_le_pow_right hB1 (Nat.le_succ i)
  have hB64 : ∀ i, 64 * B ^ i ≤ B ^ (i + 1) := fun i => by rw [pow_succ, mul_comm (B ^ i)]; exact Nat.mul_le_mul_right _ h64
  have mul2 : ∀ x y, x ≤ B → y ≤ B → x * y ≤ B ^ 2 := fun x y hx hy => by rw [hB2]; exact Nat.mul_le_mul hx hy
  -- powers of the basic quantities
  have hG2 : G * G ≤ B ^ 2 := mul2 _ _ hGB hGB
  have hG3 : G * (G * G) ≤ B ^ 3 :=
    le_trans (Nat.mul_le_mul hGB (Nat.mul_le_mul hGB hGB)) (by rw [show B ^ 3 = B * (B * B) by ring])
  have hG4B : G * G * (G * G) ≤ B ^ 4 := by
    rw [show B ^ 4 = B ^ 2 * B ^ 2 by ring]; exact Nat.mul_le_mul hG2 hG2
  have hl : lam ≤ B := by omega
  refine
    { dec := { hm := hm, hD := h2 _ (by unfold eLev; omega), hjm := hBe _ 2
                 (le_trans (Nat.mul_le_mul ht (le_trans hmb hmB)) (by rw [hB2])) (by omega)
               hmm := hBe _ 2 (le_trans (Nat.mul_le_mul (le_trans hmb hmB) (le_trans hmb hmB)) (by rw [hB2]))
                 (by omega)
               h64 := hBe _ 1 (by rw [pow_one]; exact h64) (by omega) }
      hS := h2 _ (by unfold eLev; omega)
      hW := h2 _ (by unfold eLev; omega)
      hC := hBe _ (G * G * (G * G)) (Nat.pow_le_pow_left ht _) (by omega)
      hg4 := hBe _ 4 hG4B (by omega)
      hKg := hBe _ (G * G * (G * G)) (le_trans (Nat.pow_le_pow_left hKB G)
        (Nat.pow_le_pow_right hB1 (le_trans (Nat.le_mul_of_pos_left _ (by positivity))
          (Nat.le_mul_of_pos_right _ (by positivity))))) (by omega)
      hKG := hBe _ 2 (mul2 _ _ hKB hGB) (by omega)
      hg1 := hBe _ 2 (by
        have : 3 * B ≤ B * B := Nat.mul_le_mul_right B (by omega)
        rw [hB2]; omega) (by omega)
      hgrp := h2 _ (by unfold eLev; omega)
      hLK := h2 _ (by unfold eLev; omega)
      htot := hBe _ 5 (by
        calc G * (G ^ 3 * lam) = G * (G * G) * G * lam := by ring
          _ ≤ B ^ 3 * B * B := Nat.mul_le_mul (Nat.mul_le_mul hG3 hGB) hl
          _ = B ^ 5 := by ring) (by omega)
      hUE := hBe _ 6 (by
        have : G * (G * (G ^ 2 * lam)) ≤ B ^ 5 := by
          calc G * (G * (G ^ 2 * lam)) = G * (G * G) * G * lam := by ring
            _ ≤ B ^ 3 * B * B := Nat.mul_le_mul (Nat.mul_le_mul hG3 hGB) hl
            _ = B ^ 5 := by ring
        have : 64 * B ^ 5 ≤ B ^ 6 := hB64 5
        have := Nat.one_le_pow 5 B hB1; omega) (by omega)
      hLn := hBe _ 7 (by
        have e3 : G ^ 3 ≤ B ^ 4 := le_trans (by rw [pow_succ, pow_two, mul_comm (G * G) G]; exact hG3) (hpow 3)
        have e4 : G ^ 4 ≤ B ^ 4 := by rw [show G ^ 4 = G * G * (G * G) by ring]; exact hG4B
        have e44 : G * G ^ 3 ≤ B ^ 4 := by rw [show G * G ^ 3 = G * G * (G * G) by ring]; exact hG4B
        have k3 : K ^ 3 ≤ B ^ 4 := le_trans (Nat.pow_le_pow_left hKB 3) (hpow 3)
        have b4 : 12 ≤ B ^ 4 := le_trans (by omega) (Nat.le_self_pow (by norm_num) B)
        have hQ : 12 * G ^ 3 + 11 * G ^ 4 + 24 * G ^ 4 + G * G ^ 3 + K ^ 3 + 12 ≤ B ^ 5 := by
          have : 64 * B ^ 4 ≤ B ^ 5 := hB64 4
          omega
        calc (K + 1) * ((12 * G ^ 3 + 11 * G ^ 4 + 24 * G ^ 4 + G * G ^ 3 + K ^ 3 + 12) * (lam + 1))
            ≤ B * (B ^ 5 * B) := Nat.mul_le_mul (by omega) (Nat.mul_le_mul hQ hlB)
          _ = B ^ 7 := by ring) (by omega)
      hmult := hBe _ 6 (by
        have : (tB lam + 1) * (G * G * (G * G)) ≤ B ^ 5 := by
          calc (tB lam + 1) * (G * G * (G * G)) ≤ B * B ^ 4 := Nat.mul_le_mul ht hG4B
            _ = B ^ 5 := by ring
        have : 64 * B ^ 5 ≤ B ^ 6 := hB64 5
        have := Nat.one_le_pow 5 B hB1; omega) (by omega) }

/-! ### The brute force and the chain -/

/-- The exponent of the brute force. -/
def eBr (K L mb : ℕ) : ℕ := L * (K * K) + 2 * (Nat.log 2 (mb + K + 64) + 1)

theorem bruteReq_of {V m mb K L Z : ℕ} (hm : 1 < m) (hmb : m ≤ mb) (hK : 1 ≤ K) (hZ : eBr K L mb ≤ Z)
    (hV : 2 ^ Z ≤ V) : BruteReq V m K L := by
  have hZ1 : 2 * (Nat.log 2 (mb + K + 64) + 1) ≤ Z := le_trans (by unfold eBr; omega) hZ
  have hZ2 : L * (K * K) ≤ Z := le_trans (by unfold eBr; omega) hZ
  set B := mb + K + 64
  have hPV : B ^ 2 ≤ V := le_trans (pow_le_two_pow_log B 2)
    (le_trans (Nat.pow_le_pow_right (by norm_num) hZ1) hV)
  have hB2 : B ^ 2 = B * B := by ring
  exact
    { hm := hm
      mm := le_trans (Nat.mul_le_mul (show m ≤ B by omega) (show m ≤ B by omega)) (by rw [← hB2]; exact hPV)
      hK := hK
      KK := le_trans (Nat.mul_le_mul (show K ≤ B by omega) (show K ≤ B by omega)) (by rw [← hB2]; exact hPV)
      hLK := le_trans (Nat.pow_le_pow_right (by norm_num) hZ2) hV
      two := le_trans (le_trans (show 2 ≤ B by omega) (Nat.le_mul_self B)) (by rw [← hB2]; exact hPV) }

/-- Every exponent along the chain is at most `Z`. -/
def DeepE (Z mb K0 : ℕ) : ℕ → ℕ → Prop
  | 0, L => eBr (Kb K0 0) L mb ≤ Z
  | d + 1, L => eLev (Kb K0 d) (Gs K0 d) L mb ≤ Z ∧ DeepE Z mb K0 d (Lnext (Kb K0 d) (Gs K0 d) L)

theorem deepReq_of {V m mb K0 Z : ℕ} (hm : 1 < m) (hmb : m ≤ mb) (hK : 2 ≤ K0) (hV : 2 ^ Z ≤ V) :
    ∀ d L, DeepE Z mb K0 d L → DeepReq V m K0 d L
  | 0, L, h => bruteReq_of hm hmb (by show 1 ≤ K0; omega) h hV
  | d + 1, L, h => ⟨levelReq_of hm hmb (by show 1 ≤ 3 * Kb K0 d ^ 8; have := Nat.pow_pos (n := 8) (show 0 < Kb K0 d by have := Kb_ge K0 hK d; omega); omega) h.1 hV,
      deepReq_of hm hmb hK hV d _ h.2⟩

/-! ### The top -/

/-- The polynomial exponent of the top (`B = mb + 16 n + K + g + nodes + 64`). -/
def ePolyT (K g s n mb : ℕ) : ℕ := (g + 4) * (Nat.log 2 (mb + 16 * n + K + g + mulNodes s + 64) + 1)

/-- All exponents of the top (`s = sOf n`, `K = Kb K0 ℓ`, `g = Gs K0 ℓ`). -/
def eTop (K0 ℓ n mb : ℕ) : ℕ :=
  pL (sOf n) * (16 * pA (sOf n)) + 7 * pL (sOf n) + Wc (sOf n) (Gs K0 ℓ) + clP (sOf n) (Gs K0 ℓ) +
    Wc (sOf n) (Gs K0 ℓ) * (2 * Gs K0 ℓ / Kb K0 ℓ) + Ltop (Kb K0 ℓ) (Gs K0 ℓ) (sOf n) * Kb K0 ℓ +
    ePolyT (Kb K0 ℓ) (Gs K0 ℓ) (sOf n) n mb

theorem topReq_of {V m mb K0 ℓ n Z : ℕ} (hK : 2 ≤ K0) (hm : 1 < m) (hmb : m ≤ mb) (hZ : eTop K0 ℓ n mb ≤ Z)
    (hD : DeepE Z mb K0 ℓ (Ltop (Kb K0 ℓ) (Gs K0 ℓ) (sOf n))) (hV : 2 ^ Z ≤ V) : TopReq V m K0 ℓ n := by
  have hZ1 : (Gs K0 ℓ + 4) * (Nat.log 2 (mb + 16 * n + Kb K0 ℓ + Gs K0 ℓ + mulNodes (sOf n) + 64) + 1) +
      7 * pL (sOf n) ≤ Z := le_trans (by unfold eTop ePolyT; omega) hZ
  set s := sOf n
  set K := Kb K0 ℓ
  set g := Gs K0 ℓ
  set B := mb + 16 * n + K + g + mulNodes s + 64
  have hB1 : 1 ≤ B := by omega
  have hK2 : 2 ≤ K := Kb_ge K0 hK ℓ
  have hg : 1 ≤ g := by show 1 ≤ 3 * K ^ 8; have := Nat.pow_pos (n := 8) (show 0 < K by omega); omega
  have h2 : ∀ a, a ≤ eTop K0 ℓ n mb → 2 ^ a ≤ V := fun a ha =>
    le_trans (Nat.pow_le_pow_right (by norm_num) (le_trans ha hZ)) hV
  have hPV : B ^ (g + 4) * 2 ^ (7 * pL s) ≤ V := by
    refine le_trans (Nat.mul_le_mul_right _ (pow_le_two_pow_log B (g + 4))) ?_
    rw [← pow_add]; exact le_trans (Nat.pow_le_pow_right (by norm_num) hZ1) hV
    -- every polynomial item is at most `B^(g+4)`
  have hP1 : 1 ≤ 2 ^ (7 * pL s) := Nat.one_le_two_pow
  have hBe : ∀ x i, x ≤ B ^ i → i ≤ g + 4 → x ≤ V := fun x i hx hi =>
    le_trans (le_trans (le_pow_of_le hB1 hx hi) (Nat.le_mul_of_pos_right _ hP1)) hPV
  have hB2 : B ^ 2 = B * B := by ring
  have mul2 : ∀ x y, x ≤ B → y ≤ B → x * y ≤ B ^ 2 := fun x y hx hy => by rw [hB2]; exact Nat.mul_le_mul hx hy
  have hKB : K ≤ B := by omega
  have hgB : g ≤ B := by omega
  have h64 : 64 ≤ B := by omega
  exact
    { hm := hm
      mul := by rw [← pow_mul]; exact h2 _ (by unfold eTop; omega)
      mm := hBe _ 2 (mul2 _ _ (by omega) (by omega)) (by omega)
      hn := hBe _ 1 (by rw [pow_one]; omega) (by omega)
      hL0 := by
        refine le_trans ?_ hPV
        unfold L0V
        rw [← pow_mul, mul_comm (pL s) 7]
        refine Nat.mul_le_mul_right _ (le_pow_of_le hB1 (i := 4) ?_ (show 4 ≤ g + 4 by omega))
        have k3 : Kb K0 ℓ ^ 3 ≤ B ^ 3 := Nat.pow_le_pow_left hKB 3
        have e1 : 64 * B ^ 3 ≤ B ^ 4 := by
          rw [show B ^ 4 = B * B ^ 3 by ring]; exact Nat.mul_le_mul_right _ h64
        have e2 : 64 * B ≤ B ^ 3 := by
          rw [show B ^ 3 = (B * B) * B by ring]
          exact Nat.mul_le_mul_right B (le_trans h64 (Nat.le_mul_self B))
        have e3 : K ≤ B := hKB
        have e4 : g ≤ B := hgB
        omega
      hKg := hBe _ g (Nat.pow_le_pow_left hKB g) (by omega)
      hKG := hBe _ 2 (mul2 _ _ hKB hgB) (by omega)
      hgg := hBe _ 2 (mul2 _ _ hgB hgB) (by omega)
      hg1 := hBe _ 2 (by
        have : 3 * B ≤ B * B := Nat.mul_le_mul_right B (by omega)
        rw [hB2]; omega) (by omega)
      hgN := hBe _ 2 (mul2 _ _ hgB (show mulNodes s ≤ B by omega)) (by omega)
      hWc := h2 _ (by unfold eTop; omega)
      hclP := h2 _ (by unfold eTop; omega)
      hgrp := h2 _ (by unfold eTop; omega)
      hLK := h2 _ (by unfold eTop; omega)
      deep := deepReq_of hm hmb hK hV ℓ _ hD }

/-! ### The counting expression -/

/-- **`MainReq` from exponents.** -/
theorem mainReq_of {V K0 ℓ n Z : ℕ} (hK : 2 ≤ K0)
    (hZ : eTop K0 ℓ n (2 * Mof K0 ℓ n + 1) ≤ Z)
    (hD : DeepE Z (2 * Mof K0 ℓ n + 1) K0 ℓ (Ltop (Kb K0 ℓ) (Gs K0 ℓ) (sOf n))) (hV : 2 ^ Z ≤ V) :
    MainReq V K0 ℓ n where
  top m hm hmb := topReq_of hK (by omega) hmb hZ hD hV
  hM := by
    refine le_trans ?_ (le_trans (Nat.pow_le_pow_right (by norm_num) hZ) hV)
    have hg : 1 ≤ Gs K0 ℓ := by
      show 1 ≤ 3 * Kb K0 ℓ ^ 8; have := Nat.pow_pos (n := 8) (show 0 < Kb K0 ℓ by have := Kb_ge K0 hK ℓ; omega); omega
    refine le_trans (le_two_pow_log (2 * Mof K0 ℓ n + 1 + 16 * n + Kb K0 ℓ + Gs K0 ℓ + mulNodes (sOf n) + 64)).le
      (Nat.pow_le_pow_right (by norm_num) ?_) |>.trans' (by omega)
    unfold eTop ePolyT
    have : Nat.log 2 (2 * Mof K0 ℓ n + 1 + 16 * n + Kb K0 ℓ + Gs K0 ℓ + mulNodes (sOf n) + 64) + 1 ≤
        (Gs K0 ℓ + 4) * (Nat.log 2 (2 * Mof K0 ℓ n + 1 + 16 * n + Kb K0 ℓ + Gs K0 ℓ + mulNodes (sOf n) + 64) + 1) :=
      Nat.le_mul_of_pos_left _ (by omega)
    omega

end Factoring.Aux
