/-
The uniform engine's exponent: **`uni_exp`**, one exponent `Z n` for all the requirements of
the uniform engine (`K0 = 48`, `ℓ = ellOf n`), with `Z n ≤ n / k + C_k` for every `k`.

* `UGood ℓ n` (`1 ≤ ℓ`, `Kb 48 ℓ ^ 40 ≤ n < Kb 48 (ℓ+1) ^ 40`; holds for `ℓ = ellOf n ≥ 1`), `USmall f`
  (`∀ k ≥ 1`, `k · f ℓ n ≤ n` on good pairs with `ℓ` large); `small_add`, `small_mono`, `small_poly`
  (`c · P^a` with `a < 40`, `P = Kb 48 ℓ`), **`small_bound`** (`USmall f ⇒ f (ellOf n) n ≤ n / k + C`).
* Polynomial bounds in `P` on good pairs (`good_facts`, `good_bounds`, `good_logs`: every logarithm is `≤ 801 P`).
* The top (`eTop_split`, `small_f1`, `small_f2`, `small_f3`), the chain (`ev_W`: `W ≤ 2882 n`; `ev_W0`: the bottom
  bits are `o(n)` because `(23/24)^ℓ → 0`; **`small_zC`**: the level at height `d` is charged `14 N / Kb 48 d`, small
  for `Kb 48 d` large and, for the finitely many low `d`, because `N ≤ 24^D W0`), the polynomial rest (`small_zP`).

Not an audit surface.
-/
module

public import FactoringAux.UniExpChain
public import FactoringAux.UniSet

@[expose] public section

namespace Factoring.Aux

/-! ### UGood pairs and `o(n)` -/

/-- `ℓ` is the number of levels at input length `n`. -/
def UGood (ℓ n : ℕ) : Prop := 1 ≤ ℓ ∧ Kb K0u ℓ ^ 40 ≤ n ∧ n < Kb K0u (ℓ + 1) ^ 40

theorem good_ellOf {n : ℕ} (h : 1 ≤ ellOf n) : UGood (ellOf n) n := ⟨h, Kb_ellOf_le h, lt_Kb_ellOf n⟩

/-- `f` is `o(n)` on good pairs. -/
def USmall (f : ℕ → ℕ → ℕ) : Prop := ∀ k, 1 ≤ k → ∃ X, ∀ ℓ n, X ≤ ℓ → UGood ℓ n → k * f ℓ n ≤ n

theorem small_add {f g : ℕ → ℕ → ℕ} (hf : USmall f) (hg : USmall g) : USmall (fun ℓ n => f ℓ n + g ℓ n) := by
  intro k hk
  obtain ⟨X1, h1⟩ := hf (2 * k) (by omega)
  obtain ⟨X2, h2⟩ := hg (2 * k) (by omega)
  refine ⟨max X1 X2, fun ℓ n hX h => ?_⟩
  have a := h1 ℓ n (le_trans (le_max_left _ _) hX) h
  have b := h2 ℓ n (le_trans (le_max_right _ _) hX) h
  have e : 2 * (k * (f ℓ n + g ℓ n)) = 2 * k * f ℓ n + 2 * k * g ℓ n := by ring
  show k * (f ℓ n + g ℓ n) ≤ n
  omega

theorem small_mono {f g : ℕ → ℕ → ℕ} (hle : ∀ ℓ n, UGood ℓ n → f ℓ n ≤ g ℓ n) (hg : USmall g) : USmall f :=
  fun k hk => (hg k hk).imp fun _ hX ℓ n h1 h2 => le_trans (Nat.mul_le_mul_left _ (hle ℓ n h2)) (hX ℓ n h1 h2)

theorem ev_poly (c a : ℕ) (ha : a < 40) {ℓ n : ℕ} (hc : c ≤ ℓ) (h : UGood ℓ n) : c * Kb K0u ℓ ^ a ≤ n := by
  have hP := Kb48_ge48 ℓ
  have h1 : c ≤ Kb K0u ℓ := le_trans hc (lt_Kb48 ℓ).le
  calc c * Kb K0u ℓ ^ a ≤ Kb K0u ℓ * Kb K0u ℓ ^ a := Nat.mul_le_mul_right _ h1
    _ = Kb K0u ℓ ^ (a + 1) := by ring
    _ ≤ Kb K0u ℓ ^ 40 := Nat.pow_le_pow_right (by omega) (by omega)
    _ ≤ n := h.2.1

theorem small_poly {f : ℕ → ℕ → ℕ} (c a : ℕ) (ha : a < 40) (h : ∀ ℓ n, UGood ℓ n → f ℓ n ≤ c * Kb K0u ℓ ^ a) :
    USmall f := fun k _ => ⟨k * c, fun ℓ n hX hg => by
  have := ev_poly (k * c) a ha hX hg
  calc k * f ℓ n ≤ k * (c * Kb K0u ℓ ^ a) := Nat.mul_le_mul_left _ (h ℓ n hg)
    _ = k * c * Kb K0u ℓ ^ a := by ring
    _ ≤ n := this⟩

/-- **From `o(n)` on good pairs to the required bound.** -/
theorem small_bound {f : ℕ → ℕ → ℕ} (hf : USmall f) : ∀ k, 1 ≤ k → ∃ C, ∀ n, f (ellOf n) n ≤ n / k + C := by
  intro k hk
  obtain ⟨X, hX⟩ := hf k hk
  refine ⟨∑ m ∈ Finset.range (Kb K0u (max X 1) ^ 40), f (ellOf m) m, fun n => ?_⟩
  by_cases hn : Kb K0u (max X 1) ^ 40 ≤ n
  · have h1 : max X 1 ≤ ellOf n := le_ellOf hn
    have h2 := hX (ellOf n) n (le_trans (le_max_left _ _) h1) (good_ellOf (le_trans (le_max_right _ _) h1))
    have : f (ellOf n) n ≤ n / k := (Nat.le_div_iff_mul_le (by omega)).mpr (by rw [mul_comm]; exact h2)
    omega
  · have : f (ellOf n) n ≤ ∑ m ∈ Finset.range (Kb K0u (max X 1) ^ 40), f (ellOf m) m :=
      Finset.single_le_sum (f := fun m => f (ellOf m) m) (fun _ _ => Nat.zero_le _)
        (Finset.mem_range.mpr (by omega))
    exact le_trans this (Nat.le_add_left _ _)

/-! ### Polynomial bounds in `P = Kb 48 ℓ` -/

theorem log_le_P {P x a : ℕ} (h : x ≤ P ^ a) : Nat.log 2 x ≤ P * a := by
  have h1 : P ^ a ≤ 2 ^ (P * a) := by rw [pow_mul]; exact Nat.pow_le_pow_left Nat.lt_two_pow_self.le a
  calc Nat.log 2 x ≤ Nat.log 2 (2 ^ (P * a)) := Nat.log_mono_right (le_trans h h1)
    _ = P * a := Nat.log_pow (by norm_num) _

theorem good_facts {ℓ n : ℕ} (h : UGood ℓ n) :
    48 ≤ Kb K0u ℓ ∧ ℓ ≤ Kb K0u ℓ ∧ 1 ≤ n ∧ n ≤ Kb K0u ℓ ^ 700 ∧ (2 ^ sOf n) ^ 4 ≤ Kb K0u ℓ ^ 701 := by
  obtain ⟨-, h2, h3⟩ := h
  rw [Kb_succ] at h3
  have hP := Kb48_ge48 ℓ
  have hl := (lt_Kb48 ℓ).le
  have hS := S_le_n n
  generalize Kb K0u ℓ = P at h2 h3 hP hl ⊢
  have h9 : (9 : ℕ) ^ 40 ≤ P ^ 60 := le_trans (by norm_num) (Nat.pow_le_pow_left hP 60)
  have hn : n ≤ P ^ 700 := calc n ≤ (9 * P ^ 16) ^ 40 := h3.le
      _ = 9 ^ 40 * P ^ 640 := by ring
      _ ≤ P ^ 60 * P ^ 640 := Nat.mul_le_mul_right _ h9
      _ = P ^ 700 := by ring
  have hn1 : 1 ≤ n := le_trans (Nat.one_le_pow _ _ (by omega)) h2
  refine ⟨hP, hl, hn1, hn, ?_⟩
  calc (2 ^ sOf n) ^ 4 ≤ 8 * P ^ 700 := by omega
    _ ≤ P * P ^ 700 := Nat.mul_le_mul_right _ (by omega)
    _ = P ^ 701 := by ring

theorem good_bounds {ℓ n : ℕ} (h : UGood ℓ n) :
    Gs K0u ℓ ≤ Kb K0u ℓ ^ 9 ∧ Gm4 K0u ℓ ≤ Kb K0u ℓ ^ 36 ∧ ℓ * Gm4 K0u ℓ ≤ Kb K0u ℓ ^ 37 ∧
      mbn K0u ℓ n ≤ Kb K0u ℓ ^ 778 ∧ Wn K0u ℓ n + 1 ≤ Kb K0u ℓ ^ 740 ∧ mulNodes (sOf n) ≤ Kb K0u ℓ ^ 702 := by
  obtain ⟨hP, hl, -, -, hS⟩ := good_facts h
  have hmb := mbn_le (K0 := K0u) ℓ (le_refl _) n
  have hW := Wn_le (K0 := K0u) ℓ n
  have hmN := mulNodes_le (sOf n)
  have hcW : cWn K0u ℓ = 721 + 306 * Gs K0u ℓ + 2 * ℓ * Gm4 K0u ℓ := rfl
  have hcm : cmbn K0u ℓ = 17 + 4 * ℓ * Gm4 K0u ℓ * cWn K0u ℓ := rfl
  have hG4 : Gm4 K0u ℓ = Gs K0u ℓ * Gs K0u ℓ * (Gs K0u ℓ * Gs K0u ℓ) := rfl
  have hg : Gs K0u ℓ = 3 * Kb K0u ℓ ^ 8 := rfl
  generalize (2 ^ sOf n) ^ 4 = S4 at hmb hW hmN hS
  generalize mbn K0u ℓ n = mb at hmb ⊢
  generalize Wn K0u ℓ n = W at hW ⊢
  generalize mulNodes (sOf n) = mN at hmN ⊢
  generalize cmbn K0u ℓ = cm at hcm hmb
  generalize cWn K0u ℓ = cW at hcW hW hcm
  generalize Gm4 K0u ℓ = G4 at hcW hcm hG4 ⊢
  generalize Gs K0u ℓ = g at hcW hG4 hg ⊢
  generalize Kb K0u ℓ = P at hP hl hS hg ⊢
  have hpw : ∀ i j, i ≤ j → P ^ i ≤ P ^ j := fun i j hij => Nat.pow_le_pow_right (by omega) hij
  have hP2 : 2304 ≤ P ^ 2 := by rw [pow_two]; exact Nat.mul_le_mul hP hP
  have hg9 : g ≤ P ^ 9 := by
    rw [hg]
    calc 3 * P ^ 8 ≤ P * P ^ 8 := Nat.mul_le_mul_right _ (by omega)
      _ = P ^ 9 := by ring
  have h36 : G4 ≤ P ^ 36 := by
    rw [hG4]
    calc g * g * (g * g) ≤ P ^ 9 * P ^ 9 * (P ^ 9 * P ^ 9) :=
          Nat.mul_le_mul (Nat.mul_le_mul hg9 hg9) (Nat.mul_le_mul hg9 hg9)
      _ = P ^ 36 := by ring
  have h37 : ℓ * G4 ≤ P ^ 37 := calc ℓ * G4 ≤ P * P ^ 36 := Nat.mul_le_mul hl h36
      _ = P ^ 37 := by ring
  have hcW' : cW ≤ P ^ 39 := by
    have a1 : 721 ≤ P ^ 38 := le_trans (by omega) (le_trans hP2 (hpw 2 38 (by norm_num)))
    have a2 : 306 * g ≤ P ^ 38 := calc 306 * g ≤ P ^ 2 * P ^ 9 := Nat.mul_le_mul (by omega) hg9
        _ = P ^ 11 := by ring
        _ ≤ P ^ 38 := hpw 11 38 (by norm_num)
    have a3 : 2 * ℓ * G4 ≤ P ^ 38 := calc 2 * ℓ * G4 = 2 * (ℓ * G4) := by ring
        _ ≤ P * P ^ 37 := Nat.mul_le_mul (by omega) h37
        _ = P ^ 38 := by ring
    have a4 : 3 * P ^ 38 ≤ P ^ 39 := calc 3 * P ^ 38 ≤ P * P ^ 38 := Nat.mul_le_mul_right _ (by omega)
        _ = P ^ 39 := by ring
    omega
  have hcm' : cm ≤ P ^ 77 := by
    have a1 : 4 * ℓ * G4 * cW ≤ 4 * P ^ 76 := calc 4 * ℓ * G4 * cW = 4 * (ℓ * G4 * cW) := by ring
        _ ≤ 4 * (P ^ 37 * P ^ 39) := Nat.mul_le_mul_left _ (Nat.mul_le_mul h37 hcW')
        _ = 4 * P ^ 76 := by ring
    have a2 : 17 ≤ P ^ 76 := le_trans (by omega : 17 ≤ P) (by simpa using hpw 1 76 (by norm_num))
    have a4 : 5 * P ^ 76 ≤ P ^ 77 := calc 5 * P ^ 76 ≤ P * P ^ 76 := Nat.mul_le_mul_right _ (by omega)
        _ = P ^ 77 := by ring
    omega
  refine ⟨hg9, h36, h37, ?_, ?_, ?_⟩
  · calc mb ≤ cm * S4 := hmb
      _ ≤ P ^ 77 * P ^ 701 := Nat.mul_le_mul hcm' hS
      _ = P ^ 778 := by ring
  · calc W + 1 ≤ cW * S4 := hW
      _ ≤ P ^ 39 * P ^ 701 := Nat.mul_le_mul hcW' hS
      _ = P ^ 740 := by ring
  · calc mN ≤ 12 * S4 := hmN
      _ ≤ P * P ^ 701 := Nat.mul_le_mul (by omega) hS
      _ = P ^ 702 := by ring

/-- Every logarithm is at most `801 P`. -/
theorem good_logs {ℓ n : ℕ} (h : UGood ℓ n) :
    Nat.log 2 (mbn K0u ℓ n) + 1 ≤ 801 * Kb K0u ℓ ∧
    Nat.log 2 (Wn K0u ℓ n + 1) + 1 ≤ 801 * Kb K0u ℓ ∧
    Nat.log 2 (n + ℓ + 64) + 1 ≤ 801 * Kb K0u ℓ ∧
    Nat.log 2 (mbn K0u ℓ n + 16 * n + Kb K0u ℓ + Gs K0u ℓ + mulNodes (sOf n) + 64) + 1 ≤ 801 * Kb K0u ℓ ∧
    Nat.log 2 (Wn K0u ℓ n + mbn K0u ℓ n + Gs K0u ℓ + Gs K0u ℓ + 64) + 1 ≤ 801 * Kb K0u ℓ ∧
    Nat.log 2 (mbn K0u ℓ n + K0u + 64) + 1 ≤ 801 * Kb K0u ℓ ∧
    Nat.log 2 (Kb K0u ℓ + 2) + 1 ≤ 801 * Kb K0u ℓ := by
  obtain ⟨hP, hl, -, hn, -⟩ := good_facts h
  obtain ⟨hg, -, -, hmb, hW, hmN⟩ := good_bounds h
  have hK0 : K0u = 48 := rfl
  rw [hK0]
  generalize mbn K0u ℓ n = mb at hmb ⊢
  generalize Wn K0u ℓ n = W at hW ⊢
  generalize mulNodes (sOf n) = mN at hmN ⊢
  generalize Gs K0u ℓ = g at hg ⊢
  generalize Kb K0u ℓ = P at hP hl hn hg hmb hW hmN ⊢
  have hpw : ∀ i j, i ≤ j → P ^ i ≤ P ^ j := fun i j hij => Nat.pow_le_pow_right (by omega) hij
  have hP2 : 2304 ≤ P ^ 2 := by rw [pow_two]; exact Nat.mul_le_mul hP hP
  have hQ : 48 * P ^ 799 ≤ P ^ 800 := calc 48 * P ^ 799 ≤ P * P ^ 799 := Nat.mul_le_mul_right _ hP
      _ = P ^ 800 := by ring
  have hp1 : P ≤ P ^ 799 := by simpa using hpw 1 799 (by norm_num)
  have a1 : mb ≤ P ^ 799 := le_trans hmb (hpw _ _ (by norm_num))
  have a2 : W + 1 ≤ P ^ 799 := le_trans hW (hpw _ _ (by norm_num))
  have a3 : 16 * n ≤ P ^ 799 := calc 16 * n ≤ P ^ 2 * P ^ 700 := Nat.mul_le_mul (by omega) hn
      _ = P ^ 702 := by ring
      _ ≤ P ^ 799 := hpw _ _ (by norm_num)
  have a5 : g ≤ P ^ 799 := le_trans hg (hpw _ _ (by norm_num))
  have a6 : mN ≤ P ^ 799 := le_trans hmN (hpw _ _ (by norm_num))
  have a7 : 64 ≤ P ^ 799 := le_trans (by omega) (le_trans hP2 (hpw _ _ (by norm_num)))
  have key : ∀ x, x ≤ P ^ 800 → Nat.log 2 x + 1 ≤ 801 * P := fun x hx => by have := log_le_P hx; omega
  exact ⟨key _ (by omega), key _ (by omega), key _ (by omega), key _ (by omega), key _ (by omega),
    key _ (by omega), key _ (by omega)⟩

/-! ### The top -/

theorem eTop_split (ℓ n mb : ℕ) : eTop K0u ℓ n mb ≤ 2160 * (2 ^ sOf n) ^ 4 / Kb K0u ℓ +
    (1662 * (Gs K0u ℓ * (2 ^ sOf n) ^ 3) + ePolyT (Kb K0u ℓ) (Gs K0u ℓ) (sOf n) n mb) := by
  have h := eTop_le K0u ℓ n mb (by norm_num)
  have hK1 : 0 < Kb K0u ℓ := by have := Kb48_ge48 ℓ; omega
  have hg0 : 0 < Gs K0u ℓ := by show 0 < 3 * Kb K0u ℓ ^ 8; positivity
  have h3 : 78 * (2 ^ sOf n) ^ 3 ≤ 78 * (Gs K0u ℓ * (2 ^ sOf n) ^ 3) :=
    Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ hg0)
  set R := 1584 * (Gs K0u ℓ * (2 ^ sOf n) ^ 3) + 78 * (2 ^ sOf n) ^ 3 +
    ePolyT (Kb K0u ℓ) (Gs K0u ℓ) (sOf n) n mb with hR
  have h2 : eTop K0u ℓ n mb ≤ 2160 * (2 ^ sOf n) ^ 4 / Kb K0u ℓ + R := by
    have : eTop K0u ℓ n mb ≤ (2160 * (2 ^ sOf n) ^ 4 + Kb K0u ℓ * R) / Kb K0u ℓ :=
      (Nat.le_div_iff_mul_le hK1).mpr (by rw [mul_comm]; exact h)
    rwa [Nat.add_mul_div_left _ _ hK1] at this
  omega

theorem small_f1 : USmall (fun ℓ n => 2160 * (2 ^ sOf n) ^ 4 / Kb K0u ℓ) := by
  intro k hk
  refine ⟨17280 * k, fun ℓ n hX h => ?_⟩
  obtain ⟨-, -, hn1, -, -⟩ := good_facts h
  have hS := S_le_n n
  have hlt := lt_Kb48 ℓ
  show k * (2160 * (2 ^ sOf n) ^ 4 / Kb K0u ℓ) ≤ n
  generalize (2 ^ sOf n) ^ 4 = S4 at hS ⊢
  generalize Kb K0u ℓ = P at hlt ⊢
  refine le_trans (Nat.mul_div_le_mul_div_assoc _ _ _) (Nat.div_le_of_le_mul ?_)
  have e1 : k * (2160 * S4) ≤ k * (2160 * (4 * n + 4)) := Nat.mul_le_mul_left _ (by omega)
  have e2 : 17280 * k * n ≤ P * n := Nat.mul_le_mul_right _ (by omega)
  have e3 : k ≤ k * n := Nat.le_mul_of_pos_right _ hn1
  have e4 : k * (2160 * (4 * n + 4)) = 8640 * (k * n) + 8640 * k := by ring
  have e5 : 17280 * k * n = 17280 * (k * n) := by ring
  omega

theorem small_f2 : USmall (fun ℓ n => 1662 * (Gs K0u ℓ * (2 ^ sOf n) ^ 3)) := by
  intro k hk
  obtain ⟨M, hM⟩ : ∃ M, M = 64 * 3324 ^ 4 * 81 * k ^ 4 := ⟨_, rfl⟩
  refine ⟨1 + M, fun ℓ n hX h => ?_⟩
  have hc := ev_poly (1 + M) 32 (by norm_num) hX h
  have hS := S_le_n n
  have hab := absorb_cube (3324 * k * Gs K0u ℓ) (2 ^ sOf n)
  have hP1 : 1 ≤ Kb K0u ℓ ^ 32 := Nat.one_le_pow _ _ (by have := Kb48_ge48 ℓ; omega)
  have e1 : 3324 * k * Gs K0u ℓ * (4 * (3324 * k * Gs K0u ℓ)) ^ 3 = M * Kb K0u ℓ ^ 32 := by
    rw [hM]; show 3324 * k * (3 * Kb K0u ℓ ^ 8) * (4 * (3324 * k * (3 * Kb K0u ℓ ^ 8))) ^ 3 = _; ring
  have e2 : 2 * (k * (1662 * (Gs K0u ℓ * (2 ^ sOf n) ^ 3))) = 3324 * k * Gs K0u ℓ * (2 ^ sOf n) ^ 3 := by ring
  have e3 : (1 + M) * Kb K0u ℓ ^ 32 = Kb K0u ℓ ^ 32 + M * Kb K0u ℓ ^ 32 := by ring
  show k * (1662 * (Gs K0u ℓ * (2 ^ sOf n) ^ 3)) ≤ n
  omega

theorem small_f3 : USmall (fun ℓ n => ePolyT (Kb K0u ℓ) (Gs K0u ℓ) (sOf n) n (mbn K0u ℓ n)) := by
  refine small_poly 801 10 (by norm_num) fun ℓ n h => ?_
  have hP := Kb48_ge48 ℓ
  obtain ⟨-, -, -, hA, -⟩ := good_logs h
  unfold ePolyT
  have hg : Gs K0u ℓ + 4 ≤ Kb K0u ℓ ^ 9 := by
    show 3 * Kb K0u ℓ ^ 8 + 4 ≤ _
    have h1 : 1 ≤ Kb K0u ℓ ^ 8 := Nat.one_le_pow _ _ (by omega)
    have h2 : 48 * Kb K0u ℓ ^ 8 ≤ Kb K0u ℓ * Kb K0u ℓ ^ 8 := Nat.mul_le_mul_right _ hP
    have e : Kb K0u ℓ * Kb K0u ℓ ^ 8 = Kb K0u ℓ ^ 9 := by ring
    omega
  calc _ ≤ Kb K0u ℓ ^ 9 * (801 * Kb K0u ℓ) := Nat.mul_le_mul hg hA
    _ = 801 * Kb K0u ℓ ^ 10 := by ring

/-! ### The chain -/

/-- The bits of every level: `W ≤ 2882 n`. -/
theorem ev_W : ∃ X, ∀ ℓ n, X ≤ ℓ → UGood ℓ n → Wn K0u ℓ n ≤ 2882 * n := by
  refine ⟨45451759374148, fun ℓ n hX h => ?_⟩
  have hev := ev_poly 45451759374148 37 (by norm_num) hX h
  have hP := Kb48_ge48 ℓ
  obtain ⟨-, -, h37, -⟩ := good_bounds h
  have hS := S_le_n n
  have hab := absorb_cube (306 * Gs K0u ℓ) (2 ^ sOf n)
  have hW : Wn K0u ℓ n = 720 * (2 ^ sOf n) ^ 4 + 306 * (Gs K0u ℓ * (2 ^ sOf n) ^ 3) + 2 * ℓ * Gm4 K0u ℓ := rfl
  have e1 : 306 * (Gs K0u ℓ * (2 ^ sOf n) ^ 3) = 306 * Gs K0u ℓ * (2 ^ sOf n) ^ 3 := by ring
  have e2 : 306 * Gs K0u ℓ * (4 * (306 * Gs K0u ℓ)) ^ 3 = 45451759371264 * Kb K0u ℓ ^ 32 := by
    show 306 * (3 * Kb K0u ℓ ^ 8) * (4 * (306 * (3 * Kb K0u ℓ ^ 8))) ^ 3 = _; ring
  have e3 : 2 * ℓ * Gm4 K0u ℓ = 2 * (ℓ * Gm4 K0u ℓ) := by ring
  have p1 : Kb K0u ℓ ^ 32 ≤ Kb K0u ℓ ^ 37 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have p0 : 1 ≤ Kb K0u ℓ ^ 37 := Nat.one_le_pow _ _ (by omega)
  have p2 : 45451759371264 * Kb K0u ℓ ^ 32 ≤ 45451759371264 * Kb K0u ℓ ^ 37 := Nat.mul_le_mul_left _ p1
  omega

theorem pow_dec {b j : ℕ} (h : b * 23 ^ j ≤ 24 ^ j) : ∀ ℓ, j ≤ ℓ → b * 23 ^ ℓ ≤ 24 ^ ℓ := by
  intro ℓ hl
  induction ℓ, hl using Nat.le_induction with
  | base => exact h
  | succ m _ ih =>
      calc b * 23 ^ (m + 1) = 23 * (b * 23 ^ m) := by ring
        _ ≤ 23 * 24 ^ m := Nat.mul_le_mul_left _ ih
        _ ≤ 24 ^ (m + 1) := by rw [pow_succ]; omega

/-- The bits of the bottom are `o(n)`. -/
theorem ev_W0 (a : ℕ) : ∃ X, ∀ ℓ n, X ≤ ℓ → UGood ℓ n → a * W0n K0u ℓ n ≤ n := by
  obtain ⟨X1, hX1⟩ := ev_W
  obtain ⟨j, hj⟩ := exists_ell (2 * a * 2882)
  refine ⟨X1 + j + 6 * a, fun ℓ n hX h => ?_⟩
  have hW := hX1 ℓ n (by omega) h
  have hb : 2 * a * 2882 * 23 ^ ℓ ≤ 24 ^ ℓ :=
    pow_dec (le_trans (Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ (by omega))) hj) ℓ (by omega)
  have hev := ev_poly (6 * a) 37 (by norm_num) (by omega) h
  have hP := Kb48_ge48 ℓ
  obtain ⟨-, -, h37, -⟩ := good_bounds h
  have hNt : Ntn K0u ℓ n ≤ Wn K0u ℓ n := by unfold Wn; omega
  have hW0 : W0n K0u ℓ n = 23 ^ ℓ * Ntn K0u ℓ n / 24 ^ ℓ + 1 + 2 * ℓ * Gm4 K0u ℓ := rfl
  have m1 : 2 * a * (23 ^ ℓ * Ntn K0u ℓ n / 24 ^ ℓ) ≤ n := by
    refine le_trans (Nat.mul_div_le_mul_div_assoc _ _ _) (Nat.div_le_of_le_mul ?_)
    calc 2 * a * (23 ^ ℓ * Ntn K0u ℓ n) ≤ 2 * a * (23 ^ ℓ * (2882 * n)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (le_trans hNt hW))
      _ = (2 * a * 2882 * 23 ^ ℓ) * n := by ring
      _ ≤ 24 ^ ℓ * n := Nat.mul_le_mul_right _ hb
  have m2 : 2 * a * (1 + 2 * ℓ * Gm4 K0u ℓ) ≤ n := by
    have : 1 + 2 * ℓ * Gm4 K0u ℓ ≤ 3 * Kb K0u ℓ ^ 37 := by
      have : 1 ≤ Kb K0u ℓ ^ 37 := Nat.one_le_pow _ _ (by omega)
      have : 2 * ℓ * Gm4 K0u ℓ = 2 * (ℓ * Gm4 K0u ℓ) := by ring
      omega
    calc _ ≤ 2 * a * (3 * Kb K0u ℓ ^ 37) := Nat.mul_le_mul_left _ this
      _ = 6 * a * Kb K0u ℓ ^ 37 := by ring
      _ ≤ n := hev
  rw [hW0]
  have e : a * (23 ^ ℓ * Ntn K0u ℓ n / 24 ^ ℓ + 1 + 2 * ℓ * Gm4 K0u ℓ) =
      a * (23 ^ ℓ * Ntn K0u ℓ n / 24 ^ ℓ) + a * (1 + 2 * ℓ * Gm4 K0u ℓ) := by ring
  have e2 : 2 * a * (23 ^ ℓ * Ntn K0u ℓ n / 24 ^ ℓ) = 2 * (a * (23 ^ ℓ * Ntn K0u ℓ n / 24 ^ ℓ)) := by ring
  have e3 : 2 * a * (1 + 2 * ℓ * Gm4 K0u ℓ) = 2 * (a * (1 + 2 * ℓ * Gm4 K0u ℓ)) := by ring
  omega

/-- The largest exponent along the chain. -/
def zC (ℓ n : ℕ) : ℕ := chainMax (mbn K0u ℓ n) K0u ℓ (Ltop (Kb K0u ℓ) (Gs K0u ℓ) (sOf n))

/-- **The chain's exponents are `o(n)`.** -/
theorem small_zC : USmall zC := by
  intro k hk
  obtain ⟨D, hD⟩ : ∃ D, D = 80696 * k := ⟨_, rfl⟩
  obtain ⟨X1, hX1⟩ := ev_W
  obtain ⟨X2, hX2⟩ := ev_W0 (2 * k * 24 ^ D)
  refine ⟨X1 + X2 + 2 * k * 8017 + 4 * k + 4 * k * 801, fun ℓ n hX h => ?_⟩
  have hP := Kb48_ge48 ℓ
  obtain ⟨-, h36, -⟩ := good_bounds h
  obtain ⟨-, -, -, -, hA2, hA3, -⟩ := good_logs h
  have hW := hX1 ℓ n (by omega) h
  have hW0 := hX2 ℓ n (by omega) h
  have q1 := ev_poly (2 * k * 8017) 37 (by norm_num) (by omega) h
  have q2 := ev_poly (4 * k) 36 (by norm_num) (by omega) h
  have q3 := ev_poly (4 * k * 801) 1 (by norm_num) (by omega) h
  rw [pow_one] at q3
  have hG4 : Gs K0u ℓ * Gs K0u ℓ * (Gs K0u ℓ * Gs K0u ℓ) = Gm4 K0u ℓ := rfl
  have h24 : 1 ≤ 24 ^ D := Nat.one_le_pow _ _ (by norm_num)
  have hkW0 : 2 * k * W0n K0u ℓ n ≤ n :=
    le_trans (Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ h24)) hW0
  show k * chainMax (mbn K0u ℓ n) K0u ℓ (Ltop (Kb K0u ℓ) (Gs K0u ℓ) (sOf n)) ≤ n
  suffices hc : chainMax (mbn K0u ℓ n) K0u ℓ (Ltop (Kb K0u ℓ) (Gs K0u ℓ) (sOf n)) ≤ n / k by
    exact le_trans (Nat.mul_le_mul_left _ hc) (Nat.mul_div_le n k)
  refine chainMax_le K0u (n / k) (mbn K0u ℓ n) (Wn K0u ℓ n) (W0n K0u ℓ n) (Gs K0u ℓ) (le_refl _) ?_ ?_ ℓ _
    (Kb_le_Gs (K0 := K0u) ℓ (by norm_num)) (chain_hyp1 (K0 := K0u) ℓ (by norm_num) n)
    (chain_hyp2 (K0 := K0u) ℓ (by norm_num) n)
  · intro d N hN hN23
    rw [hG4] at hN ⊢
    apply (Nat.le_div_iff_mul_le (by omega)).mpr
    set G4 := Gm4 K0u ℓ
    have hK48 : 48 ≤ Kb K0u d := Kb48_ge48 d
    have hdK : d < Kb K0u d := lt_Kb48 d
    set B := Nat.log 2 (Wn K0u ℓ n + mbn K0u ℓ n + Gs K0u ℓ + Gs K0u ℓ + 64) + 1 with hB
    have hpoly : 2 * k * (7 + (G4 + 9) * B) ≤ n := by
      have t1 : (G4 + 9) * B ≤ 10 * Kb K0u ℓ ^ 36 * (801 * Kb K0u ℓ) := by
        refine Nat.mul_le_mul ?_ hA2
        have : 1 ≤ Kb K0u ℓ ^ 36 := Nat.one_le_pow _ _ (by omega)
        omega
      have t2 : 10 * Kb K0u ℓ ^ 36 * (801 * Kb K0u ℓ) = 8010 * Kb K0u ℓ ^ 37 := by ring
      have t3 : 1 ≤ Kb K0u ℓ ^ 37 := Nat.one_le_pow _ _ (by omega)
      calc 2 * k * (7 + (G4 + 9) * B) ≤ 2 * k * (8017 * Kb K0u ℓ ^ 37) := Nat.mul_le_mul_left _ (by omega)
        _ = 2 * k * 8017 * Kb K0u ℓ ^ 37 := by ring
        _ ≤ n := q1
    have hmain : 2 * k * (14 * (N + 2 * G4) / Kb K0u d) ≤ n := by
      by_cases hDK : D ≤ Kb K0u d
      · refine le_trans (Nat.mul_div_le_mul_div_assoc _ _ _) (Nat.div_le_of_le_mul ?_)
        calc 2 * k * (14 * (N + 2 * G4)) ≤ 2 * k * (14 * (2882 * n)) :=
              Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))
          _ = D * n := by rw [hD]; ring
          _ ≤ Kb K0u d * n := Nat.mul_le_mul_right _ hDK
      · have hd1 : d + 1 ≤ D := by omega
        have hND : N ≤ 24 ^ D * W0n K0u ℓ n := by
          have e : 23 ^ D = 23 ^ (D - (d + 1)) * 23 ^ (d + 1) := by rw [← pow_add]; congr 1; omega
          have e' : 24 ^ D = 24 ^ (D - (d + 1)) * 24 ^ (d + 1) := by rw [← pow_add]; congr 1; omega
          calc N ≤ 23 ^ D * N := Nat.le_mul_of_pos_left _ (by positivity)
            _ = 23 ^ (D - (d + 1)) * (23 ^ (d + 1) * N) := by rw [e, mul_assoc]
            _ ≤ 24 ^ (D - (d + 1)) * (24 ^ (d + 1) * W0n K0u ℓ n) :=
                Nat.mul_le_mul (Nat.pow_le_pow_left (by norm_num) _) hN23
            _ = 24 ^ D * W0n K0u ℓ n := by rw [e', mul_assoc]
        have hdiv : 2 * k * (14 * (N + 2 * G4) / Kb K0u d) ≤ k * (N + 2 * G4) := by
          refine le_trans (Nat.mul_div_le_mul_div_assoc _ _ _) ?_
          refine le_trans (Nat.div_le_div_left hK48 (by norm_num)) ?_
          have : 2 * k * (14 * (N + 2 * G4)) = 28 * (k * (N + 2 * G4)) := by ring
          rw [this]; omega
        have h1 : 2 * (k * N) ≤ n := by
          calc 2 * (k * N) ≤ 2 * (k * (24 ^ D * W0n K0u ℓ n)) :=
                Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hND)
            _ = 2 * k * 24 ^ D * W0n K0u ℓ n := by ring
            _ ≤ n := hW0
        have h2 : 4 * k * G4 ≤ n := le_trans (Nat.mul_le_mul_left _ h36) q2
        have e : k * (N + 2 * G4) = k * N + 2 * (k * G4) := by ring
        have e2 : 4 * k * G4 = 4 * (k * G4) := by ring
        omega
    have e1 : 2 * k * (14 * (N + 2 * G4) / Kb K0u d) = 2 * (k * (14 * (N + 2 * G4) / Kb K0u d)) := by ring
    have e2 : 2 * k * (7 + (G4 + 9) * B) = 2 * (k * (7 + (G4 + 9) * B)) := by ring
    have e3 : (14 * (N + 2 * G4) / Kb K0u d + 7 + (G4 + 9) * B) * k =
        k * (14 * (N + 2 * G4) / Kb K0u d) + k * (7 + (G4 + 9) * B) := by ring
    omega
  · apply (Nat.le_div_iff_mul_le (by omega)).mpr
    have e1 : (W0n K0u ℓ n + 2 * (Nat.log 2 (mbn K0u ℓ n + K0u + 64) + 1)) * k =
        k * W0n K0u ℓ n + 2 * (k * (Nat.log 2 (mbn K0u ℓ n + K0u + 64) + 1)) := by ring
    have e2 : 2 * k * W0n K0u ℓ n = 2 * (k * W0n K0u ℓ n) := by ring
    have e3 : 4 * (k * (Nat.log 2 (mbn K0u ℓ n + K0u + 64) + 1)) ≤ 4 * k * 801 * Kb K0u ℓ := by
      calc 4 * (k * (Nat.log 2 (mbn K0u ℓ n + K0u + 64) + 1)) ≤ 4 * (k * (801 * Kb K0u ℓ)) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hA3)
        _ = 4 * k * 801 * Kb K0u ℓ := by ring
    omega

/-! ### The polynomial rest and the exponent -/

/-- The polynomial items: the paths, the modulus, `n + ℓ + 64`, `Kb^40`, the level's value bound `lvlV`. -/
def zP (ℓ n : ℕ) : ℕ := ℓ * Gm4 K0u ℓ * (Nat.log 2 (Wn K0u ℓ n + 1) + 1) + (Nat.log 2 (mbn K0u ℓ n) + 1) +
  (Nat.log 2 (n + ℓ + 64) + 1) + 40 * (Nat.log 2 (Kb K0u ℓ) + 1) +
  (3 * Kb K0u ℓ ^ 8 + 50) * (Nat.log 2 (Kb K0u ℓ + 2) + 1)

theorem small_zP : USmall zP := by
  refine small_poly 36000 38 (by norm_num) fun ℓ n h => ?_
  have hP := Kb48_ge48 ℓ
  obtain ⟨-, -, h37, -⟩ := good_bounds h
  obtain ⟨a1, a2, a3, -, -, -, a7⟩ := good_logs h
  have a4 : Nat.log 2 (Kb K0u ℓ) + 1 ≤ 801 * Kb K0u ℓ :=
    le_trans (Nat.add_le_add_right (Nat.log_mono_right (by omega : Kb K0u ℓ ≤ Kb K0u ℓ + 2)) 1) a7
  unfold zP
  set P := Kb K0u ℓ
  have hpw : ∀ i j, i ≤ j → P ^ i ≤ P ^ j := fun i j hij => Nat.pow_le_pow_right (by omega) hij
  have p1 : P ≤ P ^ 38 := by simpa using hpw 1 38 (by norm_num)
  have t1 : ℓ * Gm4 K0u ℓ * (Nat.log 2 (Wn K0u ℓ n + 1) + 1) ≤ 801 * P ^ 38 :=
    calc _ ≤ P ^ 37 * (801 * P) := Nat.mul_le_mul h37 a2
      _ = 801 * P ^ 38 := by ring
  have t5 : (3 * P ^ 8 + 50) * (Nat.log 2 (P + 2) + 1) ≤ 801 * P ^ 38 := by
    have h1 : 48 ≤ P ^ 8 := le_trans hP (by simpa using hpw 1 8 (by norm_num))
    have h2 : 48 * P ^ 8 ≤ P * P ^ 8 := Nat.mul_le_mul_right _ hP
    have h3 : 3 * P ^ 8 + 50 ≤ P ^ 9 := by
      have e : P * P ^ 8 = P ^ 9 := by ring
      omega
    calc _ ≤ P ^ 9 * (801 * P) := Nat.mul_le_mul h3 a7
      _ = 801 * P ^ 10 := by ring
      _ ≤ 801 * P ^ 38 := Nat.mul_le_mul_left _ (hpw _ _ (by norm_num))
  generalize (3 * P ^ 8 + 50) * (Nat.log 2 (P + 2) + 1) = T5 at t5 ⊢
  omega

/-- The top's exponents. -/
def zT (ℓ n : ℕ) : ℕ := eTop K0u ℓ n (mbn K0u ℓ n)

theorem small_zT : USmall zT :=
  small_mono (fun ℓ n _ => eTop_split ℓ n _) (small_add small_f1 (small_add small_f2 small_f3))

/-- **The exponent of the uniform engine** at `ℓ` levels. -/
def Zof (ℓ n : ℕ) : ℕ := zT ℓ n + zC ℓ n + zP ℓ n

/-- **The exponent of the uniform engine** at input length `n`. -/
def Zu (n : ℕ) : ℕ := Zof (ellOf n) n

theorem small_Zof : USmall Zof := small_add (small_add small_zT small_zC) small_zP

theorem two_pow_le {a b : ℕ} (h : a ≤ b) : 2 ^ a ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) h

/-- **The exponent of the uniform engine is `o(n)`**: one `Z` bounds every requirement of the uniform engine
(`K0 = 48`, `ℓ = ellOf n`), and `Z n ≤ n / k + C_k` for every `k ≥ 1`. -/
theorem uni_exp : ∃ Z : ℕ → ℕ,
    (∀ n, eTop K0u (ellOf n) n (2 * Mof K0u (ellOf n) n + 1) ≤ Z n) ∧
    (∀ n, DeepE (Z n) (2 * Mof K0u (ellOf n) n + 1) K0u (ellOf n)
      (Ltop (Kb K0u (ellOf n)) (Gs K0u (ellOf n)) (sOf n))) ∧
    (∀ n, NPof K0u (ellOf n) (Ltop (Kb K0u (ellOf n)) (Gs K0u (ellOf n)) (sOf n)) ≤ 2 ^ Z n) ∧
    (∀ n, 2 * Mof K0u (ellOf n) n + 1 ≤ 2 ^ Z n) ∧ (∀ n, n + ellOf n + 64 ≤ 2 ^ Z n) ∧
    (∀ n, Kb K0u (ellOf n) ^ 40 ≤ 2 ^ Z n) ∧ (∀ n, lvlV (Kb K0u (ellOf n)) ≤ 2 ^ Z n) ∧
    ∀ k : ℕ, 1 ≤ k → ∃ C : ℕ, ∀ n, Z n ≤ n / k + C := by
  have hT : ∀ n, zT (ellOf n) n ≤ Zu n := fun n => by unfold Zu Zof; omega
  have hC : ∀ n, zC (ellOf n) n ≤ Zu n := fun n => by unfold Zu Zof; omega
  have hP : ∀ n, zP (ellOf n) n ≤ Zu n := fun n => by unfold Zu Zof; omega
  refine ⟨Zu, fun n => hT n, fun n => deepE_chainMax _ _ _ _ _ (hC n), fun n => ?_, fun n => ?_, fun n => ?_,
    fun n => ?_, fun n => ?_, small_bound small_Zof⟩
  · have h := hP n
    unfold zP at h
    refine le_trans (NPof_le K0u (Wn K0u (ellOf n) n) (Gs K0u (ellOf n)) (le_refl _) (ellOf n) _
      (Kb_le_Gs (K0 := K0u) (ellOf n) (by norm_num)) (chain_hyp1 (K0 := K0u) (ellOf n) (by norm_num) n)) ?_
    refine le_trans (pow_le_two_pow_log _ _) (two_pow_le ?_)
    show ellOf n * Gm4 K0u (ellOf n) * (Nat.log 2 (Wn K0u (ellOf n) n + 1) + 1) ≤ Zu n
    omega
  · have h := hP n
    unfold zP at h
    exact le_trans (le_two_pow_log _).le (two_pow_le (by unfold mbn at h; omega))
  · have h := hP n
    unfold zP at h
    exact le_trans (le_two_pow_log _).le (two_pow_le (by omega))
  · have h := hP n
    unfold zP at h
    refine le_trans (pow_le_two_pow_log _ _) (two_pow_le ?_)
    omega
  · have h := hP n
    unfold zP at h
    refine le_trans (pow_le_two_pow_log _ _) (two_pow_le ?_)
    omega

end Factoring.Aux
