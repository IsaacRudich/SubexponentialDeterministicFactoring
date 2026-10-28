/-
The cost of the counting expression: the parameters per `k` and the counting lemma's hypothesis.

* `absorb_cube`, `log_absorb`: lower-order terms (`S³`, `log S`) fit below `S⁴/4` plus a constant;
* `exists_ell`: some `ℓ` with `a (ℓ+1) 23^ℓ ≤ 24^ℓ`;
* **`count_cost`**: for every `k ≥ 1`, parameters `K0, ℓ` and `B n ≤ C · 2^(n/k)` bounding the cost of
  `mainE K0 ℓ` — the hypothesis of `count_of_mainE`.

Not an audit surface.
-/
module

public import FactoringAux.EngineCostRate
public import FactoringAux.Final

@[expose] public section

namespace Factoring.Aux

open Finset Ex

/-! ### Lower-order terms -/

theorem absorb_cube (β S : ℕ) : β * S ^ 3 ≤ S ^ 4 / 4 + β * (4 * β) ^ 3 := by
  rcases Nat.lt_or_ge S (4 * β) with h | h
  · exact le_trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h.le 3)) (Nat.le_add_left _ _)
  · refine le_trans ?_ (Nat.le_add_right _ _)
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    calc β * S ^ 3 * 4 = (4 * β) * S ^ 3 := by ring
      _ ≤ S * S ^ 3 := Nat.mul_le_mul_right _ h
      _ = S ^ 4 := by ring

theorem s_le_S3 (s : ℕ) : s ≤ (2 ^ s) ^ 3 :=
  le_trans Nat.lt_two_pow_self.le (Nat.le_self_pow (by norm_num) _)

theorem log_le_S {X C s : ℕ} (h : X ≤ C * (2 ^ s) ^ 4) : Nat.log 2 X ≤ Nat.log 2 C + 1 + 4 * s := by
  have h1 : X < 2 ^ (Nat.log 2 C + 1 + 4 * s) := by
    calc X ≤ C * (2 ^ s) ^ 4 := h
      _ < 2 ^ (Nat.log 2 C + 1) * (2 ^ s) ^ 4 :=
          Nat.mul_lt_mul_of_pos_right (le_two_pow_log C) (by positivity)
      _ = 2 ^ (Nat.log 2 C + 1 + 4 * s) := by rw [← pow_mul, ← pow_add]; ring_nf
  exact (Nat.log_lt_of_lt_pow' (by omega) h1).le

theorem log_absorb (α C : ℕ) {X s : ℕ} (h : X ≤ C * (2 ^ s) ^ 4) :
    α * (Nat.log 2 X + 1) ≤ (2 ^ s) ^ 4 / 4 + (α * (Nat.log 2 C + 2) + 4 * α * (4 * (4 * α)) ^ 3) := by
  have h1 := log_le_S h
  have h2 := s_le_S3 s
  have h3 := absorb_cube (4 * α) (2 ^ s)
  have h4 : α * (Nat.log 2 X + 1) ≤ α * (Nat.log 2 C + 2) + 4 * α * (2 ^ s) ^ 3 := by
    have := Nat.mul_le_mul_left α (show Nat.log 2 X + 1 ≤ Nat.log 2 C + 2 + 4 * (2 ^ s) ^ 3 by omega)
    have e : α * (Nat.log 2 C + 2 + 4 * (2 ^ s) ^ 3) = α * (Nat.log 2 C + 2) + 4 * α * (2 ^ s) ^ 3 := by ring
    omega
  omega

/-! ### The choice of `ℓ` -/

theorem two_pow_ge_sq : ∀ j, 4 ≤ j → j * j ≤ 2 ^ j
  | 0, h | 1, h | 2, h | 3, h => by omega
  | 4, _ => by norm_num
  | j + 5, _ => by
      have ih := two_pow_ge_sq (j + 4) (by omega)
      rw [pow_succ]; nlinarith

theorem num_23_24 : 2 * 23 ^ 23 ≤ 24 ^ 23 := by norm_num

theorem pow_23_24 (j : ℕ) : 2 ^ j * 23 ^ (23 * j) ≤ 24 ^ (23 * j) := by
  induction j with
  | zero => simp
  | succ j ih =>
      have e1 : 2 ^ (j + 1) * 23 ^ (23 * (j + 1)) = (2 ^ j * 23 ^ (23 * j)) * (2 * 23 ^ 23) := by ring
      have e2 : 24 ^ (23 * (j + 1)) = 24 ^ (23 * j) * 24 ^ 23 := by ring
      rw [e1, e2]
      exact Nat.mul_le_mul ih num_23_24

theorem exists_ell (a : ℕ) : ∃ ℓ, a * (ℓ + 1) * 23 ^ ℓ ≤ 24 ^ ℓ := by
  obtain ⟨j, hj⟩ : ∃ j, j = 24 * (a + 1) := ⟨_, rfl⟩
  refine ⟨23 * j, ?_⟩
  have hj1 : 1 ≤ j := by omega
  have h1 : a * (23 * j + 1) ≤ j * j := by
    have e : a * (23 * j + 1) = 23 * (a * j) + a := by ring
    have e2 : j * j = 24 * (a * j) + 24 * j := by rw [hj]; ring
    have : a ≤ a * j := Nat.le_mul_of_pos_right _ hj1
    omega
  have h2 := two_pow_ge_sq j (by omega)
  have h3 := pow_23_24 j
  calc a * (23 * j + 1) * 23 ^ (23 * j) ≤ 2 ^ j * 23 ^ (23 * j) :=
        Nat.mul_le_mul_right _ (le_trans h1 h2)
    _ ≤ 24 ^ (23 * j) := h3

/-! ### The bounds along `n` -/

/-- `G⁴` at the top. -/
def Gm4 (K0 ℓ : ℕ) : ℕ := Gs K0 ℓ * Gs K0 ℓ * (Gs K0 ℓ * Gs K0 ℓ)

/-- The top clique's bits, bounded. -/
def Ntn (K0 ℓ n : ℕ) : ℕ := 720 * (2 ^ sOf n) ^ 4 + 306 * (Gs K0 ℓ * (2 ^ sOf n) ^ 3)

/-- The bound on the bits of every level. -/
def Wn (K0 ℓ n : ℕ) : ℕ := Ntn K0 ℓ n + 2 * ℓ * Gm4 K0 ℓ

/-- The bound on the bits of the brute force. -/
def W0n (K0 ℓ n : ℕ) : ℕ := 23 ^ ℓ * Ntn K0 ℓ n / 24 ^ ℓ + 1 + 2 * ℓ * Gm4 K0 ℓ

/-- The modulus bound. -/
def mbn (K0 ℓ n : ℕ) : ℕ := 2 * Mof K0 ℓ n + 1

section Bounds

variable {K0 : ℕ} (ℓ : ℕ) (hK : 48 ≤ K0)
include hK

theorem Kb_le_Gs : Kb K0 ℓ ≤ Gs K0 ℓ := K_le_G _

theorem chain_hyp1 (n : ℕ) : Kb K0 ℓ ^ 2 * Ltop (Kb K0 ℓ) (Gs K0 ℓ) (sOf n) + 2 * ℓ * Gm4 K0 ℓ ≤ Wn K0 ℓ n := by
  have := Ntop_S (Kb K0 ℓ) (Gs K0 ℓ) (sOf n) (le_trans (by omega) (Kb_ge K0 (by omega) ℓ))
  unfold Wn Ntn; omega

theorem chain_hyp2 (n : ℕ) : 23 ^ ℓ * (Kb K0 ℓ ^ 2 * Ltop (Kb K0 ℓ) (Gs K0 ℓ) (sOf n)) +
    24 ^ ℓ * (2 * ℓ * Gm4 K0 ℓ) ≤ 24 ^ ℓ * W0n K0 ℓ n := by
  have h := Ntop_S (Kb K0 ℓ) (Gs K0 ℓ) (sOf n) (le_trans (by omega) (Kb_ge K0 (by omega) ℓ))
  have h1 : 23 ^ ℓ * (Kb K0 ℓ ^ 2 * Ltop (Kb K0 ℓ) (Gs K0 ℓ) (sOf n)) ≤ 23 ^ ℓ * Ntn K0 ℓ n :=
    Nat.mul_le_mul_left _ h
  have h2 : 23 ^ ℓ * Ntn K0 ℓ n < 24 ^ ℓ * (23 ^ ℓ * Ntn K0 ℓ n / 24 ^ ℓ + 1) := by
    have := Nat.div_add_mod (23 ^ ℓ * Ntn K0 ℓ n) (24 ^ ℓ)
    have := Nat.mod_lt (23 ^ ℓ * Ntn K0 ℓ n) (Nat.pow_pos (n := ℓ) (show 0 < 24 by norm_num))
    rw [mul_add, mul_one]; omega
  unfold W0n
  have e : 24 ^ ℓ * (23 ^ ℓ * Ntn K0 ℓ n / 24 ^ ℓ + 1 + 2 * ℓ * Gm4 K0 ℓ) =
      24 ^ ℓ * (23 ^ ℓ * Ntn K0 ℓ n / 24 ^ ℓ + 1) + 24 ^ ℓ * (2 * ℓ * Gm4 K0 ℓ) := by ring
  omega

/-- `W + 1 ≤ cWn · S⁴`. -/
def cWn (K0 ℓ : ℕ) : ℕ := 721 + 306 * Gs K0 ℓ + 2 * ℓ * Gm4 K0 ℓ

/-- `mb ≤ cmbn · S⁴`. -/
def cmbn (K0 ℓ : ℕ) : ℕ := 17 + 4 * ℓ * Gm4 K0 ℓ * cWn K0 ℓ

omit hK in
theorem Wn_le (n : ℕ) : Wn K0 ℓ n + 1 ≤ cWn K0 ℓ * (2 ^ sOf n) ^ 4 := by
  have h1 : 1 ≤ (2 ^ sOf n) ^ 4 := Nat.one_le_pow _ _ (Nat.two_pow_pos _)
  have h2 : (2 ^ sOf n) ^ 3 ≤ (2 ^ sOf n) ^ 4 := Nat.pow_le_pow_right (Nat.two_pow_pos _) (by norm_num)
  have h3 : Gs K0 ℓ * (2 ^ sOf n) ^ 3 ≤ Gs K0 ℓ * (2 ^ sOf n) ^ 4 := Nat.mul_le_mul_left _ h2
  have h4 : 2 * ℓ * Gm4 K0 ℓ + 1 ≤ (2 * ℓ * Gm4 K0 ℓ + 1) * (2 ^ sOf n) ^ 4 := Nat.le_mul_of_pos_right _ h1
  unfold Wn Ntn cWn
  have e : (721 + 306 * Gs K0 ℓ + 2 * ℓ * Gm4 K0 ℓ) * (2 ^ sOf n) ^ 4 = 720 * (2 ^ sOf n) ^ 4 +
      306 * (Gs K0 ℓ * (2 ^ sOf n) ^ 4) + (2 * ℓ * Gm4 K0 ℓ + 1) * (2 ^ sOf n) ^ 4 := by ring
  omega

theorem mbn_le (n : ℕ) : mbn K0 ℓ n ≤ cmbn K0 ℓ * (2 ^ sOf n) ^ 4 := by
  have hm : mlogN K0 ℓ (Ltop (Kb K0 ℓ) (Gs K0 ℓ) (sOf n)) ≤ 2 * ℓ * Gm4 K0 ℓ * (Wn K0 ℓ n + 1) :=
    mlogN_le K0 (Wn K0 ℓ n) (Gs K0 ℓ) hK ℓ _ (Kb_le_Gs ℓ hK) (chain_hyp1 ℓ hK n)
  have hw := Wn_le (K0 := K0) ℓ n
  have hn := n_le_S n
  have h1 : 1 ≤ (2 ^ sOf n) ^ 4 := Nat.one_le_pow _ _ (Nat.two_pow_pos _)
  have h5 : 2 * ℓ * Gm4 K0 ℓ * (Wn K0 ℓ n + 1) ≤ 2 * ℓ * Gm4 K0 ℓ * (cWn K0 ℓ * (2 ^ sOf n) ^ 4) :=
    Nat.mul_le_mul_left _ hw
  unfold mbn Mof cmbn
  have e : (17 + 4 * ℓ * Gm4 K0 ℓ * cWn K0 ℓ) * (2 ^ sOf n) ^ 4 = 17 * (2 ^ sOf n) ^ 4 +
      2 * (2 * ℓ * Gm4 K0 ℓ * (cWn K0 ℓ * (2 ^ sOf n) ^ 4)) := by ring
  rw [e]
  omega

end Bounds

/-! ### The three exponent families, for the parameters of `k` -/

/-- `E = 3 (24 ℓ + 84) k`. -/
def Ek (k ℓ : ℕ) : ℕ := 3 * (24 * ℓ + 84) * k

/-- `K0 = 161280 E`. -/
def K0k (k ℓ : ℕ) : ℕ := 161280 * Ek k ℓ

theorem mulNodes_le (s : ℕ) : mulNodes s ≤ 12 * (2 ^ s) ^ 4 := by
  have h1 : 2 ^ s ≤ (2 ^ s) ^ 4 := Nat.le_self_pow (by norm_num) _
  have h2 : (2 ^ s) ^ 2 ≤ (2 ^ s) ^ 4 := Nat.pow_le_pow_right (Nat.two_pow_pos _) (by norm_num)
  unfold mulNodes; rw [pA_S]
  have e : 2 * 2 ^ s * (2 * 2 ^ s) = 4 * (2 ^ s) ^ 2 := by ring
  omega

section Exps

variable (k ℓ : ℕ) (hk : 1 ≤ k)
include hk

theorem Ek_pos : 1 ≤ Ek k ℓ := by unfold Ek; nlinarith

theorem K0k_ge : 48 ≤ K0k k ℓ := by have := Ek_pos k ℓ hk; unfold K0k; omega

/-- **The top's exponents** fit the budget. -/
theorem budget_top : ∃ c, ∀ n, 8 * Ek k ℓ * eTop (K0k k ℓ) ℓ n (mbn (K0k k ℓ) ℓ n) ≤ (2 ^ sOf n) ^ 4 + c := by
  set E := Ek k ℓ
  set K0 := K0k k ℓ
  set K := Kb K0 ℓ
  set g := Gs K0 ℓ
  have hE := Ek_pos k ℓ hk
  have hK0 : 48 ≤ K0 := K0k_ge k ℓ hk
  have hKK : K0 ≤ K := Kb_mono K0 (by omega) (Nat.zero_le ℓ)
  set Carg := cmbn K0 ℓ + 64 + K + g + 12 + 64
  set β := 8 * E * (1584 * g + 78)
  set α := 8 * E * (g + 4)
  refine ⟨β * (4 * β) ^ 3 + (α * (Nat.log 2 Carg + 2) + 4 * α * (4 * (4 * α)) ^ 3), fun n => ?_⟩
  set mb := mbn K0 ℓ n
  set S4 := (2 ^ sOf n) ^ 4
  set S3 := (2 ^ sOf n) ^ 3
  have h := eTop_le K0 ℓ n mb (by omega)
  set R := 1584 * (g * S3) + 78 * S3 + ePolyT K g (sOf n) n mb
  set Y := 2160 * S4 / K
  have hK1 : 0 < K := by omega
  have h2 : eTop K0 ℓ n mb ≤ Y + R := by
    have : eTop K0 ℓ n mb ≤ (2160 * S4 + K * R) / K := (Nat.le_div_iff_mul_le hK1).mpr (by rw [mul_comm]; exact h)
    rwa [Nat.add_mul_div_left _ _ hK1] at this
  have hY : K * Y ≤ 2160 * S4 := Nat.mul_div_le _ _
  have hKE : 69120 * E ≤ K := le_trans (by show 69120 * E ≤ 161280 * E; omega) hKK
  have h3 : 69120 * (E * Y) ≤ 2160 * S4 := by
    calc 69120 * (E * Y) = (69120 * E) * Y := by ring
      _ ≤ K * Y := Nat.mul_le_mul_right _ hKE
      _ ≤ _ := hY
  -- the lower-order part
  have hab : β * S3 ≤ S4 / 4 + β * (4 * β) ^ 3 := absorb_cube β (2 ^ sOf n)
  have harg : mb + 16 * n + K + g + mulNodes (sOf n) + 64 ≤ Carg * S4 := by
    have : mb ≤ cmbn K0 ℓ * S4 := mbn_le ℓ hK0 n
    have : n ≤ 4 * S4 := n_le_S n
    have : mulNodes (sOf n) ≤ 12 * S4 := mulNodes_le (sOf n)
    have h1 : 1 ≤ S4 := Nat.one_le_pow _ _ (Nat.two_pow_pos _)
    have hKS : K ≤ K * S4 := Nat.le_mul_of_pos_right _ h1
    have hgS : g ≤ g * S4 := Nat.le_mul_of_pos_right _ h1
    have e : Carg * S4 = cmbn K0 ℓ * S4 + 64 * S4 + K * S4 + g * S4 + 12 * S4 + 64 * S4 := by
      simp only [Carg]; ring
    omega
  have hlog : α * (Nat.log 2 (mb + 16 * n + K + g + mulNodes (sOf n) + 64) + 1) ≤
      S4 / 4 + (α * (Nat.log 2 Carg + 2) + 4 * α * (4 * (4 * α)) ^ 3) := log_absorb α Carg harg
  have e1 : 8 * E * R = β * S3 + α * (Nat.log 2 (mb + 16 * n + K + g + mulNodes (sOf n) + 64) + 1) := by
    simp only [R, β, α, ePolyT]; ring
  have e2 : 8 * E * (Y + R) = 8 * (E * Y) + 8 * E * R := by ring
  calc 8 * E * eTop K0 ℓ n mb ≤ 8 * E * (Y + R) := Nat.mul_le_mul_left _ h2
    _ ≤ _ := by rw [e2, e1]; omega

/-- **The levels' exponents** fit the budget. -/
theorem budget_level : ∃ c, ∀ n, 8 * Ek k ℓ * (14 * Wn (K0k k ℓ) ℓ n / K0k k ℓ + 7 + (Gm4 (K0k k ℓ) ℓ + 9) *
    (Nat.log 2 (Wn (K0k k ℓ) ℓ n + mbn (K0k k ℓ) ℓ n + Gs (K0k k ℓ) ℓ + Gs (K0k k ℓ) ℓ + 64) + 1)) ≤
      (2 ^ sOf n) ^ 4 + c := by
  set E := Ek k ℓ
  set K0 := K0k k ℓ
  set g := Gs K0 ℓ
  have hE := Ek_pos k ℓ hk
  have hK0 : 48 ≤ K0 := K0k_ge k ℓ hk
  set Carg := cWn K0 ℓ + cmbn K0 ℓ + g + g + 64
  set α := 8 * E * (Gm4 K0 ℓ + 9)
  set cl := α * (Nat.log 2 Carg + 2) + 4 * α * (4 * (4 * α)) ^ 3
  set cg := g * (4 * g) ^ 3
  refine ⟨306 * cg + 2 * ℓ * Gm4 K0 ℓ + cl + 56 * E, fun n => ?_⟩
  set mb := mbn K0 ℓ n
  set W := Wn K0 ℓ n
  set S4 := (2 ^ sOf n) ^ 4
  set S3 := (2 ^ sOf n) ^ 3
  set Y := 14 * W / K0
  have hY : K0 * Y ≤ 14 * W := Nat.mul_div_le _ _
  have h1 : 11520 * (E * Y) ≤ W := by
    have : 14 * (11520 * (E * Y)) = K0 * Y := by simp only [K0, K0k]; ring
    omega
  have hW : W = 720 * S4 + 306 * (g * S3) + 2 * ℓ * Gm4 K0 ℓ := rfl
  have hab : g * S3 ≤ S4 / 4 + cg := absorb_cube g (2 ^ sOf n)
  have harg : W + mb + g + g + 64 ≤ Carg * S4 := by
    have : mb ≤ cmbn K0 ℓ * S4 := mbn_le ℓ hK0 n
    have : W + 1 ≤ cWn K0 ℓ * S4 := Wn_le ℓ n
    have h1 : 1 ≤ S4 := Nat.one_le_pow _ _ (Nat.two_pow_pos _)
    have hgS : g ≤ g * S4 := Nat.le_mul_of_pos_right _ h1
    have e : Carg * S4 = cWn K0 ℓ * S4 + cmbn K0 ℓ * S4 + g * S4 + g * S4 + 64 * S4 := by simp only [Carg]; ring
    omega
  have hlog : α * (Nat.log 2 (W + mb + g + g + 64) + 1) ≤ S4 / 4 + cl := log_absorb α Carg harg
  have e : 8 * E * (Y + 7 + (Gm4 K0 ℓ + 9) * (Nat.log 2 (W + mb + g + g + 64) + 1)) =
      8 * (E * Y) + 56 * E + α * (Nat.log 2 (W + mb + g + g + 64) + 1) := by simp only [α]; ring
  rw [e]
  omega

/-- **The brute force's exponent** fits the budget. -/
theorem budget_brute (h23 : 2903040 * k * (ℓ + 1) * 23 ^ ℓ ≤ 24 ^ ℓ) : ∃ c, ∀ n, 8 * Ek k ℓ * (W0n (K0k k ℓ) ℓ n +
    2 * (Nat.log 2 (mbn (K0k k ℓ) ℓ n + K0k k ℓ + 64) + 1)) ≤ (2 ^ sOf n) ^ 4 + c := by
  set E := Ek k ℓ
  set K0 := K0k k ℓ
  set g := Gs K0 ℓ
  have hE := Ek_pos k ℓ hk
  have hK0 : 48 ≤ K0 := K0k_ge k ℓ hk
  set Carg := cmbn K0 ℓ + K0 + 64
  set α := 16 * E
  set cl := α * (Nat.log 2 Carg + 2) + 4 * α * (4 * (4 * α)) ^ 3
  set β := 4896 * E * g
  set cb := β * (4 * β) ^ 3
  refine ⟨cb + cl + 8 * E * (1 + 2 * ℓ * Gm4 K0 ℓ), fun n => ?_⟩
  set mb := mbn K0 ℓ n
  set S4 := (2 ^ sOf n) ^ 4
  set S3 := (2 ^ sOf n) ^ 3
  set P := 24 ^ ℓ
  set Q := 23 ^ ℓ
  set Nt := Ntn K0 ℓ n
  set y := Q * Nt / P
  have hP : 0 < P := Nat.pow_pos (by norm_num)
  have hQP : Q ≤ P := Nat.pow_le_pow_left (by norm_num) ℓ
  have hyP : P * y ≤ Q * Nt := Nat.mul_div_le _ _
  have hE252 : E ≤ 252 * k * (ℓ + 1) := by simp only [E, Ek]; nlinarith
  have hQ : 11520 * E * Q ≤ P := le_trans (Nat.mul_le_mul_right Q (show 11520 * E ≤ 2903040 * k * (ℓ + 1) by
    nlinarith)) h23
  have hNt : Nt = 720 * S4 + 306 * (g * S3) := rfl
  have key : P * (2 * (8 * E * y)) ≤ P * (S4 + β * S3) := by
    have a1 : P * (2 * (8 * E * y)) = 16 * E * (P * y) := by ring
    have a2 : 16 * E * (P * y) ≤ 16 * E * (Q * Nt) := Nat.mul_le_mul_left _ hyP
    have a3 : 16 * E * (Q * Nt) = (11520 * E * Q) * S4 + (16 * E * Q) * (306 * (g * S3)) := by rw [hNt]; ring
    have a4 : (11520 * E * Q) * S4 ≤ P * S4 := Nat.mul_le_mul_right _ hQ
    have a5 : (16 * E * Q) * (306 * (g * S3)) ≤ (16 * E * P) * (306 * (g * S3)) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hQP)
    have a6 : (16 * E * P) * (306 * (g * S3)) = P * (β * S3) := by simp only [β]; ring
    have a7 : P * (S4 + β * S3) = P * S4 + P * (β * S3) := by ring
    omega
  have key' : 2 * (8 * E * y) ≤ S4 + β * S3 := Nat.le_of_mul_le_mul_left key hP
  have hab : β * S3 ≤ S4 / 4 + cb := absorb_cube β (2 ^ sOf n)
  have harg : mb + K0 + 64 ≤ Carg * S4 := by
    have : mb ≤ cmbn K0 ℓ * S4 := mbn_le ℓ hK0 n
    have h1 : 1 ≤ S4 := Nat.one_le_pow _ _ (Nat.two_pow_pos _)
    have hgS : K0 ≤ K0 * S4 := Nat.le_mul_of_pos_right _ h1
    have e : Carg * S4 = cmbn K0 ℓ * S4 + K0 * S4 + 64 * S4 := by simp only [Carg]; ring
    omega
  have hlog : α * (Nat.log 2 (mb + K0 + 64) + 1) ≤ S4 / 4 + cl := log_absorb α Carg harg
  have e : 8 * E * (W0n K0 ℓ n + 2 * (Nat.log 2 (mb + K0 + 64) + 1)) =
      8 * E * y + 8 * E * (1 + 2 * ℓ * Gm4 K0 ℓ) + α * (Nat.log 2 (mb + K0 + 64) + 1) := by
    simp only [W0n, α]; ring
  rw [e]
  omega

end Exps

/-! ### The counting lemma's hypothesis -/

theorem le_div_add_of_mul_le {k a n c : ℕ} (hk : 1 ≤ k) (h : k * a ≤ n + c) : a ≤ n / k + c + 1 := by
  have h1 := Nat.div_add_mod n k
  have h2 := Nat.mod_lt n (show 0 < k by omega)
  have h3 : c ≤ k * c := Nat.le_mul_of_pos_left _ (by omega)
  have h4 : k * a < k * (n / k + c + 1) := by
    have e : k * (n / k + c + 1) = k * (n / k) + k * c + k := by ring
    omega
  exact (Nat.lt_of_mul_lt_mul_left h4).le

theorem cost_pow_le (Z D : ℕ) : (64 * (2 ^ Z + 1) ^ 3) ^ D ≤ 2 ^ ((3 * Z + 9) * D) := by
  rw [pow_mul]
  refine Nat.pow_le_pow_left ?_ D
  have h1 : 2 ^ Z + 1 ≤ 2 ^ (Z + 1) := by rw [pow_succ]; have := Nat.one_le_two_pow (n := Z); omega
  calc 64 * (2 ^ Z + 1) ^ 3 ≤ 64 * (2 ^ (Z + 1)) ^ 3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 3)
    _ = 2 ^ (3 * Z + 9) := by rw [← pow_mul]; rw [show (64 : ℕ) = 2 ^ 6 by norm_num, ← pow_add]; ring_nf

/-- **The hypothesis of `count_of_mainE`**: for every `k ≥ 1`, parameters `K0, ℓ` with a cost bound
`B n ≤ C · 2^(n/k)`. -/
theorem count_cost : ∀ k : ℕ, 1 ≤ k → ∃ (K0 ℓ T : ℕ) (B : ℕ → ℕ) (C : ℕ), 2 ≤ K0 ∧
    VB 10 (Ex.blk T (mainE K0 ℓ)) ∧
    (∀ σ A, σ 2 < σ 0 → (∀ j, A 1 j ≤ 1) → cost σ A (mainE K0 ℓ) ≤ B (σ 0)) ∧
    ∀ n, B n ≤ C * 2 ^ (n / k) := by
  intro k hk
  obtain ⟨ℓ, h23⟩ := exists_ell (2903040 * k)
  have hE := Ek_pos k ℓ hk
  have hK0 : 48 ≤ K0k k ℓ := K0k_ge k ℓ hk
  obtain ⟨c1, hc1⟩ := budget_top k ℓ hk
  obtain ⟨c2, hc2⟩ := budget_level k ℓ hk
  obtain ⟨c3, hc3⟩ := budget_brute k ℓ hk h23
  set E := Ek k ℓ
  set K0 := K0k k ℓ
  set c := c1 + c2 + c3
  set D := 24 * ℓ + 84
  let Z : ℕ → ℕ := fun n => ((2 ^ sOf n) ^ 4 + c) / (8 * E)
  have hZ : ∀ n x ci, ci ≤ c → 8 * E * x ≤ (2 ^ sOf n) ^ 4 + ci → x ≤ Z n := fun n x ci hci h =>
    (Nat.le_div_iff_mul_le (by omega)).mpr (by rw [mul_comm]; omega)
  have hMain : ∀ n, MainReq (2 ^ Z n) K0 ℓ n := fun n =>
    mainReq_of (by omega) (hZ n _ c1 (by omega) (hc1 n))
      (deepE_of K0 (Z n) (mbn K0 ℓ n) (Wn K0 ℓ n) (W0n K0 ℓ n) (Gs K0 ℓ) hK0
        (hZ n _ c2 (by omega) (hc2 n)) (hZ n _ c3 (by omega) (hc3 n)) ℓ _ (Kb_le_Gs ℓ hK0) (chain_hyp1 ℓ hK0 n)
        (chain_hyp2 ℓ hK0 n)) le_rfl
  refine ⟨K0, ℓ, 100 * ℓ + 165, fun n => (64 * (2 ^ Z n + 1) ^ 3) ^ (24 * ℓ + 84), 2 ^ (9 * D + c + 5),
    by omega, mainE_blk_vb K0 ℓ,
    cost_reduce K0 ℓ _ (fun n k' hkn A hA => mainE_cost_le (by omega) (hMain n) hkn hA), fun n => ?_⟩
  refine le_trans (cost_pow_le (Z n) D) ?_
  -- the exponent
  have h8 : 8 * E * Z n ≤ (2 ^ sOf n) ^ 4 + c := by
    have := Nat.div_mul_le_self ((2 ^ sOf n) ^ 4 + c) (8 * E)
    show 8 * E * (((2 ^ sOf n) ^ 4 + c) / (8 * E)) ≤ _
    rw [mul_comm]; exact this
  have hS := S_le_n n
  have h3 : k * (3 * D * Z n) ≤ n + (4 + c) := by
    have e : 8 * E * Z n = 8 * (k * (3 * D * Z n)) := by simp only [E, Ek, D]; ring
    omega
  have h4 := le_div_add_of_mul_le hk h3
  have h5 : (3 * Z n + 9) * D ≤ n / k + (9 * D + c + 5) := by
    have e : (3 * Z n + 9) * D = 3 * D * Z n + 9 * D := by ring
    omega
  calc 2 ^ ((3 * Z n + 9) * D) ≤ 2 ^ (n / k + (9 * D + c + 5)) := Nat.pow_le_pow_right (by norm_num) h5
    _ = 2 ^ (9 * D + c + 5) * 2 ^ (n / k) := by rw [pow_add, mul_comm]

/-- **(a)**: for every `k`, some machine factors in time `C · 2^(n/k)`. -/
theorem everyRootRate : ∀ k : ℕ, 1 ≤ k → ∃ C : ℕ, FactoringInTime (fun n => C * 2 ^ (n / k)) :=
  everyRoot_of_count (count_of_mainE count_cost)

end Factoring.Aux
