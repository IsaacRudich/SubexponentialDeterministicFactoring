/-
Value bounds of the rectangle factors' expressions: the block functions (`psiE`, `RxE`, `CxE`),
the decoder `decE` (state `j·m + acc` never grows: `decBody_div`), the pieces `pieceE` and the factors `facLE`,
`facRE`.

Not an audit surface.
-/
module

public import FactoringAux.EngineBddBase

@[expose] public section

namespace Factoring.Aux

open Finset Ex SB

namespace SB

variable {V : ℕ} {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ}

/-! ### The block functions -/

theorem bitE_le (e : Ex) (i : ℕ) : eval σ A (bitE e i) ≤ 1 := by
  rw [eval_bitE]; unfold bitN; have := Nat.mod_lt (eval σ A e / 2 ^ i) (show 0 < 2 by norm_num); omega

theorem B_bitE {e : Ex} {i : ℕ} (he : Bdd V σ A e) (hi : i < 3) (h8 : 8 ≤ V) : Bdd V σ A (bitE e i) :=
  B_mod (B_div he (B_lit (le_trans (Nat.pow_le_pow_right (by norm_num) (show i ≤ 3 by omega)) (by norm_num; omega))))
    (B_lit (by omega))

theorem B_par3E {e f h : Ex} (he : Bdd V σ A e) (hf : Bdd V σ A f) (hh : Bdd V σ A h) (h8 : 8 ≤ V) :
    Bdd V σ A (par3E e f h) := by
  have T : ∀ i < 3, Bdd V σ A (eqE (.mod (.add (.add (bitE e i) (bitE f i)) (bitE h i)) (.lit 2)) (.lit 0)) := by
    intro i hi
    have := bitE_le (σ := σ) (A := A) e i; have := bitE_le (σ := σ) (A := A) f i
    have := bitE_le (σ := σ) (A := A) h i
    exact B_eqE (B_mod (B_add (B_add (B_bitE he hi h8) (B_bitE hf hi h8) (by omega)) (B_bitE hh hi h8)
      (by simp only [Ex.eval]; omega)) (B_lit (by omega))) (B_lit (Nat.zero_le _)) (by omega)
  have l := fun (i : ℕ) => eqE_le (σ := σ) (A := A) (.mod (.add (.add (bitE e i) (bitE f i)) (bitE h i)) (.lit 2)) (.lit 0)
  have l0 := l 0; have l1 := l 1; have l2 := l 2
  refine B_mul (B_mul (T 0 (by norm_num)) (T 1 (by norm_num)) ?_) (T 2 (by norm_num)) ?_
  · exact le_trans (Nat.mul_le_mul l0 l1) (by omega)
  · simp only [Ex.eval]
    exact le_trans (Nat.mul_le_mul (Nat.mul_le_mul l0 l1) l2) (by omega)

theorem B_par4E {e f h k : Ex} (he : Bdd V σ A e) (hf : Bdd V σ A f) (hh : Bdd V σ A h) (hk : Bdd V σ A k)
    (h8 : 8 ≤ V) : Bdd V σ A (par4E e f h k) := by
  have T : ∀ i < 3, Bdd V σ A
      (eqE (.mod (.add (.add (.add (bitE e i) (bitE f i)) (bitE h i)) (bitE k i)) (.lit 2)) (.lit 0)) := by
    intro i hi
    have := bitE_le (σ := σ) (A := A) e i; have := bitE_le (σ := σ) (A := A) f i
    have := bitE_le (σ := σ) (A := A) h i; have := bitE_le (σ := σ) (A := A) k i
    exact B_eqE (B_mod (B_add (B_add (B_add (B_bitE he hi h8) (B_bitE hf hi h8) (by omega)) (B_bitE hh hi h8)
      (by simp only [Ex.eval]; omega)) (B_bitE hk hi h8) (by simp only [Ex.eval]; omega)) (B_lit (by omega)))
      (B_lit (Nat.zero_le _)) (by omega)
  have l := fun (i : ℕ) => eqE_le (σ := σ) (A := A)
    (.mod (.add (.add (.add (bitE e i) (bitE f i)) (bitE h i)) (bitE k i)) (.lit 2)) (.lit 0)
  have l0 := l 0; have l1 := l 1; have l2 := l 2
  refine B_mul (B_mul (T 0 (by norm_num)) (T 1 (by norm_num)) ?_) (T 2 (by norm_num)) ?_
  · exact le_trans (Nat.mul_le_mul l0 l1) (by omega)
  · simp only [Ex.eval]
    exact le_trans (Nat.mul_le_mul (Nat.mul_le_mul l0 l1) l2) (by omega)

theorem mul01 {a b : ℕ} (ha : a ≤ 1) (hb : b ≤ 1) : a * b ≤ 1 := le_trans (Nat.mul_le_mul ha hb) (by norm_num)

theorem B_phiE {p q : Ex} (hp : Bdd V σ A p) (hq : Bdd V σ A q) (h16 : 16 ≤ V) : Bdd V σ A (phiE p q) := by
  have h8 : 8 ≤ V := by omega
  have P0 := B_bitE hp (show 0 < 3 by norm_num) h8; have P1 := B_bitE hp (show 1 < 3 by norm_num) h8
  have P2 := B_bitE hp (show 2 < 3 by norm_num) h8
  have Q0 := B_bitE hq (show 0 < 3 by norm_num) h8; have Q1 := B_bitE hq (show 1 < 3 by norm_num) h8
  have Q2 := B_bitE hq (show 2 < 3 by norm_num) h8
  have p0 := bitE_le (σ := σ) (A := A) p 0; have p1 := bitE_le (σ := σ) (A := A) p 1
  have p2 := bitE_le (σ := σ) (A := A) p 2
  have q0 := bitE_le (σ := σ) (A := A) q 0; have q1 := bitE_le (σ := σ) (A := A) q 1
  have q2 := bitE_le (σ := σ) (A := A) q 2
  have M : ∀ {a b : Ex}, Bdd V σ A a → Bdd V σ A b → eval σ A a ≤ 1 → eval σ A b ≤ 1 →
      Bdd V σ A (.mul a b) ∧ eval σ A (.mul a b) ≤ 1 := fun Ba Bb la lb =>
    ⟨B_mul Ba Bb (le_trans (mul01 la lb) (by omega)), mul01 la lb⟩
  obtain ⟨B1, l1⟩ := M P0 Q0 p0 q0
  obtain ⟨B2, l2⟩ := M P0 Q1 p0 q1
  obtain ⟨B3, l3⟩ := M P0 Q2 p0 q2
  obtain ⟨B4, l4⟩ := M P1 Q1 p1 q1
  obtain ⟨B5, l5⟩ := M P1 Q2 p1 q2
  obtain ⟨B6, l6⟩ := M P2 Q2 p2 q2
  obtain ⟨B7a, l7a⟩ := M Q0 P1 q0 p1
  obtain ⟨B7, l7⟩ := M B7a P2 l7a p2
  obtain ⟨B8a, l8a⟩ := M P0 Q1 p0 q1
  obtain ⟨B8, l8⟩ := M B8a P2 l8a p2
  obtain ⟨B9a, l9a⟩ := M P0 P1 p0 p1
  obtain ⟨B9, l9⟩ := M B9a Q2 l9a q2
  unfold phiE
  refine B_mod ?_ (B_lit (by omega))
  refine B_add (B_add (B_add (B_add (B_add (B_add (B_add (B_add B1 B2 ?_) B3 ?_) B4 ?_) B5 ?_) B6 ?_) B7 ?_) B8 ?_)
    B9 ?_ <;> simp only [Ex.eval] at * <;> omega

theorem sgnE_le {vm : ℕ} {p q : Ex} (h1 : 1 ≤ σ vm) : eval σ A (sgnE vm p q) ≤ σ vm := by
  rw [eval_sgnE]; unfold sgnN; split_ifs <;> omega

theorem B_sgnE {vm : ℕ} {p q : Ex} (hp : Bdd V σ A p) (hq : Bdd V σ A q) (h16 : 16 ≤ V) (hmV : σ vm ≤ V) :
    Bdd V σ A (sgnE vm p q) :=
  B_ifEq (B_phiE hp hq h16) (B_lit (by omega)) (B_sub (B_var hmV) (B_lit (by omega))) (B_lit (by omega))

theorem B_psiE {vm : ℕ} {k p q : Ex} (hk : Bdd V σ A k) (hp : Bdd V σ A p) (hq : Bdd V σ A q) (h16 : 16 ≤ V)
    (hmV : σ vm ≤ V) : Bdd V σ A (psiE vm k p q) :=
  B_ifEq (B_par3E hp hq hk (by omega)) (B_lit (by omega)) (B_sgnE hp hq h16 hmV) (B_lit (Nat.zero_le _))

theorem B_RxE {vm : ℕ} {x y u v : Ex} (hx : Bdd V σ A x) (hy : Bdd V σ A y) (hu : Bdd V σ A u) (hv : Bdd V σ A v)
    (h16 : 16 ≤ V) (h1 : 1 ≤ σ vm) (hmm : σ vm * σ vm ≤ V) : Bdd V σ A (RxE vm x y u v) := by
  have hmV : σ vm ≤ V := le_trans (Nat.le_mul_of_pos_left _ (by omega)) hmm
  exact B_ifEq (B_par4E hx hy hv hu (by omega)) (B_lit (by omega))
    (B_mod (B_mul (B_sgnE hx hy h16 hmV) (B_sgnE hv hu h16 hmV) (le_trans (Nat.mul_le_mul (sgnE_le h1) (sgnE_le h1)) hmm))
      (B_var hmV)) (B_lit (Nat.zero_le _))

theorem B_CxE {vm : ℕ} {x y u v : Ex} (hx : Bdd V σ A x) (hy : Bdd V σ A y) (hu : Bdd V σ A u) (hv : Bdd V σ A v)
    (h16 : 16 ≤ V) (h1 : 1 ≤ σ vm) (hmm : σ vm * σ vm ≤ V) : Bdd V σ A (CxE vm x y u v) := by
  have hmV : σ vm ≤ V := le_trans (Nat.le_mul_of_pos_left _ (by omega)) hmm
  exact B_ifEq (B_par4E hx hu hv hy (by omega)) (B_lit (by omega))
    (B_mod (B_mul (B_sgnE hx hu h16 hmV) (B_sgnE hv hy h16 hmV) (le_trans (Nat.mul_le_mul (sgnE_le h1) (sgnE_le h1)) hmm))
      (B_var hmV)) (B_lit (Nat.zero_le _))

end SB

/-! ### The decoder -/

namespace Ex

/-- The bit test of the decoder's step. -/
def decTest (b : ℕ) (QE : Ex) : Ex :=
  .mod (.div QE (pow2 (b + 6) (.add (.add (.mul (.lit 4) (.var (b + 3))) (.mul (.lit 3) (.var (b + 4)))) (.lit 3))))
    (.lit 2)

/-- The decoder's step on a set bit. -/
def decX (b vm : ℕ) (QE cvE : Ex) : Ex :=
  .add (.mul (.var (b + 4)) (.var vm)) (.mod (.mul (.mod (.var (b + 2)) (.var vm))
    (.lett (b + 5) (.div QE (pow2 (b + 6) (.add (.mul (.lit 4) (.var (b + 3))) (.mul (.lit 3) (.var (b + 4))))))
      cvE)) (.var vm))

/-- The decoder's step on a clear bit. -/
def decY (b vm : ℕ) (QE evE : Ex) : Ex :=
  ifEq (.var (b + 4)) (.lit 0) (.lit 0)
    (.add (.mul (.sub (.var (b + 4)) (.lit 1)) (.var vm)) (.mod (.mul (.mod (.var (b + 2)) (.var vm))
      (.lett (b + 5) (.div QE (pow2 (b + 6) (.add (.mul (.lit 4) (.var (b + 3)))
        (.mul (.lit 3) (.sub (.var (b + 4)) (.lit 1)))))) evE)) (.var vm)))

/-- The decoder's step. -/
def decBody (b vm : ℕ) (tE QE cvE evE : Ex) : Ex :=
  .lett (b + 3) (.sub (.sub tE (.lit 1)) (.var (b + 1)))
    (.lett (b + 4) (.div (.var (b + 2)) (.var vm)) (ifEq (decTest b QE) (.lit 1) (decX b vm QE cvE) (decY b vm QE evE)))

theorem decE_eq (b vm : ℕ) (tE QE jE cvE evE : Ex) : decE b vm tE QE jE cvE evE =
    .lett b (.iter (b + 1) (b + 2) tE (.add (.mul jE (.var vm)) (.mod (.lit 1) (.var vm))) (decBody b vm tE QE cvE evE))
      (ifEq (.div (.var b) (.var vm)) (.lit 0) (.mod (.var b) (.var vm)) (.lit 0)) := rfl

end Ex

namespace SB

variable {V : ℕ} {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ}

theorem mul_add_mod_div {x m r : ℕ} (hm : 0 < m) : (x * m + r % m) / m = x :=
  (div_mod_pack hm (Nat.mod_lt _ hm)).1

/-- **The decoder's state never grows** (in units of `m`). -/
theorem decBody_div {b vm m : ℕ} (hvm : vm < b) (hm : σ vm = m) (hm0 : 0 < m) (tE QE cvE evE : Ex) :
    eval σ A (decBody b vm tE QE cvE evE) / m ≤ σ (b + 2) / m := by
  rw [decBody, eval_lett, eval_lett, eval_ifEq]
  set σ2 := Function.update (Function.update σ (b + 3) (eval σ A (.sub (.sub tE (.lit 1)) (.var (b + 1))))) (b + 4)
    (eval (Function.update σ (b + 3) (eval σ A (.sub (.sub tE (.lit 1)) (.var (b + 1))))) A
      (.div (.var (b + 2)) (.var vm)))
  have e4 : σ2 (b + 4) = σ (b + 2) / m := by simp only [σ2, Ex.eval]; upd; rw [hm]
  have em : σ2 vm = m := by simp only [σ2]; upd; exact hm
  split_ifs
  · simp only [decX, Ex.eval, e4, em]
    rw [mul_add_mod_div hm0]
  · rw [decY, eval_ifEq]
    simp only [Ex.eval, e4, em]
    split_ifs
    · simp
    · rw [mul_add_mod_div hm0]; omega

end SB

namespace SB

variable {V : ℕ} {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ}

theorem le_of_div_le {s m j : ℕ} (hm : 0 < m) (h : s / m ≤ j) : s + 1 ≤ (j + 1) * m := by
  have h1 := Nat.div_add_mod s m
  have h2 := Nat.mod_lt s hm
  have h3 : m * (s / m) ≤ m * j := Nat.mul_le_mul_left _ h
  rw [Nat.succ_mul]
  nlinarith

/-- One step of the decoder: every value is at most `V`. -/
theorem B_decBody {b vm m : ℕ} (hvm : vm < b) (hm : σ vm = m) (hm0 : 0 < m) {tE QE cvE evE : Ex} {t Q j : ℕ}
    (ht : ∀ σ', AgB b σ σ' → eval σ' A tE = t ∧ Bdd V σ' A tE)
    (hQ : ∀ σ', AgB b σ σ' → eval σ' A QE = Q ∧ Bdd V σ' A QE)
    (hcv : ∀ σ', AgB b σ σ' → σ' (b + 3) < t → σ' (b + 5) ≤ V → Bdd V σ' A cvE ∧ eval σ' A cvE < m)
    (hev : ∀ σ', AgB b σ σ' → σ' (b + 3) < t → σ' (b + 5) ≤ V → Bdd V σ' A evE ∧ eval σ' A evE < m)
    (hjm : (j + 1) * m ≤ V) (hmm : m * m ≤ V) (hP : 2 ^ (4 * t + 3 * j) ≤ V) (hQV : Q ≤ V) (h4 : 4 ≤ V)
    {σ' : ℕ → ℕ} (a : AgB b σ σ') (hi : σ' (b + 1) < t) (hs : σ' (b + 2) / m ≤ j) :
    Bdd V σ' A (decBody b vm tE QE cvE evE) := by
  have hN : 4 * t + 3 * j < V := lt_of_lt_of_le Nat.lt_two_pow_self hP
  have hsV : σ' (b + 2) + 1 ≤ (j + 1) * m := le_of_div_le hm0 hs
  have hjm' : j * m + m ≤ V := by rw [Nat.succ_mul] at hjm; exact hjm
  have hmV : m ≤ V := by omega
  have hm' : σ' vm = m := by rw [a vm hvm, hm]
  obtain ⟨et, Bt⟩ := ht σ' a
  unfold decBody
  refine B_lett (B_sub (B_sub Bt (B_lit (by omega))) (B_var (by omega))) ?_
  set σ3 := Function.update σ' (b + 3) (eval σ' A (.sub (.sub tE (.lit 1)) (.var (b + 1))))
  have a3 : AgB b σ σ3 := a.upd (by omega) _
  have e33 : σ3 (b + 3) = t - 1 - σ' (b + 1) := by simp only [σ3, Ex.eval, et]; upd
  refine B_lett (B_div (B_var (by simp only [σ3]; upd; omega)) (B_var (by simp only [σ3]; upd; omega))) ?_
  set σ4 := Function.update σ3 (b + 4) (eval σ3 A (.div (.var (b + 2)) (.var vm)))
  have a4 : AgB b σ σ4 := a3.upd (by omega) _
  have e3 : σ4 (b + 3) = t - 1 - σ' (b + 1) := by simp only [σ4]; upd; exact e33
  have e4 : σ4 (b + 4) = σ' (b + 2) / m := by simp only [σ4, σ3, Ex.eval]; upd; rw [hm']
  have e2 : σ4 (b + 2) = σ' (b + 2) := by simp only [σ4, σ3]; upd
  have em : σ4 vm = m := by simp only [σ4, σ3]; upd; exact hm'
  obtain ⟨eQ, BQ⟩ := hQ σ4 a4
  have hs4 : σ4 (b + 4) ≤ j := by rw [e4]; exact hs
  have hs3 : σ4 (b + 3) < t := by rw [e3]; omega
  have hmod : σ4 (b + 2) % σ4 vm < m := by rw [em]; exact Nat.mod_lt _ hm0
  have hmul4 : σ4 (b + 4) * m ≤ j * m := Nat.mul_le_mul_right _ hs4
  have hpow : ∀ e, e ≤ 4 * t + 3 * j → 2 ^ e ≤ V := fun e he =>
    le_trans (Nat.pow_le_pow_right (by norm_num) he) hP
  have V3 : Bdd V σ4 A (.var (b + 3)) := B_var (by omega)
  have V4 : Bdd V σ4 A (.var (b + 4)) := B_var (by omega)
  have Vm : Bdd V σ4 A (.var vm) := B_var (by omega)
  have V2 : Bdd V σ4 A (.var (b + 2)) := B_var (by rw [e2]; omega)
  have L4 : Bdd V σ4 A (.mul (.lit 4) (.var (b + 3))) := B_mul (B_lit (by omega)) V3 (by simp only [Ex.eval]; omega)
  have L3 : Bdd V σ4 A (.mul (.lit 3) (.var (b + 4))) := B_mul (B_lit (by omega)) V4 (by simp only [Ex.eval]; omega)
  -- the test
  have BT : Bdd V σ4 A (decTest b QE) := by
    unfold decTest
    exact B_mod (B_div BQ (B_pow2 (B_add (B_add L4 L3 (by simp only [Ex.eval]; omega)) (B_lit (by omega))
      (by simp only [Ex.eval]; omega)) (by omega) (hpow _ (by simp only [Ex.eval]; omega)))) (B_lit (by omega))
  -- a step with the coefficient `cv` or `ev`
  have step : ∀ (E : Ex) (fE : Ex), Bdd V σ4 A E → eval σ4 A E ≤ 4 * t + 3 * j →
      (∀ σ', AgB b σ σ' → σ' (b + 3) < t → σ' (b + 5) ≤ V → Bdd V σ' A fE ∧ eval σ' A fE < m) →
      Bdd V σ4 A (.mod (.mul (.mod (.var (b + 2)) (.var vm)) (.lett (b + 5) (.div QE (pow2 (b + 6) E)) fE)) (.var vm)) ∧
        eval σ4 A (.mod (.mul (.mod (.var (b + 2)) (.var vm)) (.lett (b + 5) (.div QE (pow2 (b + 6) E)) fE))
          (.var vm)) < m := by
    intro E fE BE hE hf
    have BD : Bdd V σ4 A (.div QE (pow2 (b + 6) E)) := B_div BQ (B_pow2 BE (by omega) (hpow _ hE))
    have hD : eval σ4 A (.div QE (pow2 (b + 6) E)) ≤ V := by
      simp only [Ex.eval]; rw [eQ]; exact le_trans (Nat.div_le_self _ _) hQV
    obtain ⟨Bf, lf⟩ := hf _ (a4.upd (x := b + 5) (by omega) (eval σ4 A (.div QE (pow2 (b + 6) E))))
      (by upd; exact hs3) (by upd; exact hD)
    refine ⟨B_mod (B_mul (B_mod V2 Vm) (B_lett BD Bf) ?_) Vm, ?_⟩
    · simp only [Ex.eval] at lf ⊢
      exact le_trans (Nat.mul_le_mul hmod.le lf.le) hmm
    · simp only [Ex.eval, em]; exact Nat.mod_lt _ hm0
  refine B_ifEq' BT (B_lit (by omega)) (fun _ => ?_) (fun _ => ?_)
  · obtain ⟨BS, lS⟩ := step _ cvE (B_add L4 L3 (by simp only [Ex.eval]; omega)) (by simp only [Ex.eval]; omega) hcv
    unfold decX
    refine B_add (B_mul V4 Vm (by simp only [Ex.eval, em]; omega)) BS ?_
    simp only [Ex.eval, em] at lS ⊢
    omega
  · unfold decY
    refine B_ifEq' V4 (B_lit (Nat.zero_le _)) (fun _ => B_lit (Nat.zero_le _)) (fun h0 => ?_)
    simp only [Ex.eval] at h0
    have L3' : Bdd V σ4 A (.mul (.lit 3) (.sub (.var (b + 4)) (.lit 1))) :=
      B_mul (B_lit (by omega)) (B_sub V4 (B_lit (by omega))) (by simp only [Ex.eval]; omega)
    obtain ⟨BS, lS⟩ := step _ evE (B_add L4 L3' (by simp only [Ex.eval]; omega)) (by simp only [Ex.eval]; omega) hev
    have hmul4' : (σ4 (b + 4) - 1) * m ≤ j * m := Nat.mul_le_mul_right _ (by omega)
    refine B_add (B_mul (B_sub V4 (B_lit (by omega))) Vm (by simp only [Ex.eval, em]; omega)) BS ?_
    simp only [Ex.eval, em] at lS ⊢
    omega

/-- **The decoder: every value is at most `V`.** -/
theorem B_decE {b vm m : ℕ} (hvm : vm < b) (hm : σ vm = m) (hm0 : 0 < m) {tE QE jE cvE evE : Ex} {t Q j : ℕ}
    (ht : ∀ σ', AgB b σ σ' → eval σ' A tE = t ∧ Bdd V σ' A tE)
    (hQ : ∀ σ', AgB b σ σ' → eval σ' A QE = Q ∧ Bdd V σ' A QE)
    (hj : eval σ A jE = j) (Bj : Bdd V σ A jE)
    (hcv : ∀ σ', AgB b σ σ' → σ' (b + 3) < t → σ' (b + 5) ≤ V → Bdd V σ' A cvE ∧ eval σ' A cvE < m)
    (hev : ∀ σ', AgB b σ σ' → σ' (b + 3) < t → σ' (b + 5) ≤ V → Bdd V σ' A evE ∧ eval σ' A evE < m)
    (hjm : (j + 1) * m ≤ V) (hmm : m * m ≤ V) (hP : 2 ^ (4 * t + 3 * j) ≤ V) (hQV : Q ≤ V) (h4 : 4 ≤ V) :
    Bdd V σ A (decE b vm tE QE jE cvE evE) := by
  have hjm' : j * m + m ≤ V := by rw [Nat.succ_mul] at hjm; exact hjm
  have hmV : m ≤ V := by omega
  rw [decE_eq]
  set F : ℕ → ℕ → ℕ := fun i s => eval (Function.update (Function.update σ (b + 1) i) (b + 2) s) A
    (decBody b vm tE QE cvE evE)
  set I := eval σ A (.add (.mul jE (.var vm)) (.mod (.lit 1) (.var vm)))
  have eI : I = j * m + 1 % m := by simp only [I, Ex.eval, hj, hm]
  have inv : ∀ i, iterF F I i / m ≤ j := by
    intro i
    induction i with
    | zero => show I / m ≤ j; rw [eI, mul_add_mod_div hm0]
    | succ i ih =>
        refine le_trans ?_ ih
        show F i (iterF F I i) / m ≤ _
        refine le_trans (decBody_div (σ := Function.update (Function.update σ (b + 1) i) (b + 2) (iterF F I i))
          hvm (by upd; exact hm) hm0 tE QE cvE evE) ?_
        simp
  have et := (ht σ (AgB.refl _ _)).1
  refine B_lett ⟨(ht σ (AgB.refl _ _)).2, B_add (B_mul Bj (B_var (by omega)) (by simp only [Ex.eval]; rw [hj, hm]; omega))
    (B_mod (B_lit (by omega)) (B_var (by omega))) (by simp only [Ex.eval, hj, hm]; have := Nat.mod_le 1 m; omega),
    fun i hi => ?_⟩ ?_
  · rw [et] at hi
    show Bdd V (Function.update (Function.update σ (b + 1) i) (b + 2) (iterF F I i)) A _
    exact B_decBody hvm hm hm0 ht hQ hcv hev hjm hmm hP hQV h4
      (((AgB.refl b σ).upd (by omega) i).upd (by omega) _) (by upd; exact hi) (by upd; exact inv i)
  · have hF : eval σ A (.iter (b + 1) (b + 2) tE (.add (.mul jE (.var vm)) (.mod (.lit 1) (.var vm)))
        (decBody b vm tE QE cvE evE)) = iterF F I t := by rw [eval_iter, et]
    rw [hF]
    have hsV : iterF F I t + 1 ≤ (j + 1) * m := le_of_div_le hm0 (inv t)
    have VB : Bdd V (Function.update σ b (iterF F I t)) A (.var b) := B_var (by simp; omega)
    have VM : Bdd V (Function.update σ b (iterF F I t)) A (.var vm) := B_var (by upd; omega)
    exact B_ifEq (B_div VB VM) (B_lit (Nat.zero_le _)) (B_mod VB VM) (B_lit (Nat.zero_le _))

end SB

/-! ### Pieces and rectangle factors -/

namespace SB

variable {V : ℕ} {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ}

theorem decE_lt {b vm m : ℕ} (hvm : vm < b) (hm : σ vm = m) (hm0 : 0 < m) (tE QE jE cvE evE : Ex) :
    eval σ A (decE b vm tE QE jE cvE evE) < m := by
  rw [decE_eq, eval_lett, eval_ifEq]
  split_ifs
  · simp only [Ex.eval]; upd; rw [hm]; exact Nat.mod_lt _ hm0
  · exact hm0

theorem tB_ge (lam : ℕ) : lam ≤ 3 * tB lam := by unfold tB; omega

/-- Small consequences of `2^(7 tB λ) ≤ V`, `64 ≤ V`. -/
theorem lam_facts {lam : ℕ} (hD : 2 ^ (7 * tB lam) ≤ V) (h64 : 64 ≤ V) :
    lam + 2 ≤ V ∧ 2 ^ (lam + lam) ≤ V ∧ 2 ^ lam ≤ V ∧ 7 * tB lam < V ∧ 2 * lam + 1 ≤ V := by
  have h3 := tB_ge lam
  have p1 : 2 ^ (lam + lam) ≤ V := le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) hD
  have p2 : 2 ^ lam ≤ V := le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) p1
  refine ⟨?_, p1, p2, lt_of_lt_of_le Nat.lt_two_pow_self hD,
    by have := lt_of_lt_of_le (Nat.lt_two_pow_self (n := lam + lam)) p1; omega⟩
  rcases Nat.eq_zero_or_pos lam with h0 | h0
  · omega
  · have : lam + 2 ≤ 2 ^ (lam + lam) := by
      have := Nat.lt_two_pow_self (n := lam)
      have : 2 ^ (lam + lam) = 2 ^ lam * 2 ^ lam := pow_add _ _ _
      have : 2 ≤ 2 ^ lam := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ lam := Nat.pow_le_pow_right (by norm_num) h0
      nlinarith
    omega

theorem B_tBE {vl lam : ℕ} (hl : σ vl = lam) (hV : lam + 2 ≤ V) (h3 : 3 ≤ V) : Bdd V σ A (tBE vl) :=
  B_div (B_add (B_var (by omega)) (B_lit (by omega)) (by simp only [Ex.eval, hl]; omega)) (B_lit h3)

theorem B_blkAt {b vX : ℕ} (hX : σ vX ≤ V) {t : ℕ} (hs : σ (b + 3) < t) (hP : 2 ^ (3 * t) ≤ V) (h4 : 4 ≤ V) :
    Bdd V σ A (blkAt b vX) := by
  have hp : 2 ^ (3 * σ (b + 3)) ≤ V := le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) hP
  have ht : 3 * t < V := lt_of_lt_of_le Nat.lt_two_pow_self hP
  exact B_div (B_var hX) (B_pow2 (B_mul (B_lit (by omega)) (B_var (by omega))
    (by simp only [Ex.eval]; exact le_trans Nat.lt_two_pow_self.le hp)) (by omega) (by simpa [Ex.eval] using hp))

/-- The hypotheses on `V` for the decoders at label width `λ`. -/
structure DecV (V m lam : ℕ) : Prop where
  hm : 1 < m
  hD : 2 ^ (7 * tB lam) ≤ V
  hjm : (tB lam + 1) * m ≤ V
  hmm : m * m ≤ V
  h64 : 64 ≤ V

theorem DecV.mV {V m lam : ℕ} (h : DecV V m lam) : m ≤ V :=
  le_trans (Nat.le_mul_of_pos_left _ (by have := h.hm; omega)) h.hmm

/-- The three decoders, generically: `cvE`, `evE` read `b+3` (block), `b+5` (block code), `vX`, `vY`, `vm`. -/
theorem B_decG {b vm vl m lam : ℕ} (hD : DecV V m lam) (hvm : vm < b) (hvl : vl < b) (hm : σ vm = m)
    (hl : σ vl = lam) {jE QE cvE evE : Ex} {j Q : ℕ} (hj : eval σ A jE = j) (Bj : Bdd V σ A jE) (hjt : j ≤ tB lam)
    (hQ : ∀ σ', AgB b σ σ' → eval σ' A QE = Q ∧ Bdd V σ' A QE) (hQV : Q ≤ V)
    (hcv : ∀ σ', AgB b σ σ' → σ' (b + 3) < tB lam → σ' (b + 5) ≤ V → Bdd V σ' A cvE ∧ eval σ' A cvE < m)
    (hev : ∀ σ', AgB b σ σ' → σ' (b + 3) < tB lam → σ' (b + 5) ≤ V → Bdd V σ' A evE ∧ eval σ' A evE < m) :
    Bdd V σ A (decE b vm (tBE vl) QE jE cvE evE) := by
  obtain ⟨hl2, -, -, -, -⟩ := lam_facts hD.hD hD.h64
  refine B_decE hvm hm (by have := hD.hm; omega) (t := tB lam) (fun σ' a => ⟨eval_tBE (by rw [a vl hvl, hl]),
    B_tBE (by rw [a vl hvl, hl]) hl2 (by have := hD.h64; omega)⟩) hQ hj Bj hcv hev
    (le_trans (Nat.mul_le_mul_right _ (by omega)) hD.hjm) hD.hmm
    (le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) hD.hD) hQV (by have := hD.h64; omega)

theorem B_decLE {b vm vl vX vY m lam : ℕ} (hD : DecV V m lam) (hvm : vm < b) (hvl : vl < b) (hm : σ vm = m)
    (hl : σ vl = lam) (hX : vX < b) (hY : vY < b) (hXV : σ vX ≤ V) (hYV : σ vY ≤ V)
    {jE QE : Ex} {j Q : ℕ} (hj : eval σ A jE = j) (Bj : Bdd V σ A jE) (hjt : j ≤ tB lam)
    (hQ : ∀ σ', AgB b σ σ' → eval σ' A QE = Q ∧ Bdd V σ' A QE) (hQV : Q ≤ V) :
    Bdd V σ A (decLE b vm vl vX vY jE QE) := by
  have h64 := hD.h64
  have hP : 2 ^ (3 * tB lam) ≤ V := le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) hD.hD
  refine B_decG hD hvm hvl hm hl hj Bj hjt hQ hQV (fun σ' a hs h5 => ⟨?_, ?_⟩) (fun σ' a hs h5 => ⟨?_, ?_⟩)
  · exact B_psiE (B_var h5) (B_blkAt (by rw [a vX hX]; exact hXV) hs hP (by omega))
      (B_blkAt (by rw [a vY hY]; exact hYV) hs hP (by omega)) (by omega) (by rw [a vm hvm, hm]; exact hD.mV)
  · rw [eval_cvPE vX vY (by rw [a vm hvm, hm])]; exact psiN_lt hD.hm _ _ _
  · have Bx := B_blkAt (A := A) (by rw [a vX hX]; exact hXV) hs hP (by omega)
    have By := B_blkAt (A := A) (by rw [a vY hY]; exact hYV) hs hP (by omega)
    unfold evLE
    refine B_ifEq (B_mod (B_var h5) (B_lit h64)) (B_add (B_mod Bx (B_lit (by omega)))
      (B_mul (B_lit (by omega)) (B_mod By (B_lit (by omega))) ?_) ?_) (B_lit (by omega)) (B_lit (Nat.zero_le _))
    · simp only [Ex.eval]; have := Nat.mod_lt (eval σ' A (blkAt b vY)) (show 0 < 8 by norm_num); omega
    · simp only [Ex.eval]
      have := Nat.mod_lt (eval σ' A (blkAt b vY)) (show 0 < 8 by norm_num)
      have := Nat.mod_lt (eval σ' A (blkAt b vX)) (show 0 < 8 by norm_num); omega
  · unfold evLE; exact lt_of_le_of_lt (ifEq_le (c := 1) (by simp [Ex.eval]) (by simp [Ex.eval])) hD.hm

theorem B_decRRE {b vm vl vU vV m lam : ℕ} (hD : DecV V m lam) (hvm : vm < b) (hvl : vl < b) (hm : σ vm = m)
    (hl : σ vl = lam) (hU : vU < b) (hV' : vV < b) (hUV : σ vU ≤ V) (hVV : σ vV ≤ V)
    {jE QE : Ex} {j Q : ℕ} (hj : eval σ A jE = j) (Bj : Bdd V σ A jE) (hjt : j ≤ tB lam)
    (hQ : ∀ σ', AgB b σ σ' → eval σ' A QE = Q ∧ Bdd V σ' A QE) (hQV : Q ≤ V) :
    Bdd V σ A (decRRE b vm vl vU vV jE QE) := by
  have h64 := hD.h64
  have hP : 2 ^ (3 * tB lam) ≤ V := le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) hD.hD
  refine B_decG hD hvm hvl hm hl hj Bj hjt hQ hQV (fun σ' a hs h5 => ⟨?_, ?_⟩) (fun σ' a hs h5 => ⟨?_, ?_⟩)
  · exact B_psiE (B_var h5) (B_blkAt (by rw [a vV hV']; exact hVV) hs hP (by omega))
      (B_blkAt (by rw [a vU hU]; exact hUV) hs hP (by omega)) (by omega) (by rw [a vm hvm, hm]; exact hD.mV)
  · rw [eval_cvRE vU vV (by rw [a vm hvm, hm])]; exact psiN_lt hD.hm _ _ _
  · exact B_CxE (B_var h5) (B_div (B_var h5) (B_lit (by omega))) (B_blkAt (by rw [a vU hU]; exact hUV) hs hP (by omega))
      (B_blkAt (by rw [a vV hV']; exact hVV) hs hP (by omega)) (by omega) (by rw [a vm hvm, hm]; have := hD.hm; omega)
      (by rw [a vm hvm, hm]; exact hD.hmm)
  · rw [evRRE, eval_CxE, a vm hvm, hm]; exact CxN_lt hD.hm _ _ _ _

theorem B_decCRE {b vm vl vU vV m lam : ℕ} (hD : DecV V m lam) (hvm : vm < b) (hvl : vl < b) (hm : σ vm = m)
    (hl : σ vl = lam) (hU : vU < b) (hV' : vV < b) (hUV : σ vU ≤ V) (hVV : σ vV ≤ V)
    {jE QE : Ex} {j Q : ℕ} (hj : eval σ A jE = j) (Bj : Bdd V σ A jE) (hjt : j ≤ tB lam)
    (hQ : ∀ σ', AgB b σ σ' → eval σ' A QE = Q ∧ Bdd V σ' A QE) (hQV : Q ≤ V) :
    Bdd V σ A (decCRE b vm vl vU vV jE QE) := by
  have h64 := hD.h64
  have hP : 2 ^ (3 * tB lam) ≤ V := le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) hD.hD
  refine B_decG hD hvm hvl hm hl hj Bj hjt hQ hQV (fun σ' a hs h5 => ⟨?_, ?_⟩) (fun σ' a hs h5 => ⟨?_, ?_⟩)
  · exact B_psiE (B_var h5) (B_blkAt (by rw [a vV hV']; exact hVV) hs hP (by omega))
      (B_blkAt (by rw [a vU hU]; exact hUV) hs hP (by omega)) (by omega) (by rw [a vm hvm, hm]; exact hD.mV)
  · rw [eval_cvRE vU vV (by rw [a vm hvm, hm])]; exact psiN_lt hD.hm _ _ _
  · exact B_RxE (B_var h5) (B_blkAt (by rw [a vU hU]; exact hUV) hs hP (by omega)) (B_div (B_var h5) (B_lit (by omega)))
      (B_blkAt (by rw [a vV hV']; exact hVV) hs hP (by omega)) (by omega) (by rw [a vm hvm, hm]; have := hD.hm; omega)
      (by rw [a vm hvm, hm]; exact hD.hmm)
  · rw [evCRE, eval_RxE, a vm hvm, hm]; exact RxN_lt hD.hm _ _ _ _

end SB

namespace SB

variable {V : ℕ} {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ}

theorem B_pieceE {b vm vl vi vX vY vU vV m lam : ℕ} (hD : DecV V m lam) (hvm : vm < b) (hvl : vl < b) (hi : vi < b)
    (hX : vX < b) (hY : vY < b) (hU : vU < b) (hV' : vV < b) (hm : σ vm = m) (hl : σ vl = lam)
    (hiv : σ vi ≤ tB lam) (hXV : σ vX ≤ V) (hYV : σ vY ≤ V) (hUV : σ vU ≤ V) (hVV : σ vV ≤ V) :
    Bdd V σ A (pieceE b vm vl vi vX vY vU vV) := by
  obtain ⟨hl2, -, -, h7, -⟩ := lam_facts hD.hD hD.h64
  have h64 := hD.h64; have hm1 := hD.hm; have hmV := hD.mV
  have hP : 2 ^ (4 * tB lam + 3 * σ vi) ≤ V := le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) hD.hD
  unfold pieceE
  refine B_zsum (by omega) (by omega) (B_pow2 (B_add (B_mul (B_lit (by omega)) (B_tBE hl hl2 (by omega))
    (by rw [eval_tBE hl]; simp only [Ex.eval]; omega)) (B_mul (B_lit (by omega)) (B_var (by omega))
    (by simp only [Ex.eval]; omega)) (by simp only [Ex.eval, eval_tBE hl]; omega)) (by omega)
    (by simp only [Ex.eval, eval_tBE hl]; exact hP)) fun q hq => ?_
  rw [eval_pow2] at hq; simp only [Ex.eval, eval_tBE hl] at hq
  have hqV : q ≤ V := by have := lt_of_lt_of_le hq hP; omega
  set σ1 := Function.update σ b q
  have e : ∀ v, v < b → σ1 v = σ v := fun v hv => by simp only [σ1]; upd
  have hm' : σ1 vm = m := by rw [e vm hvm, hm]
  have hl' : σ1 vl = lam := by rw [e vl hvl, hl]
  have hQ : ∀ (k : ℕ), b < k → ∀ σ', AgB k σ1 σ' → eval σ' A (.var b) = q ∧ Bdd V σ' A (.var b) := by
    intro k hk σ' a
    have : σ' b = q := by rw [a b hk]; simp [σ1]
    exact ⟨this, B_var (by rw [this]; exact hqV)⟩
  have hj : eval σ1 A (.var vi) = σ vi := e vi hi
  have Bj : Bdd V σ1 A (.var vi) := B_var (by rw [e vi hi]; omega)
  have l1 : eval σ1 A (decLE (b + 2) vm vl vX vY (.var vi) (.var b)) < m :=
    decE_lt (b := b + 2) (by omega) hm' (by omega) _ _ _ _ _
  have l2 : eval σ1 A (decRRE (b + 10) vm vl vU vV (.var vi) (.var b)) < m :=
    decE_lt (b := b + 10) (by omega) hm' (by omega) _ _ _ _ _
  exact B_zmul (B_decLE hD (by omega) (by omega) hm' hl' (by omega) (by omega) (by rw [e vX hX]; exact hXV)
      (by rw [e vY hY]; exact hYV) hj Bj hiv (hQ (b + 2) (by omega)) hqV)
    (B_decRRE hD (by omega) (by omega) hm' hl' (by omega) (by omega) (by rw [e vU hU]; exact hUV)
      (by rw [e vV hV']; exact hVV) hj Bj hiv (hQ (b + 10) (by omega)) hqV)
    (by rw [hm']; exact hmV) (le_trans (Nat.mul_le_mul l1.le l2.le) hD.hmm)

theorem B_jOf (tr : Bool) {vl vi lam : ℕ} (hl : σ vl = lam) (hV : lam + 2 ≤ V) (h3 : 3 ≤ V) (hiV : σ vi ≤ V) :
    Bdd V σ A (jOf tr vl vi) := by
  cases tr
  · exact B_var hiV
  · exact B_sub (B_tBE hl hV h3) (B_var hiV)

theorem jOf_le (tr : Bool) {vl vi lam : ℕ} (hl : σ vl = lam) (hiv : σ vi ≤ tB lam) :
    eval σ A (jOf tr vl vi) ≤ tB lam := by
  rw [eval_jOf tr hl]; split_ifs <;> omega

theorem lt_pow_mul {X Y P : ℕ} (hX : X < P) (hY : Y < P) : X + P * Y < P * P := by nlinarith

/-- **The left rectangle factor.** -/
theorem B_facLE (tr : Bool) {b vm vl vi vX vY vQ m lam : ℕ} (hD : DecV V m lam) (hvm : vm < b) (hvl : vl < b)
    (_hi : vi < b) (hX : vX < b) (hY : vY < b) (hQ : vQ < b) (hm : σ vm = m) (hl : σ vl = lam)
    (hiv : σ vi ≤ tB lam) (hXv : σ vX < 2 ^ lam) (hYv : σ vY < 2 ^ lam) (hQV : σ vQ ≤ V) :
    Bdd V σ A (facLE tr b vm vl vi vX vY vQ) := by
  obtain ⟨hl2, h2l, hpl, h7, hl21⟩ := lam_facts hD.hD hD.h64
  have h64 := hD.h64
  unfold facLE
  refine B_lett (B_jOf tr hl hl2 (by omega) (by omega)) ?_
  have hjt := jOf_le (A := A) tr hl hiv
  set j := eval σ A (jOf tr vl vi)
  set σ1 := Function.update σ b j
  have e : ∀ v, v < b → σ1 v = σ v := fun v hv => by simp only [σ1]; upd
  have hm' : σ1 vm = m := by rw [e vm hvm, hm]
  have hl' : σ1 vl = lam := by rw [e vl hvl, hl]
  have eb : σ1 b = j := by simp [σ1]
  have BT := B_tBE (A := A) hl' hl2 (by omega)
  refine B_ifLt' (B_add (B_mul (B_lit (by omega)) BT (by rw [eval_tBE hl']; simp only [Ex.eval]; omega))
      (B_mul (B_lit (by omega)) (B_var (by rw [eb]; omega)) (by simp only [Ex.eval, eb]; omega))
      (by simp only [Ex.eval, eval_tBE hl', eb]; omega))
    (B_add (B_mul (B_lit (by omega)) (B_var (by rw [hl']; omega)) (by simp only [Ex.eval, hl']; omega))
      (B_lit (by omega)) (by simp only [Ex.eval, hl']; omega)) (fun _ => ?_) (fun _ => ?_)
  · exact B_decLE hD (by omega) (by omega) hm' hl' (by omega) (by omega)
      (by rw [e vX hX]; omega) (by rw [e vY hY]; omega) eb (B_var (by rw [eb]; omega)) hjt
      (fun σ' a => by
        have : σ' vQ = σ vQ := by rw [a vQ (by omega), e vQ hQ]
        exact ⟨this, B_var (by rw [this]; exact hQV)⟩) hQV
  · have hX1 : σ1 vX < 2 ^ lam := by rw [e vX hX]; exact hXv
    have hY1 : σ1 vY < 2 ^ lam := by rw [e vY hY]; exact hYv
    have hpp := lt_pow_mul hX1 hY1
    rw [← pow_add] at hpp
    refine B_ifEq (B_mod (B_var (by rw [e vQ hQ]; exact hQV)) (B_pow2 (B_add (B_var (by rw [hl']; omega))
      (B_var (by rw [hl']; omega)) (by simp only [Ex.eval, hl']; exact le_trans Nat.lt_two_pow_self.le h2l))
      (by omega) (by simp only [Ex.eval, hl']; exact h2l)))
      (B_add (B_var (by omega)) (B_mul (B_pow2 (B_var (by rw [hl']; omega)) (by omega) (by simp only [Ex.eval, hl']; exact hpl))
        (B_var (by omega)) (by simp only [Ex.eval, eval_pow2, hl']; omega))
        (by simp only [Ex.eval, eval_pow2, hl']; omega)) (B_lit (by omega)) (B_lit (Nat.zero_le _))

/-- **The right rectangle factor.** -/
theorem B_facRE (tr : Bool) {b vm vl vi vU vV vQ m lam : ℕ} (hD : DecV V m lam) (hvm : vm < b) (hvl : vl < b)
    (hi : vi < b) (hU : vU < b) (hV' : vV < b) (hQ : vQ < b) (hm : σ vm = m) (hl : σ vl = lam)
    (hiv : σ vi ≤ tB lam) (hUv : σ vU < 2 ^ lam) (hVv : σ vV < 2 ^ lam) (hQV : σ vQ ≤ V) :
    Bdd V σ A (facRE tr b vm vl vi vU vV vQ) := by
  obtain ⟨hl2, h2l, hpl, h7, hl21⟩ := lam_facts hD.hD hD.h64
  have h64 := hD.h64
  unfold facRE
  refine B_lett (B_jOf tr hl hl2 (by omega) (by omega)) ?_
  have hjt := jOf_le (A := A) tr hl hiv
  set j := eval σ A (jOf tr vl vi)
  set σ1 := Function.update σ b j
  have e : ∀ v, v < b → σ1 v = σ v := fun v hv => by simp only [σ1]; upd
  have hm' : σ1 vm = m := by rw [e vm hvm, hm]
  have hl' : σ1 vl = lam := by rw [e vl hvl, hl]
  have eb : σ1 b = j := by simp [σ1]
  have BT := B_tBE (A := A) hl' hl2 (by omega)
  have hQ1 : ∀ σ', AgB (b + 1) σ1 σ' → eval σ' A (.var vQ) = σ vQ ∧ Bdd V σ' A (.var vQ) := fun σ' a => by
    have : σ' vQ = σ vQ := by rw [a vQ (by omega), e vQ hQ]
    exact ⟨this, B_var (by rw [this]; exact hQV)⟩
  have hU1 : σ1 vU ≤ V := by rw [e vU hU]; omega
  have hV1 : σ1 vV ≤ V := by rw [e vV hV']; omega
  refine B_ifLt' (B_add (B_mul (B_lit (by omega)) BT (by rw [eval_tBE hl']; simp only [Ex.eval]; omega))
      (B_mul (B_lit (by omega)) (B_var (by rw [eb]; omega)) (by simp only [Ex.eval, eb]; omega))
      (by simp only [Ex.eval, eval_tBE hl', eb]; omega))
    (B_add (B_mul (B_lit (by omega)) (B_var (by rw [hl']; omega)) (by simp only [Ex.eval, hl']; omega))
      (B_lit (by omega)) (by simp only [Ex.eval, hl']; omega)) (fun _ => ?_) (fun _ => ?_)
  · cases tr
    · exact B_decRRE hD (by omega) (by omega) hm' hl' (by omega) (by omega) hU1 hV1 eb (B_var (by rw [eb]; omega)) hjt
        hQ1 hQV
    · exact B_decCRE hD (by omega) (by omega) hm' hl' (by omega) (by omega) hU1 hV1 eb (B_var (by rw [eb]; omega)) hjt
        hQ1 hQV
  · have BP : ∀ σ' : ℕ → ℕ, σ' vl = lam → Bdd V σ' A (pow2 (b + 3) (.var vl)) := fun σ' h' =>
      B_pow2 (B_var (by rw [h']; omega)) (by omega) (by simp only [Ex.eval, h']; exact hpl)
    have hQ1' : σ1 vQ ≤ V := by rw [e vQ hQ]; exact hQV
    refine B_lett (B_mod (B_var hQ1') (BP σ1 hl')) ?_
    set σ2 := Function.update σ1 (b + 1) (eval σ1 A (.mod (.var vQ) (pow2 (b + 3) (.var vl))))
    have hl2' : σ2 vl = lam := by simp only [σ2]; upd; exact hl'
    have v1 : σ2 (b + 1) < 2 ^ lam := by
      simp only [σ2, Ex.eval, eval_pow2, hl']; upd; exact Nat.mod_lt _ (by positivity)
    refine B_lett (B_mod (B_div (B_var (by simp only [σ2]; upd; exact hQ1')) (BP σ2 hl2')) (BP σ2 hl2')) ?_
    set σ3 := Function.update σ2 (b + 2) (eval σ2 A (.mod (.div (.var vQ) (pow2 (b + 3) (.var vl))) (pow2 (b + 3) (.var vl))))
    have e3 : ∀ v, v < b → σ3 v = σ v := fun v hv => by simp only [σ3, σ2]; upd; exact e v hv
    have w1 : σ3 (b + 1) < 2 ^ lam := by simp only [σ3]; upd; exact v1
    have w2 : σ3 (b + 2) < 2 ^ lam := by
      simp only [σ3, Ex.eval, eval_pow2, hl2']; upd; exact Nat.mod_lt _ (by positivity)
    have hm3 : σ3 vm = m := by rw [e3 vm hvm, hm]
    have hl3 : σ3 vl = lam := by rw [e3 vl hvl, hl]
    cases tr
    · exact B_pieceE hD (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hm3 hl3
        (by rw [e3 vi hi]; exact hiv) (by omega) (by omega) (by rw [e3 vU hU]; omega) (by rw [e3 vV hV']; omega)
    · exact B_pieceE hD (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hm3 hl3
        (by rw [e3 vi hi]; exact hiv) (by omega) (by rw [e3 vU hU]; omega) (by omega) (by rw [e3 vV hV']; omega)

end SB

end Factoring.Aux
