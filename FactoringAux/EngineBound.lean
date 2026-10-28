/-
Generic facts about expressions (`Ex`) for the counting engine.

* `Ex.FV s e`: every free variable of `e` satisfies `s` (binders of `lett`, `sum`, `prod`, `iter` are not free).
  **`FV_congr`**: value and cost depend only on the free variables.  `VB_blk`: a block whose free variables are below
  `t` and whose variables (bound ones included) are below `T` satisfies `VB t`.
* `Ex.dp e`: the nesting depth.
* `Ex.Bdd V σ A e`: every value met while evaluating `e` (and every loop bound and partial fold) is at most `V`.
  **`cost_le_of_Bdd`**: then `cost σ A e ≤ (64 (V+1)^3)^(dp e)`; `eval_le_of_Bdd`: the value is at most `V`.

So the cost of a fixed expression is a polynomial (of fixed degree `3 dp e`) in the largest value it meets.

Not an audit surface.
-/
module

public import FactoringAux.Ex

@[expose] public section

namespace Factoring.Aux

open Finset

namespace Ex

/-- Every free variable of `e` satisfies `s`. -/
def FV (s : ℕ → Prop) : Ex → Prop
  | lit _ => True
  | var x => s x
  | rd _ i => FV s i
  | add e f => FV s e ∧ FV s f
  | sub e f => FV s e ∧ FV s f
  | mul e f => FV s e ∧ FV s f
  | div e f => FV s e ∧ FV s f
  | mod e f => FV s e ∧ FV s f
  | ifLt e f u v => FV s e ∧ FV s f ∧ FV s u ∧ FV s v
  | lett x e b => FV s e ∧ FV (fun y => s y ∨ y = x) b
  | sum x n m b => FV s n ∧ FV s m ∧ FV (fun y => s y ∨ y = x) b
  | prod x n m b => FV s n ∧ FV s m ∧ FV (fun y => s y ∨ y = x) b
  | blk _ e => FV s e
  | iter x y n i b => FV s n ∧ FV s i ∧ FV (fun z => (s z ∨ z = x) ∨ z = y) b

theorem agree_upd {s : ℕ → Prop} {σ σ' : ℕ → ℕ} (h : ∀ y, s y → σ y = σ' y) (x v : ℕ) :
    ∀ y, (s y ∨ y = x) → Function.update σ x v y = Function.update σ' x v y := by
  intro y hy
  by_cases hyx : y = x
  · subst hyx; simp
  · simp only [Function.update_apply, hyx, if_false]
    exact h y (hy.resolve_right hyx)

/-- Value and cost depend only on the free variables. -/
theorem FV_congr (A : ℕ → ℕ → ℕ) : ∀ (e : Ex) (s : ℕ → Prop) (σ σ' : ℕ → ℕ), (∀ y, s y → σ y = σ' y) →
    FV s e → eval σ A e = eval σ' A e ∧ cost σ A e = cost σ' A e
  | lit _, _, _, _, _, _ => ⟨rfl, rfl⟩
  | var x, _, _, _, h, hv => ⟨h x hv, rfl⟩
  | rd a i, s, σ, σ', h, hv => by
      obtain ⟨h1, h2⟩ := FV_congr A i s σ σ' h hv
      constructor <;> simp only [eval, cost, h1, h2]
  | add e f, s, σ, σ', h, hv | sub e f, s, σ, σ', h, hv | mul e f, s, σ, σ', h, hv
  | div e f, s, σ, σ', h, hv | mod e f, s, σ, σ', h, hv => by
      obtain ⟨h1, h2⟩ := FV_congr A e s σ σ' h hv.1
      obtain ⟨h3, h4⟩ := FV_congr A f s σ σ' h hv.2
      constructor <;> simp only [eval, cost, h1, h2, h3, h4]
  | ifLt e f u v, s, σ, σ', h, hv => by
      obtain ⟨h1, h2⟩ := FV_congr A e s σ σ' h hv.1
      obtain ⟨h3, h4⟩ := FV_congr A f s σ σ' h hv.2.1
      obtain ⟨h5, h6⟩ := FV_congr A u s σ σ' h hv.2.2.1
      obtain ⟨h7, h8⟩ := FV_congr A v s σ σ' h hv.2.2.2
      constructor <;> simp only [eval, cost, h1, h2, h3, h4, h5, h6, h7, h8]
  | lett x e b, s, σ, σ', h, hv => by
      obtain ⟨h1, h2⟩ := FV_congr A e s σ σ' h hv.1
      obtain ⟨h3, h4⟩ := FV_congr A b _ _ _ (agree_upd h x (eval σ A e)) hv.2
      constructor <;> simp only [eval, cost, h2, h3, h4, ← h1]
  | sum x n m b, s, σ, σ', h, hv | prod x n m b, s, σ, σ', h, hv => by
      obtain ⟨h1, h2⟩ := FV_congr A n s σ σ' h hv.1
      obtain ⟨h3, h4⟩ := FV_congr A m s σ σ' h hv.2.1
      have hb : ∀ j, eval (Function.update σ x j) A b = eval (Function.update σ' x j) A b ∧
          cost (Function.update σ x j) A b = cost (Function.update σ' x j) A b :=
        fun j => FV_congr A b _ _ _ (agree_upd h x j) hv.2.2
      constructor <;> simp only [eval, cost, h1, h2, h3, h4, fun j => (hb j).1, fun j => (hb j).2]
  | blk _ e, s, σ, σ', h, hv => FV_congr A e s σ σ' h hv
  | iter x y n i b, s, σ, σ', h, hv => by
      obtain ⟨h1, h2⟩ := FV_congr A n s σ σ' h hv.1
      obtain ⟨h3, h4⟩ := FV_congr A i s σ σ' h hv.2.1
      have hb : ∀ j v, eval (Function.update (Function.update σ x j) y v) A b =
            eval (Function.update (Function.update σ' x j) y v) A b ∧
          cost (Function.update (Function.update σ x j) y v) A b =
            cost (Function.update (Function.update σ' x j) y v) A b :=
        fun j v => FV_congr A b _ _ _ (agree_upd (agree_upd h x j) y v) hv.2.2
      constructor <;> simp only [eval, cost, h1, h2, h3, h4, fun j v => (hb j v).1, fun j v => (hb j v).2]

theorem FV_mono {s s' : ℕ → Prop} (h : ∀ y, s y → s' y) : ∀ e : Ex, FV s e → FV s' e
  | lit _, _ => trivial
  | var _, hv => h _ hv
  | rd _ i, hv => FV_mono h i hv
  | add e f, hv | sub e f, hv | mul e f, hv | div e f, hv | mod e f, hv => ⟨FV_mono h e hv.1, FV_mono h f hv.2⟩
  | ifLt e f u v, hv => ⟨FV_mono h e hv.1, FV_mono h f hv.2.1, FV_mono h u hv.2.2.1, FV_mono h v hv.2.2.2⟩
  | lett x e b, hv => ⟨FV_mono h e hv.1, FV_mono (fun y hy => hy.imp_left (h y)) b hv.2⟩
  | sum x n m b, hv | prod x n m b, hv => ⟨FV_mono h n hv.1, FV_mono h m hv.2.1,
      FV_mono (fun y hy => hy.imp_left (h y)) b hv.2.2⟩
  | blk _ e, hv => FV_mono h e hv
  | iter x y n i b, hv => ⟨FV_mono h n hv.1, FV_mono h i hv.2.1,
      FV_mono (fun z hz => hz.imp_left (fun hz' => hz'.imp_left (h z))) b hv.2.2⟩

/-- A block whose free variables are below `t` and all of whose variables are below `T`. -/
theorem VB_blk {t T : ℕ} {e : Ex} (hf : FV (· < t) e) (hv : VB T e) : VB t (blk T e) :=
  ⟨hv, fun σ σ' A h => FV_congr A e _ σ σ' h hf⟩

/-- The nesting depth. -/
def dp : Ex → ℕ
  | lit _ => 1
  | var _ => 1
  | rd _ i => dp i + 1
  | add e f => max (dp e) (dp f) + 1
  | sub e f => max (dp e) (dp f) + 1
  | mul e f => max (dp e) (dp f) + 1
  | div e f => max (dp e) (dp f) + 1
  | mod e f => max (dp e) (dp f) + 1
  | ifLt e f u v => max (max (dp e) (dp f)) (max (dp u) (dp v)) + 1
  | lett _ e b => max (dp e) (dp b) + 1
  | sum _ n m b => max (max (dp n) (dp m)) (dp b) + 1
  | prod _ n m b => max (max (dp n) (dp m)) (dp b) + 1
  | blk _ e => dp e + 1
  | iter _ _ n i b => max (max (dp n) (dp i)) (dp b) + 1

/-- Every value met in the evaluation is at most `V`. -/
def Bdd (V : ℕ) (σ : ℕ → ℕ) (A : ℕ → ℕ → ℕ) : Ex → Prop
  | lit k => k ≤ V
  | var x => σ x ≤ V
  | rd a i => Bdd V σ A i ∧ A a (eval σ A i) ≤ V
  | add e f => Bdd V σ A e ∧ Bdd V σ A f ∧ eval σ A e + eval σ A f ≤ V
  | sub e f => Bdd V σ A e ∧ Bdd V σ A f
  | mul e f => Bdd V σ A e ∧ Bdd V σ A f ∧ eval σ A e * eval σ A f ≤ V
  | div e f => Bdd V σ A e ∧ Bdd V σ A f
  | mod e f => Bdd V σ A e ∧ Bdd V σ A f
  | ifLt e f u v => Bdd V σ A e ∧ Bdd V σ A f ∧
      (if eval σ A e < eval σ A f then Bdd V σ A u else Bdd V σ A v)
  | lett x e b => Bdd V σ A e ∧ Bdd V (Function.update σ x (eval σ A e)) A b
  | sum x n m b => Bdd V σ A n ∧ Bdd V σ A m ∧ (∀ j < eval σ A n, Bdd V (Function.update σ x j) A b) ∧
      ∀ j ≤ eval σ A n, foldSum (fun i => eval (Function.update σ x i) A b) (eval σ A m) j ≤ V
  | prod x n m b => Bdd V σ A n ∧ Bdd V σ A m ∧ (∀ j < eval σ A n, Bdd V (Function.update σ x j) A b) ∧
      ∀ j ≤ eval σ A n, foldProd (fun i => eval (Function.update σ x i) A b) (eval σ A m) j ≤ V
  | blk _ e => Bdd V σ A e
  | iter x y n i b => Bdd V σ A n ∧ Bdd V σ A i ∧ ∀ j < eval σ A n,
      Bdd V (Function.update (Function.update σ x j) y
        (iterF (fun j s => eval (Function.update (Function.update σ x j) y s) A b) (eval σ A i) j)) A b

theorem eval_le_of_Bdd {V : ℕ} (A : ℕ → ℕ → ℕ) : ∀ (e : Ex) (σ : ℕ → ℕ), Bdd V σ A e → eval σ A e ≤ V
  | lit _, _, h => h
  | var _, _, h => h
  | rd _ _, _, h => h.2
  | add _ _, _, h => h.2.2
  | sub e f, σ, h => le_trans (Nat.sub_le _ _) (eval_le_of_Bdd A e σ h.1)
  | mul _ _, _, h => h.2.2
  | div e f, σ, h => le_trans (Nat.div_le_self _ _) (eval_le_of_Bdd A e σ h.1)
  | mod e f, σ, h => le_trans (Nat.mod_le _ _) (eval_le_of_Bdd A e σ h.1)
  | ifLt e f u v, σ, h => by
      simp only [eval]
      have h3 := h.2.2
      split_ifs at h3 ⊢
      · exact eval_le_of_Bdd A u σ h3
      · exact eval_le_of_Bdd A v σ h3
  | lett x e b, σ, h => eval_le_of_Bdd A b _ h.2
  | sum _ _ _ _, _, h => h.2.2.2 _ le_rfl
  | prod _ _ _ _, _, h => h.2.2.2 _ le_rfl
  | blk _ e, σ, h => eval_le_of_Bdd A e σ h
  | iter x y n i b, σ, h => by
      simp only [eval]
      obtain ⟨h1, h2, h3⟩ := h
      rcases Nat.eq_zero_or_pos (eval σ A n) with h0 | h0
      · rw [h0]; exact eval_le_of_Bdd A i σ h2
      · obtain ⟨k, hk⟩ : ∃ k, eval σ A n = k + 1 := ⟨eval σ A n - 1, by omega⟩
        rw [hk]
        exact eval_le_of_Bdd A b _ (h3 k (by omega))

theorem sum_le_card_mul {f : ℕ → ℕ} {N B : ℕ} (h : ∀ j < N, f j ≤ B) : ∑ j ∈ range N, f j ≤ N * B := by
  calc ∑ j ∈ range N, f j ≤ ∑ _j ∈ range N, B := Finset.sum_le_sum fun j hj => h j (Finset.mem_range.mp hj)
    _ = N * B := by simp

theorem close_step {V W c : ℕ} (hW : 1 ≤ W) (h : c ≤ (V + 4) * W + 32 * (V + 1) ^ 3) :
    c ≤ W * (64 * (V + 1) ^ 3) := by
  have h0 : V + 1 ≤ (V + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
  have h1 : V + 4 ≤ 32 * (V + 1) ^ 3 := by omega
  have h2 : 32 * (V + 1) ^ 3 ≤ 32 * (V + 1) ^ 3 * W := Nat.le_mul_of_pos_right _ hW
  have h3 : (V + 4) * W ≤ 32 * (V + 1) ^ 3 * W := Nat.mul_le_mul_right _ h1
  nlinarith

theorem close_pow {V M c : ℕ} (h : c ≤ (V + 4) * (64 * (V + 1) ^ 3) ^ M + 32 * (V + 1) ^ 3) :
    c ≤ (64 * (V + 1) ^ 3) ^ (M + 1) := by
  rw [pow_succ]
  exact close_step (Nat.one_le_pow _ _ (by have := Nat.one_le_pow 3 (V + 1) (by omega); omega)) h

/-- **The cost of an expression is a polynomial in the largest value it meets.** -/
theorem cost_le_of_Bdd {V : ℕ} (A : ℕ → ℕ → ℕ) :
    ∀ (e : Ex) (σ : ℕ → ℕ), Bdd V σ A e → cost σ A e ≤ (64 * (V + 1) ^ 3) ^ dp e := by
  have hX : 1 ≤ 64 * (V + 1) ^ 3 := by have := Nat.one_le_pow 3 (V + 1) (by omega); omega
  have mono : ∀ {a b : ℕ}, a ≤ b → (64 * (V + 1) ^ 3) ^ a ≤ (64 * (V + 1) ^ 3) ^ b :=
    fun h => Nat.pow_le_pow_right hX h
  have one : ∀ a, 1 ≤ (64 * (V + 1) ^ 3) ^ a := fun a => Nat.one_le_pow _ _ hX
  have cube : V * (2 * V + 6) + 16 * V + 30 ≤ 32 * (V + 1) ^ 3 := by
    nlinarith [Nat.zero_le V, sq_nonneg V]
  intro e
  induction e with
  | lit k => intro σ _; simpa [cost, dp] using hX
  | var x => intro σ _; simpa [cost, dp] using hX
  | rd a i ih =>
      intro σ h
      simp only [cost, dp]
      have := ih σ h.1
      refine close_pow ?_
      have := one (dp i)
      generalize (64 * (V + 1) ^ 3) ^ dp i = W at *
      nlinarith
  | add e f ihe ihf | sub e f ihe ihf | mul e f ihe ihf | div e f ihe ihf | mod e f ihe ihf =>
      intro σ h
      have hfB : Bdd V σ A f := by first | exact h.2.1 | exact h.2
      have he := le_trans (ihe σ h.1) (mono (le_max_left (dp e) (dp f)))
      have hf := le_trans (ihf σ hfB) (mono (le_max_right (dp e) (dp f)))
      have ve := eval_le_of_Bdd A e σ h.1
      have vf := eval_le_of_Bdd A f σ hfB
      have W1 := one (max (dp e) (dp f))
      simp only [cost, dp]
      refine close_pow ?_
      generalize (64 * (V + 1) ^ 3) ^ max (dp e) (dp f) = W at *
      first
        | nlinarith
        | (have : eval σ A f * (2 * eval σ A e + 6) ≤ V * (2 * V + 6) := Nat.mul_le_mul vf (by omega)
           nlinarith)
  | ifLt e f u v ihe ihf ihu ihv =>
      intro σ h
      obtain ⟨h1, h2, h3⟩ := h
      set M := max (max (dp e) (dp f)) (max (dp u) (dp v))
      have he := le_trans (ihe σ h1) (mono (show dp e ≤ M by simp [M]))
      have hf := le_trans (ihf σ h2) (mono (show dp f ≤ M by simp [M]))
      have hb : (if eval σ A e < eval σ A f then cost σ A u else cost σ A v) ≤ (64 * (V + 1) ^ 3) ^ M := by
        split_ifs at h3 ⊢
        · exact le_trans (ihu σ h3) (mono (show dp u ≤ M by simp [M]))
        · exact le_trans (ihv σ h3) (mono (show dp v ≤ M by simp [M]))
      simp only [cost, dp]
      refine close_pow ?_
      generalize (64 * (V + 1) ^ 3) ^ M = W at *
      nlinarith
  | lett x e b ihe ihb =>
      intro σ h
      have he := le_trans (ihe σ h.1) (mono (le_max_left (dp e) (dp b)))
      have hb := le_trans (ihb _ h.2) (mono (le_max_right (dp e) (dp b)))
      simp only [cost, dp]
      refine close_pow ?_
      generalize (64 * (V + 1) ^ 3) ^ max (dp e) (dp b) = W at *
      nlinarith
  | sum x n m b ihn ihm ihb =>
      intro σ h
      obtain ⟨h1, h2, h3, h4⟩ := h
      set M := max (max (dp n) (dp m)) (dp b)
      have hn := le_trans (ihn σ h1) (mono (show dp n ≤ M by simp [M]))
      have hm := le_trans (ihm σ h2) (mono (show dp m ≤ M by simp [M]))
      have vn := eval_le_of_Bdd A n σ h1
      have hs := sum_le_card_mul (N := eval σ A n)
        (B := (64 * (V + 1) ^ 3) ^ M + 16 * V + 30)
        (f := fun j => cost (Function.update σ x j) A b + 9 * eval (Function.update σ x j) A b +
          7 * foldSum (fun i => eval (Function.update σ x i) A b) (eval σ A m) j + 30) (fun j hj => by
            have c1 := le_trans (ihb _ (h3 j hj)) (mono (show dp b ≤ M by simp [M]))
            have c2 := eval_le_of_Bdd A b _ (h3 j hj)
            have c3 := h4 j hj.le
            omega)
      simp only [cost, dp]
      refine close_pow ?_
      generalize (64 * (V + 1) ^ 3) ^ M = W at *
      generalize ∑ j ∈ range (eval σ A n), (cost (Function.update σ x j) A b + 9 * eval (Function.update σ x j) A b +
          7 * foldSum (fun i => eval (Function.update σ x i) A b) (eval σ A m) j + 30) = S at *
      have : eval σ A n * (W + 16 * V + 30) ≤ V * W + V * (16 * V + 30) := by
        have := Nat.mul_le_mul_right (W + 16 * V + 30) vn
        nlinarith
      nlinarith
  | prod x n m b ihn ihm ihb =>
      intro σ h
      obtain ⟨h1, h2, h3, h4⟩ := h
      set M := max (max (dp n) (dp m)) (dp b)
      have hn := le_trans (ihn σ h1) (mono (show dp n ≤ M by simp [M]))
      have hm := le_trans (ihm σ h2) (mono (show dp m ≤ M by simp [M]))
      have vn := eval_le_of_Bdd A n σ h1
      have hs := sum_le_card_mul (N := eval σ A n)
        (B := (64 * (V + 1) ^ 3) ^ M + V * (2 * V + 6) + 7 * (V * V) + 30)
        (f := fun j => cost (Function.update σ x j) A b + eval (Function.update σ x j) A b *
          (2 * foldProd (fun i => eval (Function.update σ x i) A b) (eval σ A m) j + 6) +
          7 * (foldProd (fun i => eval (Function.update σ x i) A b) (eval σ A m) j *
            eval (Function.update σ x j) A b) + 30) (fun j hj => by
            have c1 := le_trans (ihb _ (h3 j hj)) (mono (show dp b ≤ M by simp [M]))
            have c2 := eval_le_of_Bdd A b _ (h3 j hj)
            have c3 := h4 j hj.le
            have d1 := Nat.mul_le_mul c2 (show 2 * foldProd (fun i => eval (Function.update σ x i) A b)
              (eval σ A m) j + 6 ≤ 2 * V + 6 by omega)
            have d2 := Nat.mul_le_mul c3 c2
            omega)
      simp only [cost, dp]
      refine close_pow ?_
      generalize (64 * (V + 1) ^ 3) ^ M = W at *
      generalize ∑ j ∈ range (eval σ A n), (cost (Function.update σ x j) A b + eval (Function.update σ x j) A b *
          (2 * foldProd (fun i => eval (Function.update σ x i) A b) (eval σ A m) j + 6) +
          7 * (foldProd (fun i => eval (Function.update σ x i) A b) (eval σ A m) j *
            eval (Function.update σ x j) A b) + 30) = S at *
      have h5 : eval σ A n * (W + V * (2 * V + 6) + 7 * (V * V) + 30) ≤
          V * W + V * (V * (2 * V + 6) + 7 * (V * V) + 30) := by
        have := Nat.mul_le_mul_right (W + V * (2 * V + 6) + 7 * (V * V) + 30) vn
        nlinarith
      have h6 : V * (V * (2 * V + 6) + 7 * (V * V) + 30) + 14 ≤ 32 * (V + 1) ^ 3 := by
        nlinarith [Nat.zero_le V, sq_nonneg V]
      nlinarith
  | blk T e ih =>
      intro σ h
      simp only [cost, dp]
      exact le_trans (ih σ h) (mono (Nat.le_succ _))
  | iter x y n i b ihn ihi ihb =>
      intro σ h
      obtain ⟨h1, h2, h3⟩ := h
      set M := max (max (dp n) (dp i)) (dp b)
      have hn := le_trans (ihn σ h1) (mono (show dp n ≤ M by simp [M]))
      have hi := le_trans (ihi σ h2) (mono (show dp i ≤ M by simp [M]))
      have vn := eval_le_of_Bdd A n σ h1
      have hs := sum_le_card_mul (N := eval σ A n) (B := (64 * (V + 1) ^ 3) ^ M + 5)
        (f := fun j => cost (Function.update (Function.update σ x j) y
          (iterF (fun j s => eval (Function.update (Function.update σ x j) y s) A b) (eval σ A i) j)) A b + 5)
        (fun j hj => by
          have c1 := le_trans (ihb _ (h3 j hj)) (mono (show dp b ≤ M by simp [M]))
          omega)
      simp only [cost, dp]
      refine close_pow ?_
      generalize (64 * (V + 1) ^ 3) ^ M = W at *
      generalize ∑ j ∈ range (eval σ A n), (cost (Function.update (Function.update σ x j) y
          (iterF (fun j s => eval (Function.update (Function.update σ x j) y s) A b) (eval σ A i) j)) A b + 5) = S
        at *
      have : eval σ A n * (W + 5) ≤ V * (W + 5) := Nat.mul_le_mul_right _ vn
      nlinarith

end Ex

end Factoring.Aux
