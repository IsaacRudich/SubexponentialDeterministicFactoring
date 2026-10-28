/-
Expressions that read arrays only through the test `0 < A a i` (`bitRd`): their value and cost do not change when
every array cell is replaced by `[cell ≠ 0]`, so cost bounds may assume cells `≤ 1`.

* `RdN b e` (`b`: `e` is the right operand of a test `lit 0 < ·`; an array read is allowed only there);
  **`RdN_congr`**; `normA A` (cells replaced by `0/1`), `normA_le`, `normA_iff`, **`eval_cost_normA`**.

Not an audit surface.
-/
module

public import FactoringAux.EngineIn

@[expose] public section

namespace Factoring.Aux

open Finset

namespace Ex

/-- Is `e` the literal `0`? -/
def isZ : Ex → Bool
  | lit 0 => true
  | _ => false

/-- Array reads only as `lit 0 < rd a i`. -/
def RdN : Bool → Ex → Prop
  | _, lit _ => True
  | _, var _ => True
  | b, rd _ i => b = true ∧ RdN false i
  | _, add e f => RdN false e ∧ RdN false f
  | _, sub e f => RdN false e ∧ RdN false f
  | _, mul e f => RdN false e ∧ RdN false f
  | _, div e f => RdN false e ∧ RdN false f
  | _, mod e f => RdN false e ∧ RdN false f
  | _, ifLt e f u v => RdN false e ∧ RdN (isZ e) f ∧ RdN false u ∧ RdN false v
  | _, lett _ e b => RdN false e ∧ RdN false b
  | _, sum _ n m b => RdN false n ∧ RdN false m ∧ RdN false b
  | _, prod _ n m b => RdN false n ∧ RdN false m ∧ RdN false b
  | _, blk _ e => RdN false e
  | _, iter _ _ n i b => RdN false n ∧ RdN false i ∧ RdN false b

theorem isZ_eq {e : Ex} (h : isZ e = true) : e = lit 0 := by
  match e, h with
  | lit 0, _ => rfl

/-- **Reads through `0 < ·` only**: the cost, whether the value is `0`, and (outside a test) the value depend on the
arrays only through `[cell ≠ 0]`. -/
theorem RdN_congr {A A' : ℕ → ℕ → ℕ} (hA : ∀ a j, (A a j = 0 ↔ A' a j = 0)) :
    ∀ (e : Ex) (b : Bool) (σ : ℕ → ℕ), RdN b e →
      cost σ A e = cost σ A' e ∧ (eval σ A e = 0 ↔ eval σ A' e = 0) ∧ (b = false → eval σ A e = eval σ A' e)
  | lit _, _, _, _ => ⟨rfl, Iff.rfl, fun _ => rfl⟩
  | var _, _, _, _ => ⟨rfl, Iff.rfl, fun _ => rfl⟩
  | rd a i, b, σ, h => by
      obtain ⟨c1, -, e1⟩ := RdN_congr hA i false σ h.2
      refine ⟨by simp only [cost, c1], ?_, fun hb => absurd (h.1.symm.trans hb) (by decide)⟩
      show A a (eval σ A i) = 0 ↔ A' a (eval σ A' i) = 0
      rw [← e1 rfl]; exact hA _ _
  | add e f, _, σ, h | sub e f, _, σ, h | mul e f, _, σ, h | div e f, _, σ, h | mod e f, _, σ, h => by
      obtain ⟨c1, -, e1⟩ := RdN_congr hA e false σ h.1
      obtain ⟨c2, -, e2⟩ := RdN_congr hA f false σ h.2
      have v1 := e1 rfl; have v2 := e2 rfl
      refine ⟨by simp only [cost, c1, c2, v1, v2], by simp only [eval, v1, v2], fun _ => by simp only [eval, v1, v2]⟩
  | ifLt e f u v, _, σ, h => by
      obtain ⟨c1, -, e1⟩ := RdN_congr hA e false σ h.1
      obtain ⟨c2, z2, e2⟩ := RdN_congr hA f (isZ e) σ h.2.1
      obtain ⟨c3, -, e3⟩ := RdN_congr hA u false σ h.2.2.1
      obtain ⟨c4, -, e4⟩ := RdN_congr hA v false σ h.2.2.2
      have v1 := e1 rfl; have v3 := e3 rfl; have v4 := e4 rfl
      have hc : (eval σ A e < eval σ A f) ↔ (eval σ A' e < eval σ A' f) := by
        cases hz : isZ e
        · rw [v1, e2 hz]
        · rw [isZ_eq hz] at v1 ⊢
          show 0 < eval σ A f ↔ 0 < eval σ A' f
          rw [Nat.pos_iff_ne_zero, Nat.pos_iff_ne_zero, Ne, Ne, z2]
      have hv : eval σ A (ifLt e f u v) = eval σ A' (ifLt e f u v) := by
        show (if eval σ A e < eval σ A f then eval σ A u else eval σ A v) =
          (if eval σ A' e < eval σ A' f then eval σ A' u else eval σ A' v)
        by_cases hp : eval σ A e < eval σ A f
        · rw [if_pos hp, if_pos (hc.mp hp), v3]
        · rw [if_neg hp, if_neg (fun h' => hp (hc.mpr h')), v4]
      refine ⟨?_, by rw [hv], fun _ => hv⟩
      show cost σ A e + cost σ A f + (if eval σ A e < eval σ A f then cost σ A u else cost σ A v) + 6 =
        cost σ A' e + cost σ A' f + (if eval σ A' e < eval σ A' f then cost σ A' u else cost σ A' v) + 6
      by_cases hp : eval σ A e < eval σ A f
      · rw [if_pos hp, if_pos (hc.mp hp), c1, c2, c3]
      · rw [if_neg hp, if_neg (fun h' => hp (hc.mpr h')), c1, c2, c4]
  | lett x e b, _, σ, h => by
      obtain ⟨c1, -, e1⟩ := RdN_congr hA e false σ h.1
      have v1 := e1 rfl
      obtain ⟨c2, -, e2⟩ := RdN_congr hA b false (Function.update σ x (eval σ A e)) h.2
      have v2 := e2 rfl
      have hv : eval σ A (lett x e b) = eval σ A' (lett x e b) := by simp only [eval, ← v1, v2]
      exact ⟨by simp only [cost, c1, ← v1, c2], by rw [hv], fun _ => hv⟩
  | sum x n m b, _, σ, h => by
      obtain ⟨c1, -, e1⟩ := RdN_congr hA n false σ h.1
      obtain ⟨c2, -, e2⟩ := RdN_congr hA m false σ h.2.1
      have v1 := e1 rfl; have v2 := e2 rfl
      have hb : ∀ j, eval (Function.update σ x j) A b = eval (Function.update σ x j) A' b ∧
          cost (Function.update σ x j) A b = cost (Function.update σ x j) A' b :=
        fun j => by
          obtain ⟨c, -, e⟩ := RdN_congr hA b false (Function.update σ x j) h.2.2
          exact ⟨e rfl, c⟩
      have hv : eval σ A (sum x n m b) = eval σ A' (sum x n m b) := by
        simp only [eval, v1, v2, fun j => (hb j).1]
      exact ⟨by simp only [cost, c1, c2, v1, v2, fun j => (hb j).1, fun j => (hb j).2], by rw [hv], fun _ => hv⟩
  | prod x n m b, _, σ, h => by
      obtain ⟨c1, -, e1⟩ := RdN_congr hA n false σ h.1
      obtain ⟨c2, -, e2⟩ := RdN_congr hA m false σ h.2.1
      have v1 := e1 rfl; have v2 := e2 rfl
      have hb : ∀ j, eval (Function.update σ x j) A b = eval (Function.update σ x j) A' b ∧
          cost (Function.update σ x j) A b = cost (Function.update σ x j) A' b :=
        fun j => by
          obtain ⟨c, -, e⟩ := RdN_congr hA b false (Function.update σ x j) h.2.2
          exact ⟨e rfl, c⟩
      have hv : eval σ A (prod x n m b) = eval σ A' (prod x n m b) := by
        simp only [eval, v1, v2, fun j => (hb j).1]
      exact ⟨by simp only [cost, c1, c2, v1, v2, fun j => (hb j).1, fun j => (hb j).2], by rw [hv], fun _ => hv⟩
  | blk _ e, _, σ, h => by
      obtain ⟨c1, -, e1⟩ := RdN_congr hA e false σ h
      exact ⟨c1, by simp only [eval, e1 rfl], fun _ => e1 rfl⟩
  | iter x y n i b, _, σ, h => by
      obtain ⟨c1, -, e1⟩ := RdN_congr hA n false σ h.1
      obtain ⟨c2, -, e2⟩ := RdN_congr hA i false σ h.2.1
      have v1 := e1 rfl; have v2 := e2 rfl
      have hb : ∀ j s, eval (Function.update (Function.update σ x j) y s) A b =
            eval (Function.update (Function.update σ x j) y s) A' b ∧
          cost (Function.update (Function.update σ x j) y s) A b =
            cost (Function.update (Function.update σ x j) y s) A' b :=
        fun j s => by
          obtain ⟨c, -, e⟩ := RdN_congr hA b false (Function.update (Function.update σ x j) y s) h.2.2
          exact ⟨e rfl, c⟩
      have hv : eval σ A (iter x y n i b) = eval σ A' (iter x y n i b) := by
        simp only [eval, v1, v2, fun j s => (hb j s).1]
      exact ⟨by simp only [cost, c1, c2, v1, v2, fun j s => (hb j s).1, fun j s => (hb j s).2], by rw [hv],
        fun _ => hv⟩

end Ex

/-- The arrays with every cell replaced by `[cell ≠ 0]`. -/
def normA (A : ℕ → ℕ → ℕ) : ℕ → ℕ → ℕ := fun a j => if A a j = 0 then 0 else 1

theorem normA_le (A : ℕ → ℕ → ℕ) (a j : ℕ) : normA A a j ≤ 1 := by unfold normA; split_ifs <;> omega

theorem normA_iff (A : ℕ → ℕ → ℕ) (a j : ℕ) : (A a j = 0 ↔ normA A a j = 0) := by
  unfold normA; split_ifs with h <;> simp [h]

/-- **Cost and value with normalized arrays.** -/
theorem eval_cost_normA {e : Ex} (h : Ex.RdN false e) (σ : ℕ → ℕ) (A : ℕ → ℕ → ℕ) :
    Ex.eval σ A e = Ex.eval σ (normA A) e ∧ Ex.cost σ A e = Ex.cost σ (normA A) e := by
  obtain ⟨c, -, v⟩ := Ex.RdN_congr (normA_iff A) e false σ h
  exact ⟨v rfl, c⟩

end Factoring.Aux
