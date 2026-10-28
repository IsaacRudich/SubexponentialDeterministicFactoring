/-
Expressions over ℕ, compiled to the copied PLIB `Cmd` (the source language of the engine).

`Ex`: literals, variables (scalars), reads of arrays, `+ - * / %` (unary arithmetic: cost grows with the values),
a comparison, `let`, and folds `sum x n m b = (∑_{x<n} b) % m`, `prod x n m b = (∏_{x<n} b) % m` computed term by
term modulo `m` (`m = 0`: no reduction; `prod` of zero terms is `1`).

* `Ex.eval σ A e`: the value, for scalars `σ` and arrays `A`; `Ex.cost σ A e`: a bound on the source cost.
* `Ex.comp e d t`: a `Cmd` writing the value into scalar `d`, using scratch scalars `≥ t`.
* **`comp_spec`**: if every variable of `e` and `d` are below `t`, the command writes `eval` into `d`, keeps every
  other scalar below `t` and every array, and costs at most `cost`.

Values may be large: the engine keeps them below a polynomial in its running time (residues modulo small numbers),
so unary arithmetic costs at most that polynomial.

Not an audit surface.
-/
module

public import FactoringAux.ExCmd

@[expose] public section

namespace Factoring.Aux

open Factoring.Aux.Copied Factoring.Aux.Copied.PLib Finset

/-- Expressions. -/
inductive Ex where
  | lit (k : ℕ)
  | var (x : ℕ)
  | rd (a : ℕ) (i : Ex)
  | add (e f : Ex)
  | sub (e f : Ex)
  | mul (e f : Ex)
  | div (e f : Ex)
  | mod (e f : Ex)
  | ifLt (e f u v : Ex)
  | lett (x : ℕ) (e b : Ex)
  | sum (x : ℕ) (n m b : Ex)
  | prod (x : ℕ) (n m b : Ex)
  /-- A block with its own variables: same value as `e`; compiled with scratch from `max t T`, so `e` may bind any
  variable below `T` (its free variables must be below the enclosing bound, see `VB`). -/
  | blk (T : ℕ) (e : Ex)
  /-- A state fold: `s₀ = i`, `s_{j+1} = b` with `x := j`, `y := s_j`; the value is `s_n`. -/
  | iter (x y : ℕ) (n i b : Ex)
  deriving Inhabited

/-- `∑_{i<n} f i`, reduced modulo `m` after every term. -/
def foldSum (f : ℕ → ℕ) (m : ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => (foldSum f m i + f i) % m

/-- The state after `n` turns of `f`, from `s`. -/
def iterF (f : ℕ → ℕ → ℕ) (s : ℕ) : ℕ → ℕ
  | 0 => s
  | j + 1 => f j (iterF f s j)

/-- `∏_{i<n} f i`, reduced modulo `m` after every factor. -/
def foldProd (f : ℕ → ℕ) (m : ℕ) : ℕ → ℕ
  | 0 => 1
  | i + 1 => (foldProd f m i * f i) % m

namespace Ex

/-- The value. -/
def eval (σ : ℕ → ℕ) (A : ℕ → ℕ → ℕ) : Ex → ℕ
  | lit k => k
  | var x => σ x
  | rd a i => A a (eval σ A i)
  | add e f => eval σ A e + eval σ A f
  | sub e f => eval σ A e - eval σ A f
  | mul e f => eval σ A e * eval σ A f
  | div e f => eval σ A e / eval σ A f
  | mod e f => eval σ A e % eval σ A f
  | ifLt e f u v => if eval σ A e < eval σ A f then eval σ A u else eval σ A v
  | lett x e b => eval (Function.update σ x (eval σ A e)) A b
  | sum x n m b => foldSum (fun i => eval (Function.update σ x i) A b) (eval σ A m) (eval σ A n)
  | prod x n m b => foldProd (fun i => eval (Function.update σ x i) A b) (eval σ A m) (eval σ A n)
  | blk _ e => eval σ A e
  | iter x y n i b => iterF (fun j s => eval (Function.update (Function.update σ x j) y s) A b) (eval σ A i)
      (eval σ A n)

/-- A bound on the source cost. -/
def cost (σ : ℕ → ℕ) (A : ℕ → ℕ → ℕ) : Ex → ℕ
  | lit _ => 1
  | var _ => 1
  | rd _ i => cost σ A i + 2
  | add e f => cost σ A e + cost σ A f + 2 * eval σ A f + 12
  | sub e f => cost σ A e + cost σ A f + 2 * eval σ A f + 12
  | mul e f => cost σ A e + cost σ A f + eval σ A f * (2 * eval σ A e + 6) + 8
  | div e f => cost σ A e + cost σ A f + 7 * eval σ A e + 16
  | mod e f => cost σ A e + cost σ A f + 7 * eval σ A e + 16
  | ifLt e f u v => cost σ A e + cost σ A f + (if eval σ A e < eval σ A f then cost σ A u else cost σ A v) + 6
  | lett x e b => cost σ A e + cost (Function.update σ x (eval σ A e)) A b + 12
  | sum x n m b => cost σ A n + cost σ A m + 14 + ∑ j ∈ range (eval σ A n),
      (cost (Function.update σ x j) A b + 9 * eval (Function.update σ x j) A b +
        7 * foldSum (fun i => eval (Function.update σ x i) A b) (eval σ A m) j + 30)
  | prod x n m b => cost σ A n + cost σ A m + 14 + ∑ j ∈ range (eval σ A n),
      (cost (Function.update σ x j) A b + eval (Function.update σ x j) A b *
          (2 * foldProd (fun i => eval (Function.update σ x i) A b) (eval σ A m) j + 6) +
        7 * (foldProd (fun i => eval (Function.update σ x i) A b) (eval σ A m) j *
          eval (Function.update σ x j) A b) + 30)
  | blk _ e => cost σ A e
  | iter x y n i b => cost σ A n + cost σ A i + 14 + ∑ j ∈ range (eval σ A n),
      (cost (Function.update (Function.update σ x j) y
        (iterF (fun j s => eval (Function.update (Function.update σ x j) y s) A b) (eval σ A i) j)) A b + 5)

/-- Every variable is below `t`. -/
def VB (t : ℕ) : Ex → Prop
  | lit _ => True
  | var x => x < t
  | rd _ i => VB t i
  | add e f => VB t e ∧ VB t f
  | sub e f => VB t e ∧ VB t f
  | mul e f => VB t e ∧ VB t f
  | div e f => VB t e ∧ VB t f
  | mod e f => VB t e ∧ VB t f
  | ifLt e f u v => VB t e ∧ VB t f ∧ VB t u ∧ VB t v
  | lett x e b => x < t ∧ VB t e ∧ VB t b
  | sum x n m b => x < t ∧ VB t n ∧ VB t m ∧ VB t b
  | prod x n m b => x < t ∧ VB t n ∧ VB t m ∧ VB t b
  | blk T e => VB T e ∧ ∀ (σ σ' : ℕ → ℕ) (A : ℕ → ℕ → ℕ), (∀ y < t, σ y = σ' y) →
      eval σ A e = eval σ' A e ∧ cost σ A e = cost σ' A e
  | iter x y n i b => x < t ∧ y < t ∧ VB t n ∧ VB t i ∧ VB t b

theorem VB_mono {t t' : ℕ} (h : t ≤ t') : ∀ e : Ex, VB t e → VB t' e
  | lit _, _ => trivial
  | var _, hv => lt_of_lt_of_le hv h
  | rd _ i, hv => VB_mono h i hv
  | add e f, hv => ⟨VB_mono h e hv.1, VB_mono h f hv.2⟩
  | sub e f, hv => ⟨VB_mono h e hv.1, VB_mono h f hv.2⟩
  | mul e f, hv => ⟨VB_mono h e hv.1, VB_mono h f hv.2⟩
  | div e f, hv => ⟨VB_mono h e hv.1, VB_mono h f hv.2⟩
  | mod e f, hv => ⟨VB_mono h e hv.1, VB_mono h f hv.2⟩
  | ifLt e f u v, hv => ⟨VB_mono h e hv.1, VB_mono h f hv.2.1, VB_mono h u hv.2.2.1, VB_mono h v hv.2.2.2⟩
  | lett _ e b, hv => ⟨lt_of_lt_of_le hv.1 h, VB_mono h e hv.2.1, VB_mono h b hv.2.2⟩
  | sum _ n m b, hv => ⟨lt_of_lt_of_le hv.1 h, VB_mono h n hv.2.1, VB_mono h m hv.2.2.1, VB_mono h b hv.2.2.2⟩
  | prod _ n m b, hv => ⟨lt_of_lt_of_le hv.1 h, VB_mono h n hv.2.1, VB_mono h m hv.2.2.1, VB_mono h b hv.2.2.2⟩
  | blk _ _, hv => ⟨hv.1, fun σ σ' A hσ => hv.2 σ σ' A fun y hy => hσ y (lt_of_lt_of_le hy h)⟩
  | iter _ _ n i b, hv => ⟨lt_of_lt_of_le hv.1 h, lt_of_lt_of_le hv.2.1 h, VB_mono h n hv.2.2.1,
      VB_mono h i hv.2.2.2.1, VB_mono h b hv.2.2.2.2⟩

theorem agree_update {t : ℕ} {σ σ' : ℕ → ℕ} (h : ∀ y < t, σ y = σ' y) (x v : ℕ) :
    ∀ y < t, Function.update σ x v y = Function.update σ' x v y := by
  intro y hy; by_cases hyx : y = x
  · subst hyx; simp
  · simp [Function.update_apply, hyx, h y hy]

/-- Value and cost depend only on the variables below `t`. -/
theorem congr (A : ℕ → ℕ → ℕ) {t : ℕ} : ∀ (e : Ex) (σ σ' : ℕ → ℕ), (∀ y < t, σ y = σ' y) → VB t e →
    eval σ A e = eval σ' A e ∧ cost σ A e = cost σ' A e
  | lit _, _, _, _, _ => ⟨rfl, rfl⟩
  | var x, σ, σ', h, hv => ⟨h x hv, rfl⟩
  | rd a i, σ, σ', h, hv => by
      obtain ⟨h1, h2⟩ := congr A i σ σ' h hv
      constructor <;> simp only [eval, cost, h1, h2]
  | add e f, σ, σ', h, hv | sub e f, σ, σ', h, hv | mul e f, σ, σ', h, hv
  | div e f, σ, σ', h, hv | mod e f, σ, σ', h, hv => by
      obtain ⟨h1, h2⟩ := congr A e σ σ' h hv.1
      obtain ⟨h3, h4⟩ := congr A f σ σ' h hv.2
      constructor <;> simp only [eval, cost, h1, h2, h3, h4]
  | ifLt e f u v, σ, σ', h, hv => by
      obtain ⟨h1, h2⟩ := congr A e σ σ' h hv.1
      obtain ⟨h3, h4⟩ := congr A f σ σ' h hv.2.1
      obtain ⟨h5, h6⟩ := congr A u σ σ' h hv.2.2.1
      obtain ⟨h7, h8⟩ := congr A v σ σ' h hv.2.2.2
      constructor <;> simp only [eval, cost, h1, h2, h3, h4, h5, h6, h7, h8]
  | lett x e b, σ, σ', h, hv => by
      obtain ⟨h1, h2⟩ := congr A e σ σ' h hv.2.1
      obtain ⟨h3, h4⟩ := congr A b _ _ (agree_update h x (eval σ A e)) hv.2.2
      constructor <;> simp only [eval, cost, h2, h3, h4, ← h1]
  | sum x n m b, σ, σ', h, hv | prod x n m b, σ, σ', h, hv => by
      obtain ⟨h1, h2⟩ := congr A n σ σ' h hv.2.1
      obtain ⟨h3, h4⟩ := congr A m σ σ' h hv.2.2.1
      have hb : ∀ j, eval (Function.update σ x j) A b = eval (Function.update σ' x j) A b ∧
          cost (Function.update σ x j) A b = cost (Function.update σ' x j) A b :=
        fun j => congr A b _ _ (agree_update h x j) hv.2.2.2
      constructor <;> simp only [eval, cost, h1, h2, h3, h4, fun j => (hb j).1, fun j => (hb j).2]
  | blk _ _, σ, σ', h, hv => hv.2 σ σ' A h
  | iter x y n i b, σ, σ', h, hv => by
      obtain ⟨h1, h2⟩ := congr A n σ σ' h hv.2.2.1
      obtain ⟨h3, h4⟩ := congr A i σ σ' h hv.2.2.2.1
      have hb : ∀ j s, eval (Function.update (Function.update σ x j) y s) A b =
            eval (Function.update (Function.update σ' x j) y s) A b ∧
          cost (Function.update (Function.update σ x j) y s) A b =
            cost (Function.update (Function.update σ' x j) y s) A b :=
        fun j s => congr A b _ _ (agree_update (agree_update h x j) y s) hv.2.2.2.2
      constructor <;> simp only [eval, cost, h1, h2, h3, h4, fun j s => (hb j s).1, fun j s => (hb j s).2]

/-- The compiled command: the value into scalar `d`, scratch from `t`. -/
def comp : Ex → ℕ → ℕ → Cmd
  | lit k, d, _ => .setK d k
  | var x, d, _ => .copy d x
  | rd a i, d, t => .seq (comp i t (t + 1)) (.rd d a t 0)
  | add e f, d, t => .seq (comp e t (t + 1)) (.seq (comp f (t + 1) (t + 2))
      (.seq (.copy d t) (addTo d (t + 1) (t + 2))))
  | sub e f, d, t => .seq (comp e t (t + 1)) (.seq (comp f (t + 1) (t + 2))
      (.seq (.copy d t) (subFrom d (t + 1) (t + 2))))
  | mul e f, d, t => .seq (comp e t (t + 1)) (.seq (comp f (t + 1) (t + 2)) (mulCmd d t (t + 1) (t + 2) (t + 3)))
  | div e f, d, t => .seq (comp e t (t + 1)) (.seq (comp f (t + 1) (t + 2))
      (.seq (dmCmd (t + 2) (t + 3) t (t + 1) (t + 4)) (.ifZero (t + 1) (.setK d 0) (.copy d (t + 2)))))
  | mod e f, d, t => .seq (comp e t (t + 1)) (.seq (comp f (t + 1) (t + 2))
      (.seq (dmCmd (t + 2) (t + 3) t (t + 1) (t + 4)) (.ifZero (t + 1) (.copy d t) (.copy d (t + 3)))))
  | ifLt e f u v, d, t => .seq (comp e t (t + 1)) (.seq (comp f (t + 1) (t + 2))
      (.ifLt t (t + 1) (comp u d (t + 2)) (comp v d (t + 2))))
  | lett x e b, d, t => .seq (comp e t (t + 1)) (.seq (.copy (t + 1) x) (.seq (.copy x t)
      (.seq (comp b (t + 2) (t + 3)) (.seq (.copy x (t + 1)) (.copy d (t + 2))))))
  | sum x n m b, d, t => .seq (comp n t (t + 1)) (.seq (comp m (t + 1) (t + 2)) (.seq (.setK (t + 2) 0)
      (.seq (.copy (t + 3) x) (.seq (.loop t (t + 4) (.seq (.copy x (t + 4)) (.seq (comp b (t + 5) (t + 6))
        (.seq (addTo (t + 2) (t + 5) (t + 6)) (modIn (t + 2) (t + 1) (t + 6))))))
        (.seq (.copy x (t + 3)) (.copy d (t + 2)))))))
  | prod x n m b, d, t => .seq (comp n t (t + 1)) (.seq (comp m (t + 1) (t + 2)) (.seq (.setK (t + 2) 1)
      (.seq (.copy (t + 3) x) (.seq (.loop t (t + 4) (.seq (.copy x (t + 4)) (.seq (comp b (t + 5) (t + 6))
        (.seq (mulCmd (t + 6) (t + 2) (t + 5) (t + 7) (t + 8)) (.seq (.copy (t + 2) (t + 6))
          (modIn (t + 2) (t + 1) (t + 7)))))))
        (.seq (.copy x (t + 3)) (.copy d (t + 2)))))))
  | blk T e, d, t => comp e d (max t T)
  | iter x y n i b, d, t => .seq (comp n t (t + 1)) (.seq (comp i (t + 1) (t + 2)) (.seq (.copy (t + 2) x)
      (.seq (.copy (t + 3) y) (.seq (.loop t (t + 4) (.seq (.copy x (t + 4)) (.seq (.copy y (t + 1))
        (comp b (t + 1) (t + 5)))))
      (.seq (.copy x (t + 2)) (.seq (.copy y (t + 3)) (.copy d (t + 1))))))))

/-- `c` writes `v` into `d`, keeps the other scalars below `t` and every array, and costs at most `C`. -/
def Wr (c : Cmd) (st : St) (d t v C : ℕ) : Prop :=
  (Cmd.run c st).1.sc d = v ∧ (∀ y < t, y ≠ d → (Cmd.run c st).1.sc y = st.sc y) ∧
    (Cmd.run c st).1.ar = st.ar ∧ (Cmd.run c st).2 ≤ C

/-- After a command that keeps every scalar below `t` and every array, an expression over them keeps its value
and cost. -/
theorem keep {c : Cmd} {st : St} {d t' v C : ℕ} (hw : Wr c st d t' v C) {t : ℕ} (ht : t ≤ t') (hd : t ≤ d)
    {f : Ex} (hf : VB t f) :
    eval (Cmd.run c st).1.sc (Cmd.run c st).1.ar f = eval st.sc st.ar f ∧
      cost (Cmd.run c st).1.sc (Cmd.run c st).1.ar f = cost st.sc st.ar f := by
  rw [hw.2.2.1]; exact congr _ f _ _ (fun y hy => hw.2.1 y (by omega) (by omega)) hf

theorem nd3 {d t : ℕ} (hd : d < t) : [d, t + 1, t + 2].Nodup := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, not_false_eq_true, and_true]
  omega

/-- **The compiler is correct**, within the cost bound. -/
theorem comp_spec : ∀ (e : Ex) (d t : ℕ) (st : St), VB t e → d < t →
    Wr (comp e d t) st d t (eval st.sc st.ar e) (cost st.sc st.ar e) := by
  intro e
  induction e with
  | lit k =>
      intro d t st _ _
      refine ⟨by simp [comp, Cmd.run_setK, eval], fun y _ hy => by simp [comp, Cmd.run_setK, hy], rfl, by
        simp [comp, Cmd.run_setK, cost]⟩
  | var x =>
      intro d t st _ _
      refine ⟨by simp [comp, Cmd.run_copy, eval], fun y _ hy => by simp [comp, Cmd.run_copy, hy], rfl, by
        simp [comp, Cmd.run_copy, cost]⟩
  | rd a i ih =>
      intro d t st hv hd
      have w := ih t (t + 1) st (VB_mono (by omega) i hv) (by omega)
      simp only [Wr, comp, Cmd.run_seq, Cmd.run_rd, eval, cost] at w ⊢
      obtain ⟨a1, a2, a3, a4⟩ := w
      refine ⟨by simp [a1, a3], fun y hy hyd => ?_, by simp [a3], by omega⟩
      simp [Function.update_apply, hyd, a2 y (by omega) (by omega)]
  | add e f ihe ihf =>
      intro d t st hv hd
      have w1 := ihe t (t + 1) st (VB_mono (by omega) e hv.1) (by omega)
      have w2 := ihf (t + 1) (t + 2) (Cmd.run (comp e t (t + 1)) st).1 (VB_mono (by omega) f hv.2) (by omega)
      obtain ⟨ef, cf⟩ := keep w1 (by omega) le_rfl hv.2
      rw [ef, cf] at w2
      simp only [Wr, comp, Cmd.run_seq, Cmd.run_copy, eval, cost] at w1 w2 ⊢
      generalize Cmd.run (comp e t (t + 1)) st = r1 at *
      generalize Cmd.run (comp f (t + 1) (t + 2)) r1.1 = r2 at *
      obtain ⟨a1, a2, a3, a4⟩ := w1
      obtain ⟨b1, b2, b3, b4⟩ := w2
      rw [(run_addTo (nd3 hd) _).1, (run_addTo (nd3 hd) _).2]
      have ht : r2.1.sc t = eval st.sc st.ar e := by rw [b2 t (by omega) (by omega), a1]
      have h1 : (r2.1.setSc d (r2.1.sc t)).sc (t + 1) = eval st.sc st.ar f := by
        simp [Function.update_apply, show t + 1 ≠ d by omega, b1]
      refine ⟨?_, fun y hy hyd => ?_, by simp [b3, a3], ?_⟩
      · simp [Function.update_apply, show d ≠ t + 2 by omega, ht, b1, show t + 1 ≠ d by omega]
      · simp [Function.update_apply, hyd, show y ≠ t + 2 by omega, b2 y (by omega) (by omega),
          a2 y (by omega) (by omega)]
      · rw [h1]; omega
  | sub e f ihe ihf =>
      intro d t st hv hd
      have w1 := ihe t (t + 1) st (VB_mono (by omega) e hv.1) (by omega)
      have w2 := ihf (t + 1) (t + 2) (Cmd.run (comp e t (t + 1)) st).1 (VB_mono (by omega) f hv.2) (by omega)
      obtain ⟨ef, cf⟩ := keep w1 (by omega) le_rfl hv.2
      rw [ef, cf] at w2
      simp only [Wr, comp, Cmd.run_seq, Cmd.run_copy, eval, cost] at w1 w2 ⊢
      generalize Cmd.run (comp e t (t + 1)) st = r1 at *
      generalize Cmd.run (comp f (t + 1) (t + 2)) r1.1 = r2 at *
      obtain ⟨a1, a2, a3, a4⟩ := w1
      obtain ⟨b1, b2, b3, b4⟩ := w2
      rw [(run_subFrom (nd3 hd) _).1, (run_subFrom (nd3 hd) _).2]
      have ht : r2.1.sc t = eval st.sc st.ar e := by rw [b2 t (by omega) (by omega), a1]
      have h1 : (r2.1.setSc d (r2.1.sc t)).sc (t + 1) = eval st.sc st.ar f := by
        simp [Function.update_apply, show t + 1 ≠ d by omega, b1]
      refine ⟨?_, fun y hy hyd => ?_, by simp [b3, a3], ?_⟩
      · simp [Function.update_apply, show d ≠ t + 2 by omega, ht, b1, show t + 1 ≠ d by omega]
      · simp [Function.update_apply, hyd, show y ≠ t + 2 by omega, b2 y (by omega) (by omega),
          a2 y (by omega) (by omega)]
      · rw [h1]; omega
  | mul e f ihe ihf =>
      intro d t st hv hd
      have w1 := ihe t (t + 1) st (VB_mono (by omega) e hv.1) (by omega)
      have w2 := ihf (t + 1) (t + 2) (Cmd.run (comp e t (t + 1)) st).1 (VB_mono (by omega) f hv.2) (by omega)
      obtain ⟨ef, cf⟩ := keep w1 (by omega) le_rfl hv.2
      rw [ef, cf] at w2
      simp only [Wr, comp, Cmd.run_seq, eval, cost] at w1 w2 ⊢
      generalize Cmd.run (comp e t (t + 1)) st = r1 at *
      generalize Cmd.run (comp f (t + 1) (t + 2)) r1.1 = r2 at *
      obtain ⟨a1, a2, a3, a4⟩ := w1
      obtain ⟨b1, b2, b3, b4⟩ := w2
      have hnd : [d, t, t + 1, t + 2, t + 3].Nodup := by
        simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil,
          not_false_eq_true, and_true]; omega
      obtain ⟨m1, m2, m3, m4⟩ := run_mulCmd hnd r2.1
      have ht : r2.1.sc t = eval st.sc st.ar e := by rw [b2 t (by omega) (by omega), a1]
      refine ⟨by rw [m1, ht, b1], fun y hy hyd => ?_, by rw [m3, b3, a3], ?_⟩
      · rw [m2 y hyd (by omega) (by omega), b2 y (by omega) (by omega), a2 y (by omega) (by omega)]
      · rw [ht, b1] at m4; omega
  | div e f ihe ihf =>
      intro d t st hv hd
      have w1 := ihe t (t + 1) st (VB_mono (by omega) e hv.1) (by omega)
      have w2 := ihf (t + 1) (t + 2) (Cmd.run (comp e t (t + 1)) st).1 (VB_mono (by omega) f hv.2) (by omega)
      obtain ⟨ef, cf⟩ := keep w1 (by omega) le_rfl hv.2
      rw [ef, cf] at w2
      simp only [Wr, comp, Cmd.run_seq, Cmd.run_ifZero, Cmd.run_setK, Cmd.run_copy, eval, cost] at w1 w2 ⊢
      generalize Cmd.run (comp e t (t + 1)) st = r1 at *
      generalize Cmd.run (comp f (t + 1) (t + 2)) r1.1 = r2 at *
      obtain ⟨a1, a2, a3, a4⟩ := w1
      obtain ⟨b1, b2, b3, b4⟩ := w2
      have hnd : [t + 2, t + 3, t, t + 1, t + 4].Nodup := by
        simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil,
          not_false_eq_true, and_true]; omega
      have ht : r2.1.sc t = eval st.sc st.ar e := by rw [b2 t (by omega) (by omega), a1]
      obtain ⟨f1, f2, f3⟩ := run_dmCmd_frame hnd r2.1
      have hf1 : (Cmd.run (dmCmd (t + 2) (t + 3) t (t + 1) (t + 4)) r2.1).1.sc (t + 1) = eval st.sc st.ar f := by
        rw [f1 _ (by omega) (by omega) (by omega), b1]
      rw [hf1]
      rw [ht] at f3
      have fr : ∀ y < t, (Cmd.run (dmCmd (t + 2) (t + 3) t (t + 1) (t + 4)) r2.1).1.sc y = st.sc y := fun y hy => by
        rw [f1 y (by omega) (by omega) (by omega), b2 y (by omega) (by omega), a2 y (by omega) (by omega)]
      split_ifs with h0
      · refine ⟨by simp [h0], fun y hy hyd => by simp [hyd, fr y hy], by simp [f2, b3, a3], by omega⟩
      · obtain ⟨q1, -, -, -, -⟩ := run_dmCmd hnd r2.1 (by rw [b1]; omega)
        refine ⟨by simp [q1, ht, b1], fun y hy hyd => by simp [hyd, fr y hy], by simp [f2, b3, a3], by omega⟩
  | mod e f ihe ihf =>
      intro d t st hv hd
      have w1 := ihe t (t + 1) st (VB_mono (by omega) e hv.1) (by omega)
      have w2 := ihf (t + 1) (t + 2) (Cmd.run (comp e t (t + 1)) st).1 (VB_mono (by omega) f hv.2) (by omega)
      obtain ⟨ef, cf⟩ := keep w1 (by omega) le_rfl hv.2
      rw [ef, cf] at w2
      simp only [Wr, comp, Cmd.run_seq, Cmd.run_ifZero, Cmd.run_setK, Cmd.run_copy, eval, cost] at w1 w2 ⊢
      generalize Cmd.run (comp e t (t + 1)) st = r1 at *
      generalize Cmd.run (comp f (t + 1) (t + 2)) r1.1 = r2 at *
      obtain ⟨a1, a2, a3, a4⟩ := w1
      obtain ⟨b1, b2, b3, b4⟩ := w2
      have hnd : [t + 2, t + 3, t, t + 1, t + 4].Nodup := by
        simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil,
          not_false_eq_true, and_true]; omega
      have ht : r2.1.sc t = eval st.sc st.ar e := by rw [b2 t (by omega) (by omega), a1]
      obtain ⟨f1, f2, f3⟩ := run_dmCmd_frame hnd r2.1
      have hf1 : (Cmd.run (dmCmd (t + 2) (t + 3) t (t + 1) (t + 4)) r2.1).1.sc (t + 1) = eval st.sc st.ar f := by
        rw [f1 _ (by omega) (by omega) (by omega), b1]
      have ht' : (Cmd.run (dmCmd (t + 2) (t + 3) t (t + 1) (t + 4)) r2.1).1.sc t = eval st.sc st.ar e := by
        rw [f1 _ (by omega) (by omega) (by omega), ht]
      rw [hf1]
      rw [ht] at f3
      have fr : ∀ y < t, (Cmd.run (dmCmd (t + 2) (t + 3) t (t + 1) (t + 4)) r2.1).1.sc y = st.sc y := fun y hy => by
        rw [f1 y (by omega) (by omega) (by omega), b2 y (by omega) (by omega), a2 y (by omega) (by omega)]
      split_ifs with h0
      · refine ⟨by simp [h0, ht'], fun y hy hyd => by simp [hyd, fr y hy], by simp [f2, b3, a3], by omega⟩
      · obtain ⟨-, q2, -, -, -⟩ := run_dmCmd hnd r2.1 (by rw [b1]; omega)
        refine ⟨by simp [q2, ht, b1], fun y hy hyd => by simp [hyd, fr y hy], by simp [f2, b3, a3], by omega⟩
  | ifLt e f u v ihe ihf ihu ihv =>
      intro d t st hv hd
      have w1 := ihe t (t + 1) st (VB_mono (by omega) e hv.1) (by omega)
      have w2 := ihf (t + 1) (t + 2) (Cmd.run (comp e t (t + 1)) st).1 (VB_mono (by omega) f hv.2.1) (by omega)
      obtain ⟨ef, cf⟩ := keep w1 (by omega) le_rfl hv.2.1
      obtain ⟨eu, cu⟩ := keep w1 (by omega) le_rfl hv.2.2.1
      obtain ⟨ev, cv⟩ := keep w1 (by omega) le_rfl hv.2.2.2
      rw [ef, cf] at w2
      have wu := ihu d (t + 2) (Cmd.run (comp f (t + 1) (t + 2)) (Cmd.run (comp e t (t + 1)) st).1).1
        (VB_mono (by omega) u hv.2.2.1) (by omega)
      have wv := ihv d (t + 2) (Cmd.run (comp f (t + 1) (t + 2)) (Cmd.run (comp e t (t + 1)) st).1).1
        (VB_mono (by omega) v hv.2.2.2) (by omega)
      obtain ⟨eu2, cu2⟩ := keep w2 (by omega) (by omega) (VB_mono (by omega) u hv.2.2.1 : VB (t + 1) u)
      obtain ⟨ev2, cv2⟩ := keep w2 (by omega) (by omega) (VB_mono (by omega) v hv.2.2.2 : VB (t + 1) v)
      rw [eu2, cu2, eu, cu] at wu
      rw [ev2, cv2, ev, cv] at wv
      simp only [Wr, comp, Cmd.run_seq, Cmd.run_ifLt, eval, cost] at w1 w2 wu wv ⊢
      generalize Cmd.run (comp e t (t + 1)) st = r1 at *
      generalize Cmd.run (comp f (t + 1) (t + 2)) r1.1 = r2 at *
      obtain ⟨a1, a2, a3, a4⟩ := w1
      obtain ⟨b1, b2, b3, b4⟩ := w2
      have ht : r2.1.sc t = eval st.sc st.ar e := by rw [b2 t (by omega) (by omega), a1]
      rw [ht, b1]
      split_ifs with hc
      · obtain ⟨u1, u2, u3, u4⟩ := wu
        refine ⟨u1, fun y hy hyd => ?_, by rw [u3, b3, a3], by omega⟩
        rw [u2 y (by omega) hyd, b2 y (by omega) (by omega), a2 y (by omega) (by omega)]
      · obtain ⟨u1, u2, u3, u4⟩ := wv
        refine ⟨u1, fun y hy hyd => ?_, by rw [u3, b3, a3], by omega⟩
        rw [u2 y (by omega) hyd, b2 y (by omega) (by omega), a2 y (by omega) (by omega)]
  | lett x e b ihe ihb =>
      intro d t st hv hd
      obtain ⟨hx, he, hb⟩ := hv
      have w1 := ihe t (t + 1) st (VB_mono (by omega) e he) (by omega)
      simp only [Wr, comp, Cmd.run_seq, Cmd.run_copy, eval, cost] at w1 ⊢
      generalize Cmd.run (comp e t (t + 1)) st = r1 at *
      obtain ⟨a1, a2, a3, a4⟩ := w1
      have hs1 : ((r1.1.setSc (t + 1) (r1.1.sc x)).setSc x ((r1.1.setSc (t + 1) (r1.1.sc x)).sc t)).sc (t + 1)
          = st.sc x := by simp [Function.update_apply, show t + 1 ≠ x by omega, a2 x (by omega) (by omega)]
      have hs3 : ((r1.1.setSc (t + 1) (r1.1.sc x)).setSc x ((r1.1.setSc (t + 1) (r1.1.sc x)).sc t)).ar = st.ar := by
        simp [a3]
      have hag : ∀ y < t, ((r1.1.setSc (t + 1) (r1.1.sc x)).setSc x
          ((r1.1.setSc (t + 1) (r1.1.sc x)).sc t)).sc y = Function.update st.sc x (eval st.sc st.ar e) y := by
        intro y hy
        by_cases hyx : y = x
        · subst hyx; simp [Function.update_apply, a1]
        · simp [Function.update_apply, hyx, show y ≠ t + 1 by omega, a2 y (by omega) (by omega)]
      generalize ((r1.1.setSc (t + 1) (r1.1.sc x)).setSc x ((r1.1.setSc (t + 1) (r1.1.sc x)).sc t)) = s2 at *
      have wb := ihb (t + 2) (t + 3) s2 (VB_mono (by omega) b hb) (by omega)
      obtain ⟨c1, c2⟩ := congr st.ar b _ _ hag hb
      rw [hs3, c1, c2] at wb
      simp only [Wr] at wb
      generalize Cmd.run (comp b (t + 2) (t + 3)) s2 = r3 at *
      obtain ⟨b1, b2, b3, b4⟩ := wb
      refine ⟨?_, fun y hy hyd => ?_, by simp [b3, hs3], by omega⟩
      · simp [Function.update_apply, b1, show t + 2 ≠ x by omega]
      · by_cases hyx : y = x
        · subst hyx
          simp [Function.update_apply, hyd, b2 (t + 1) (by omega) (by omega), hs1]
        · have := hag y hy
          simp only [Function.update_apply, hyx, if_false] at this
          simp [Function.update_apply, hyd, hyx, b2 y (by omega) (by omega), this]
  | sum x n m b ihn ihm ihb =>
      intro d t st hv hd
      obtain ⟨hx, hn, hm, hb⟩ := hv
      have w1 := ihn t (t + 1) st (VB_mono (by omega) n hn) (by omega)
      have w2 := ihm (t + 1) (t + 2) (Cmd.run (comp n t (t + 1)) st).1 (VB_mono (by omega) m hm) (by omega)
      obtain ⟨em, cm⟩ := keep w1 (by omega) le_rfl hm
      rw [em, cm] at w2
      simp only [Wr, comp, Cmd.run_seq, Cmd.run_copy, Cmd.run_setK, eval, cost] at w1 w2 ⊢
      generalize Cmd.run (comp n t (t + 1)) st = r1 at *
      generalize Cmd.run (comp m (t + 1) (t + 2)) r1.1 = r2 at *
      obtain ⟨a1, a2, a3, a4⟩ := w1
      obtain ⟨b1, b2, b3, b4⟩ := w2
      set F : ℕ → ℕ := fun i => eval (Function.update st.sc x i) st.ar b with hF
      set vm := eval st.sc st.ar m with hvm
      have q0 : ((r2.1.setSc (t + 2) 0).setSc (t + 3) ((r2.1.setSc (t + 2) 0).sc x)).sc t = eval st.sc st.ar n := by
        simp [Function.update_apply, b2 t (by omega) (by omega), a1]
      have q1 : ((r2.1.setSc (t + 2) 0).setSc (t + 3) ((r2.1.setSc (t + 2) 0).sc x)).sc (t + 1) = vm := by
        simp [Function.update_apply, b1]
      have q2 : ((r2.1.setSc (t + 2) 0).setSc (t + 3) ((r2.1.setSc (t + 2) 0).sc x)).sc (t + 2) = 0 := by
        simp [Function.update_apply]
      have q3 : ((r2.1.setSc (t + 2) 0).setSc (t + 3) ((r2.1.setSc (t + 2) 0).sc x)).sc (t + 3) = st.sc x := by
        simp [Function.update_apply, show x ≠ t + 2 by omega, b2 x (by omega) (by omega), a2 x (by omega) (by omega)]
      have q4 : ∀ y < t, ((r2.1.setSc (t + 2) 0).setSc (t + 3) ((r2.1.setSc (t + 2) 0).sc x)).sc y = st.sc y := by
        intro y hy
        simp [Function.update_apply, show y ≠ t + 2 by omega, show y ≠ t + 3 by omega,
          b2 y (by omega) (by omega), a2 y (by omega) (by omega)]
      have q5 : ((r2.1.setSc (t + 2) 0).setSc (t + 3) ((r2.1.setSc (t + 2) 0).sc x)).ar = st.ar := by simp [b3, a3]
      generalize ((r2.1.setSc (t + 2) 0).setSc (t + 3) ((r2.1.setSc (t + 2) 0).sc x)) = s3 at *
      let P : ℕ → St → Prop := fun j s' => s'.sc (t + 2) = foldSum F vm j ∧ s'.sc (t + 1) = vm ∧
        s'.sc (t + 3) = st.sc x ∧ (∀ y < t, y ≠ x → s'.sc y = st.sc y) ∧ s'.ar = st.ar
      have body : ∀ j s', P j s' →
          P (j + 1) (Cmd.run (.seq (.copy x (t + 4)) (.seq (comp b (t + 5) (t + 6))
            (.seq (addTo (t + 2) (t + 5) (t + 6)) (modIn (t + 2) (t + 1) (t + 6))))) (s'.setSc (t + 4) j)).1 ∧
          (Cmd.run (.seq (.copy x (t + 4)) (.seq (comp b (t + 5) (t + 6))
            (.seq (addTo (t + 2) (t + 5) (t + 6)) (modIn (t + 2) (t + 1) (t + 6))))) (s'.setSc (t + 4) j)).2 ≤
            cost (Function.update st.sc x j) st.ar b + 9 * F j + 7 * foldSum F vm j + 29 := by
        intro j s' ⟨p1, p2, p3, p4, p5⟩
        simp only [Cmd.run_seq, Cmd.run_copy]
        have u1 : ∀ y < t, ((s'.setSc (t + 4) j).setSc x ((s'.setSc (t + 4) j).sc (t + 4))).sc y =
            Function.update st.sc x j y := by
          intro y hy
          by_cases hyx : y = x
          · subst hyx; simp
          · simp [Function.update_apply, hyx, show y ≠ t + 4 by omega, p4 y hy hyx]
        have u2 : ((s'.setSc (t + 4) j).setSc x ((s'.setSc (t + 4) j).sc (t + 4))).sc (t + 2) = foldSum F vm j := by
          simp [Function.update_apply, show t + 2 ≠ x by omega, p1]
        have u3 : ((s'.setSc (t + 4) j).setSc x ((s'.setSc (t + 4) j).sc (t + 4))).sc (t + 1) = vm := by
          simp [Function.update_apply, show t + 1 ≠ x by omega, p2]
        have u4 : ((s'.setSc (t + 4) j).setSc x ((s'.setSc (t + 4) j).sc (t + 4))).sc (t + 3) = st.sc x := by
          simp [Function.update_apply, show t + 3 ≠ x by omega, p3]
        have u5 : ((s'.setSc (t + 4) j).setSc x ((s'.setSc (t + 4) j).sc (t + 4))).ar = st.ar := by simp [p5]
        generalize ((s'.setSc (t + 4) j).setSc x ((s'.setSc (t + 4) j).sc (t + 4))) = s1 at *
        have wb := ihb (t + 5) (t + 6) s1 (VB_mono (by omega) b hb) (by omega)
        obtain ⟨c1, c2⟩ := congr st.ar b _ _ u1 hb
        rw [u5, c1, c2] at wb
        simp only [Wr] at wb
        generalize Cmd.run (comp b (t + 5) (t + 6)) s1 = r3 at *
        obtain ⟨e1, e2, e3, e4⟩ := wb
        have nd : [t + 2, t + 5, t + 6].Nodup := by
          simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil,
            not_false_eq_true, and_true]; omega
        rw [(run_addTo nd _).1, (run_addTo nd _).2]
        obtain ⟨m1, m2, m3, m4⟩ := run_modIn (y := t + 2) (m := t + 1) (b := t + 6) (by omega) (by omega) (by omega)
          ((r3.1.setSc (t + 2) (r3.1.sc (t + 2) + r3.1.sc (t + 5))).setSc (t + 6) 0)
        have v2 : r3.1.sc (t + 2) = foldSum F vm j := by rw [e2 _ (by omega) (by omega), u2]
        have v1 : r3.1.sc (t + 1) = vm := by rw [e2 _ (by omega) (by omega), u3]
        have s42 : ((r3.1.setSc (t + 2) (r3.1.sc (t + 2) + r3.1.sc (t + 5))).setSc (t + 6) 0).sc (t + 2) =
            foldSum F vm j + F j := by simp [Function.update_apply, v2, e1, hF]
        have s41 : ((r3.1.setSc (t + 2) (r3.1.sc (t + 2) + r3.1.sc (t + 5))).setSc (t + 6) 0).sc (t + 1) = vm := by
          simp [Function.update_apply, v1]
        have s4f : ∀ y < t + 6, y ≠ t + 2 →
            ((r3.1.setSc (t + 2) (r3.1.sc (t + 2) + r3.1.sc (t + 5))).setSc (t + 6) 0).sc y = r3.1.sc y := by
          intro y hy hy2; simp [Function.update_apply, hy2, show y ≠ t + 6 by omega]
        have s4a : ((r3.1.setSc (t + 2) (r3.1.sc (t + 2) + r3.1.sc (t + 5))).setSc (t + 6) 0).ar = r3.1.ar := by simp
        generalize ((r3.1.setSc (t + 2) (r3.1.sc (t + 2) + r3.1.sc (t + 5))).setSc (t + 6) 0) = s4 at *
        rw [s42, s41] at m1
        have hm4 := m4
        rw [s42] at hm4
        have he1 : r3.1.sc (t + 5) = F j := by rw [e1]
        rw [he1]
        refine ⟨⟨by rw [m1]; rfl, ?_, ?_, fun y hy hyx => ?_, by rw [m3, s4a, e3, u5]⟩, by omega⟩
        · rw [m2 (t + 1) (by omega) (by omega), s41]
        · rw [m2 (t + 3) (by omega) (by omega), s4f _ (by omega) (by omega), e2 (t + 3) (by omega) (by omega), u4]
        · rw [m2 y (by omega) (by omega), s4f _ (by omega) (by omega), e2 y (by omega) (by omega)]
          have := u1 y hy
          simp only [Function.update_apply, hyx, if_false] at this
          exact this
      have h0 : P 0 s3 := ⟨q2, q1, q3, fun y hy _ => q4 y hy, q5⟩
      have inv := Cmd.loop_inv (b := t) (c := t + 4) P h0 (fun j s' _ hp => (body j s' hp).1)
      have hc := loop_cost_sum (b := t) (c := t + 4) P
        (fun j => cost (Function.update st.sc x j) st.ar b + 9 * F j + 7 * foldSum F vm j + 29) h0
        (fun j s' _ hp => (body j s' hp).1) (fun j s' _ hp => (body j s' hp).2)
      rw [q0] at inv hc
      generalize Cmd.run (.loop t (t + 4) _) s3 = L at *
      obtain ⟨l1, -, l3, l4, l5⟩ := inv
      refine ⟨?_, fun y hy hyd => ?_, by simp [l5], ?_⟩
      · simp [Function.update_apply, show t + 2 ≠ x by omega, l1]
      · by_cases hyx : y = x
        · subst hyx; simp [Function.update_apply, hyd, l3]
        · simp [Function.update_apply, hyd, hyx, l4 y hy hyx]
      · simp only [hF] at hc ⊢
        have e2 : ∀ j, cost (Function.update st.sc x j) st.ar b + 9 * eval (Function.update st.sc x j) st.ar b +
            7 * foldSum (fun i => eval (Function.update st.sc x i) st.ar b) vm j + 29 + 1 =
            cost (Function.update st.sc x j) st.ar b + 9 * eval (Function.update st.sc x j) st.ar b +
            7 * foldSum (fun i => eval (Function.update st.sc x i) st.ar b) vm j + 30 := fun j => rfl
        simp only [e2] at hc
        omega
  | prod x n m b ihn ihm ihb =>
      intro d t st hv hd
      obtain ⟨hx, hn, hm, hb⟩ := hv
      have w1 := ihn t (t + 1) st (VB_mono (by omega) n hn) (by omega)
      have w2 := ihm (t + 1) (t + 2) (Cmd.run (comp n t (t + 1)) st).1 (VB_mono (by omega) m hm) (by omega)
      obtain ⟨em, cm⟩ := keep w1 (by omega) le_rfl hm
      rw [em, cm] at w2
      simp only [Wr, comp, Cmd.run_seq, Cmd.run_copy, Cmd.run_setK, eval, cost] at w1 w2 ⊢
      generalize Cmd.run (comp n t (t + 1)) st = r1 at *
      generalize Cmd.run (comp m (t + 1) (t + 2)) r1.1 = r2 at *
      obtain ⟨a1, a2, a3, a4⟩ := w1
      obtain ⟨b1, b2, b3, b4⟩ := w2
      set F : ℕ → ℕ := fun i => eval (Function.update st.sc x i) st.ar b with hF
      set vm := eval st.sc st.ar m with hvm
      have q0 : ((r2.1.setSc (t + 2) 1).setSc (t + 3) ((r2.1.setSc (t + 2) 1).sc x)).sc t = eval st.sc st.ar n := by
        simp [Function.update_apply, b2 t (by omega) (by omega), a1]
      have q1 : ((r2.1.setSc (t + 2) 1).setSc (t + 3) ((r2.1.setSc (t + 2) 1).sc x)).sc (t + 1) = vm := by
        simp [Function.update_apply, b1]
      have q2 : ((r2.1.setSc (t + 2) 1).setSc (t + 3) ((r2.1.setSc (t + 2) 1).sc x)).sc (t + 2) = 1 := by
        simp [Function.update_apply]
      have q3 : ((r2.1.setSc (t + 2) 1).setSc (t + 3) ((r2.1.setSc (t + 2) 1).sc x)).sc (t + 3) = st.sc x := by
        simp [Function.update_apply, show x ≠ t + 2 by omega, b2 x (by omega) (by omega), a2 x (by omega) (by omega)]
      have q4 : ∀ y < t, ((r2.1.setSc (t + 2) 1).setSc (t + 3) ((r2.1.setSc (t + 2) 1).sc x)).sc y = st.sc y := by
        intro y hy
        simp [Function.update_apply, show y ≠ t + 2 by omega, show y ≠ t + 3 by omega,
          b2 y (by omega) (by omega), a2 y (by omega) (by omega)]
      have q5 : ((r2.1.setSc (t + 2) 1).setSc (t + 3) ((r2.1.setSc (t + 2) 1).sc x)).ar = st.ar := by simp [b3, a3]
      generalize ((r2.1.setSc (t + 2) 1).setSc (t + 3) ((r2.1.setSc (t + 2) 1).sc x)) = s3 at *
      let P : ℕ → St → Prop := fun j s' => s'.sc (t + 2) = foldProd F vm j ∧ s'.sc (t + 1) = vm ∧
        s'.sc (t + 3) = st.sc x ∧ (∀ y < t, y ≠ x → s'.sc y = st.sc y) ∧ s'.ar = st.ar
      have body : ∀ j s', P j s' →
          P (j + 1) (Cmd.run (.seq (.copy x (t + 4)) (.seq (comp b (t + 5) (t + 6))
            (.seq (mulCmd (t + 6) (t + 2) (t + 5) (t + 7) (t + 8)) (.seq (.copy (t + 2) (t + 6))
              (modIn (t + 2) (t + 1) (t + 7)))))) (s'.setSc (t + 4) j)).1 ∧
          (Cmd.run (.seq (.copy x (t + 4)) (.seq (comp b (t + 5) (t + 6))
            (.seq (mulCmd (t + 6) (t + 2) (t + 5) (t + 7) (t + 8)) (.seq (.copy (t + 2) (t + 6))
              (modIn (t + 2) (t + 1) (t + 7)))))) (s'.setSc (t + 4) j)).2 ≤
            cost (Function.update st.sc x j) st.ar b + F j * (2 * foldProd F vm j + 6) +
              7 * (foldProd F vm j * F j) + 29 := by
        intro j s' ⟨p1, p2, p3, p4, p5⟩
        simp only [Cmd.run_seq, Cmd.run_copy]
        have u1 : ∀ y < t, ((s'.setSc (t + 4) j).setSc x ((s'.setSc (t + 4) j).sc (t + 4))).sc y =
            Function.update st.sc x j y := by
          intro y hy
          by_cases hyx : y = x
          · subst hyx; simp
          · simp [Function.update_apply, hyx, show y ≠ t + 4 by omega, p4 y hy hyx]
        have u2 : ((s'.setSc (t + 4) j).setSc x ((s'.setSc (t + 4) j).sc (t + 4))).sc (t + 2) = foldProd F vm j := by
          simp [Function.update_apply, show t + 2 ≠ x by omega, p1]
        have u3 : ((s'.setSc (t + 4) j).setSc x ((s'.setSc (t + 4) j).sc (t + 4))).sc (t + 1) = vm := by
          simp [Function.update_apply, show t + 1 ≠ x by omega, p2]
        have u4 : ((s'.setSc (t + 4) j).setSc x ((s'.setSc (t + 4) j).sc (t + 4))).sc (t + 3) = st.sc x := by
          simp [Function.update_apply, show t + 3 ≠ x by omega, p3]
        have u5 : ((s'.setSc (t + 4) j).setSc x ((s'.setSc (t + 4) j).sc (t + 4))).ar = st.ar := by simp [p5]
        generalize ((s'.setSc (t + 4) j).setSc x ((s'.setSc (t + 4) j).sc (t + 4))) = s1 at *
        have wb := ihb (t + 5) (t + 6) s1 (VB_mono (by omega) b hb) (by omega)
        obtain ⟨c1, c2⟩ := congr st.ar b _ _ u1 hb
        rw [u5, c1, c2] at wb
        simp only [Wr] at wb
        generalize Cmd.run (comp b (t + 5) (t + 6)) s1 = r3 at *
        obtain ⟨e1, e2, e3, e4⟩ := wb
        have nd : [t + 6, t + 2, t + 5, t + 7, t + 8].Nodup := by
          simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil,
            not_false_eq_true, and_true]; omega
        obtain ⟨k1, k2, k3, k4⟩ := run_mulCmd nd r3.1
        have v2 : r3.1.sc (t + 2) = foldProd F vm j := by rw [e2 _ (by omega) (by omega), u2]
        have v1 : r3.1.sc (t + 1) = vm := by rw [e2 _ (by omega) (by omega), u3]
        have he1 : r3.1.sc (t + 5) = F j := by rw [e1]
        rw [v2, he1] at k1 k4
        generalize Cmd.run (mulCmd (t + 6) (t + 2) (t + 5) (t + 7) (t + 8)) r3.1 = r4 at *
        obtain ⟨m1, m2, m3, m4⟩ := run_modIn (y := t + 2) (m := t + 1) (b := t + 7) (by omega) (by omega) (by omega)
          (r4.1.setSc (t + 2) (r4.1.sc (t + 6)))
        have s42 : (r4.1.setSc (t + 2) (r4.1.sc (t + 6))).sc (t + 2) = foldProd F vm j * F j := by simp [k1]
        have s41 : (r4.1.setSc (t + 2) (r4.1.sc (t + 6))).sc (t + 1) = vm := by
          simp [Function.update_apply, k2 (t + 1) (by omega) (by omega) (by omega), v1]
        have s4f : ∀ y < t + 6, y ≠ t + 2 → (r4.1.setSc (t + 2) (r4.1.sc (t + 6))).sc y = r3.1.sc y := by
          intro y hy hy2; simp [Function.update_apply, hy2, k2 y (by omega) (by omega) (by omega)]
        have s4a : (r4.1.setSc (t + 2) (r4.1.sc (t + 6))).ar = r3.1.ar := by simp [k3]
        generalize (r4.1.setSc (t + 2) (r4.1.sc (t + 6))) = s4 at *
        rw [s42, s41] at m1
        have hm4 := m4
        rw [s42] at hm4
        refine ⟨⟨by rw [m1]; rfl, ?_, ?_, fun y hy hyx => ?_, by rw [m3, s4a, e3, u5]⟩, by omega⟩
        · rw [m2 (t + 1) (by omega) (by omega), s41]
        · rw [m2 (t + 3) (by omega) (by omega), s4f _ (by omega) (by omega), e2 (t + 3) (by omega) (by omega), u4]
        · rw [m2 y (by omega) (by omega), s4f _ (by omega) (by omega), e2 y (by omega) (by omega)]
          have := u1 y hy
          simp only [Function.update_apply, hyx, if_false] at this
          exact this
      have h0 : P 0 s3 := ⟨q2, q1, q3, fun y hy _ => q4 y hy, q5⟩
      have inv := Cmd.loop_inv (b := t) (c := t + 4) P h0 (fun j s' _ hp => (body j s' hp).1)
      have hc := loop_cost_sum (b := t) (c := t + 4) P
        (fun j => cost (Function.update st.sc x j) st.ar b + F j * (2 * foldProd F vm j + 6) +
          7 * (foldProd F vm j * F j) + 29) h0
        (fun j s' _ hp => (body j s' hp).1) (fun j s' _ hp => (body j s' hp).2)
      rw [q0] at inv hc
      generalize Cmd.run (.loop t (t + 4) _) s3 = L at *
      obtain ⟨l1, -, l3, l4, l5⟩ := inv
      refine ⟨?_, fun y hy hyd => ?_, by simp [l5], ?_⟩
      · simp [Function.update_apply, show t + 2 ≠ x by omega, l1]
      · by_cases hyx : y = x
        · subst hyx; simp [Function.update_apply, hyd, l3]
        · simp [Function.update_apply, hyd, hyx, l4 y hy hyx]
      · simp only [hF] at hc ⊢
        have e2 : ∀ j, cost (Function.update st.sc x j) st.ar b + eval (Function.update st.sc x j) st.ar b *
            (2 * foldProd (fun i => eval (Function.update st.sc x i) st.ar b) vm j + 6) +
            7 * (foldProd (fun i => eval (Function.update st.sc x i) st.ar b) vm j *
              eval (Function.update st.sc x j) st.ar b) + 29 + 1 =
            cost (Function.update st.sc x j) st.ar b + eval (Function.update st.sc x j) st.ar b *
            (2 * foldProd (fun i => eval (Function.update st.sc x i) st.ar b) vm j + 6) +
            7 * (foldProd (fun i => eval (Function.update st.sc x i) st.ar b) vm j *
              eval (Function.update st.sc x j) st.ar b) + 30 := fun j => rfl
        simp only [e2] at hc
        omega

  | blk T e ih =>
      intro d t st hv hd
      obtain ⟨a1, a2, a3, a4⟩ := ih d (max t T) st (VB_mono (le_max_right t T) e hv.1)
        (lt_of_lt_of_le hd (le_max_left t T))
      exact ⟨a1, fun y hy hyd => a2 y (lt_of_lt_of_le hy (le_max_left t T)) hyd, a3, a4⟩
  | iter x y n i b ihn ihi ihb =>
      intro d t st hv hd
      obtain ⟨hx, hy, hn, hi, hb⟩ := hv
      have w1 := ihn t (t + 1) st (VB_mono (by omega) n hn) (by omega)
      have w2 := ihi (t + 1) (t + 2) (Cmd.run (comp n t (t + 1)) st).1 (VB_mono (by omega) i hi) (by omega)
      obtain ⟨ei, ci⟩ := keep w1 (by omega) le_rfl hi
      rw [ei, ci] at w2
      simp only [Wr, comp, Cmd.run_seq, Cmd.run_copy, eval, cost] at w1 w2 ⊢
      generalize Cmd.run (comp n t (t + 1)) st = r1 at *
      generalize Cmd.run (comp i (t + 1) (t + 2)) r1.1 = r2 at *
      obtain ⟨a1, a2, a3, a4⟩ := w1
      obtain ⟨b1, b2, b3, b4⟩ := w2
      set F : ℕ → ℕ → ℕ := fun j s => eval (Function.update (Function.update st.sc x j) y s) st.ar b with hF
      set s0 := eval st.sc st.ar i with hs0
      have q0 : ((r2.1.setSc (t + 2) (r2.1.sc x)).setSc (t + 3) ((r2.1.setSc (t + 2) (r2.1.sc x)).sc y)).sc t =
          eval st.sc st.ar n := by
        simp [Function.update_apply, b2 t (by omega) (by omega), a1]
      have q1 : ((r2.1.setSc (t + 2) (r2.1.sc x)).setSc (t + 3) ((r2.1.setSc (t + 2) (r2.1.sc x)).sc y)).sc (t + 1)
          = s0 := by
        simp [Function.update_apply, b1]
      have q2 : ((r2.1.setSc (t + 2) (r2.1.sc x)).setSc (t + 3) ((r2.1.setSc (t + 2) (r2.1.sc x)).sc y)).sc (t + 2)
          = st.sc x := by
        simp [Function.update_apply, b2 x (by omega) (by omega), a2 x (by omega) (by omega)]
      have q3 : ((r2.1.setSc (t + 2) (r2.1.sc x)).setSc (t + 3) ((r2.1.setSc (t + 2) (r2.1.sc x)).sc y)).sc (t + 3)
          = st.sc y := by
        simp [Function.update_apply, show y ≠ t + 2 by omega, b2 y (by omega) (by omega), a2 y (by omega) (by omega)]
      have q4 : ∀ z < t, ((r2.1.setSc (t + 2) (r2.1.sc x)).setSc (t + 3)
          ((r2.1.setSc (t + 2) (r2.1.sc x)).sc y)).sc z = st.sc z := by
        intro z hz
        simp [Function.update_apply, show z ≠ t + 2 by omega, show z ≠ t + 3 by omega,
          b2 z (by omega) (by omega), a2 z (by omega) (by omega)]
      have q5 : ((r2.1.setSc (t + 2) (r2.1.sc x)).setSc (t + 3) ((r2.1.setSc (t + 2) (r2.1.sc x)).sc y)).ar =
          st.ar := by simp [b3, a3]
      generalize ((r2.1.setSc (t + 2) (r2.1.sc x)).setSc (t + 3) ((r2.1.setSc (t + 2) (r2.1.sc x)).sc y)) = s3 at *
      let P : ℕ → St → Prop := fun j s' => s'.sc (t + 1) = iterF F s0 j ∧ s'.sc (t + 2) = st.sc x ∧
        s'.sc (t + 3) = st.sc y ∧ (∀ z < t, z ≠ x → z ≠ y → s'.sc z = st.sc z) ∧ s'.ar = st.ar
      have body : ∀ j s', P j s' →
          P (j + 1) (Cmd.run (.seq (.copy x (t + 4)) (.seq (.copy y (t + 1)) (comp b (t + 1) (t + 5))))
            (s'.setSc (t + 4) j)).1 ∧
          (Cmd.run (.seq (.copy x (t + 4)) (.seq (.copy y (t + 1)) (comp b (t + 1) (t + 5))))
            (s'.setSc (t + 4) j)).2 ≤
            cost (Function.update (Function.update st.sc x j) y (iterF F s0 j)) st.ar b + 4 := by
        intro j s' ⟨p1, p2, p3, p4, p5⟩
        simp only [Cmd.run_seq, Cmd.run_copy]
        have u1 : ∀ z < t, (((s'.setSc (t + 4) j).setSc x ((s'.setSc (t + 4) j).sc (t + 4))).setSc y
            (((s'.setSc (t + 4) j).setSc x ((s'.setSc (t + 4) j).sc (t + 4))).sc (t + 1))).sc z =
            Function.update (Function.update st.sc x j) y (iterF F s0 j) z := by
          intro z hz
          by_cases hzy : z = y
          · subst hzy
            simp [Function.update_apply, show t + 1 ≠ x by omega, p1]
          · by_cases hzx : z = x
            · subst hzx; simp [Function.update_apply, hzy]
            · simp [Function.update_apply, hzx, hzy, show z ≠ t + 4 by omega, p4 z hz hzx hzy]
        have u2 : (((s'.setSc (t + 4) j).setSc x ((s'.setSc (t + 4) j).sc (t + 4))).setSc y
            (((s'.setSc (t + 4) j).setSc x ((s'.setSc (t + 4) j).sc (t + 4))).sc (t + 1))).sc (t + 2) = st.sc x := by
          simp [Function.update_apply, show t + 2 ≠ x by omega, show t + 2 ≠ y by omega, p2]
        have u3 : (((s'.setSc (t + 4) j).setSc x ((s'.setSc (t + 4) j).sc (t + 4))).setSc y
            (((s'.setSc (t + 4) j).setSc x ((s'.setSc (t + 4) j).sc (t + 4))).sc (t + 1))).sc (t + 3) = st.sc y := by
          simp [Function.update_apply, show t + 3 ≠ x by omega, show t + 3 ≠ y by omega, p3]
        have u5 : (((s'.setSc (t + 4) j).setSc x ((s'.setSc (t + 4) j).sc (t + 4))).setSc y
            (((s'.setSc (t + 4) j).setSc x ((s'.setSc (t + 4) j).sc (t + 4))).sc (t + 1))).ar = st.ar := by
          simp [p5]
        generalize (((s'.setSc (t + 4) j).setSc x ((s'.setSc (t + 4) j).sc (t + 4))).setSc y
            (((s'.setSc (t + 4) j).setSc x ((s'.setSc (t + 4) j).sc (t + 4))).sc (t + 1))) = s1 at *
        have wb := ihb (t + 1) (t + 5) s1 (VB_mono (by omega) b hb) (by omega)
        obtain ⟨c1, c2⟩ := congr st.ar b _ _ u1 hb
        rw [u5, c1, c2] at wb
        simp only [Wr] at wb
        generalize Cmd.run (comp b (t + 1) (t + 5)) s1 = r3 at *
        obtain ⟨e1, e2, e3, e4⟩ := wb
        refine ⟨⟨by rw [e1]; rfl, by rw [e2 _ (by omega) (by omega), u2], by rw [e2 _ (by omega) (by omega), u3],
          fun z hz hzx hzy => ?_, by rw [e3, u5]⟩, by omega⟩
        rw [e2 z (by omega) (by omega)]
        have := u1 z hz
        simp only [Function.update_apply, hzx, hzy, if_false] at this
        exact this
      have h0 : P 0 s3 := ⟨q1, q2, q3, fun z hz _ _ => q4 z hz, q5⟩
      have inv := Cmd.loop_inv (b := t) (c := t + 4) P h0 (fun j s' _ hp => (body j s' hp).1)
      have hc := loop_cost_sum (b := t) (c := t + 4) P
        (fun j => cost (Function.update (Function.update st.sc x j) y (iterF F s0 j)) st.ar b + 4) h0
        (fun j s' _ hp => (body j s' hp).1) (fun j s' _ hp => (body j s' hp).2)
      rw [q0] at inv hc
      generalize Cmd.run (.loop t (t + 4) _) s3 = L at *
      obtain ⟨l1, l2, l3, l4, l5⟩ := inv
      refine ⟨?_, fun z hz hzd => ?_, by simp [l5], ?_⟩
      · simp [Function.update_apply, show t + 1 ≠ x by omega, show t + 1 ≠ y by omega, l1]
      · by_cases hzy : z = y
        · subst hzy; simp [Function.update_apply, hzd, l3, show t + 3 ≠ x by omega]
        · by_cases hzx : z = x
          · subst hzx; simp [Function.update_apply, hzd, hzy, l2]
          · simp [Function.update_apply, hzd, hzx, hzy, l4 z hz hzx hzy]
      · simp only [hF, hs0, Nat.add_assoc, show (4 : ℕ) + 1 = 5 from rfl] at hc ⊢
        omega
end Ex

theorem foldSum_eq (f : ℕ → ℕ) (m : ℕ) : ∀ n, foldSum f m n = (∑ i ∈ range n, f i) % m
  | 0 => by simp [foldSum]
  | n + 1 => by rw [foldSum, foldSum_eq f m n, sum_range_succ, Nat.mod_add_mod]

theorem foldProd_eq (f : ℕ → ℕ) (m : ℕ) : ∀ n, 0 < n → foldProd f m n = (∏ i ∈ range n, f i) % m
  | 0, h => absurd h (lt_irrefl 0)
  | 1, _ => by simp [foldProd]
  | n + 2, _ => by
      rw [foldProd, foldProd_eq f m (n + 1) (by omega), Nat.mod_mul_mod, ← prod_range_succ]

theorem foldSum_lt (f : ℕ → ℕ) {m : ℕ} (hm : 0 < m) (n : ℕ) : foldSum f m n < m := by
  cases n with
  | zero => simpa [foldSum] using hm
  | succ n => exact Nat.mod_lt _ hm

theorem foldProd_le (f : ℕ → ℕ) {m : ℕ} (hm : 0 < m) (n : ℕ) : foldProd f m n ≤ m := by
  cases n with
  | zero => simp only [foldProd]; omega
  | succ n => exact (Nat.mod_lt _ hm).le

end Factoring.Aux
