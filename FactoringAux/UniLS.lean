/-
Literals replaced by variables.

The uniform engine evaluates one fixed level expression for every level, so every literal that depends on the
level's parameters (`K`, `G`) must be read from a variable set beforehand. This file gives the relation between an
expression and such a copy.

* `LSB ok nb e e'`: `e'` is `e` with some literals `k` replaced by variables `v` with `ok v k`; every binder of `e`
  satisfies `nb`; blocks (`blk`) are kept unchanged. `LS ok := LSB ok (fun x => ∀ k, ¬ ok x k)`: no binder is a
  literal variable.
* **`LSB.eval_cost`**, **`LS.eval_cost`**: if every literal variable holds its literal, the copy has the same value and
  the same cost. **`LSB.dp`**: the same depth. **`LSB.VB`**, **`LSB.FV`**: variable bounds and free variables
  transfer (literal variables below the bound). `LSB.refl_true`: every expression is related to itself when no
  condition is put on the binders (`nb = True`); used for the variable bounds of copies over an arbitrary table.
  `Ex.BGe t e` (every binder at least `t`), `LSB.refl_ge`: such an expression is related to itself.
* `NLS`: the five fields of a network expression (`NEx`); **`coarsen_LS`**, **`clique_LS`**: the coarsening and
  clique builders (data given as expressions) respect the relation.
* `ls_step`: one step of a relation proof (constructors, literal variables and binder side goals from hypotheses).

Not an audit surface.
-/
module

public import FactoringAux.EngineVBGroup

@[expose] public section

namespace Factoring.Aux

open Ex

/-- `e'` is `e` with some literals replaced by variables holding them (`ok v k`: variable `v` holds `k`); every
binder of `e` satisfies `nb`; blocks are kept unchanged. -/
inductive LSB (ok : ℕ → ℕ → Prop) (nb : ℕ → Prop) : Ex → Ex → Prop
  | lit (k : ℕ) : LSB ok nb (.lit k) (.lit k)
  | lv {k v : ℕ} : ok v k → LSB ok nb (.lit k) (.var v)
  | var (x : ℕ) : LSB ok nb (.var x) (.var x)
  | rd (a : ℕ) {i i' : Ex} : LSB ok nb i i' → LSB ok nb (.rd a i) (.rd a i')
  | add {e e' f f' : Ex} : LSB ok nb e e' → LSB ok nb f f' → LSB ok nb (.add e f) (.add e' f')
  | sub {e e' f f' : Ex} : LSB ok nb e e' → LSB ok nb f f' → LSB ok nb (.sub e f) (.sub e' f')
  | mul {e e' f f' : Ex} : LSB ok nb e e' → LSB ok nb f f' → LSB ok nb (.mul e f) (.mul e' f')
  | div {e e' f f' : Ex} : LSB ok nb e e' → LSB ok nb f f' → LSB ok nb (.div e f) (.div e' f')
  | mod {e e' f f' : Ex} : LSB ok nb e e' → LSB ok nb f f' → LSB ok nb (.mod e f) (.mod e' f')
  | ifLt {e e' f f' u u' v v' : Ex} : LSB ok nb e e' → LSB ok nb f f' → LSB ok nb u u' → LSB ok nb v v' →
      LSB ok nb (.ifLt e f u v) (.ifLt e' f' u' v')
  | lett {x : ℕ} {e e' b b' : Ex} : nb x → LSB ok nb e e' → LSB ok nb b b' → LSB ok nb (.lett x e b) (.lett x e' b')
  | sum {x : ℕ} {n n' m m' b b' : Ex} : nb x → LSB ok nb n n' → LSB ok nb m m' → LSB ok nb b b' →
      LSB ok nb (.sum x n m b) (.sum x n' m' b')
  | prod {x : ℕ} {n n' m m' b b' : Ex} : nb x → LSB ok nb n n' → LSB ok nb m m' → LSB ok nb b b' →
      LSB ok nb (.prod x n m b) (.prod x n' m' b')
  | blk (T : ℕ) (e : Ex) : LSB ok nb (.blk T e) (.blk T e)
  | iter {x y : ℕ} {n n' i i' b b' : Ex} : nb x → nb y → LSB ok nb n n' → LSB ok nb i i' → LSB ok nb b b' →
      LSB ok nb (.iter x y n i b) (.iter x y n' i' b')

/-- **The relation**: literals replaced by variables holding them, no binder being such a variable. -/
abbrev LS (ok : ℕ → ℕ → Prop) : Ex → Ex → Prop := LSB ok (fun x => ∀ k, ¬ ok x k)

/-- The relation on the five fields of a network expression. -/
def NLS (ok : ℕ → ℕ → Prop) (nb : ℕ → Prop) (E E' : NEx) : Prop :=
  LSB ok nb E.sz E'.sz ∧ LSB ok nb E.W E'.W ∧ LSB ok nb E.c E'.c ∧ LSB ok nb E.l E'.l ∧ LSB ok nb E.r E'.r

namespace LSB

variable {ok : ℕ → ℕ → Prop} {nb : ℕ → Prop}

theorem upd_ok (hnb : ∀ x, nb x → ∀ k, ¬ ok x k) {σ : ℕ → ℕ} (hσ : ∀ v k, ok v k → σ v = k) {x : ℕ} (hx : nb x)
    (j : ℕ) : ∀ v k, ok v k → Function.update σ x j v = k := by
  intro v k h
  have hv : v ≠ x := by rintro rfl; exact hnb v hx k h
  rw [Function.update_of_ne hv]; exact hσ v k h

/-- **Same value, same cost**, when every literal variable holds its literal. -/
theorem eval_cost (hnb : ∀ x, nb x → ∀ k, ¬ ok x k) {e e' : Ex} (h : LSB ok nb e e') :
    ∀ (σ : ℕ → ℕ) (A : ℕ → ℕ → ℕ), (∀ v k, ok v k → σ v = k) →
      eval σ A e' = eval σ A e ∧ cost σ A e' = cost σ A e := by
  induction h with
  | lit k => intro σ A _; exact ⟨rfl, rfl⟩
  | lv hv => intro σ A hσ; exact ⟨hσ _ _ hv, rfl⟩
  | var x => intro σ A _; exact ⟨rfl, rfl⟩
  | rd a _ ih =>
      intro σ A hσ
      obtain ⟨h1, h2⟩ := ih σ A hσ
      constructor <;> simp only [eval, cost, h1, h2]
  | add _ _ ih1 ih2 | sub _ _ ih1 ih2 | mul _ _ ih1 ih2 | div _ _ ih1 ih2 | mod _ _ ih1 ih2 =>
      intro σ A hσ
      obtain ⟨h1, h2⟩ := ih1 σ A hσ
      obtain ⟨h3, h4⟩ := ih2 σ A hσ
      constructor <;> simp only [eval, cost, h1, h2, h3, h4]
  | ifLt _ _ _ _ ih1 ih2 ih3 ih4 =>
      intro σ A hσ
      obtain ⟨h1, h2⟩ := ih1 σ A hσ
      obtain ⟨h3, h4⟩ := ih2 σ A hσ
      obtain ⟨h5, h6⟩ := ih3 σ A hσ
      obtain ⟨h7, h8⟩ := ih4 σ A hσ
      constructor <;> simp only [eval, cost, h1, h2, h3, h4, h5, h6, h7, h8]
  | @lett x e e' b b' hx _ _ ih1 ih2 =>
      intro σ A hσ
      obtain ⟨h1, h2⟩ := ih1 σ A hσ
      obtain ⟨h3, h4⟩ := ih2 _ A (upd_ok hnb hσ hx (eval σ A e))
      constructor <;> simp only [eval, cost, h1, h2, h3, h4]
  | @sum x n n' m m' b b' hx _ _ _ ih1 ih2 ih3 | @prod x n n' m m' b b' hx _ _ _ ih1 ih2 ih3 =>
      intro σ A hσ
      obtain ⟨h1, h2⟩ := ih1 σ A hσ
      obtain ⟨h3, h4⟩ := ih2 σ A hσ
      have hb : ∀ j, eval (Function.update σ x j) A b' = eval (Function.update σ x j) A b ∧
          cost (Function.update σ x j) A b' = cost (Function.update σ x j) A b :=
        fun j => ih3 _ A (upd_ok hnb hσ hx j)
      constructor <;> simp only [eval, cost, h1, h2, h3, h4, fun j => (hb j).1, fun j => (hb j).2]
  | blk T e => intro σ A _; exact ⟨rfl, rfl⟩
  | @iter x y n n' i i' b b' hx hy _ _ _ ih1 ih2 ih3 =>
      intro σ A hσ
      obtain ⟨h1, h2⟩ := ih1 σ A hσ
      obtain ⟨h3, h4⟩ := ih2 σ A hσ
      have hb : ∀ j s, eval (Function.update (Function.update σ x j) y s) A b' =
            eval (Function.update (Function.update σ x j) y s) A b ∧
          cost (Function.update (Function.update σ x j) y s) A b' =
            cost (Function.update (Function.update σ x j) y s) A b :=
        fun j s => ih3 _ A (upd_ok hnb (upd_ok hnb hσ hx j) hy s)
      constructor <;> simp only [eval, cost, h1, h2, h3, h4, fun j s => (hb j s).1, fun j s => (hb j s).2]

/-- The same nesting depth. -/
theorem dp {e e' : Ex} (h : LSB ok nb e e') : Ex.dp e' = Ex.dp e := by
  induction h <;> simp only [Ex.dp, *]

/-- **Variable bounds transfer** (every literal variable below the bound). -/
theorem VB {e e' : Ex} (h : LSB ok nb e e') {t : ℕ} (hok : ∀ v k, ok v k → v < t) : Ex.VB t e → Ex.VB t e' := by
  induction h with
  | lit k => exact id
  | lv hv => intro _; exact hok _ _ hv
  | var x => exact id
  | rd a _ ih => exact ih
  | add _ _ ih1 ih2 | sub _ _ ih1 ih2 | mul _ _ ih1 ih2 | div _ _ ih1 ih2 | mod _ _ ih1 ih2 =>
      exact fun hv => ⟨ih1 hv.1, ih2 hv.2⟩
  | ifLt _ _ _ _ ih1 ih2 ih3 ih4 => exact fun hv => ⟨ih1 hv.1, ih2 hv.2.1, ih3 hv.2.2.1, ih4 hv.2.2.2⟩
  | lett _ _ _ ih1 ih2 => exact fun hv => ⟨hv.1, ih1 hv.2.1, ih2 hv.2.2⟩
  | sum _ _ _ _ ih1 ih2 ih3 | prod _ _ _ _ ih1 ih2 ih3 =>
      exact fun hv => ⟨hv.1, ih1 hv.2.1, ih2 hv.2.2.1, ih3 hv.2.2.2⟩
  | blk T e => exact id
  | iter _ _ _ _ _ ih1 ih2 ih3 => exact fun hv => ⟨hv.1, hv.2.1, ih1 hv.2.2.1, ih2 hv.2.2.2.1, ih3 hv.2.2.2.2⟩

/-- **Free variables transfer** (every literal variable in the set). -/
theorem FV {e e' : Ex} (h : LSB ok nb e e') :
    ∀ {s : ℕ → Prop}, (∀ v k, ok v k → s v) → Ex.FV s e → Ex.FV s e' := by
  induction h with
  | lit k => exact fun _ => id
  | lv hv => intro s hs _; exact hs _ _ hv
  | var x => exact fun _ => id
  | rd a _ ih => exact fun hs => ih hs
  | add _ _ ih1 ih2 | sub _ _ ih1 ih2 | mul _ _ ih1 ih2 | div _ _ ih1 ih2 | mod _ _ ih1 ih2 =>
      exact fun hs hv => ⟨ih1 hs hv.1, ih2 hs hv.2⟩
  | ifLt _ _ _ _ ih1 ih2 ih3 ih4 =>
      exact fun hs hv => ⟨ih1 hs hv.1, ih2 hs hv.2.1, ih3 hs hv.2.2.1, ih4 hs hv.2.2.2⟩
  | lett _ _ _ ih1 ih2 => exact fun hs hv => ⟨ih1 hs hv.1, ih2 (fun v k h => Or.inl (hs v k h)) hv.2⟩
  | sum _ _ _ _ ih1 ih2 ih3 | prod _ _ _ _ ih1 ih2 ih3 =>
      exact fun hs hv => ⟨ih1 hs hv.1, ih2 hs hv.2.1, ih3 (fun v k h => Or.inl (hs v k h)) hv.2.2⟩
  | blk T e => exact fun _ => id
  | iter _ _ _ _ _ ih1 ih2 ih3 =>
      exact fun hs hv => ⟨ih1 hs hv.1, ih2 hs hv.2.1, ih3 (fun v k h => Or.inl (Or.inl (hs v k h))) hv.2.2⟩

/-- Every expression is related to itself when the binders are free. -/
theorem refl_true : ∀ e : Ex, LSB ok (fun _ => True) e e
  | .lit k => .lit k
  | .var x => .var x
  | .rd a i => .rd a (refl_true i)
  | .add e f => .add (refl_true e) (refl_true f)
  | .sub e f => .sub (refl_true e) (refl_true f)
  | .mul e f => .mul (refl_true e) (refl_true f)
  | .div e f => .div (refl_true e) (refl_true f)
  | .mod e f => .mod (refl_true e) (refl_true f)
  | .ifLt e f u v => .ifLt (refl_true e) (refl_true f) (refl_true u) (refl_true v)
  | .lett _ e b => .lett trivial (refl_true e) (refl_true b)
  | .sum _ n m b => .sum trivial (refl_true n) (refl_true m) (refl_true b)
  | .prod _ n m b => .prod trivial (refl_true n) (refl_true m) (refl_true b)
  | .blk T e => .blk T e
  | .iter _ _ n i b => .iter trivial trivial (refl_true n) (refl_true i) (refl_true b)

/-- Weakening the binder condition. -/
theorem mono_nb {nb' : ℕ → Prop} (hn : ∀ x, nb x → nb' x) {e e' : Ex} (h : LSB ok nb e e') : LSB ok nb' e e' := by
  induction h with
  | lit k => exact .lit k
  | lv hv => exact .lv hv
  | var x => exact .var x
  | rd a _ ih => exact .rd a ih
  | add _ _ ih1 ih2 => exact .add ih1 ih2
  | sub _ _ ih1 ih2 => exact .sub ih1 ih2
  | mul _ _ ih1 ih2 => exact .mul ih1 ih2
  | div _ _ ih1 ih2 => exact .div ih1 ih2
  | mod _ _ ih1 ih2 => exact .mod ih1 ih2
  | ifLt _ _ _ _ ih1 ih2 ih3 ih4 => exact .ifLt ih1 ih2 ih3 ih4
  | lett hx _ _ ih1 ih2 => exact .lett (hn _ hx) ih1 ih2
  | sum hx _ _ _ ih1 ih2 ih3 => exact .sum (hn _ hx) ih1 ih2 ih3
  | prod hx _ _ _ ih1 ih2 ih3 => exact .prod (hn _ hx) ih1 ih2 ih3
  | blk T e => exact .blk T e
  | iter hx hy _ _ _ ih1 ih2 ih3 => exact .iter (hn _ hx) (hn _ hy) ih1 ih2 ih3

/-- Every binder is at least `t`. -/
def _root_.Factoring.Aux.Ex.BGe (t : ℕ) : Ex → Prop
  | .lit _ => True
  | .var _ => True
  | .rd _ i => Ex.BGe t i
  | .add e f => Ex.BGe t e ∧ Ex.BGe t f
  | .sub e f => Ex.BGe t e ∧ Ex.BGe t f
  | .mul e f => Ex.BGe t e ∧ Ex.BGe t f
  | .div e f => Ex.BGe t e ∧ Ex.BGe t f
  | .mod e f => Ex.BGe t e ∧ Ex.BGe t f
  | .ifLt e f u v => Ex.BGe t e ∧ Ex.BGe t f ∧ Ex.BGe t u ∧ Ex.BGe t v
  | .lett x e b => t ≤ x ∧ Ex.BGe t e ∧ Ex.BGe t b
  | .sum x n m b => t ≤ x ∧ Ex.BGe t n ∧ Ex.BGe t m ∧ Ex.BGe t b
  | .prod x n m b => t ≤ x ∧ Ex.BGe t n ∧ Ex.BGe t m ∧ Ex.BGe t b
  | .blk _ _ => True
  | .iter x y n i b => t ≤ x ∧ t ≤ y ∧ Ex.BGe t n ∧ Ex.BGe t i ∧ Ex.BGe t b

/-- An expression whose binders are all at least `t` is related to itself. -/
theorem refl_ge {t : ℕ} (hnb : ∀ x, t ≤ x → nb x) : ∀ e : Ex, Ex.BGe t e → LSB ok nb e e
  | .lit k, _ => .lit k
  | .var x, _ => .var x
  | .rd a i, h => .rd a (refl_ge hnb i h)
  | .add e f, h => .add (refl_ge hnb e h.1) (refl_ge hnb f h.2)
  | .sub e f, h => .sub (refl_ge hnb e h.1) (refl_ge hnb f h.2)
  | .mul e f, h => .mul (refl_ge hnb e h.1) (refl_ge hnb f h.2)
  | .div e f, h => .div (refl_ge hnb e h.1) (refl_ge hnb f h.2)
  | .mod e f, h => .mod (refl_ge hnb e h.1) (refl_ge hnb f h.2)
  | .ifLt e f u v, h => .ifLt (refl_ge hnb e h.1) (refl_ge hnb f h.2.1) (refl_ge hnb u h.2.2.1)
      (refl_ge hnb v h.2.2.2)
  | .lett _ e b, h => .lett (hnb _ h.1) (refl_ge hnb e h.2.1) (refl_ge hnb b h.2.2)
  | .sum _ n m b, h => .sum (hnb _ h.1) (refl_ge hnb n h.2.1) (refl_ge hnb m h.2.2.1) (refl_ge hnb b h.2.2.2)
  | .prod _ n m b, h => .prod (hnb _ h.1) (refl_ge hnb n h.2.1) (refl_ge hnb m h.2.2.1) (refl_ge hnb b h.2.2.2)
  | .blk T e, _ => .blk T e
  | .iter _ _ n i b, h => .iter (hnb _ h.1) (hnb _ h.2.1) (refl_ge hnb n h.2.2.1) (refl_ge hnb i h.2.2.2.1)
      (refl_ge hnb b h.2.2.2.2)

end LSB

/-- **`LS`: same value, same cost**, when every literal variable holds its literal. -/
theorem LS.eval_cost {ok : ℕ → ℕ → Prop} {e e' : Ex} (h : LS ok e e') {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ}
    (hσ : ∀ v k, ok v k → σ v = k) : eval σ A e' = eval σ A e ∧ cost σ A e' = cost σ A e :=
  LSB.eval_cost (fun _ hx => hx) h σ A hσ

/-- `LS`: the same nesting depth. -/
theorem LS.dp {ok : ℕ → ℕ → Prop} {e e' : Ex} (h : LS ok e e') : Ex.dp e' = Ex.dp e := LSB.dp h

/-- `LS`: variable bounds transfer. -/
theorem LS.VB {ok : ℕ → ℕ → Prop} {e e' : Ex} {t : ℕ} (h : LS ok e e') (hv : Ex.VB t e)
    (hok : ∀ v k, ok v k → v < t) : Ex.VB t e' := LSB.VB h hok hv

/-! ### Proof steps -/

set_option hygiene false in
/-- One step of a relation proof: `assumption`, a constructor, a literal variable (`ok` from a hypothesis), or a
binder side goal from a hypothesis `hnb : ∀ x, _ ≤ x → nb x` (or `hnb' …`). -/
macro "ls_step" : tactic => `(tactic| first
  | assumption
  | exact LSB.lit _
  | exact LSB.var _
  | (apply LSB.lv; assumption)
  | apply LSB.rd
  | apply LSB.add
  | apply LSB.sub
  | apply LSB.mul
  | apply LSB.div
  | apply LSB.mod
  | apply LSB.ifLt
  | apply LSB.lett
  | apply LSB.sum
  | apply LSB.prod
  | apply LSB.iter
  | (apply hnb <;> omega)
  | (apply hnb' <;> omega))

/-! ### Coarsening and clique builders (data given as expressions) -/

theorem coarsen_LS {ok : ℕ → ℕ → Prop} {nb : ℕ → Prop} (u w vm : ℕ) {E E' : NEx} {gE gE' χE χE' : Ex}
    (hE : NLS ok nb E E') (hg : LSB ok nb gE gE') (hχ : LSB ok nb χE χE')
    (hnb : ∀ x, u ≤ x → nb x) (hnb' : ∀ x, w ≤ x → nb x) :
    NLS ok nb (CoarsenEx.nex ⟨u, w, vm, E, gE, χE⟩) (CoarsenEx.nex ⟨u, w, vm, E', gE', χE'⟩) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hE
  simp only [NLS]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [CoarsenEx.nex, CoarsenEx.sz, CoarsenEx.W, CoarsenEx.c, CoarsenEx.l, CoarsenEx.r, CoarsenEx.sgE,
      CoarsenEx.ppE, CoarsenEx.digE, CoarsenEx.digB, CoarsenEx.chiB, CoarsenEx.crossE, CoarsenEx.usedE,
      CoarsenEx.atPair, CoarsenEx.offE, ifEq, nprod, nsum, zmul, zprod, zsum, pow2] <;>
    repeat ls_step

theorem clique_LS {ok : ℕ → ℕ → Prop} {nb : ℕ → Prop} (u w vm : ℕ) {E E' : NEx} {kE kE' LE LE' : Ex}
    (hE : NLS ok nb E E') (hk : LSB ok nb kE kE') (hL : LSB ok nb LE LE')
    (hnb : ∀ x, u ≤ x → nb x) (hnb' : ∀ x, w ≤ x → nb x) :
    LSB ok nb (CliqueEx.tab ⟨u, w, vm, E, kE, LE⟩) (CliqueEx.tab ⟨u, w, vm, E', kE', LE'⟩) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hE
  simp only [CliqueEx.tab, CliqueEx.padL, CliqueEx.padR, CliqueEx.unitE, CliqueEx.blkQ, ifEq, zmul, zprod, zsum,
    pow2]
  repeat ls_step

end Factoring.Aux
