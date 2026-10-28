/-
Adapted from the authors' related work (the whole file).

Not an audit surface.
-/
/-
PLIB, part 4: scalar arithmetic and array segments, as source routines.

Every routine is a Lean function returning a `Cmd`; its arguments are the
numerals of the scalars and arrays it uses, scratch included.  Every routine
ends by zeroing its scratch scalars, so its spec is an **exact equation** for the
final state, plus a source-cost bound.  Distinctness hypotheses come as
`List.Nodup [...]`, which `decide` proves for concrete numerals.

Not an audit surface.
-/
module

public import FactoringAux.Copied.PlibLogic

@[expose] public section

namespace Factoring.Aux.Copied.PLib

open Factoring.Aux.Copied Factoring.Aux.Copied.Aux Cmd

/-! ### State lemmas -/

namespace St

@[simp] theorem setSc_sc_self (st : St) (x v : ℕ) : (st.setSc x v).sc x = v := by simp [setSc]
@[simp] theorem setSc_sc_ne (st : St) {x y : ℕ} (v : ℕ) (h : y ≠ x) : (st.setSc x v).sc y = st.sc y := by
  simp [setSc, h]

theorem setSc_same (st : St) (x : ℕ) : st.setSc x (st.sc x) = st := by
  ext <;> simp [setSc]

theorem setSc_setSc_self (st : St) (x v w : ℕ) : (st.setSc x v).setSc x w = st.setSc x w := by
  ext <;> simp [setSc, Function.update_apply]

theorem setSc_comm (st : St) {x y : ℕ} (h : x ≠ y) (v w : ℕ) :
    (st.setSc x v).setSc y w = (st.setSc y w).setSc x v := by
  ext z <;> simp only [setSc_sc, setSc_ar, Function.update_apply]
  split_ifs <;> simp_all

theorem putAr_setSc (st : St) (a : ℕ) (f : ℕ → ℕ) (x v : ℕ) :
    (st.putAr a f).setSc x v = (st.setSc x v).putAr a f := rfl

theorem putAr_putAr_self (st : St) (a : ℕ) (f g : ℕ → ℕ) : (st.putAr a f).putAr a g = st.putAr a g := by
  ext <;> simp [putAr, Function.update_apply]

@[simp] theorem putAr_ar_self (st : St) (a : ℕ) (f : ℕ → ℕ) : (st.putAr a f).ar a = f := by simp [putAr]
@[simp] theorem putAr_ar_ne (st : St) {a b : ℕ} (f : ℕ → ℕ) (h : b ≠ a) : (st.putAr a f).ar b = st.ar b := by
  simp [putAr, h]

theorem setAr_eq_putAr (st : St) (a i v : ℕ) :
    st.setAr a i v = st.putAr a (Function.update (st.ar a) i v) := rfl

end St

/-- Clear every hypothesis `¬ x = y` between two variables, so that `omega` does not case-split on them. -/
elab "clear_ne" : tactic => Lean.Elab.Tactic.withMainContext do
  let mut g ← Lean.Elab.Tactic.getMainGoal
  for d in (← Lean.getLCtx) do
    if d.isImplementationDetail then continue
    let t ← Lean.instantiateMVars d.type
    let isNe := (t.isAppOfArity ``Not 1 && (t.getArg! 0).isAppOfArity ``Eq 3 &&
        ((t.getArg! 0).getArg! 1).isFVar && ((t.getArg! 0).getArg! 2).isFVar) ||
      (t.isAppOfArity ``Ne 3 && (t.getArg! 1).isFVar && (t.getArg! 2).isFVar)
    if isNe then
      try g ← g.clear d.fvarId catch _ => pure ()
  Lean.Elab.Tactic.replaceMainGoal [g]

/-- For every hypothesis `h : ¬ x = y` between two variables, add `¬ y = x`. -/
elab "symm_ne" : tactic => Lean.Elab.Tactic.withMainContext do
  let mut g ← Lean.Elab.Tactic.getMainGoal
  for d in (← Lean.getLCtx) do
    if d.isImplementationDetail then continue
    let t ← Lean.instantiateMVars d.type
    if t.isAppOfArity ``Not 1 && (t.getArg! 0).isAppOfArity ``Eq 3 &&
        ((t.getArg! 0).getArg! 1).isFVar && ((t.getArg! 0).getArg! 2).isFVar then
      let pf ← Lean.Meta.mkAppM ``Ne.symm #[d.toExpr]
      let ty ← Lean.Meta.inferType pf
      let (_, g') ← (← g.assert d.userName ty pf).intro1P
      g := g'
  Lean.Elab.Tactic.replaceMainGoal [g]

/-- Close a scalar goal `(…).sc z = (…).sc z` by cases `z = v₁`, `z = v₂`, …, then
none of them: linear in the number of names, unlike `split_ifs`. -/
syntax "sc_split " ident " [" ident,* "]" : tactic
macro_rules
  | `(tactic| sc_split $z []) => `(tactic| simp [Function.update_apply, *])
  | `(tactic| sc_split $z [$v]) => `(tactic| ((rcases eq_or_ne $z $v with hsc | hsc) <;>
      first | (subst hsc; simp [Function.update_apply, *]; done) | simp [Function.update_apply, *]))
  | `(tactic| sc_split $z [$v, $vs,*]) => `(tactic| ((rcases eq_or_ne $z $v with hsc | hsc) <;>
      first | (subst hsc; simp [Function.update_apply, *]; done) | sc_split $z [$vs,*]))

/-- Close an equation between source states built from `setSc`/`setAr`/`putAr`:
compare pointwise, then split every `if`. -/
syntax "st_eq" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| st_eq) => `(tactic| st_eq [St.setSc_sc])
  | `(tactic| st_eq [$ls,*]) => `(tactic| (ext <;> simp only [St.setSc_sc, St.setSc_ar, St.putAr_sc,
      St.putAr_ar, St.setAr_sc, St.setAr_ar, Function.update_apply, $ls,*] <;> (try split_ifs) <;>
      (try simp only [Function.update_apply, $ls,*]) <;> (try split_ifs) <;>
      (try simp_all) <;> (try (clear_ne; omega))))

/-- Prove `[x, y, …].Nodup` from pairwise `≠` hypotheses in context. -/
macro "nodup_tac" : tactic => `(tactic| (simp only [List.nodup_cons, List.mem_cons,
  List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true]; (repeat' constructor) <;>
  first | assumption | exact List.nodup_nil | exact True.intro | exact fun e => e |
    (intro e; subst e; contradiction)))

/-- **A loop given by its states.**  If `E j` is the state after `j` turns with
the counter zeroed, the loop ends in `E b` once its counter is zeroed. -/
theorem loop_exact {b c : ℕ} {body : Cmd} {st : St} (E : ℕ → St) (h0 : st.setSc c 0 = E 0)
    (hstep : ∀ j, j < st.sc b → (Cmd.run body ((E j).setSc c j)).1.setSc c 0 = E (j + 1)) :
    (Cmd.run (.loop b c body) st).1.setSc c 0 = E (st.sc b) := by
  refine loop_inv (fun j st' => st'.setSc c 0 = E j) h0 (fun j st' hj hp => ?_)
  have : st'.setSc c j = (E j).setSc c j := by rw [← hp, St.setSc_setSc_self]
  simp only [this]; exact hstep j hj

/-- Its cost, from a per-turn bound on the states `E j`. -/
theorem loop_exact_cost {b c : ℕ} {body : Cmd} {st : St} (E : ℕ → St) (K : ℕ)
    (h0 : st.setSc c 0 = E 0)
    (hstep : ∀ j, j < st.sc b → (Cmd.run body ((E j).setSc c j)).1.setSc c 0 = E (j + 1))
    (hcost : ∀ j, j < st.sc b → (Cmd.run body ((E j).setSc c j)).2 ≤ K) :
    (Cmd.run (.loop b c body) st).2 ≤ st.sc b * (K + 1) + 1 := by
  refine loop_cost_le (fun j st' => st'.setSc c 0 = E j) K h0 (fun j st' hj hp => ?_)
    (fun j st' hj hp => ?_)
  · have : st'.setSc c j = (E j).setSc c j := by rw [← hp, St.setSc_setSc_self]
    simp only [this]; exact hstep j hj
  · have : st'.setSc c j = (E j).setSc c j := by rw [← hp, St.setSc_setSc_self]
    rw [this]; exact hcost j hj

/-- Exact cost of a loop whose turns all cost `K`, along the states `E j`. -/
theorem loop_exact_cost_eq {b c : ℕ} {body : Cmd} {st : St} (E : ℕ → St) (K : ℕ)
    (h0 : st.setSc c 0 = E 0)
    (hstep : ∀ j, j < st.sc b → (Cmd.run body ((E j).setSc c j)).1.setSc c 0 = E (j + 1))
    (hcost : ∀ j, j < st.sc b → (Cmd.run body ((E j).setSc c j)).2 = K) :
    (Cmd.run (.loop b c body) st).2 = st.sc b * (K + 1) + 1 := by
  rw [Cmd.run_loop_eq]
  have : ∀ j, j ≤ st.sc b → (Cmd.loopSt body c j st).setSc c 0 = E j ∧
      Cmd.loopCost body c j st = j * (K + 1) + 1 := by
    intro j
    induction j with
    | zero => intro _; exact ⟨h0, by simp [Cmd.loopCost]⟩
    | succ j ih =>
        intro hj
        obtain ⟨p, q⟩ := ih (by omega)
        have e : (Cmd.loopSt body c j st).setSc c j = (E j).setSc c j := by
          rw [← p, St.setSc_setSc_self]
        refine ⟨?_, ?_⟩
        · show (Cmd.run body ((Cmd.loopSt body c j st).setSc c j)).1.setSc c 0 = _
          rw [e]; exact hstep j (by omega)
        · show Cmd.loopCost body c j st + (Cmd.run body ((Cmd.loopSt body c j st).setSc c j)).2 + 1 = _
          rw [e, q, hcost j (by omega)]; ring
  exact (this _ le_rfl).2

/-- Exact cost of a loop whose body costs `K` from every state. -/
theorem loop_cost_eq' {b c : ℕ} {body : Cmd} {st : St} (K : ℕ)
    (hcost : ∀ st', (Cmd.run body st').2 = K) :
    (Cmd.run (.loop b c body) st).2 = st.sc b * (K + 1) + 1 := by
  rw [Cmd.run_loop_eq]
  have : ∀ j, Cmd.loopCost body c j st = j * (K + 1) + 1 := by
    intro j
    induction j with
    | zero => simp [Cmd.loopCost]
    | succ j ih => simp only [Cmd.loopCost]; rw [ih, hcost]; ring
  exact this _

/-! ### Scalar arithmetic -/

/-- `x := x + y`, scratch `t`. -/
def addTo (x y t : ℕ) : Cmd := seqs [.loop y t (.incr x), .setK t 0]

theorem run_addTo {x y t : ℕ} (h : [x, y, t].Nodup) (st : St) :
    (Cmd.run (addTo x y t) st).1 = (st.setSc x (st.sc x + st.sc y)).setSc t 0 ∧
    (Cmd.run (addTo x y t) st).2 = 2 * st.sc y + 5 := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  obtain ⟨⟨hxy, hxt⟩, hyt, -⟩ := h
  have inv := loop_inv (b := y) (c := t) (body := .incr x) (st := st)
    (fun j st' => st'.sc x = st.sc x + j ∧ st'.ar = st.ar ∧ ∀ z, z ≠ x → z ≠ t → st'.sc z = st.sc z)
    ⟨by simp, rfl, fun _ _ _ => rfl⟩ (fun j st' _ ⟨h1, h2, h3⟩ => by
      refine ⟨?_, ?_, fun z hz1 hz2 => ?_⟩
      · simp [run_incr, St.setSc_sc_ne _ _ hxt, h1]; omega
      · simp [run_incr, h2]
      · simp [run_incr, St.setSc_sc_ne _ _ hz1, St.setSc_sc_ne _ _ hz2, h3 z hz1 hz2])
  have hc := loop_cost_eq' (b := y) (c := t) (body := .incr x) (st := st) 1 (fun _ => rfl)
  obtain ⟨h1, h2, h3⟩ := inv
  simp only [addTo, Cmd.run_seqs_cons, Cmd.run_setK, Cmd.run_seqs_nil]
  refine ⟨?_, by omega⟩
  ext z
  · simp only [St.setSc_sc, Function.update_apply]
    split_ifs with hzt hzx
    · rfl
    · subst hzx; exact h1
    · exact h3 z hzx hzt
  · simp [h2]

/-- `x := x - y` (truncated), scratch `t`. -/
def subFrom (x y t : ℕ) : Cmd := seqs [.loop y t (.decr x), .setK t 0]

theorem run_subFrom {x y t : ℕ} (h : [x, y, t].Nodup) (st : St) :
    (Cmd.run (subFrom x y t) st).1 = (st.setSc x (st.sc x - st.sc y)).setSc t 0 ∧
    (Cmd.run (subFrom x y t) st).2 = 2 * st.sc y + 5 := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  obtain ⟨⟨hxy, hxt⟩, hyt, -⟩ := h
  have e := loop_exact (b := y) (c := t) (body := .decr x) (st := st)
    (fun j => (st.setSc t 0).setSc x (st.sc x - j)) (by st_eq) (fun j _ => by
      simp only [run_decr]; st_eq)
  have hc := loop_cost_eq' (b := y) (c := t) (body := .decr x) (st := st) 1 (fun _ => rfl)
  simp only [subFrom, Cmd.run_seqs_cons, Cmd.run_setK, Cmd.run_seqs_nil, e]
  exact ⟨by st_eq, by omega⟩

/-! ### Array segments -/

/-- The array `b` with cells `ob … ob+n-1` replaced by cells `oa …` of `a`. -/
def segCopy (fb fa : ℕ → ℕ) (ob oa n : ℕ) : ℕ → ℕ :=
  fun r => if ob ≤ r ∧ r < ob + n then fa (oa + (r - ob)) else fb r

/-- `b[ob + k] := a[oa + k]` for `k < n` (`ob oa n` scalars, `a ≠ b`).
Scratch `c p q v`. -/
def copySeg (b ob a oa n c p q v : ℕ) : Cmd :=
  seqs [.copy p oa, .copy q ob, .setK v 0,
    .loop n c (seqs [.rd v a p 0, .wr b q 0 v, .incr p, .incr q, .setK v 0]),
    .setK c 0, .setK p 0, .setK q 0]

theorem run_copySeg {b ob a oa n c p q v : ℕ} (hab : a ≠ b)
    (h : [ob, oa, n, c, p, q, v].Nodup) (st : St) :
    (Cmd.run (copySeg b ob a oa n c p q v) st).1
      = ((((st.putAr b (segCopy (st.ar b) (st.ar a) (st.sc ob) (st.sc oa) (st.sc n))).setSc c 0).setSc
          p 0).setSc q 0).setSc v 0 ∧
    (Cmd.run (copySeg b ob a oa n c p q v) st).2 = 12 * st.sc n + 15 := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  obtain ⟨⟨h1, h2, h3, h4, h5, h6⟩, ⟨h7, h8, h9, h10, h11⟩, ⟨h12, h13, h14, h15⟩, ⟨h16, h17, h18⟩,
    ⟨h19, h20⟩, h21, -⟩ := h
  set st1 := ((st.setSc p (st.sc oa)).setSc q (st.sc ob)).setSc v 0 with hst1
  have hn : st1.sc n = st.sc n := by simp [st1, Function.update_apply, *]
  let E : ℕ → St := fun j => ((((st.setSc c 0).setSc p (st.sc oa + j)).setSc q (st.sc ob + j)).setSc v
    0).putAr b (segCopy (st.ar b) (st.ar a) (st.sc ob) (st.sc oa) j)
  have hstep : ∀ j, j < st1.sc n → (Cmd.run (seqs [.rd v a p 0, .wr b q 0 v, .incr p, .incr q, .setK v 0])
      ((E j).setSc c j)).1.setSc c 0 = E (j + 1) := by
    intro j _
    simp only [Cmd.run_seqs_cons, Cmd.run_seqs_nil, run_rd, run_wr, run_incr, Cmd.run_setK, E]
    st_eq [segCopy]
  have e := loop_exact (st := st1) E (by simp only [E, st1]; st_eq [segCopy]) hstep
  have hc := loop_exact_cost_eq (st := st1) E 11 (by simp only [E, st1]; st_eq [segCopy]) hstep
    (fun j _ => by simp [Cmd.run_seqs_cons, Cmd.run_seqs_nil, run_rd, run_wr, run_incr, Cmd.run_setK])
  rw [hn] at e hc
  simp only [copySeg, Cmd.run_seqs_cons, Cmd.run_seqs_nil, Cmd.run_copy, Cmd.run_setK]
  have hst1e : ((st.setSc p (st.sc oa)).setSc q ((st.setSc p (st.sc oa)).sc ob)).setSc v 0 = st1 := by
    st_eq
  rw [hst1e]
  constructor
  · rw [e]; simp only [E]; st_eq [segCopy]
  · omega

/-- The array `b` with cells `ob … ob+n-1` set to `val`. -/
def segFill (fb : ℕ → ℕ) (ob n val : ℕ) : ℕ → ℕ := fun r => if ob ≤ r ∧ r < ob + n then val else fb r

/-- `b[ob + k] := val` for `k < n` (`ob n val` scalars).  Scratch `c q`. -/
def fillSeg (b ob n val c q : ℕ) : Cmd :=
  seqs [.copy q ob, .loop n c (seqs [.wr b q 0 val, .incr q]), .setK c 0, .setK q 0]

theorem run_fillSeg {b ob n val c q : ℕ} (h : [ob, n, val, c, q].Nodup) (st : St) :
    (Cmd.run (fillSeg b ob n val c q) st).1
      = ((st.putAr b (segFill (st.ar b) (st.sc ob) (st.sc n) (st.sc val))).setSc c 0).setSc q 0 ∧
    (Cmd.run (fillSeg b ob n val c q) st).2 = 6 * st.sc n + 9 := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  obtain ⟨⟨h1, h2, h3, h4⟩, ⟨h5, h6, h7⟩, ⟨h8, h9⟩, h10, -⟩ := h
  set st1 := st.setSc q (st.sc ob) with hst1
  have hn : st1.sc n = st.sc n := by simp [st1, *]
  let E : ℕ → St := fun j => ((st.setSc c 0).setSc q (st.sc ob + j)).putAr b
    (segFill (st.ar b) (st.sc ob) j (st.sc val))
  have hstep : ∀ j, j < st1.sc n → (Cmd.run (seqs [.wr b q 0 val, .incr q])
      ((E j).setSc c j)).1.setSc c 0 = E (j + 1) := by
    intro j _
    simp only [Cmd.run_seqs_cons, Cmd.run_seqs_nil, run_wr, run_incr, E]
    st_eq [segFill]
  have e := loop_exact (st := st1) E (by simp only [E, st1]; st_eq [segFill]) hstep
  have hc := loop_exact_cost_eq (st := st1) E 5 (by simp only [E, st1]; st_eq [segFill]) hstep
    (fun j _ => by simp [Cmd.run_seqs_cons, Cmd.run_seqs_nil, run_wr, run_incr])
  rw [hn] at e hc
  simp only [fillSeg, Cmd.run_seqs_cons, Cmd.run_seqs_nil, Cmd.run_copy, Cmd.run_setK]
  rw [← hst1]
  constructor
  · rw [e]; simp only [E]; st_eq [segFill]
  · omega

/-- Cell `0` of `f` is a length `L`; cells `1 … L` read as bits; the rest from `g`. -/
def cleanArr (f g : ℕ → ℕ) : ℕ → ℕ :=
  fun r => if r = 0 then f 0 else if r ≤ f 0 then (if f r = 0 then 0 else 1) else g r

theorem cleanArr_zero (μ : Memory) : cleanArr μ (fun _ => 0) = startingMemory (outOf μ) := by
  funext r
  simp only [cleanArr]
  by_cases h0 : r = 0
  · subst h0; simp [outOf, startingMemory_zero_eq]
  · rw [if_neg h0]
    by_cases hr : r ≤ μ 0
    · rw [if_pos hr]
      simp only [startingMemory, if_neg h0]
      have hlt : r - 1 < (outOf μ).length := by simp [outOf]; omega
      rw [List.getD_eq_getElem _ _ hlt]
      simp only [outOf, List.getElem_ofFn, show r - 1 + 1 = r by omega]
      by_cases hz : μ r = 0 <;> simp [hz]
    · rw [if_neg hr, startingMemory_gt _ (by simp [outOf]; omega)]

/-- `b := ` array `a` read as a string in the input format, cleaned: cell `0` the
length `L = a[0]`, cells `1 … L` the bits `a[r] ≠ 0` as `0`/`1`; cells past `L`
of `b` untouched.  Scratch `l c v z`. -/
def cleanStr (b a l c v z : ℕ) : Cmd :=
  seqs [.setK z 0, .rd l a z 0, .wr b z 0 l, .setK v 0,
    .loop l c (seqs [.rd v a c 1, .ifZero v .skip (.setK v 1), .wr b c 1 v, .setK v 0]),
    .setK c 0, .setK l 0]

theorem run_cleanStr {b a l c v z : ℕ} (hab : a ≠ b) (h : [l, c, v, z].Nodup) (st : St) :
    (Cmd.run (cleanStr b a l c v z) st).1
      = ((((st.putAr b (cleanArr (st.ar a) (st.ar b))).setSc z 0).setSc l 0).setSc v 0).setSc c 0 ∧
    (Cmd.run (cleanStr b a l c v z) st).2 = 11 * st.ar a 0 + 15 := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  obtain ⟨⟨h1, h2, h3⟩, ⟨h4, h5⟩, h6, -⟩ := h
  set L := st.ar a 0
  set st1 := (((st.setSc z 0).setSc l L).putAr b (Function.update (st.ar b) 0 L)).setSc v 0 with hst1
  have hl : st1.sc l = L := by simp [st1, *]
  let G : ℕ → ℕ → ℕ := fun j r => if r = 0 then L else if 1 ≤ r ∧ r ≤ j then
    (if st.ar a r = 0 then 0 else 1) else st.ar b r
  let E : ℕ → St := fun j => ((((st.setSc z 0).setSc l L).setSc v 0).setSc c 0).putAr b (G j)
  have hstep : ∀ j, j < st1.sc l → (Cmd.run (seqs [.rd v a c 1, .ifZero v .skip (.setK v 1),
      .wr b c 1 v, .setK v 0]) ((E j).setSc c j)).1.setSc c 0 = E (j + 1) := by
    intro j _
    simp only [Cmd.run_seqs_cons, Cmd.run_seqs_nil, run_rd, run_wr, Cmd.run_ifZero, Cmd.run_setK,
      Cmd.run_skip, E]
    by_cases hz : st.ar a (j + 1) = 0
    · simp only [St.putAr_ar, St.setSc_ar, St.setSc_sc, Function.update_apply, if_true,
        if_neg hab, hz]
      st_eq [G]
    · simp only [St.putAr_ar, St.setSc_ar, St.setSc_sc, Function.update_apply, if_true,
        if_neg hab, hz, if_false]
      st_eq [G]
  have e0 : st1.setSc c 0 = E 0 := by simp only [E, st1, G]; st_eq
  have e := loop_exact (st := st1) E e0 hstep
  have hc := loop_exact_cost_eq (st := st1) E 10 e0 hstep (fun j _ => by
    simp only [Cmd.run_seqs_cons, Cmd.run_seqs_nil, run_rd, run_wr, Cmd.run_ifZero, Cmd.run_setK,
      Cmd.run_skip]
    split_ifs <;> simp)
  rw [hl] at e hc
  simp only [cleanStr, Cmd.run_seqs_cons, Cmd.run_seqs_nil, Cmd.run_rd, Cmd.run_wr, Cmd.run_setK]
  have hst1e : ((((st.setSc z 0).setSc l (((st.setSc z 0).ar a ((st.setSc z 0).sc z + 0)))).setAr b
      (((st.setSc z 0).setSc l ((st.setSc z 0).ar a ((st.setSc z 0).sc z + 0))).sc z + 0)
      (((st.setSc z 0).setSc l ((st.setSc z 0).ar a ((st.setSc z 0).sc z + 0))).sc l)).setSc v 0)
      = st1 := by simp only [st1, L]; st_eq
  rw [hst1e]
  constructor
  · rw [e]; simp only [E, G, L]; st_eq [cleanArr]
  · omega

end Factoring.Aux.Copied.PLib
