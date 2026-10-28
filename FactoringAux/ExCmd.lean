/-
Source routines for the expression compiler (`Ex.lean`), on the copied PLIB `Cmd`.

* `loop_cost_sum`: a loop whose turn `j` costs at most `K j` costs at most `∑_{j<b} (K j + 1) + 1`.
* `divmod_succ`: one more unit, in quotient and remainder.
* `dmCmd q r a m c`: `q := a / m`, `r := a % m` (for `m > 0`), by counting `a` units (`run_dmCmd`).

Not an audit surface.
-/
module

public import FactoringAux.Copied.PlibArr

@[expose] public section

namespace Factoring.Aux

open Factoring.Aux.Copied Factoring.Aux.Copied.PLib Finset

/-- A loop whose turn `j` costs at most `K j`. -/
theorem loop_cost_sum {b c : ℕ} {body : Cmd} {st : St} (P : ℕ → St → Prop) (K : ℕ → ℕ) (h0 : P 0 st)
    (hstep : ∀ j st', j < st.sc b → P j st' → P (j + 1) (Cmd.run body (st'.setSc c j)).1)
    (hcost : ∀ j st', j < st.sc b → P j st' → (Cmd.run body (st'.setSc c j)).2 ≤ K j) :
    (Cmd.run (.loop b c body) st).2 ≤ ∑ j ∈ range (st.sc b), (K j + 1) + 1 := by
  rw [Cmd.run_loop_eq]
  have : ∀ j, j ≤ st.sc b → P j (Cmd.loopSt body c j st) ∧
      Cmd.loopCost body c j st ≤ ∑ i ∈ range j, (K i + 1) + 1 := by
    intro j
    induction j with
    | zero => intro _; exact ⟨h0, by simp [Cmd.loopCost]⟩
    | succ j ih =>
        intro hj
        obtain ⟨p, q⟩ := ih (by omega)
        refine ⟨hstep j _ (by omega) p, ?_⟩
        show Cmd.loopCost body c j st + (Cmd.run body ((Cmd.loopSt body c j st).setSc c j)).2 + 1 ≤ _
        have := hcost j _ (by omega) p
        rw [sum_range_succ]; omega
  exact (this _ le_rfl).2

theorem divmod_succ (j M : ℕ) (hM : 0 < M) :
    (j % M + 1 < M → (j + 1) % M = j % M + 1 ∧ (j + 1) / M = j / M) ∧
    (¬ j % M + 1 < M → (j + 1) % M = 0 ∧ (j + 1) / M = j / M + 1) := by
  have h := Nat.div_add_mod j M
  have hr := Nat.mod_lt j hM
  set q := j / M
  set r := j % M
  refine ⟨fun h1 => ?_, fun h1 => ?_⟩
  · have e : j + 1 = (r + 1) + M * q := by omega
    rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h1, Nat.add_mul_div_left _ _ hM, Nat.div_eq_of_lt h1]
    simp
  · have e : j + 1 = M * (q + 1) := by
      have : r + 1 = M := by omega
      rw [mul_add, mul_one]; omega
    rw [e, Nat.mul_mod_right, Nat.mul_div_cancel_left _ hM]
    simp

/-- `q := a / m`, `r := a % m`, counting the `a` units with counter `c`. -/
def dmCmd (q r a m c : ℕ) : Cmd :=
  .seq (.setK q 0) (.seq (.setK r 0)
    (.loop a c (.seq (.incr r) (.ifLt r m .skip (.seq (.setK r 0) (.incr q))))))

theorem run_dmCmd {q r a m c : ℕ} (h : [q, r, a, m, c].Nodup) (st : St) (hm : 0 < st.sc m) :
    (Cmd.run (dmCmd q r a m c) st).1.sc q = st.sc a / st.sc m ∧
    (Cmd.run (dmCmd q r a m c) st).1.sc r = st.sc a % st.sc m ∧
    (∀ y, y ≠ q → y ≠ r → y ≠ c → (Cmd.run (dmCmd q r a m c) st).1.sc y = st.sc y) ∧
    (Cmd.run (dmCmd q r a m c) st).1.ar = st.ar ∧
    (Cmd.run (dmCmd q r a m c) st).2 ≤ 7 * st.sc a + 8 := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  obtain ⟨⟨hqr, hqa, hqm, hqc⟩, ⟨hra, hrm, hrc⟩, ⟨-, -⟩, hmc, -⟩ := h
  have hne := And.intro (Ne.symm hrc) (And.intro (Ne.symm hqc) (Ne.symm hmc))
  set st0 := (st.setSc q 0).setSc r 0 with hst0
  have hm0 : st0.sc m = st.sc m := by simp [st0, Function.update_apply, Ne.symm hqm, Ne.symm hrm]
  have ha0 : st0.sc a = st.sc a := by simp [st0, Function.update_apply, Ne.symm hqa, Ne.symm hra]
  let P : ℕ → St → Prop := fun j st' => st'.sc q = j / st.sc m ∧ st'.sc r = j % st.sc m ∧
    (∀ y, y ≠ q → y ≠ r → y ≠ c → st'.sc y = st.sc y) ∧ st'.ar = st.ar
  have h0 : P 0 st0 := by
    refine ⟨by simp [st0, Function.update_apply, hqr], by simp [st0], fun y h1 h2 _ => ?_, rfl⟩
    simp [st0, Function.update_apply, h1, h2]
  have hstep : ∀ j st', j < st0.sc a → P j st' →
      P (j + 1) (Cmd.run (.seq (.incr r) (.ifLt r m .skip (.seq (.setK r 0) (.incr q)))) (st'.setSc c j)).1 := by
    intro j st' _ ⟨p1, p2, p3, p4⟩
    have hmst : st'.sc m = st.sc m := p3 m (Ne.symm hqm) (Ne.symm hrm) hmc
    obtain ⟨d1, d2⟩ := divmod_succ j (st.sc m) hm
    simp only [Cmd.run_seq, Cmd.run_incr, Cmd.run_ifLt, Cmd.run_skip, Cmd.run_setK]
    have er : ((st'.setSc c j).setSc r ((st'.setSc c j).sc r + 1)).sc r = j % st.sc m + 1 := by
      simp [Function.update_apply, hqr, hqa, hqm, hqc, hra, hrm, hrc, hmc, Ne.symm hqr, Ne.symm hrc, Ne.symm hqc, Ne.symm hmc, Ne.symm hrm, Ne.symm hqm, Ne.symm hrc, p2]
    have em : ((st'.setSc c j).setSc r ((st'.setSc c j).sc r + 1)).sc m = st.sc m := by
      simp [Function.update_apply, hqr, hqa, hqm, hqc, hra, hrm, hrc, hmc, Ne.symm hqr, Ne.symm hrc, Ne.symm hqc, Ne.symm hmc, Ne.symm hrm, Ne.symm hqm, Ne.symm hrm, hmc, hmst]
    rw [er, em]
    split_ifs with hc
    · obtain ⟨e1, e2⟩ := d1 hc
      refine ⟨?_, ?_, fun y h1 h2 h3 => ?_, ?_⟩
      · simp [Function.update_apply, hqr, hqa, hqm, hqc, hra, hrm, hrc, hmc, Ne.symm hqr, Ne.symm hrc, Ne.symm hqc, Ne.symm hmc, Ne.symm hrm, Ne.symm hqm, hqr, hqc, p1, e2]
      · simp [Function.update_apply, hqr, hqa, hqm, hqc, hra, hrm, hrc, hmc, Ne.symm hqr, Ne.symm hrc, Ne.symm hqc, Ne.symm hmc, Ne.symm hrm, Ne.symm hqm, Ne.symm hrc, p2, e1]
      · simp [Function.update_apply, hqr, hqa, hqm, hqc, hra, hrm, hrc, hmc, Ne.symm hqr, Ne.symm hrc, Ne.symm hqc, Ne.symm hmc, Ne.symm hrm, Ne.symm hqm, h2, h3, p3 y h1 h2 h3]
      · simp [p4]
    · obtain ⟨e1, e2⟩ := d2 hc
      refine ⟨?_, ?_, fun y h1 h2 h3 => ?_, ?_⟩
      · simp [Function.update_apply, hqr, hqa, hqm, hqc, hra, hrm, hrc, hmc, Ne.symm hqr, Ne.symm hrc, Ne.symm hqc, Ne.symm hmc, Ne.symm hrm, Ne.symm hqm, hqr, hqc, p1, e2]
      · simp [Function.update_apply, hqr, hqa, hqm, hqc, hra, hrm, hrc, hmc, Ne.symm hqr, Ne.symm hrc, Ne.symm hqc, Ne.symm hmc, Ne.symm hrm, Ne.symm hqm, Ne.symm hqr, e1]
      · simp [Function.update_apply, hqr, hqa, hqm, hqc, hra, hrm, hrc, hmc, Ne.symm hqr, Ne.symm hrc, Ne.symm hqc, Ne.symm hmc, Ne.symm hrm, Ne.symm hqm, h1, h2, h3, p3 y h1 h2 h3]
      · simp [p4]
  have inv := Cmd.loop_inv (b := a) (c := c) P h0 hstep
  have hc := Cmd.loop_cost_le (b := a) (c := c) P 6 h0 hstep (fun j st' _ _ => by
    simp only [Cmd.run_seq, Cmd.run_incr, Cmd.run_ifLt, Cmd.run_skip, Cmd.run_setK]
    split_ifs <;> simp)
  simp only [dmCmd, Cmd.run_seq, Cmd.run_setK]
  rw [← hst0]
  rw [ha0] at inv hc
  obtain ⟨p1, p2, p3, p4⟩ := inv
  refine ⟨p1, p2, p3, p4, ?_⟩
  nlinarith

/-- `dmCmd` writes only `q`, `r`, `c`, and its cost, for any `m`. -/
theorem run_dmCmd_frame {q r a m c : ℕ} (h : [q, r, a, m, c].Nodup) (st : St) :
    (∀ y, y ≠ q → y ≠ r → y ≠ c → (Cmd.run (dmCmd q r a m c) st).1.sc y = st.sc y) ∧
    (Cmd.run (dmCmd q r a m c) st).1.ar = st.ar ∧
    (Cmd.run (dmCmd q r a m c) st).2 ≤ 7 * st.sc a + 8 := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  obtain ⟨⟨hqr, hqa, hqm, hqc⟩, ⟨hra, hrm, hrc⟩, ⟨-, -⟩, hmc, -⟩ := h
  set st0 := (st.setSc q 0).setSc r 0 with hst0
  have ha0 : st0.sc a = st.sc a := by simp [st0, Function.update_apply, Ne.symm hqa, Ne.symm hra]
  let P : ℕ → St → Prop := fun _ st' => (∀ y, y ≠ q → y ≠ r → y ≠ c → st'.sc y = st.sc y) ∧ st'.ar = st.ar
  have h0 : P 0 st0 := ⟨fun y h1 h2 _ => by simp [st0, Function.update_apply, h1, h2], rfl⟩
  have hstep : ∀ j st', j < st0.sc a → P j st' →
      P (j + 1) (Cmd.run (.seq (.incr r) (.ifLt r m .skip (.seq (.setK r 0) (.incr q)))) (st'.setSc c j)).1 := by
    intro j st' _ ⟨p3, p4⟩
    simp only [Cmd.run_seq, Cmd.run_incr, Cmd.run_ifLt, Cmd.run_skip, Cmd.run_setK]
    split_ifs
    · exact ⟨fun y h1 h2 h3 => by simp [Function.update_apply, h2, h3, p3 y h1 h2 h3], by simp [p4]⟩
    · exact ⟨fun y h1 h2 h3 => by simp [Function.update_apply, h1, h2, h3, p3 y h1 h2 h3], by simp [p4]⟩
  have inv := Cmd.loop_inv (b := a) (c := c) P h0 hstep
  have hc := Cmd.loop_cost_le (b := a) (c := c) P 6 h0 hstep (fun j st' _ _ => by
    simp only [Cmd.run_seq, Cmd.run_incr, Cmd.run_ifLt, Cmd.run_skip, Cmd.run_setK]
    split_ifs <;> simp)
  simp only [dmCmd, Cmd.run_seq, Cmd.run_setK]
  rw [← hst0]
  rw [ha0] at inv hc
  exact ⟨inv.1, inv.2, by nlinarith⟩

/-- `d := y * z`, counter `c`, scratch `tmp`. -/
def mulCmd (d y z c tmp : ℕ) : Cmd := .seq (.setK d 0) (.loop z c (addTo d y tmp))

theorem run_mulCmd {d y z c tmp : ℕ} (h : [d, y, z, c, tmp].Nodup) (st : St) :
    (Cmd.run (mulCmd d y z c tmp) st).1.sc d = st.sc y * st.sc z ∧
    (∀ w, w ≠ d → w ≠ c → w ≠ tmp → (Cmd.run (mulCmd d y z c tmp) st).1.sc w = st.sc w) ∧
    (Cmd.run (mulCmd d y z c tmp) st).1.ar = st.ar ∧
    (Cmd.run (mulCmd d y z c tmp) st).2 ≤ st.sc z * (2 * st.sc y + 6) + 3 := by
  have h' := h
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at h'
  obtain ⟨⟨hdy, hdz, hdc, hdt⟩, ⟨hyz, hyc, hyt⟩, ⟨hzc, hzt⟩, hct, -⟩ := h'
  set st0 := st.setSc d 0 with hst0
  have hy0 : st0.sc y = st.sc y := by simp [st0, Function.update_apply, Ne.symm hdy]
  have hz0 : st0.sc z = st.sc z := by simp [st0, Function.update_apply, Ne.symm hdz]
  have hnd : [d, y, tmp].Nodup := by simp [hdy, hdt, hyt]
  let P : ℕ → St → Prop := fun j st' => st'.sc d = st.sc y * j ∧
    (∀ w, w ≠ d → w ≠ c → w ≠ tmp → st'.sc w = st.sc w) ∧ st'.ar = st.ar
  have h0 : P 0 st0 := ⟨by simp [st0], fun w h1 _ _ => by simp [st0, Function.update_apply, h1], rfl⟩
  have hstep : ∀ j st', j < st0.sc z → P j st' → P (j + 1) (Cmd.run (addTo d y tmp) (st'.setSc c j)).1 := by
    intro j st' _ ⟨p1, p2, p3⟩
    rw [(run_addTo hnd _).1]
    have ey : (st'.setSc c j).sc y = st.sc y := by
      simp [Function.update_apply, hyc, p2 y (Ne.symm hdy) hyc hyt]
    refine ⟨?_, fun w h1 h2 h3 => ?_, by simp [p3]⟩
    · simp [Function.update_apply, hdt, hdc, p1, ey]; ring
    · simp [Function.update_apply, h1, h2, h3, p2 w h1 h2 h3]
  have inv := Cmd.loop_inv (b := z) (c := c) P h0 hstep
  have hc := Cmd.loop_cost_le (b := z) (c := c) P (2 * st.sc y + 5) h0 hstep (fun j st' _ hp => by
    rw [(run_addTo hnd _).2]
    have : (st'.setSc c j).sc y = st.sc y := by
      simp [Function.update_apply, hyc, hp.2.1 y (Ne.symm hdy) hyc hyt]
    omega)
  simp only [mulCmd, Cmd.run_seq, Cmd.run_setK]
  rw [← hst0]
  rw [hz0] at inv hc
  refine ⟨by rw [inv.1, mul_comm], inv.2.1, inv.2.2, by nlinarith⟩

/-- `y := y % m` (unchanged when `m = 0`), scratch from `b`. -/
def modIn (y m b : ℕ) : Cmd := .seq (dmCmd b (b + 1) y m (b + 2)) (.ifZero m .skip (.copy y (b + 1)))

theorem run_modIn {y m b : ℕ} (hy : y < b) (hm : m < b) (hym : y ≠ m) (st : St) :
    (Cmd.run (modIn y m b) st).1.sc y = st.sc y % st.sc m ∧
    (∀ w < b, w ≠ y → (Cmd.run (modIn y m b) st).1.sc w = st.sc w) ∧
    (Cmd.run (modIn y m b) st).1.ar = st.ar ∧
    (Cmd.run (modIn y m b) st).2 ≤ 7 * st.sc y + 12 := by
  have hnd : [b, b + 1, y, m, b + 2].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true]
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨hym, ?_⟩, ?_, not_false⟩ <;> omega
  obtain ⟨f1, f2, f3⟩ := run_dmCmd_frame hnd st
  have ey : (Cmd.run (dmCmd b (b + 1) y m (b + 2)) st).1.sc y = st.sc y := f1 y (by omega) (by omega) (by omega)
  have em : (Cmd.run (dmCmd b (b + 1) y m (b + 2)) st).1.sc m = st.sc m := f1 m (by omega) (by omega) (by omega)
  simp only [modIn, Cmd.run_seq, Cmd.run_ifZero, Cmd.run_skip, Cmd.run_copy]
  rw [em]
  split_ifs with hm0
  · refine ⟨by rw [ey, hm0, Nat.mod_zero], fun w hw _ => f1 w (by omega) (by omega) (by omega), f2, by omega⟩
  · obtain ⟨-, r2, -, -, -⟩ := run_dmCmd hnd st (by omega)
    refine ⟨by simp [r2], fun w hw hwy => ?_, by simpa using f2, by simp; omega⟩
    simp [Function.update_apply, hwy, f1 w (by omega) (by omega) (by omega)]

end Factoring.Aux
