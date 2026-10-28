/-
The uniform engine: what the counting command never touches (scalars `0`, `2`, `4` and arrays `0, 1, 2`),
for every start state (**`uniC_keep`**), and its output is a bit (**`uniC_le_one`**).

* `Keeps c W` (scalars below `990` outside `W` and every array but `3` kept), composition lemmas.

Not an audit surface.
-/
module

public import FactoringAux.UniSetupSpec

@[expose] public section

namespace Factoring.Aux

open Factoring.Aux.Copied Factoring.Aux.Copied.PLib Ex Uni

attribute [local irreducible] cset fillC UP lvlSet topSet

/-- `c` keeps the scalars below `990` outside `W` and every array but `3`. -/
def Keeps (c : Cmd) (W : ℕ → Prop) : Prop :=
  ∀ st : St, (∀ y < 990, ¬ W y → (Cmd.run c st).1.sc y = st.sc y) ∧ ∀ a, a ≠ 3 → (Cmd.run c st).1.ar a = st.ar a

namespace Keeps

variable {W : ℕ → Prop}

theorem ne_of {x z : ℕ} (hx : W x) (hz : ¬ W z) : z ≠ x := fun e => hz (e ▸ hx)

theorem seq {s t : Cmd} (hs : Keeps s W) (ht : Keeps t W) : Keeps (.seq s t) W := fun st => by
  simp only [Cmd.run_seq]
  exact ⟨fun y hy hW => by rw [(ht _).1 y hy hW, (hs st).1 y hy hW],
    fun a ha => by rw [(ht _).2 a ha, (hs st).2 a ha]⟩

theorem loop {b c : ℕ} {body : Cmd} (h : Keeps body W) (hc : W c) : Keeps (.loop b c body) W := fun st =>
  Cmd.loop_inv (b := b) (c := c) (body := body) (st := st)
    (fun _ s => (∀ y < 990, ¬ W y → s.sc y = st.sc y) ∧ ∀ a, a ≠ 3 → s.ar a = st.ar a)
    ⟨fun _ _ _ => rfl, fun _ _ => rfl⟩ (fun j s _ ⟨h1, h2⟩ => ⟨fun y hy hW => by
      rw [(h _).1 y hy hW]; simp only [St.setSc_sc]
      rw [Function.update_of_ne (ne_of hc hW)]; exact h1 y hy hW,
      fun a ha => by rw [(h _).2 a ha]; exact h2 a ha⟩)

theorem cset {e : Ex} {d : ℕ} (hv : VB 1000 e) (hd1 : d < 1000) (hd : W d) : Keeps (Factoring.Aux.cset e d) W :=
  fun st => by
    obtain ⟨-, a2, a3, -⟩ := cset_spec e d st hv hd1
    exact ⟨fun y hy hW => a2 y (by omega) (ne_of hd hW), fun a _ => by rw [a3]⟩

theorem copy {x y : ℕ} (hx : W x) : Keeps (.copy x y) W := fun st =>
  ⟨fun z _ hz => by simp [Cmd.run_copy, Function.update_of_ne (ne_of hx hz)], fun _ _ => rfl⟩

theorem setK {x k : ℕ} (hx : W x) : Keeps (.setK x k) W := fun st =>
  ⟨fun z _ hz => by simp [Cmd.run_setK, Function.update_of_ne (ne_of hx hz)], fun _ _ => rfl⟩

theorem skip : Keeps .skip W := fun _ => ⟨fun _ _ _ => rfl, fun _ _ => rfl⟩

theorem ifLt {x y : ℕ} {s t : Cmd} (hs : Keeps s W) (ht : Keeps t W) : Keeps (.ifLt x y s t) W := fun st => by
  rw [Cmd.run_ifLt]
  split_ifs
  · exact hs st
  · exact ht st

theorem wr3 {i o y : ℕ} : Keeps (.wr 3 i o y) W := fun st =>
  ⟨fun _ _ _ => rfl, fun a ha => by simp [Cmd.run_wr, St.setAr, Function.update_of_ne ha]⟩

end Keeps

theorem keeps_fill {W : ℕ → Prop} {f : Ex} {vn vi vK vγ vΘ vpar : ℕ} (hf : VB 990 f) (h1 : vi < 990) (h2 : vK < 990)
    (h3 : vγ < 990) (h4 : vΘ < 990) (h5 : vpar < 990) (hW : W vi) (h990 : W 990) (h991 : W 991) :
    Keeps (fillC f vn vi vK vγ vΘ vpar) W := by
  have v1 : VB 1000 (fillE f vi vK vγ vΘ) :=
    ⟨by omega, ⟨by show vi < 1000; omega, by show vK < 1000; omega⟩, by omega,
      ⟨by show vi < 1000; omega, by show vK < 1000; omega⟩, VB_mono (by omega) f hf⟩
  have v2 : VB 1000 (cellE vi vpar) := ⟨⟨trivial, by show vi < 1000; omega⟩, by show vpar < 1000; omega⟩
  unfold fillC
  exact Keeps.loop (Keeps.seq (Keeps.cset v1 (by norm_num) h990)
    (Keeps.seq (Keeps.cset v2 (by norm_num) h991) Keeps.wr3)) hW

theorem keeps_lset {W : ℕ → Prop} (hW : ∀ y, 20 ≤ y → y < 40 → W y) : Keeps UP.lset W := fun st =>
  ⟨fun y hy hy' => (UP_ok.lset st).2.1 y (by omega) (by
      by_contra h; exact hy' (hW y (by omega) (by omega))),
    fun a _ => by rw [(UP_ok.lset st).2.2]⟩

theorem keeps_tset {W : ℕ → Prop} (hW : ∀ y, y = 1 ∨ y = 3 ∨ (5 ≤ y ∧ y ≤ 9) → W y) : Keeps UP.tset W := fun st =>
  ⟨fun y hy hy' => (UP_ok.tset st).2.1 y (by omega) (fun e => hy' (hW y (Or.inl e)))
      (fun e => hy' (hW y (Or.inr (Or.inl e)))) (by
        by_contra h; exact hy' (hW y (Or.inr (Or.inr (by omega))))),
    fun a _ => by rw [(UP_ok.tset st).2.2]⟩

namespace Uni

/-- Every scalar but `0`, `2`, `4`. -/
def Wu (y : ℕ) : Prop := y ≠ 0 ∧ y ≠ 2 ∧ y ≠ 4

end Uni

theorem vb_c1E : VB 1000 c1E := by simp [c1E, ifEq, nsum, xBit, bitRd, VB]

set_option maxRecDepth 20000 in
/-- **The counting command keeps scalars `0, 2, 4` and arrays `0, 1, 2`.** -/
theorem uniC_keeps : Keeps (uniC UP) Wu := by
  unfold uniC setup modBody countM pathBody lvlBody sweepBody dmLoop dmBody
  repeat' (first | apply Keeps.seq | apply Keeps.loop | apply Keeps.ifLt | apply Keeps.skip | apply Keeps.copy | apply Keeps.setK | apply keeps_fill | apply keeps_lset | apply keeps_tset | apply Keeps.cset)
  all_goals first
    | exact UP_ok.vlnE | exact UP_ok.vsrE _ | exact UP_ok.vnxE | exact UP_ok.vl0E | exact UP_ok.vtsE
    | exact UP_ok.vttE | exact vb_dE | exact vb_kbE _ (by norm_num) | exact vb_NcE | exact vb_bruteU | exact vb_c1E
    | (simp only [Wu]; omega)
    | (intro y hy; simp only [Wu]; omega)
    | (norm_num; done)
    | (simp [VB, pow2, multV, multVm, gE, g4E, powE, tBE, sE, ellE, kbE, mE, Uni.bitE, flagE, ifEq, c1E, nsum, xBit, bitRd];
        done)

end Factoring.Aux
