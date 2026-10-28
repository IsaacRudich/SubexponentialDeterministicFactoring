/-
The uniform engine: one path (all its levels, then the brute force) and the sum over the paths.

* **`lvlLoop_spec`**: after the levels of the path `P`, a clique at depth `0` whose value is `chainVal … P`;
* **`pathBody_spec`**, **`pathLoop_spec`**: the sum over the paths `P < NP`, modulo `m`, in scalar `308`.

Not an audit surface.
-/
module

public import FactoringAux.UniLevelSpec
public import FactoringAux.EngineVBTop

@[expose] public section

namespace Factoring.Aux

open Factoring.Aux.Copied Factoring.Aux.Copied.PLib Ex Uni Finset

theorem hK0u : 2 ≤ K0u := by norm_num

/-- The invariant of the level loop after `j` levels. -/
def LvlInv {m : ℕ} (st : St) (ℓ L0 : ℕ) (T0 : Clique (ZMod m) (Kb K0u ℓ) L0) (P j : ℕ) (s : St) : Prop :=
  (∀ d, d + j = ℓ → ∃ (L' : ℕ) (T : Clique (ZMod m) (Kb K0u d) L'), s.sc 40 = L' ∧
      s.sc 41 = (if j = 0 then 2 else (j - 1) % 2) ∧ s.sc 42 = Kb K0u d ∧ Holds s.ar (s.sc 41) T ∧
      chainVal K0u hK0u d L' T (s.sc 305) = chainVal K0u hK0u ℓ L0 T0 P) ∧
    s.sc 10 = st.sc 10 ∧ s.sc 307 = st.sc 307 ∧
    (∀ y < 990, ¬ WL y → y ≠ 306 → s.sc y = st.sc y) ∧ (∀ x, x % 3 = 2 → s.ar 3 x = st.ar 3 x) ∧
    (∀ a, a ≠ 3 → s.ar a = st.ar a)

/-- **The levels of one path.** -/
theorem lvlLoop_spec (U : UParts) {lok tok : ℕ → ℕ → ℕ → Prop} (H : UOK U lok tok) {m ℓ L0 P : ℕ}
    (T0 : Clique (ZMod m) (Kb K0u ℓ) L0) (st : St) (hm : 1 < m) (h10 : st.sc 10 = m) (h307 : st.sc 307 = ℓ)
    (h40 : st.sc 40 = L0) (h41 : st.sc 41 = 2) (h42 : st.sc 42 = Kb K0u ℓ) (h305 : st.sc 305 = P)
    (hT : Holds st.ar 2 T0) :
    LvlInv st ℓ L0 T0 P ℓ (Cmd.run (.loop 307 306 (lvlBody U)) st).1 := by
  have h0 : LvlInv st ℓ L0 T0 P 0 st := by
    refine ⟨fun d hd => ?_, rfl, rfl, fun _ _ _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
    obtain rfl : d = ℓ := by omega
    exact ⟨L0, T0, h40, by simp [h41], h42, by rw [h41]; exact hT, by rw [h305]⟩
  have := Cmd.loop_inv (b := 307) (c := 306) (body := lvlBody U) (st := st) (LvlInv st ℓ L0 T0 P) h0 ?_
  · rwa [h307] at this
  intro j s hj ⟨hI, s10, s307, sfr, stop, sar⟩
  rw [h307] at hj
  set s' := s.setSc 306 j
  obtain ⟨d, rfl⟩ : ∃ d, ℓ = d + 1 + j := ⟨ℓ - 1 - j, by omega⟩
  obtain ⟨L', T, e40, e41, e42, eH, eV⟩ := hI (d + 1) (by omega)
  have hpar : (if j = 0 then 2 else (j - 1) % 2) < 3 := by split_ifs <;> omega
  have hpj : (if j = 0 then 2 else (j - 1) % 2) ≠ j % 2 := by split_ifs <;> omega
  have g : ∀ y, y ≠ 306 → s'.sc y = s.sc y := fun y hy => by simp [s', Function.update_of_ne hy]
  obtain ⟨r40, r41, r42, r305, rH, rA, rfr⟩ := lvlBody_spec U H s' T hm
    (by rw [g 10 (by norm_num), s10, h10]) (by rw [g 307 (by norm_num), s307, h307]; simp [s'])
    (by rw [g 40 (by norm_num), e40]) (by rw [g 41 (by norm_num), e41]) hpar
    (by simp only [s', St.setSc_sc, Function.update_self]; exact hpj) (by rw [g 42 (by norm_num), e42]) rfl
    (by rw [e41] at eH; exact eH)
  have j306 : s'.sc 306 = j := by simp [s']
  rw [j306] at r41 rH rA
  refine ⟨fun d' hd' => ?_, ?_, ?_, fun y hy hW h306 => ?_, fun x hx => ?_, fun a ha => ?_⟩
  · obtain rfl : d' = d := by omega
    refine ⟨_, _, r40, by rw [r41]; simp, r42, by rw [r41]; exact rH, ?_⟩
    rw [r305, ← eV, g 305 (by norm_num)]
    rfl
  · rw [rfr 10 (by norm_num) (by simp [WL]), g 10 (by norm_num), s10]
  · rw [rfr 307 (by norm_num) (by simp [WL]), g 307 (by norm_num), s307]
  · rw [rfr y hy hW, g y h306, sfr y hy hW h306]
  · rw [rA.2 x (by omega)]; exact stop x hx
  · rw [rA.1 a ha]; exact sar a ha


namespace Uni

/-- The scalars a path writes (below `990`). -/
def WP (y : ℕ) : Prop := WL y ∨ y = 306 ∨ y = 308 ∨ y = 312

theorem vb_rdT : VB 1000 rdT := by simp [rdT, rdTE, pow2, VB]
theorem vb_bruteU : VB 1000 bruteU :=
  deep_vb K0u 0 100 10 40 60 61 rdT 1000 (by norm_num) (by norm_num) (by norm_num) (by norm_num) vb_rdT
    (by norm_num)

end Uni

theorem ZMod.val_add_val {m : ℕ} [NeZero m] (a b : ZMod m) : (a.val + b.val) % m = (a + b).val := by
  rw [ZMod.val_add]

set_option maxRecDepth 20000 in
/-- **One path**: its bottom value added to the sum. -/
theorem pathBody_spec (U : UParts) {lok tok : ℕ → ℕ → ℕ → Prop} (H : UOK U lok tok) {m ℓ L0 P acc : ℕ}
    (T0 : Clique (ZMod m) (Kb K0u ℓ) L0) (st : St) (hm : 1 < m) (h10 : st.sc 10 = m) (h307 : st.sc 307 = ℓ)
    (h12 : st.sc 12 = L0) (h316 : st.sc 316 = Kb K0u ℓ) (h304 : st.sc 304 = P) (h308 : st.sc 308 = acc)
    (hT : Holds st.ar 2 T0) :
    (Cmd.run (pathBody U) st).1.sc 308 = (acc + (chainVal K0u hK0u ℓ L0 T0 P).val) % m ∧
      (∀ y < 990, ¬ WP y → (Cmd.run (pathBody U) st).1.sc y = st.sc y) ∧
      (∀ x, x % 3 = 2 → (Cmd.run (pathBody U) st).1.ar 3 x = st.ar 3 x) ∧
      (∀ a, a ≠ 3 → (Cmd.run (pathBody U) st).1.ar a = st.ar a) := by
  have : NeZero m := ⟨by omega⟩
  rw [pathBody]
  repeat rw [Cmd.run_seq]
  obtain ⟨v1, a1, -⟩ := vw_copy (show 305 < 1000 by norm_num) (show 304 < 1000 by norm_num) st
  set q1 := (Cmd.run (.copy 305 304) st).1
  obtain ⟨v2, a2, -⟩ := vw_copy (show 40 < 1000 by norm_num) (show 12 < 1000 by norm_num) q1
  set q2 := (Cmd.run (.copy 40 12) q1).1
  obtain ⟨v3, a3, -⟩ := vw_setK (k := 2) (show 41 < 1000 by norm_num) q2
  set q3 := (Cmd.run (.setK 41 2) q2).1
  obtain ⟨v4, a4, -⟩ := vw_copy (show 42 < 1000 by norm_num) (show 316 < 1000 by norm_num) q3
  set q4 := (Cmd.run (.copy 42 316) q3).1
  have w4 : ∀ y, y ≠ 305 → y ≠ 40 → y ≠ 41 → y ≠ 42 → vw q4 y = vw st y := fun y h1 h2 h3 h4 => by
    rw [v4, Function.update_of_ne h4, v3, Function.update_of_ne h3, v2, Function.update_of_ne h2, v1,
      Function.update_of_ne h1]
  have g4 : ∀ y < 1000, y ≠ 305 → y ≠ 40 → y ≠ 41 → y ≠ 42 → q4.sc y = st.sc y := fun y hy h1 h2 h3 h4 => by
    rw [← vw_lt hy, w4 y h1 h2 h3 h4, vw_lt hy]
  have ar4 : q4.ar = st.ar := by rw [a4, a3, a2, a1]
  have k40 : q4.sc 40 = L0 := by
    rw [← vw_lt (show 40 < 1000 by norm_num), v4, Function.update_of_ne (by norm_num), v3,
      Function.update_of_ne (by norm_num), v2, Function.update_self, v1, Function.update_of_ne (by norm_num),
      vw_lt (by norm_num), h12]
  have k41 : q4.sc 41 = 2 := by
    rw [← vw_lt (show 41 < 1000 by norm_num), v4, Function.update_of_ne (by norm_num), v3, Function.update_self]
  have k42 : q4.sc 42 = Kb K0u ℓ := by
    rw [← vw_lt (show 42 < 1000 by norm_num), v4, Function.update_self, v3, Function.update_of_ne (by norm_num), v2,
      Function.update_of_ne (by norm_num), v1, Function.update_of_ne (by norm_num), vw_lt (by norm_num), h316]
  have k305 : q4.sc 305 = P := by
    rw [← vw_lt (show 305 < 1000 by norm_num), v4, Function.update_of_ne (by norm_num), v3,
      Function.update_of_ne (by norm_num), v2, Function.update_of_ne (by norm_num), v1, Function.update_self,
      vw_lt (by norm_num), h304]
  obtain ⟨hI, i10, i307, ifr, itop, iar⟩ := lvlLoop_spec U H T0 q4 hm
    (by rw [g4 10 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), h10])
    (by rw [g4 307 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), h307])
    k40 k41 k42 k305 (by rw [ar4]; exact hT)
  set q5 := (Cmd.run (.loop 307 306 (lvlBody U)) q4).1
  obtain ⟨L', T, e40, -, e42, eH, eV⟩ := hI 0 (by omega)
  -- the brute force
  obtain ⟨v6, a6, -⟩ := vw_cset vb_bruteU (show 312 < 1000 by norm_num) q5
  set q6 := (Cmd.run (cset bruteU 312) q5).1
  have hr : TRep m 60 (vw q5) q5.ar 60 61 rdT T :=
    rdTE_rep (K := Kb K0u 0) hm eH (by rw [vw_lt (by norm_num), e42]) (by rw [vw_lt (by norm_num), e40])
      (by rw [vw_lt (by norm_num)]) (by norm_num) (by norm_num) (by norm_num)
  have hb : ZR m (eval (vw q5) q5.ar bruteU) T.value :=
    brute_rep (K := K0u) hm hr (by rw [vw_lt (by norm_num), i10, g4 10 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num), h10]) (by rw [vw_lt (by norm_num), e40]) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (Ag.refl _ _)
  have hval : T.value = chainVal K0u hK0u ℓ L0 T0 P := eV
  obtain ⟨v7, a7, -⟩ := vw_cset (e := .mod (.add (.var 308) (.var 312)) (.var 10)) (by simp [VB])
    (show 308 < 1000 by norm_num) q6
  have m6 : vw q6 10 = m := by
    rw [v6, Function.update_of_ne (by norm_num), vw_lt (by norm_num), i10,
      g4 10 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), h10]
  have c6 : vw q6 308 = acc := by
    rw [v6, Function.update_of_ne (by norm_num), vw_lt (by norm_num),
      ifr 308 (by norm_num) (by simp [WL]) (by norm_num),
      g4 308 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), h308]
  have b6 : vw q6 312 = (chainVal K0u hK0u ℓ L0 T0 P).val := by
    rw [v6, Function.update_self, hb.eq_val, hval]
  refine ⟨?_, fun y hy hW => ?_, fun x hx => ?_, fun a ha => ?_⟩
  · rw [← vw_lt (show 308 < 1000 by norm_num), v7, Function.update_self]
    simp only [Ex.eval, m6, c6, b6]
  · simp only [WP, WL] at hW
    rw [← vw_lt (show y < 1000 by omega), v7, Function.update_of_ne (by omega), v6,
      Function.update_of_ne (by omega), vw_lt (by omega), ifr y hy (by simp only [WL]; omega) (by omega),
      g4 y (by omega) (by omega) (by omega) (by omega) (by omega)]
  · rw [a7, a6, itop x hx, ar4]
  · rw [a7, a6, iar a ha, ar4]

/-- The invariant of the path loop. -/
def PathInv {m : ℕ} (st : St) (ℓ L0 : ℕ) (T0 : Clique (ZMod m) (Kb K0u ℓ) L0) (j : ℕ) (s : St) : Prop :=
  s.sc 308 = (∑ P ∈ range j, chainVal K0u hK0u ℓ L0 T0 P).val ∧
    (∀ y < 990, ¬ WP y → y ≠ 304 → s.sc y = st.sc y) ∧ (∀ x, x % 3 = 2 → s.ar 3 x = st.ar 3 x) ∧
    (∀ a, a ≠ 3 → s.ar a = st.ar a)

/-- **The sum over the paths.** -/
theorem pathLoop_spec (U : UParts) {lok tok : ℕ → ℕ → ℕ → Prop} (H : UOK U lok tok) {m ℓ L0 : ℕ}
    (T0 : Clique (ZMod m) (Kb K0u ℓ) L0) (st : St) (hm : 1 < m) (h10 : st.sc 10 = m) (h307 : st.sc 307 = ℓ)
    (h12 : st.sc 12 = L0) (h316 : st.sc 316 = Kb K0u ℓ) (h308 : st.sc 308 = 0) (hT : Holds st.ar 2 T0) :
    PathInv st ℓ L0 T0 (st.sc 303) (Cmd.run (.loop 303 304 (pathBody U)) st).1 := by
  have : NeZero m := ⟨by omega⟩
  refine Cmd.loop_inv (PathInv st ℓ L0 T0) ⟨by simp [h308], fun _ _ _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩ ?_
  intro j s _ ⟨s308, sfr, stop, sar⟩
  set s' := s.setSc 304 j
  have g : ∀ y, y ≠ 304 → s'.sc y = s.sc y := fun y hy => by simp [s', Function.update_of_ne hy]
  have f : ∀ y, y ∈ [10, 307, 12, 316] → s'.sc y = st.sc y := fun y hy => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rw [g y (by omega), sfr y (by omega) (by simp only [WP, WL]; omega) (by omega)]
  obtain ⟨r308, rfr, rtop, rar⟩ := pathBody_spec (P := j) (acc := s.sc 308) U H T0 s' hm (by rw [f 10 (by simp), h10])
    (by rw [f 307 (by simp), h307]) (by rw [f 12 (by simp), h12]) (by rw [f 316 (by simp), h316])
    (by simp [s']) (g 308 (by norm_num))
    (fun γ hγ Q hQ => by rw [show s'.ar = s.ar from rfl, stop _ (by omega)]; exact hT γ hγ Q hQ)
  refine ⟨?_, fun y hy hW h304 => ?_, fun x hx => ?_, fun a ha => ?_⟩
  · rw [r308, s308, sum_range_succ, ZMod.val_add_val]
  · rw [rfr y hy hW, g y h304, sfr y hy hW h304]
  · rw [rtop x hx]; exact stop x hx
  · rw [rar a ha]; exact sar a ha

end Factoring.Aux
