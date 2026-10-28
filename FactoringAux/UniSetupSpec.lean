/-
The uniform engine: the parameters and the sweep (**`setup_spec`**: `s`, `ℓ = ellOf n`, `K_top`, the top
literal variables, `L_top`, and `NPof`, `deepMult`, `mlogN` of the chain).

Not an audit surface.
-/
module

public import FactoringAux.UniTopSpec

@[expose] public section

namespace Factoring.Aux

open Factoring.Aux.Copied Factoring.Aux.Copied.PLib Ex Uni Finset

attribute [local irreducible] cset

namespace Uni

/-- The scalars a sweep level writes (below `1000`). -/
def WS (y : ℕ) : Prop := (20 ≤ y ∧ y < 40) ∨ y = 40 ∨ y = 43 ∨ y = 45 ∨ y = 47 ∨ y = 101 ∨ y = 303 ∨ y = 309 ∨ y = 310

end Uni

/-- **One level of the sweep.** -/
theorem sweepBody_spec (st : St) {d L : ℕ} (h307 : st.sc 307 = d + 1 + st.sc 306) (h40 : st.sc 40 = L) :
    (Cmd.run (sweepBody UP) st).1.sc 40 = Lnext (Kb K0u d) (Gs K0u d) L ∧
      (Cmd.run (sweepBody UP) st).1.sc 303 = st.sc 303 * Nc K0u d L ∧
      (Cmd.run (sweepBody UP) st).1.sc 310 = st.sc 310 + 2 * Gs K0u d ^ 4 * tB L ∧
      (∀ y < 1000, ¬ WS y → (Cmd.run (sweepBody UP) st).1.sc y = st.sc y) ∧
      (Cmd.run (sweepBody UP) st).1.ar = st.ar := by
  rw [sweepBody]
  repeat rw [Cmd.run_seq]
  set K := Kb K0u d
  obtain ⟨v1, a1, -⟩ := vw_cset vb_dE (show 45 < 1000 by norm_num) st
  set s1 := (Cmd.run (cset dE 45) st).1
  rw [show eval (vw st) st.ar dE = d by
    simp only [dE, Ex.eval, vw_lt (show 307 < 1000 by norm_num), vw_lt (show 306 < 1000 by norm_num), h307]
    omega] at v1
  obtain ⟨v2, a2, -⟩ := vw_cset (vb_kbE 45 (by norm_num)) (show 43 < 1000 by norm_num) s1
  set s2 := (Cmd.run (cset (kbE 45) 43) s1).1
  rw [eval_kbE, v1, Function.update_self] at v2
  have L2 : vw s2 40 = L := by
    rw [v2, Function.update_of_ne (by norm_num), Function.update_of_ne (by norm_num), vw_lt (by norm_num), h40]
  have K2 : vw s2 43 = K := by rw [v2, Function.update_self]
  obtain ⟨v3, a3, -⟩ := vw_cset vb_NcE (show 47 < 1000 by norm_num) s2
  set s3 := (Cmd.run (cset (NcE 43 40) 47) s2).1
  rw [eval_NcE (d := d) (L := L) (by norm_num) (by norm_num) (by norm_num) K2 L2] at v3
  obtain ⟨v4, a4, -⟩ := vw_cset (e := .mul (.var 303) (.var 47)) (by simp [VB]) (show 303 < 1000 by norm_num) s3
  set s4 := (Cmd.run (cset (.mul (.var 303) (.var 47)) 303) s3).1
  have P3 : vw s3 303 = st.sc 303 := by
    rw [v3, Function.update_of_ne (by norm_num), v2, Function.update_of_ne (by norm_num),
      Function.update_of_ne (by norm_num), vw_lt (by norm_num)]
  rw [show eval (vw s3) s3.ar (.mul (.var 303) (.var 47)) = st.sc 303 * Nc K0u d L by
    simp only [Ex.eval, P3, v3, Function.update_self]] at v4
  have K4 : vw s4 43 = K := by rw [v4, Function.update_of_ne (by norm_num), v3, Function.update_of_ne (by norm_num), K2]
  have L4 : vw s4 40 = L := by rw [v4, Function.update_of_ne (by norm_num), v3, Function.update_of_ne (by norm_num), L2]
  obtain ⟨v6, a6, -⟩ := vw_cset (e := .add (.var 310) (.mul (.mul (.lit 2) (g4E 43)) (tBE 40)))
    (by simp [VB, g4E, gE, powE, tBE]) (show 310 < 1000 by norm_num) s4
  set s6 := (Cmd.run (cset (.add (.var 310) (.mul (.mul (.lit 2) (g4E 43)) (tBE 40))) 310) s4).1
  have K5 : vw s4 43 = K := K4
  have L5 : vw s4 40 = L := L4
  have M5 : vw s4 310 = st.sc 310 := by
    rw [v4, Function.update_of_ne (by norm_num), v3,
      Function.update_of_ne (by norm_num), v2, Function.update_of_ne (by norm_num), Function.update_of_ne (by norm_num),
      vw_lt (by norm_num)]
  rw [show eval (vw s4) s4.ar (.add (.var 310) (.mul (.mul (.lit 2) (g4E 43)) (tBE 40))) =
      st.sc 310 + 2 * Gs K0u d ^ 4 * tB L by
    simp only [Ex.eval]; rw [eval_g4E (by norm_num) (by norm_num), eval_tBE L5, K5, M5]; rfl] at v6
  -- the level literals
  obtain ⟨l1, l2, a7⟩ := UP_ok.lset s6
  set s7 := (Cmd.run UP.lset s6).1
  have K6 : s6.sc 43 = K := by
    rw [← vw_lt (show 43 < 1000 by norm_num), v6, Function.update_of_ne (by norm_num), K5]
  rw [K6] at l1
  have w7 : ∀ y, ¬ (20 ≤ y ∧ y < 40) → vw s7 y = vw s6 y := fun y hy => by
    by_cases hy' : y < 1000
    · rw [vw_lt hy', vw_lt hy', l2 y hy' (by omega)]
    · simp [vw, hy']
  have lit7 : ∀ v k, lokU K v k → vw s7 v = k := fun v k h => by
    have := UP_ok.lvar K v k h; rw [vw_lt (by omega), l1 v k h]
  obtain ⟨v8, a8, -⟩ := vw_cset UP_ok.vlnE (show 101 < 1000 by norm_num) s7
  set s8 := (Cmd.run (cset UP.lnE 101) s7).1
  have L7 : vw s7 40 = L := by
    rw [w7 40 (by omega), v6, Function.update_of_ne (by norm_num), L5]
  rw [(UP_ok.lnE K (vw s7) s7.ar lit7).1, LevelEx.eval_LnE (lam := L) (P := lvP K) L7] at v8
  obtain ⟨v9, a9, -⟩ := vw_copy (show 40 < 1000 by norm_num) (show 101 < 1000 by norm_num) s8
  set s9 := (Cmd.run (.copy 40 101) s8).1
  have fr : ∀ y < 1000, ¬ WS y → vw s9 y = vw st y := fun y _ hW => by
    simp only [WS] at hW
    rw [v9, Function.update_of_ne (by omega), v8, Function.update_of_ne (by omega), w7 y (by omega), v6,
      Function.update_of_ne (by omega), v4, Function.update_of_ne (by omega),
      v3, Function.update_of_ne (by omega), v2, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  have g303 : vw s9 303 = st.sc 303 * Nc K0u d L := by
    rw [v9, Function.update_of_ne (by norm_num), v8, Function.update_of_ne (by norm_num), w7 303 (by omega), v6,
      Function.update_of_ne (by norm_num), v4, Function.update_self]
  have g310 : vw s9 310 = st.sc 310 + 2 * Gs K0u d ^ 4 * tB L := by
    rw [v9, Function.update_of_ne (by norm_num), v8, Function.update_of_ne (by norm_num), w7 310 (by omega), v6,
      Function.update_self]
  refine ⟨?_, ?_, ?_, fun y hy hW => ?_, ?_⟩
  · rw [← vw_lt (show 40 < 1000 by norm_num), v9, Function.update_self, v8, Function.update_self]; rfl
  · rw [← vw_lt (show 303 < 1000 by norm_num), g303]
  · rw [← vw_lt (show 310 < 1000 by norm_num), g310]
  · rw [← vw_lt hy, fr y hy hW, vw_lt hy]
  · rw [a9, a8, a7, a6, a4, a3, a2, a1]

/-- The invariant of the sweep after `j` levels. -/
def SwInv (st : St) (ℓ L : ℕ) (j : ℕ) (s : St) : Prop :=
  (∀ d, d + j = ℓ → ∃ lam, s.sc 40 = lam ∧ s.sc 303 * NPof K0u d lam = NPof K0u ℓ L ∧
      s.sc 310 + mlogN K0u d lam = mlogN K0u ℓ L) ∧
    (∀ y < 1000, ¬ WS y → y ≠ 306 → s.sc y = st.sc y) ∧ s.ar = st.ar

/-- **The sweep.** -/
theorem sweep_spec (st : St) {ℓ L : ℕ} (h307 : st.sc 307 = ℓ) (h40 : st.sc 40 = L) (h303 : st.sc 303 = 1)
    (h310 : st.sc 310 = 0) :
    SwInv st ℓ L ℓ (Cmd.run (.loop 307 306 (sweepBody UP)) st).1 := by
  have h0 : SwInv st ℓ L 0 st := by
    refine ⟨fun d hd => ⟨L, h40, ?_, ?_⟩, fun _ _ _ _ => rfl, rfl⟩ <;> obtain rfl : d = ℓ := by omega
    · rw [h303, one_mul]
    · rw [h310, zero_add]
  have := Cmd.loop_inv (b := 307) (c := 306) (body := sweepBody UP) (st := st) (SwInv st ℓ L) h0 ?_
  · rwa [h307] at this
  intro j s hj ⟨hI, sfr, sar⟩
  rw [h307] at hj
  set s' := s.setSc 306 j
  obtain ⟨d, rfl⟩ : ∃ d, ℓ = d + 1 + j := ⟨ℓ - 1 - j, by omega⟩
  obtain ⟨lam, e40, e303, e310⟩ := hI (d + 1) (by omega)
  have g : ∀ y, y ≠ 306 → s'.sc y = s.sc y := fun y hy => by simp [s', Function.update_of_ne hy]
  obtain ⟨r40, r303, r310, rfr, rar⟩ := sweepBody_spec s' (d := d) (L := lam)
    (by rw [g 307 (by norm_num), sfr 307 (by norm_num) (by simp [WS]) (by norm_num), h307]; simp [s'])
    (by rw [g 40 (by norm_num), e40])
  refine ⟨fun d' hd' => ?_, fun y hy hW h306 => ?_, by rw [rar]; exact sar⟩
  · obtain rfl : d' = d := by omega
    refine ⟨_, r40, ?_, ?_⟩
    · rw [r303, g 303 (by norm_num), ← e303, NPof]; ring
    · rw [r310, g 310 (by norm_num), ← e310, mlogN]; ring
  · rw [rfr y hy hW, g y h306, sfr y hy hW h306]

set_option maxRecDepth 20000 in
/-- **The parameters and the sweep.** -/
theorem setup_spec (st : St) :
    let n := st.sc 0
    let ℓ := ellOf n
    let K := Kb K0u ℓ
    let L := Ltop K (Gs K0u ℓ) (sOf n)
    let r := (Cmd.run (setup UP) st).1
    r.sc 11 = sOf n ∧ r.sc 307 = ℓ ∧ r.sc 316 = K ∧ r.sc 12 = L ∧ r.sc 303 = NPof K0u ℓ L ∧
      r.sc 310 = mlogN K0u ℓ L ∧ (∀ v k, tokU K v k → r.sc v = k) ∧
      (∀ y < 1000, y ≠ 1 → y ≠ 3 → (y < 5 ∨ 9 < y) → ¬ WS y → y ≠ 306 → y ≠ 11 → y ≠ 307 → y ≠ 316 →
        y ≠ 12 → r.sc y = st.sc y) ∧ r.ar = st.ar := by
  intro n ℓ K L r
  obtain ⟨v1, a1, -⟩ := vw_cset (e := sE) (by simp [sE, pow2, VB]) (show 11 < 1000 by norm_num) st
  set e1 := (Cmd.run (cset sE 11) st).1
  rw [eval_sE, vw_lt (show 0 < 1000 by norm_num)] at v1
  obtain ⟨v2, a2, -⟩ := vw_cset (e := ellE) (by simp [ellE, kbE, powE, VB]) (show 307 < 1000 by norm_num) e1
  set e2 := (Cmd.run (cset ellE 307) e1).1
  rw [eval_ellE, v1, Function.update_of_ne (by norm_num), vw_lt (show 0 < 1000 by norm_num)] at v2
  obtain ⟨v3, a3, -⟩ := vw_cset (vb_kbE 307 (by norm_num)) (show 43 < 1000 by norm_num) e2
  set e3 := (Cmd.run (cset (kbE 307) 43) e2).1
  rw [eval_kbE, v2, Function.update_self] at v3
  obtain ⟨v4, a4, -⟩ := vw_copy (show 316 < 1000 by norm_num) (show 43 < 1000 by norm_num) e3
  set e4 := (Cmd.run (.copy 316 43) e3).1
  rw [v3, Function.update_self] at v4
  obtain ⟨t1, t2, a5⟩ := UP_ok.tset e4
  set e5 := (Cmd.run UP.tset e4).1
  have K4 : e4.sc 43 = K := by
    rw [← vw_lt (show 43 < 1000 by norm_num), v4, Function.update_of_ne (by norm_num), Function.update_self]
  rw [K4] at t1
  have w5 : ∀ y < 1000, y ≠ 1 → y ≠ 3 → (y < 5 ∨ 9 < y) → vw e5 y = vw e4 y := fun y hy h1 h3 h59 => by
    rw [vw_lt hy, vw_lt hy, t2 y hy h1 h3 h59]
  obtain ⟨v6, a6, -⟩ := vw_cset UP_ok.vl0E (show 12 < 1000 by norm_num) e5
  set e6 := (Cmd.run (cset UP.l0E 12) e5).1
  have tk5 : ∀ v k, tokU K v k → vw e5 v = k := fun v k h => by
    have := topOk_lt h; rw [vw_lt (by omega), t1 v k h]
  have s5 : vw e5 11 = sOf n := by
    rw [w5 11 (by norm_num) (by norm_num) (by norm_num) (by norm_num), v4, Function.update_of_ne (by norm_num),
      Function.update_of_ne (by norm_num), Function.update_of_ne (by norm_num), Function.update_self]
  rw [(UP_ok.l0E K (vw e5) e5.ar tk5).1, eval_L0E s5] at v6
  obtain ⟨v7, a7, -⟩ := vw_copy (show 40 < 1000 by norm_num) (show 12 < 1000 by norm_num) e6
  set e7 := (Cmd.run (.copy 40 12) e6).1
  obtain ⟨v8, a8, -⟩ := vw_setK (k := 1) (show 303 < 1000 by norm_num) e7
  set e8 := (Cmd.run (.setK 303 1) e7).1
  obtain ⟨v10, a10, -⟩ := vw_setK (k := 0) (show 310 < 1000 by norm_num) e8
  set e10 := (Cmd.run (.setK 310 0) e8).1
  have pre : ∀ y < 1000, y ≠ 1 → y ≠ 3 → (y < 5 ∨ 9 < y) → y ≠ 310 → y ≠ 309 → y ≠ 303 → y ≠ 40 → y ≠ 12 →
      y ≠ 316 → y ≠ 43 → y ≠ 307 → y ≠ 11 → vw e10 y = vw st y :=
    fun y hy h1 h3 h59 a b c d e f g h i => by
      rw [v10, Function.update_of_ne a, v8, Function.update_of_ne c, v7,
        Function.update_of_ne d, v6, Function.update_of_ne e, w5 y hy h1 h3 h59, v4, Function.update_of_ne f,
        Function.update_of_ne g, Function.update_of_ne h, Function.update_of_ne i]
  have L6 : vw e6 12 = L := by rw [v6, Function.update_self]; rfl
  have g10 : ∀ y, y ≠ 310 → y ≠ 309 → y ≠ 303 → y ≠ 40 → vw e10 y = vw e6 y := fun y a b c d => by
    rw [v10, Function.update_of_ne a, v8, Function.update_of_ne c, v7,
      Function.update_of_ne d]
  have k6 : ∀ y, y ∈ [307, 316, 11] → vw e6 y = vw e4 y := fun y hy => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rw [v6, Function.update_of_ne (by omega), w5 y (by omega) (by omega) (by omega) (by omega)]
  obtain ⟨sI, sfr, sar⟩ := sweep_spec e10 (ℓ := ℓ) (L := L)
    (by rw [← vw_lt (show 307 < 1000 by norm_num), g10 307 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
      k6 307 (by simp), v4]; simp [ℓ, n])
    (by rw [← vw_lt (show 40 < 1000 by norm_num), v10, Function.update_of_ne (by norm_num),
      v8, Function.update_of_ne (by norm_num), v7, Function.update_self, L6])
    (by rw [← vw_lt (show 303 < 1000 by norm_num), v10, Function.update_of_ne (by norm_num),
      v8, Function.update_self])
    (by rw [← vw_lt (show 310 < 1000 by norm_num), v10, Function.update_self])
  set e11 := (Cmd.run (.loop 307 306 (sweepBody UP)) e10).1
  obtain ⟨lam, l40, l303, l310⟩ := sI 0 (by omega)
  simp only [NPof, mlogN, mul_one, add_zero] at l303 l310
  have hrun : (Cmd.run (setup UP) st).1 = e11 := by simp only [setup, Cmd.run_seq]; rfl
  have f11 : ∀ y, y ∈ [307, 316, 11, 12] → e11.sc y = vw e6 y := fun y hy => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rw [sfr y (by omega) (by simp only [WS]; omega) (by omega), ← vw_lt (show y < 1000 by omega),
      g10 y (by omega) (by omega) (by omega) (by omega)]
  have tk6 : ∀ v k, tokU K v k → vw e6 v = k := fun v k h => by
    have := topOk_lt h; have := h.1; rw [v6, Function.update_of_ne (by omega), tk5 v k h]
  simp only [r]
  rw [hrun]
  refine ⟨?_, ?_, ?_, ?_, l303, l310, fun v k h => ?_, fun y hy h1 h3 h59 hW h306 h11 h307 h316 h12 => ?_, ?_⟩
  · rw [f11 11 (by simp), k6 11 (by simp), v4]; simp [n]
  · rw [f11 307 (by simp), k6 307 (by simp), v4]; simp [ℓ, n]
  · rw [f11 316 (by simp), k6 316 (by simp), v4]; simp [K, ℓ, n]
  · rw [f11 12 (by simp), L6]
  · have := topOk_lt h; have := h.1
    rw [sfr v (by omega) (by simp only [WS]; omega) (by omega), ← vw_lt (show v < 1000 by omega),
      g10 v (by omega) (by omega) (by omega) (by omega), tk6 v k h]
  · rw [sfr y hy hW h306, ← vw_lt hy, pre y hy h1 h3 h59 (by simp only [WS] at hW; omega)
      (by simp only [WS] at hW; omega) (by simp only [WS] at hW; omega) (by simp only [WS] at hW; omega) h12 h316
      (by simp only [WS] at hW; omega) h307 h11, vw_lt hy]
  · rw [sar, a10, a8, a7, a6, a5, a4, a3, a2, a1]

end Factoring.Aux
