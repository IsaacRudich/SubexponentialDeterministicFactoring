/-
The cost of the uniform counting command: the levels of one path, one path, all paths.

* `CI` (the level loop's invariant, with the chain's requirements `DeepReq` and `2^(L K) ≤ V`), `ci_step`,
  **`lvlLoop_cost`**; **`pathBody_cost`**; **`pathLoop_cost`**.

Not an audit surface.
-/
module

public import FactoringAux.UniCostLvl

@[expose] public section

namespace Factoring.Aux

open Factoring.Aux.Copied Factoring.Aux.Copied.PLib Ex Uni Finset SB

namespace UCost

theorem lvlV_mono {K K' : ℕ} (h : K ≤ K') : lvlV K ≤ lvlV K' := by
  unfold lvlV
  exact le_trans (Nat.pow_le_pow_left (by omega) _)
    (Nat.pow_le_pow_right (by omega) (by have := Nat.pow_le_pow_left h 8; omega))

/-- The invariant of the level loop (costs). -/
def CI (V m ℓ : ℕ) (j : ℕ) (s : St) : Prop :=
  (∀ d, d + j = ℓ → ∃ (L : ℕ) (T : Clique (ZMod m) (Kb K0u d) L), s.sc 40 = L ∧
      s.sc 41 = (if j = 0 then 2 else (j - 1) % 2) ∧ s.sc 42 = Kb K0u d ∧ Holds s.ar (s.sc 41) T ∧
      DeepReq V m K0u d L ∧ 2 ^ (L * Kb K0u d) ≤ V) ∧
    s.sc 10 = m ∧ s.sc 307 = ℓ ∧ s.sc 305 ≤ V

set_option maxRecDepth 8192 in
theorem ci_step {V m ℓ : ℕ} (hm : 1 < m) (hℓ : ℓ ≤ V) (hlv : lvlV (Kb K0u ℓ) ≤ V) (j : ℕ) (s : St) (hj : j < ℓ)
    (hs : CI V m ℓ j s) :
    CI V m ℓ (j + 1) (Cmd.run (lvlBody UP) (s.setSc 306 j)).1 ∧ (Cmd.run (lvlBody UP) (s.setSc 306 j)).2 ≤ 40 * YB V := by
  obtain ⟨hI, s10, s307, s305⟩ := hs
  set s' := s.setSc 306 j
  obtain ⟨d, rfl⟩ : ∃ d, ℓ = d + 1 + j := ⟨ℓ - 1 - j, by omega⟩
  obtain ⟨L, T, e40, e41, e42, eH, eR, eLK⟩ := hI (d + 1) (by omega)
  have hpar : (if j = 0 then 2 else (j - 1) % 2) < 3 := by split_ifs <;> omega
  have hpj : (if j = 0 then 2 else (j - 1) % 2) ≠ j % 2 := by split_ifs <;> omega
  have g : ∀ y, y ≠ 306 → s'.sc y = s.sc y := fun y hy => by simp [s', Function.update_of_ne hy]
  have j306 : s'.sc 306 = j := by simp [s']
  have h10 : s'.sc 10 = m := by rw [g 10 (by norm_num), s10]
  have h307 : s'.sc 307 = d + 1 + s'.sc 306 := by rw [g 307 (by norm_num), s307, j306]
  have h40 : s'.sc 40 = L := by rw [g 40 (by norm_num), e40]
  have h41 : s'.sc 41 = (if j = 0 then 2 else (j - 1) % 2) := by rw [g 41 (by norm_num), e41]
  have h42 : s'.sc 42 = Kb K0u (d + 1) := by rw [g 42 (by norm_num), e42]
  have hpj' : (if j = 0 then 2 else (j - 1) % 2) ≠ s'.sc 306 % 2 := by rw [j306]; exact hpj
  have hT : Holds s'.ar (if j = 0 then 2 else (j - 1) % 2) T := by rw [e41] at eH; exact eH
  obtain ⟨r40, r41, r42, r305, rH, -, rfr⟩ := lvlBody_spec UP UP_ok s' T hm h10 h307 h40 h41 hpar hpj' h42 rfl hT
  have hc := lvlBody_cost s' T hm h10 h307 h40 h41 hpar hpj' h42 hT (by rw [g 305 (by norm_num)]; exact s305)
    (by rw [g 307 (by norm_num), s307]; exact hℓ) eR.1 eLK (le_trans (lvlV_mono (Kb_le (by omega))) hlv)
  rw [j306] at r41 rH
  refine ⟨⟨fun d' hd' => ?_, ?_, ?_, ?_⟩, hc⟩
  · obtain rfl : d' = d := by omega
    refine ⟨_, _, r40, by rw [r41]; simp, r42, by rw [r41]; exact rH, eR.2, eR.1.hLK⟩
  · rw [rfr 10 (by norm_num) (by simp [WL]), h10]
  · rw [rfr 307 (by norm_num) (by simp [WL]), g 307 (by norm_num), s307]
  · rw [r305, g 305 (by norm_num)]; exact le_trans (Nat.div_le_self _ _) s305

/-- **The levels of one path**: the invariant at the end, and the cost. -/
theorem lvlLoop_cost {V m ℓ : ℕ} (hm : 1 < m) (hℓ : ℓ ≤ V) (hlv : lvlV (Kb K0u ℓ) ≤ V) (st : St)
    (h0 : CI V m ℓ 0 st) :
    CI V m ℓ ℓ (Cmd.run (.loop 307 306 (lvlBody UP)) st).1 ∧
      (Cmd.run (.loop 307 306 (lvlBody UP)) st).2 ≤ 42 * YB V ^ 2 := by
  have h307 : st.sc 307 = ℓ := h0.2.2.1
  constructor
  · have := Cmd.loop_inv (b := 307) (c := 306) (body := lvlBody UP) (st := st) (CI V m ℓ) h0
      (fun j s hj hs => (ci_step hm hℓ hlv j s (by omega) hs).1)
    rwa [h307] at this
  · have := Cmd.loop_cost_le (b := 307) (c := 306) (body := lvlBody UP) (st := st) (CI V m ℓ) (40 * YB V ^ 1) h0
      (fun j s hj hs => (ci_step hm hℓ hlv j s (by omega) hs).1)
      (fun j s hj hs => by rw [pow_one]; exact (ci_step hm hℓ hlv j s (by omega) hs).2)
    rw [h307] at this
    exact le_trans this (loop_le (le_trans hℓ le_Wv))

theorem dp_bruteU : Ex.dp bruteU ≤ 100 := le_trans (dpT_bruteE _ _ _ _ _ _ _) (by rw [dp_rdT]; norm_num)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
/-- **The cost of one path.** -/
theorem pathBody_cost {V m ℓ L0 : ℕ} (T0 : Clique (ZMod m) (Kb K0u ℓ) L0) (st : St) (hm : 1 < m)
    (h10 : st.sc 10 = m) (h307 : st.sc 307 = ℓ) (h12 : st.sc 12 = L0) (h316 : st.sc 316 = Kb K0u ℓ)
    (h304 : st.sc 304 ≤ V) (h308 : st.sc 308 < m) (hT : Holds st.ar 2 T0) (hR : DeepReq V m K0u ℓ L0)
    (hLK : 2 ^ (L0 * Kb K0u ℓ) ≤ V) (hℓ : ℓ ≤ V) (hlv : lvlV (Kb K0u ℓ) ≤ V) :
    (Cmd.run (pathBody UP) st).2 ≤ 50 * YB V ^ 2 := by
  have hW := @le_Wv V
  have hY := YB_ge V
  have hPB := PB_le_YB V
  have hY2 : YB V ≤ YB V ^ 2 := Nat.le_self_pow (by norm_num) _
  have hW2 : 2 * V ≤ Wv V := by
    unfold Wv; rcases Nat.eq_zero_or_pos V with h | h
    · subst h; simp
    · nlinarith
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
  have k305 : q4.sc 305 = st.sc 304 := by
    rw [← vw_lt (show 305 < 1000 by norm_num), v4, Function.update_of_ne (by norm_num), v3,
      Function.update_of_ne (by norm_num), v2, Function.update_of_ne (by norm_num), v1, Function.update_self,
      vw_lt (by norm_num)]
  have k10 : q4.sc 10 = m := by rw [g4 10 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), h10]
  have k307 : q4.sc 307 = ℓ := by
    rw [g4 307 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), h307]
  have hI0 : CI V m ℓ 0 q4 := by
    refine ⟨fun d hd => ?_, k10, k307, by rw [k305]; exact h304⟩
    obtain rfl : d = ℓ := by omega
    exact ⟨L0, T0, k40, by simp [k41], k42, by rw [k41, ar4]; exact hT, hR, hLK⟩
  obtain ⟨hI, kL⟩ := lvlLoop_cost hm hℓ hlv q4 hI0
  set q5 := (Cmd.run (.loop 307 306 (lvlBody UP)) q4).1
  obtain ⟨hI5, i10, -, -⟩ := hI
  obtain ⟨L, T, e40, e41, e42, eH, eR, eLK⟩ := hI5 0 (by omega)
  obtain ⟨-, -, -, ifr, -, -⟩ := lvlLoop_spec UP UP_ok T0 q4 hm k10 k307 k40 k41 k42 rfl (by rw [ar4]; exact hT)
  -- the brute force
  obtain ⟨v6, a6, k6⟩ := vw_cset vb_bruteU (show 312 < 1000 by norm_num) q5
  set q6 := (Cmd.run (cset bruteU 312) q5).1
  have hpar : q5.sc 41 < 3 := by rw [e41]; split_ifs <;> omega
  have hmV : m ≤ V := eR.mV
  have hK0V : Kb K0u 0 ≤ V := eR.KV
  have hTB : TBdd (Wv V) 60 (vw q5) q5.ar 60 61 rdT (Kb K0u 0) :=
    rdT_tbdd eH (by rw [vw_lt (by norm_num), e42]) (by rw [vw_lt (by norm_num), e40]) (by rw [vw_lt (by norm_num)])
      hpar hm hmV hK0V eLK
  have m5 : vw q5 10 = m := by rw [vw_lt (by norm_num), i10]
  have k6' : (Cmd.run (cset bruteU 312) q5).2 ≤ PB V := by
    refine le_trans k6 (cost_le_PB ?_ dp_bruteU)
    exact brute_bdd (BruteReq.mono eR hW) hTB m5 (by rw [vw_lt (by norm_num), e40]) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (Ag.refl _ _)
  have hb : eval (vw q5) q5.ar bruteU < m := by
    rw [← m5]; exact lt_zsum (by rw [m5]; omega)
  obtain ⟨v7, a7, k7⟩ := vw_cset (e := .mod (.add (.var 308) (.var 312)) (.var 10)) (by simp [VB])
    (show 308 < 1000 by norm_num) q6
  have m6 : vw q6 10 = m := by rw [v6, Function.update_of_ne (by norm_num), m5]
  have c6 : vw q6 308 = st.sc 308 := by
    rw [v6, Function.update_of_ne (by norm_num), vw_lt (by norm_num),
      ifr 308 (by norm_num) (by simp [WL]) (by norm_num),
      g4 308 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  have b6 : vw q6 312 = eval (vw q5) q5.ar bruteU := by rw [v6, Function.update_self]
  have k7' : (Cmd.run (cset (.mod (.add (.var 308) (.var 312)) (.var 10)) 308) q6).2 ≤ PB V := by
    refine le_trans k7 (cost_le_PB ?_ (by simp [Ex.dp]))
    refine B_mod (B_add (B_var (by rw [c6]; omega)) (B_var (by rw [b6]; omega)) ?_) (B_var (by rw [m6]; omega))
    simp only [Ex.eval, c6, b6]; omega
  have hle := seq_le (le_refl (Cmd.run (.copy 305 304) st).2) (seq_le (le_refl (Cmd.run (.copy 40 12) q1).2)
    (seq_le (le_refl (Cmd.run (.setK 41 2) q2).2) (seq_le (le_refl (Cmd.run (.copy 42 316) q3).2)
      (seq_le kL (seq_le k6' k7')))))
  have e : (Cmd.run (pathBody UP) st).2 = (Cmd.run (.seq (.copy 305 304) <| .seq (.copy 40 12) <| .seq (.setK 41 2) <|
      .seq (.copy 42 316) <| .seq (.loop 307 306 (lvlBody UP)) <|
      .seq (cset bruteU 312) (cset (.mod (.add (.var 308) (.var 312)) (.var 10)) 308)) st).2 := rfl
  rw [e]
  refine le_trans hle ?_
  simp only [Cmd.run_copy, Cmd.run_setK]
  omega

/-- **The cost of all paths.** -/
theorem pathLoop_cost {V m ℓ L0 : ℕ} (T0 : Clique (ZMod m) (Kb K0u ℓ) L0) (st : St) (hm : 1 < m)
    (h10 : st.sc 10 = m) (h307 : st.sc 307 = ℓ) (h12 : st.sc 12 = L0) (h316 : st.sc 316 = Kb K0u ℓ)
    (h308 : st.sc 308 = 0) (h303 : st.sc 303 ≤ V) (hT : Holds st.ar 2 T0) (hR : DeepReq V m K0u ℓ L0)
    (hLK : 2 ^ (L0 * Kb K0u ℓ) ≤ V) (hℓ : ℓ ≤ V) (hlv : lvlV (Kb K0u ℓ) ≤ V) :
    (Cmd.run (.loop 303 304 (pathBody UP)) st).2 ≤ 52 * YB V ^ 3 := by
  have : NeZero m := ⟨by omega⟩
  have hstep : ∀ j s, j < st.sc 303 → PathInv st ℓ L0 T0 j s →
      PathInv st ℓ L0 T0 (j + 1) (Cmd.run (pathBody UP) (s.setSc 304 j)).1 ∧
        (Cmd.run (pathBody UP) (s.setSc 304 j)).2 ≤ 50 * YB V ^ 2 := by
    intro j s hj ⟨s308, sfr, stop, sar⟩
    set s' := s.setSc 304 j
    have g : ∀ y, y ≠ 304 → s'.sc y = s.sc y := fun y hy => by simp [s', Function.update_of_ne hy]
    have f : ∀ y, y ∈ [10, 307, 12, 316] → s'.sc y = st.sc y := fun y hy => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rw [g y (by omega), sfr y (by omega) (by simp only [WP, WL]; omega) (by omega)]
    have hT' : Holds s'.ar 2 T0 :=
      fun γ hγ Q hQ => by rw [show s'.ar = s.ar from rfl, stop _ (by omega)]; exact hT γ hγ Q hQ
    obtain ⟨r308, rfr, rtop, rar⟩ := pathBody_spec (P := j) (acc := s.sc 308) UP UP_ok T0 s' hm
      (by rw [f 10 (by simp), h10]) (by rw [f 307 (by simp), h307]) (by rw [f 12 (by simp), h12])
      (by rw [f 316 (by simp), h316]) (by simp [s']) (g 308 (by norm_num)) hT'
    refine ⟨⟨?_, fun y hy hW h304 => ?_, fun x hx => ?_, fun a ha => ?_⟩, ?_⟩
    · rw [r308, s308, sum_range_succ, ZMod.val_add_val]
    · rw [rfr y hy hW, g y h304, sfr y hy hW h304]
    · rw [rtop x hx]; exact stop x hx
    · rw [rar a ha]; exact sar a ha
    · refine pathBody_cost T0 s' hm (by rw [f 10 (by simp), h10]) (by rw [f 307 (by simp), h307])
        (by rw [f 12 (by simp), h12]) (by rw [f 316 (by simp), h316]) (by simp [s']; omega) ?_ hT' hR hLK hℓ hlv
      rw [g 308 (by norm_num), s308]; exact ZMod.val_lt _
  have := Cmd.loop_cost_le (b := 303) (c := 304) (body := pathBody UP) (st := st) (PathInv st ℓ L0 T0)
    (50 * YB V ^ 2) ⟨by simp [h308], fun _ _ _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
    (fun j s hj hs => (hstep j s hj hs).1) (fun j s hj hs => (hstep j s hj hs).2)
  exact le_trans this (loop_le (le_trans h303 le_Wv))

end UCost

end Factoring.Aux
