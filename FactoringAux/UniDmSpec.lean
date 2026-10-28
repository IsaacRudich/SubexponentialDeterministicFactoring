/-
The uniform engine: the multiplier `deepMult` modulo `m`, computed per modulus by a loop over the levels with
every product reduced (**`dmLoop_spec`**), so that no value exceeds a polynomial in the running time.

Not an audit surface.
-/
module

public import FactoringAux.UniSetupSpec

@[expose] public section

namespace Factoring.Aux

open Factoring.Aux.Copied Factoring.Aux.Copied.PLib Ex Uni Finset

attribute [local irreducible] cset

variable {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ}

theorem foldProd_const_mod {m : ℕ} (hm : 0 < m) (c : ℕ) :
    ∀ n, foldProd (fun _ => c % m) m n % m = c ^ n % m
  | 0 => rfl
  | n + 1 => by
      rw [foldProd, Nat.mod_mod, Nat.mul_mod, foldProd_const_mod hm c n, Nat.mod_mod, ← Nat.mul_mod, pow_succ]

theorem eval_multVm {vK vl vm d L m : ℕ} (hm : 0 < m) (h1 : vK ≠ 906) (h3 : vl < 910) (h4 : vm < 910)
    (hK : σ vK = Kb K0u d) (hl : σ vl = L) (hσm : σ vm = m) :
    eval σ A (multVm vK vl vm) = mult (Gs K0u d) L % m := by
  rw [multVm, eval_lett, eval_gE h1, hK]
  set G := 3 * Kb K0u d ^ 8
  set σ1 := Function.update σ 910 G
  rw [eval_lett]
  have e2 : eval σ1 A (.div (.mul (.var 910) (.sub (.var 910) (.lit 1))) (.lit 2)) = G * (G - 1) / 2 := by
    simp [σ1, Ex.eval]
  rw [e2, eval_lett]
  set σ2 := Function.update σ1 911 (G * (G - 1) / 2)
  have e3 : eval σ2 A (.mul (.var 911) (.var 911)) = (G * (G - 1) / 2) * (G * (G - 1) / 2) := by
    simp [σ2, Ex.eval]
  rw [e3]
  set σ3 := Function.update σ2 912 ((G * (G - 1) / 2) * (G * (G - 1) / 2))
  have t3 : ∀ σ' : ℕ → ℕ, (∀ y < 910, σ' y = σ y) → eval σ' A (tBE vl) = tB L := fun σ' h' => by
    rw [eval_tBE (by rw [h' vl h3, hl])]
  have a3 : ∀ y < 910, σ3 y = σ y := fun y hy => by simp only [σ3, σ2, σ1]; upd
  have v910 : σ3 910 = G := by simp [σ3, σ2, σ1]
  have v912 : σ3 912 = (G * (G - 1) / 2) * (G * (G - 1) / 2) := by simp [σ3]
  have m3 : ∀ i, Function.update σ3 913 i vm = m := fun i => by
    rw [Function.update_of_ne (by omega), a3 vm h4, hσm]
  simp only [Ex.eval]
  rw [eval_powE 914 _ 4 (fun i => by simp [Ex.eval]), show eval σ3 A (.var 910) = G from v910, v912,
    show σ3 vm = m by rw [a3 vm h4, hσm]]
  rw [show (fun i => (eval (Function.update σ3 913 i) A (tBE vl) + 1) % Function.update σ3 913 i vm) =
      fun _ => (tB L + 1) % m from funext fun i => by
        rw [t3 _ (fun y hy => by rw [Function.update_of_ne (by omega)]; exact a3 y hy), m3],
    show (fun i => 2 % Function.update σ3 913 i vm) = fun _ => 2 % m from
      funext fun i => by rw [m3], t3 _ a3]
  rw [Nat.mul_mod, foldProd_const_mod hm, foldProd_const_mod hm, ← Nat.mul_mod]
  rw [mult, nonRects_eq, card_rects, Gs_eq]

theorem mod_mul3 (a b c m : ℕ) : ((a * (b % m)) % m * c) % m = (a * (b * c)) % m := by
  rw [Nat.mod_mul_mod, show a * (b % m) * c = (a * c) * (b % m) by ring, Nat.mul_mod_mod]; ring_nf

namespace Uni

/-- The scalars a level of the multiplier loop writes (below `1000`). -/
def WD (y : ℕ) : Prop := (20 ≤ y ∧ y < 40) ∨ y = 40 ∨ y = 43 ∨ y = 45 ∨ y = 101 ∨ y = 309

end Uni

/-- **One level of the multiplier loop.** -/
theorem dmBody_spec (st : St) {d L m : ℕ} (hm : 0 < m) (h307 : st.sc 307 = d + 1 + st.sc 306)
    (h40 : st.sc 40 = L) (h10 : st.sc 10 = m) :
    (Cmd.run (dmBody UP) st).1.sc 40 = Lnext (Kb K0u d) (Gs K0u d) L ∧
      (Cmd.run (dmBody UP) st).1.sc 309 = (st.sc 309 * (mult (Gs K0u d) L % m)) % m ∧
      (∀ y < 1000, ¬ WD y → (Cmd.run (dmBody UP) st).1.sc y = st.sc y) ∧
      (Cmd.run (dmBody UP) st).1.ar = st.ar := by
  rw [dmBody]
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
  have M2 : vw s2 10 = m := by
    rw [v2, Function.update_of_ne (by norm_num), Function.update_of_ne (by norm_num), vw_lt (by norm_num), h10]
  have D2 : vw s2 309 = st.sc 309 := by
    rw [v2, Function.update_of_ne (by norm_num), Function.update_of_ne (by norm_num), vw_lt (by norm_num)]
  obtain ⟨v3, a3, -⟩ := vw_cset (e := .mod (.mul (.var 309) (multVm 43 40 10)) (.var 10))
    (by simp [VB, multVm, gE, powE, tBE]) (show 309 < 1000 by norm_num) s2
  set s3 := (Cmd.run (cset (.mod (.mul (.var 309) (multVm 43 40 10)) (.var 10)) 309) s2).1
  rw [show eval (vw s2) s2.ar (.mod (.mul (.var 309) (multVm 43 40 10)) (.var 10)) =
      (st.sc 309 * (mult (Gs K0u d) L % m)) % m by
    simp only [Ex.eval]; rw [eval_multVm hm (by norm_num) (by norm_num) (by norm_num) K2 L2 M2, D2, M2]] at v3
  obtain ⟨l1, l2, a4⟩ := UP_ok.lset s3
  set s4 := (Cmd.run UP.lset s3).1
  have K3 : s3.sc 43 = K := by
    rw [← vw_lt (show 43 < 1000 by norm_num), v3, Function.update_of_ne (by norm_num), K2]
  rw [K3] at l1
  have w4 : ∀ y, ¬ (20 ≤ y ∧ y < 40) → vw s4 y = vw s3 y := fun y hy => by
    by_cases hy' : y < 1000
    · rw [vw_lt hy', vw_lt hy', l2 y hy' (by omega)]
    · simp [vw, hy']
  have lit4 : ∀ v k, lokU K v k → vw s4 v = k := fun v k h => by
    have := UP_ok.lvar K v k h; rw [vw_lt (by omega), l1 v k h]
  obtain ⟨v5, a5, -⟩ := vw_cset UP_ok.vlnE (show 101 < 1000 by norm_num) s4
  set s5 := (Cmd.run (cset UP.lnE 101) s4).1
  have L4 : vw s4 40 = L := by rw [w4 40 (by omega), v3, Function.update_of_ne (by norm_num), L2]
  rw [(UP_ok.lnE K (vw s4) s4.ar lit4).1, LevelEx.eval_LnE (lam := L) (P := lvP K) L4] at v5
  obtain ⟨v6, a6, -⟩ := vw_copy (show 40 < 1000 by norm_num) (show 101 < 1000 by norm_num) s5
  refine ⟨?_, ?_, fun y hy hW => ?_, ?_⟩
  · rw [← vw_lt (show 40 < 1000 by norm_num), v6, Function.update_self, v5, Function.update_self]; rfl
  · rw [← vw_lt (show 309 < 1000 by norm_num), v6, Function.update_of_ne (by norm_num), v5,
      Function.update_of_ne (by norm_num), w4 309 (by omega), v3, Function.update_self]
  · simp only [WD] at hW
    rw [← vw_lt hy, v6, Function.update_of_ne (by omega), v5, Function.update_of_ne (by omega), w4 y (by omega), v3,
      Function.update_of_ne (by omega), v2, Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      vw_lt hy]
  · rw [a6, a5, a4, a3, a2, a1]

/-- **The multiplier modulo `m`.** -/
theorem dmLoop_spec (st : St) {ℓ L m : ℕ} (hm : 0 < m) (h307 : st.sc 307 = ℓ) (h12 : st.sc 12 = L)
    (h10 : st.sc 10 = m) :
    (Cmd.run (dmLoop UP) st).1.sc 309 % m = deepMult K0u ℓ L % m ∧
      (∀ y < 1000, ¬ WD y → y ≠ 306 → (Cmd.run (dmLoop UP) st).1.sc y = st.sc y) ∧
      (Cmd.run (dmLoop UP) st).1.ar = st.ar := by
  rw [dmLoop]
  repeat rw [Cmd.run_seq]
  set s1 := (Cmd.run (.copy 40 12) st).1
  set s2 := (Cmd.run (.setK 309 1) s1).1
  have g2 : ∀ y, y ≠ 309 → y ≠ 40 → s2.sc y = st.sc y := fun y a b => by
    simp [s2, s1, Cmd.run_setK, Cmd.run_copy, Function.update_of_ne a, Function.update_of_ne b]
  let DI : ℕ → St → Prop := fun j s =>
    (∀ d, d + j = ℓ → ∃ lam, s.sc 40 = lam ∧ (s.sc 309 * deepMult K0u d lam) % m = deepMult K0u ℓ L % m) ∧
    (∀ y < 1000, ¬ WD y → y ≠ 306 → s.sc y = s2.sc y) ∧ s.ar = s2.ar
  have h0 : DI 0 s2 := ⟨fun d hd => ⟨L, by simp [s2, s1, Cmd.run_setK, Cmd.run_copy, h12], by
      obtain rfl : d = ℓ := by omega
      simp [s2, Cmd.run_setK]⟩, fun _ _ _ _ => rfl, rfl⟩
  have hI := Cmd.loop_inv (b := 307) (c := 306) (body := dmBody UP) (st := s2) DI h0 (by
    intro j s hj ⟨hI, sfr, sar⟩
    have e307 : s2.sc 307 = ℓ := by rw [g2 307 (by norm_num) (by norm_num), h307]
    rw [e307] at hj
    set s' := s.setSc 306 j
    obtain ⟨d, rfl⟩ : ∃ d, ℓ = d + 1 + j := ⟨ℓ - 1 - j, by omega⟩
    obtain ⟨lam, e40, e309⟩ := hI (d + 1) (by omega)
    have g : ∀ y, y ≠ 306 → s'.sc y = s.sc y := fun y hy => by simp [s', Function.update_of_ne hy]
    obtain ⟨r40, r309, rfr, rar⟩ := dmBody_spec s' (d := d) (L := lam) (m := m) hm
      (by rw [g 307 (by norm_num), sfr 307 (by norm_num) (by simp [WD]) (by norm_num), e307]; simp [s'])
      (by rw [g 40 (by norm_num), e40])
      (by rw [g 10 (by norm_num), sfr 10 (by norm_num) (by simp [WD]) (by norm_num),
        g2 10 (by norm_num) (by norm_num), h10])
    refine ⟨fun d' hd' => ?_, fun y hy hW h306 => ?_, by rw [rar]; exact sar⟩
    · obtain rfl : d' = d := by omega
      refine ⟨_, r40, ?_⟩
      rw [r309, g 309 (by norm_num), mod_mul3, ← e309, deepMult]
    · rw [rfr y hy hW, g y h306, sfr y hy hW h306])
  rw [g2 307 (by norm_num) (by norm_num), h307] at hI
  obtain ⟨hv, hfr, har⟩ := hI
  obtain ⟨lam, -, e⟩ := hv 0 (by omega)
  refine ⟨by rw [← e, deepMult, mul_one], fun y hy hW h306 => ?_, ?_⟩
  · simp only [WD] at hW
    rw [hfr y hy (by simp only [WD]; omega) h306, g2 y (by omega) (by omega)]
  · rw [har]; rfl

end Factoring.Aux
