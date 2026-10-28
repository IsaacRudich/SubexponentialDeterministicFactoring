/-
The uniform engine: the moduli loop and the output bit (**`uniC_val`**, **`uniC_le_one`**).

For every modulus `2 ≤ m ≤ 2M`, `M = n + mlogN + 4`, the count `deepMult · cntAll` modulo `m` is compared with
`deepMult · [the divisor 1 has the high bits]`; they agree iff `m ∣ deepMult · cntPre` (`flag_key`); the output is
`1` iff all agree, which (`eq_zero_of_all_dvd`, as in `eval_mainE`) happens iff `cntPre = 0`.

Not an audit surface.
-/
module

public import FactoringAux.UniKeep
public import FactoringAux.UniDmSpec

@[expose] public section

namespace Factoring.Aux

open Factoring.Aux.Copied Factoring.Aux.Copied.PLib Ex Uni Finset

attribute [local irreducible] cset fillC UP

theorem flag_key {m D c c1 : ℕ} (hm : 1 < m) :
    ((D : ZMod m) * ((c + c1 : ℕ) : ZMod m)).val = (D % m * c1) % m ↔ m ∣ D * c := by
  have : NeZero m := ⟨by omega⟩
  rw [show (D % m * c1) % m = ((D * c1 : ℕ) : ZMod m).val by rw [ZMod.val_natCast, Nat.mod_mul_mod]]
  rw [← Nat.cast_mul, ZMod.val_injective m |>.eq_iff, ← ZMod.natCast_eq_zero_iff]
  push_cast
  constructor
  · intro h; linear_combination h
  · intro h; linear_combination h

/-- The scalars a modulus writes (below `990`). -/
def Uni.WM (y : ℕ) : Prop := WC y ∨ y = 10 ∨ y = 300 ∨ y = 301 ∨ y = 315 ∨ y = 309

theorem uniC_le_one (st : St) : (Cmd.run (uniC UP) st).1.sc 3 ≤ 1 := by
  have h : ∀ X : St, (Cmd.run (cset Uni.bitE 3) X).1.sc 3 ≤ 1 := fun X => by
    obtain ⟨v, -, -⟩ := vw_cset (e := Uni.bitE) (by simp [Uni.bitE, VB]) (show 3 < 1000 by norm_num) X
    rw [← vw_lt (show 3 < 1000 by norm_num), v, Function.update_self]
    rw [Uni.bitE, eval_ifLt']; split_ifs <;> simp [Ex.eval]
  exact h _

set_option maxRecDepth 20000 in
/-- **One modulus.** -/
theorem modBody_spec (s : St) (j : ℕ) {n k ℓ : ℕ} (h11 : s.sc 11 = sOf n) (h0 : s.sc 0 = n) (h2 : s.sc 2 = k)
    (hkn : k < n) (h307 : s.sc 307 = ℓ) (h316 : s.sc 316 = Kb K0u ℓ)
    (h12 : s.sc 12 = Ltop (Kb K0u ℓ) (Gs K0u ℓ) (sOf n))
    (h303 : s.sc 303 = NPof K0u ℓ (Ltop (Kb K0u ℓ) (Gs K0u ℓ) (sOf n)))
    (htok : ∀ v k', tokU (Kb K0u ℓ) v k' → s.sc v = k') (hN : 1 ≤ numCells (s.ar 0) 1 n)
    (hD : s.ar 1 k = 0) :
    (Cmd.run (modBody UP) (s.setSc 300 j)).1.sc 301 = s.sc 301 +
        (if 2 ≤ j ∧ ¬ j ∣ deepMult K0u ℓ (Ltop (Kb K0u ℓ) (Gs K0u ℓ) (sOf n)) *
          cntPre (numCells (s.ar 0) 1 n) k (numCells (s.ar 1) k (n - k)) then 1 else 0) ∧
      (∀ y < 990, ¬ WM y → (Cmd.run (modBody UP) (s.setSc 300 j)).1.sc y = s.sc y) ∧
      (∀ a, a ≠ 3 → (Cmd.run (modBody UP) (s.setSc 300 j)).1.ar a = s.ar a) := by
  set D := deepMult K0u ℓ (Ltop (Kb K0u ℓ) (Gs K0u ℓ) (sOf n))
  set N := numCells (s.ar 0) 1 n
  set x := numCells (s.ar 1) k (n - k)
  set s' := s.setSc 300 j
  set t1 := (Cmd.run (.copy 10 300) s').1
  set t2 := (Cmd.run (.setK 315 2) t1).1
  have g2 : ∀ y, y ≠ 315 → y ≠ 10 → y ≠ 300 → t2.sc y = s.sc y := fun y a b c => by
    simp [t2, t1, s', Cmd.run_setK, Cmd.run_copy, Function.update_of_ne a, Function.update_of_ne b,
      Function.update_of_ne c]
  have j10 : t2.sc 10 = j := by simp [t2, t1, s', Cmd.run_setK, Cmd.run_copy]
  have c315 : t2.sc 315 = 2 := by simp [t2, Cmd.run_setK]
  have hrun : (Cmd.run (modBody UP) s').1 =
      (Cmd.run (.ifLt 10 315 .skip (.seq (countM UP) (.seq (dmLoop UP) (cset flagE 301)))) t2).1 := by
    simp only [modBody, Cmd.run_seq]; rfl
  rw [hrun, Cmd.run_ifLt, j10, c315]
  by_cases hj : j < 2
  · rw [if_pos hj, if_neg (by omega), add_zero]
    refine ⟨g2 301 (by norm_num) (by norm_num) (by norm_num), fun y hy hW => ?_, fun a _ => rfl⟩
    simp only [WM] at hW
    exact g2 y (by omega) (by omega) (by omega)
  rw [if_neg hj]
  have hm : 1 < j := by omega
  obtain ⟨c308, cfr, car⟩ := countM_spec (m := j) (n := n) (k := k) (ℓ := ℓ) t2 hm j10
    (by rw [g2 11 (by norm_num) (by norm_num) (by norm_num), h11]) (by rw [g2 0 (by norm_num) (by norm_num) (by norm_num), h0])
    (by rw [g2 2 (by norm_num) (by norm_num) (by norm_num), h2]) hkn
    (by rw [g2 307 (by norm_num) (by norm_num) (by norm_num), h307])
    (by rw [g2 316 (by norm_num) (by norm_num) (by norm_num), h316])
    (by rw [g2 12 (by norm_num) (by norm_num) (by norm_num), h12])
    (by rw [g2 303 (by norm_num) (by norm_num) (by norm_num), h303])
    (fun v k' h => by have := topOk_lt h; have := h.1; rw [g2 v (by omega) (by omega) (by omega), htok v k' h])
    (by rw [show t2.ar = s.ar from rfl]; exact hN)
  set t3 := (Cmd.run (countM UP) t2).1
  obtain ⟨dm309, dfr, dar⟩ := dmLoop_spec t3 (ℓ := ℓ) (L := Ltop (Kb K0u ℓ) (Gs K0u ℓ) (sOf n)) (m := j)
    (by omega) (by rw [cfr 307 (by norm_num) (by simp [WC, WP, WL]), g2 307 (by norm_num) (by norm_num) (by norm_num), h307])
    (by rw [cfr 12 (by norm_num) (by simp [WC, WP, WL]), g2 12 (by norm_num) (by norm_num) (by norm_num), h12])
    (by rw [cfr 10 (by norm_num) (by simp [WC, WP, WL]), j10])
  set t4 := (Cmd.run (dmLoop UP) t3).1
  have ar3 : ∀ a, a ≠ 3 → t4.ar a = s.ar a := fun a ha => by rw [dar, car a ha]; rfl
  have f3 : ∀ y < 990, ¬ WC y → y ≠ 315 → y ≠ 10 → y ≠ 300 → y ≠ 309 → t4.sc y = s.sc y :=
    fun y hy hW a b c e => by
      have hW' := hW
      simp only [WC, WP, WL] at hW'
      rw [dfr y (by omega) (by simp only [WD]; omega) (by omega), cfr y hy hW, g2 y a b c]
  obtain ⟨v4, a4, -⟩ := vw_cset (e := flagE) (by simp [flagE, ifEq, c1E, nsum, xBit, bitRd, VB])
    (show 301 < 1000 by norm_num) t4
  simp only [Cmd.run_seq]
  have m3 : vw t4 10 = j := by
    rw [vw_lt (by norm_num), dfr 10 (by norm_num) (by simp [WD]) (by norm_num),
      cfr 10 (by norm_num) (by simp [WC, WP, WL]), j10]
  have d3 : vw t4 309 % j = D % j := by rw [vw_lt (by norm_num)]; exact dm309
  have e0 : vw t4 0 = n := by
    rw [vw_lt (by norm_num), f3 0 (by norm_num) (by simp [WC, WP, WL]) (by norm_num) (by norm_num) (by norm_num) (by norm_num), h0]
  have e2 : vw t4 2 = k := by
    rw [vw_lt (by norm_num), f3 2 (by norm_num) (by simp [WC, WP, WL]) (by norm_num) (by norm_num) (by norm_num) (by norm_num), h2]
  have hc1 : eval (vw t4) t4.ar c1E = if 1 / 2 ^ k = x then 1 else 0 := by
    rw [eval_c1E (by rw [e2, ar3 1 (by norm_num)]; exact hD) (by rw [e2, e0]; exact hkn), e2, e0,
      ar3 1 (by norm_num)]
  have hsplit := count_split N k x (by omega)
  rw [show t2.ar = s.ar from rfl] at c308
  have r308 : vw t4 308 = ((D : ZMod j) * ((cntPre N k x + (if 1 / 2 ^ k = x then 1 else 0) : ℕ) : ZMod j)).val := by
    rw [vw_lt (by norm_num), dfr 308 (by norm_num) (by simp [WD]) (by norm_num), c308]; congr 2
    rw [cntAll, hsplit]
  have hval : eval (vw t4) t4.ar flagE = vw t4 301 + (if ¬ j ∣ D * cntPre N k x then 1 else 0) := by
    rw [flagE, eval_ifEq]
    simp only [Ex.eval, m3, d3, hc1, r308]
    by_cases hdv : j ∣ D * cntPre N k x
    · rw [if_pos ((flag_key hm).mpr hdv), if_neg (not_not.mpr hdv), add_zero]
    · rw [if_neg (fun h => hdv ((flag_key hm).mp h)), if_pos hdv]
  refine ⟨?_, fun y hy hW => ?_, fun a ha => ?_⟩
  · rw [← vw_lt (show 301 < 1000 by norm_num), v4, Function.update_self, hval, vw_lt (by norm_num),
      f3 301 (by norm_num) (by simp [WC, WP, WL]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
    by_cases hdv : j ∣ D * cntPre N k x
    · rw [if_neg (not_not.mpr hdv), if_neg (fun h => h.2 hdv)]
    · rw [if_pos hdv, if_pos ⟨by omega, hdv⟩]
  · simp only [WM] at hW
    rw [← vw_lt (show y < 1000 by omega), v4, Function.update_of_ne (by omega), vw_lt (by omega),
      f3 y hy (by tauto) (by omega) (by omega) (by omega) (by omega)]
  · rw [a4, ar3 a ha]

/-- The flag count after the moduli `m < j`. -/
def flagCount (D c j : ℕ) : ℕ := ∑ m ∈ range j, if 2 ≤ m ∧ ¬ m ∣ D * c then 1 else 0

/-- The output bit from the flags (the end of `eval_mainE`). -/
theorem bit_of_flags {n D c ML : ℕ} (hD0 : 0 < D) (hDl : D ≤ 2 ^ ML) (hcn : c < 2 ^ n) :
    (if 0 < flagCount D c (2 * (n + ML + 4) + 1) then 0 else 1) = if 0 < c then 0 else 1 := by
  set M := n + ML + 4
  by_cases hc : c = 0
  · have hz : flagCount D c (2 * M + 1) = 0 :=
      Finset.sum_eq_zero fun m _ => by rw [if_neg (fun h => h.2 (by rw [hc, mul_zero]; exact dvd_zero m))]
    rw [hz, if_neg (lt_irrefl 0), if_neg (by omega)]
  · rw [if_pos (Nat.pos_of_ne_zero hc)]
    refine if_pos (Nat.pos_of_ne_zero fun hs => ?_)
    unfold flagCount at hs
    rw [Finset.sum_eq_zero_iff] at hs
    have hall : ∀ m, 1 ≤ m → m ≤ 2 * M → m ∣ D * c := by
      intro m h1 h2
      rcases Nat.lt_or_ge m 2 with h | h
      · rw [show m = 1 by omega]; exact one_dvd _
      · by_contra hnd
        have := hs m (mem_range.mpr (by omega))
        rw [if_pos ⟨h, hnd⟩] at this
        exact one_ne_zero this
    have hlt : (2 * M + 1) * (D * c) < 4 ^ M := by
      have h1 : D * c < 2 ^ (n + ML) := by
        rw [pow_add]
        calc D * c ≤ 2 ^ ML * c := Nat.mul_le_mul_right _ hDl
          _ < 2 ^ ML * 2 ^ n := Nat.mul_lt_mul_of_pos_left hcn (by positivity)
          _ = 2 ^ n * 2 ^ ML := by ring
      have h2 := two_pow_big (n + ML)
      calc (2 * M + 1) * (D * c) < (2 * M + 1) * 2 ^ (n + ML) := Nat.mul_lt_mul_of_pos_left h1 (by omega)
        _ ≤ 2 ^ (n + ML + 8) * 2 ^ (n + ML) := Nat.mul_le_mul_right _ (by simp only [M]; omega)
        _ = 4 ^ M := by
            rw [← pow_add, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]; congr 1; simp only [M]; ring
    have h0 := eq_zero_of_all_dvd (by omega) hall hlt
    rcases Nat.mul_eq_zero.mp h0 with h | h
    · omega
    · exact hc h

set_option maxRecDepth 20000 in
/-- **The output bit of the counting command.** -/
theorem uniC_val (st : St) (hkn : st.sc 2 < st.sc 0) (hN : 2 ≤ numCells (st.ar 0) 1 (st.sc 0))
    (hD : st.ar 1 (st.sc 2) = 0) :
    (Cmd.run (uniC UP) st).1.sc 3 = if 0 < cntPre (numCells (st.ar 0) 1 (st.sc 0)) (st.sc 2)
      (numCells (st.ar 1) (st.sc 2) (st.sc 0 - st.sc 2)) then 0 else 1 := by
  set n := st.sc 0
  set k := st.sc 2
  set ℓ := ellOf n
  set L := Ltop (Kb K0u ℓ) (Gs K0u ℓ) (sOf n)
  set D := deepMult K0u ℓ L
  set c := cntPre (numCells (st.ar 0) 1 n) k (numCells (st.ar 1) k (n - k))
  obtain ⟨s11, s307, s316, s12, s303, s310, stok, sfr, sar⟩ := setup_spec st
  set b1 := (Cmd.run (setup UP) st).1
  obtain ⟨v2, a2, -⟩ := vw_cset (e := mE) (by simp [mE, VB]) (show 314 < 1000 by norm_num) b1
  set b2 := (Cmd.run (cset mE 314) b1).1
  set b3 := (Cmd.run (.setK 301 0) b2).1
  have g3 : ∀ y < 1000, y ≠ 301 → y ≠ 314 → b3.sc y = b1.sc y := fun y hy h1 h2 => by
    simp only [b3, Cmd.run_setK, St.setSc_sc, Function.update_of_ne h1]
    rw [← vw_lt hy, v2, Function.update_of_ne h2, vw_lt hy]
  have ar3 : b3.ar = st.ar := by simp only [b3, Cmd.run_setK, St.setSc_ar]; rw [a2, sar]
  have b0 : b1.sc 0 = n := sfr 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by simp [WS]) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have b2' : b1.sc 2 = k := sfr 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by simp [WS])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have M314 : b3.sc 314 = 2 * (n + mlogN K0u ℓ L + 4) + 1 := by
    simp only [b3, Cmd.run_setK, St.setSc_sc, Function.update_of_ne (show (314 : ℕ) ≠ 301 by norm_num)]
    rw [← vw_lt (show 314 < 1000 by norm_num), v2, Function.update_self]
    simp only [mE, Ex.eval, vw_lt (show 0 < 1000 by norm_num), vw_lt (show 310 < 1000 by norm_num), b0, s310]
    rfl
  -- the moduli loop
  let MI : ℕ → St → Prop := fun j s => s.sc 301 = flagCount D c j ∧
    (∀ y < 990, ¬ WM y → s.sc y = b3.sc y) ∧ (∀ a, a ≠ 3 → s.ar a = b3.ar a)
  have hloop := Cmd.loop_inv (b := 314) (c := 300) (body := modBody UP) (st := b3) MI
    ⟨by simp [b3, Cmd.run_setK, flagCount], fun _ _ _ => rfl, fun _ _ => rfl⟩ (by
      intro j s _ ⟨f301, ffr, far⟩
      have q : ∀ y, y ∈ [11, 0, 2, 307, 316, 12, 303] → s.sc y = b1.sc y := fun y hy => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        rw [ffr y (by omega) (by simp only [WM, WC, WP, WL]; omega), g3 y (by omega) (by omega) (by omega)]
      have sa : ∀ a, a ≠ 3 → s.ar a = st.ar a := fun a ha => by rw [far a ha, ar3]
      obtain ⟨r301, rfr, rar⟩ := modBody_spec s j (n := n) (k := k) (ℓ := ℓ) (by rw [q 11 (by simp), s11])
        (by rw [q 0 (by simp), b0]) (by rw [q 2 (by simp), b2']) hkn (by rw [q 307 (by simp), s307])
        (by rw [q 316 (by simp), s316]) (by rw [q 12 (by simp), s12]) (by rw [q 303 (by simp), s303])
        (fun v k' h => by
          have := topOk_lt h; have := h.1
          rw [ffr v (by omega) (by simp only [WM, WC, WP, WL]; omega), g3 v (by omega) (by omega) (by omega),
            stok v k' h])
        (by rw [sa 0 (by norm_num)]; omega) (by rw [sa 1 (by norm_num)]; exact hD)
      rw [sa 0 (by norm_num), sa 1 (by norm_num)] at r301
      refine ⟨by rw [r301, f301]; simp only [flagCount]; rw [Finset.sum_range_succ], fun y hy hW => by rw [rfr y hy hW, ffr y hy hW],
        fun a ha => by rw [rar a ha, far a ha]⟩)
  rw [M314] at hloop
  obtain ⟨l301, -, -⟩ := hloop
  set b4 := (Cmd.run (.loop 314 300 (modBody UP)) b3).1
  obtain ⟨v5, -, -⟩ := vw_cset (e := Uni.bitE) (by simp [Uni.bitE, VB]) (show 3 < 1000 by norm_num) b4
  have hrun : (Cmd.run (uniC UP) st).1 = (Cmd.run (cset Uni.bitE 3) b4).1 := by
    simp only [uniC, Cmd.run_seq]; rfl
  rw [hrun, ← vw_lt (show 3 < 1000 by norm_num), v5, Function.update_self, Uni.bitE, eval_ifLt']
  simp only [Ex.eval, vw_lt (show 301 < 1000 by norm_num), l301]
  exact bit_of_flags (deepMult_pos K0u ℓ L) (deepMult_le K0u ℓ L)
    (lt_of_le_of_lt (le_trans (Finset.card_le_card (Finset.filter_subset _ _)) (Nat.card_divisors_le_self _))
      (numCells_lt _ _ _))

end Factoring.Aux
