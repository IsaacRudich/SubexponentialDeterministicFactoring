/-
The multiplication network as expressions: values.

* Values of the constants (`eval_AE`, …), the layer dispatch (`eval_sel_*`), residues modulo `M` (`ZR_mM`, `ZR_sM`,
  `ZR_pw`), digits (`eval_dD`, `eval_dZ`).
* The messages: `faMsg_ZR`, `hat_ZR`, `midMsg_ZR`, `ibMsg_ZR`; **`msg_val`**: the message expression is `mV` at
  every pair of gates.  `lnk_val`, `W_val`.

Not an audit surface.
-/
module

public import FactoringAux.EngineMul

@[expose] public section

namespace Factoring.Aux

open Finset Ex MulEx

variable {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ} {u vs s : ℕ}

theorem upd_lt {σ : ℕ → ℕ} {x y : ℕ} (v : ℕ) (h : y < x) : Function.update σ x v y = σ y :=
  upd_ne v (by omega)

/-! ### Constants -/

section Const

variable (h : σ vs = s)
include h

theorem eval_hE : eval σ A (hE u vs) = ph s := by rw [hE, eval_pow2]; simp [Ex.eval, h, ph]
theorem eval_AE : eval σ A (AE u vs) = pA s := by rw [AE, eval_pow2]; simp [Ex.eval, h, pA]
theorem eval_LLE : eval σ A (LLE u vs) = pL s := by rw [LLE, eval_pow2]; simp [Ex.eval, h, pL]
theorem eval_fwE : eval σ A (fwE u vs) = fw s := by simp [fwE, Ex.eval, eval_LLE h, fw, pm]
theorem eval_ME : eval σ A (ME u vs) = pM s := by
  simp only [ME, Ex.eval, eval_pow2, eval_LLE h, pM, pm]
theorem eval_TLE : eval σ A (TLE u vs) = 2 ^ pL s := by rw [TLE, eval_pow2, eval_LLE h]
theorem eval_PfE : eval σ A (PfE u vs) = 2 ^ fw s := by rw [PfE, eval_pow2, eval_fwE h]
theorem eval_kA (c : ℕ) : eval σ A (kA u vs c) = c * pA s := by simp only [kA, Ex.eval, eval_AE h]

theorem eval_PZE (hvs : vs < u) : eval σ A (PZE u vs) = pZ s := by
  rw [PZE, eval_nprod, eval_AE h, pZ]
  exact pp_congr fun i _ => eval_ME (by rw [upd_lt _ (by omega), h])

theorem eval_PDE (hvs : vs < u) : eval σ A (PDE u vs) = pD s := by
  rw [PDE, eval_nprod, eval_hE h, pD]
  exact pp_congr fun i _ => eval_TLE (by rw [upd_lt _ (by omega), h])

end Const

theorem eval_nprodK {x : ℕ} {n b : Ex} {c : ℕ} (hb : ∀ i, eval (Function.update σ x i) A b = c) :
    eval σ A (nprod x n b) = pp (fun _ => c) (eval σ A n) := by
  rw [eval_nprod]; exact pp_congr fun i _ => hb i

/-! ### The layer dispatch -/

section Sel

variable {v : ℕ} {e0 e1 e2 e3 e4 : Ex} (h : σ vs = s)
include h

theorem eval_sel_faP {r : ℕ} (hr : r < pA s) (hv : σ v = r) : eval σ A (sel u vs v e0 e1 e2 e3 e4) = eval σ A e0 := by
  simp only [sel, eval_ifLt', Ex.eval, eval_kA h, hv]; rw [if_pos (by omega)]

theorem eval_sel_faQ {r : ℕ} (hr : r < pA s) (hv : σ v = pA s + r) :
    eval σ A (sel u vs v e0 e1 e2 e3 e4) = eval σ A e1 := by
  simp only [sel, eval_ifLt', Ex.eval, eval_kA h, hv]; rw [if_neg (by omega), if_pos (by omega)]

theorem eval_sel_mid {r : ℕ} (hr : r < pA s) (hv : σ v = pA s + (pA s + r)) :
    eval σ A (sel u vs v e0 e1 e2 e3 e4) = eval σ A e2 := by
  simp only [sel, eval_ifLt', Ex.eval, eval_kA h, hv]; rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]

theorem eval_sel_ib {r : ℕ} (hr : r < pA s) (hv : σ v = pA s + (pA s + (pA s + r))) :
    eval σ A (sel u vs v e0 e1 e2 e3 e4) = eval σ A e3 := by
  simp only [sel, eval_ifLt', Ex.eval, eval_kA h, hv]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]

theorem eval_sel_carry {r : ℕ} (hv : σ v = pA s + (pA s + (pA s + (pA s + r)))) :
    eval σ A (sel u vs v e0 e1 e2 e3 e4) = eval σ A e4 := by
  simp only [sel, eval_ifLt', Ex.eval, eval_kA h, hv]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

end Sel

/-! ### Residues modulo `M` -/

theorem ZR.val_eq {M v : ℕ} {x : ZMod M} (hv : ZR M v x) : x.val = v := by
  rw [← hv.2, ZMod.val_cast_of_lt hv.1]

theorem ZR_val {M : ℕ} [NeZero M] (x : ZMod M) : ZR M x.val x := ⟨ZMod.val_lt x, ZMod.natCast_zmod_val x⟩

theorem one_lt_pM (s : ℕ) : 1 < pM s := by
  have : 0 < 2 ^ pm s := by positivity
  simp only [pM]; omega

theorem sixteen_lt_pM (s : ℕ) : 16 < pM s := by
  have h1 : 4 ≤ pm s := by unfold pm; have := pL_pos s; omega
  have : 2 ^ 4 ≤ 2 ^ pm s := Nat.pow_le_pow_right (by norm_num) h1
  simp only [pM]; omega

theorem two_pow_pL_lt_pM (s : ℕ) : 2 ^ pL s < pM s := by
  have : 2 ^ pL s ≤ 2 ^ pm s := Nat.pow_le_pow_right (by norm_num) (by unfold pm; omega)
  simp only [pM]; omega

section Res

variable (h : σ vs = s)
include h

theorem ZR_mM {e f : Ex} {x y : ZMod (pM s)} (he : ZR (pM s) (eval σ A e) x) (hf : ZR (pM s) (eval σ A f) y) :
    ZR (pM s) (eval σ A (mM u vs e f)) (x * y) := by
  simp only [mM, Ex.eval, eval_ME h]
  refine ⟨Nat.mod_lt _ (by positivity), ?_⟩
  rw [ZMod.natCast_mod, Nat.cast_mul, he.2, hf.2]

theorem ZR_sM (x : ℕ) {n b : Ex} {N : ℕ} (hn : eval σ A n = N) (F : ℕ → ZMod (pM s))
    (hb : ∀ j < N, ZR (pM s) (eval (Function.update σ x j) A b) (F j)) :
    ZR (pM s) (eval σ A (sM u vs x n b)) (∑ j ∈ range N, F j) := by
  simp only [sM, Ex.eval, eval_ME h, hn, foldSum_eq]
  refine ⟨Nat.mod_lt _ (by positivity), ?_⟩
  rw [ZMod.natCast_mod, Nat.cast_sum]
  exact sum_congr rfl fun j hj => (hb j (mem_range.mp hj)).2

theorem ZR_pw {b : ℕ} (_hb : b < pM s) {e : Ex} {E : ℕ} (he : eval σ A e = E) :
    ZR (pM s) (eval σ A (pw u vs b e)) ((b : ZMod (pM s)) ^ E) := by
  simp only [pw, Ex.eval, eval_ME h, he]
  rcases Nat.eq_zero_or_pos E with h0 | h0
  · subst h0; exact ⟨by simp [foldProd], by simp [foldProd]⟩
  · rw [foldProd_eq _ _ _ h0]
    refine ⟨Nat.mod_lt _ (by positivity), ?_⟩
    rw [ZMod.natCast_mod, Nat.cast_prod, prod_const, card_range]

theorem ZR_pw16 {e : Ex} {E : ℕ} (he : eval σ A e = E) :
    ZR (pM s) (eval σ A (pw u vs 16 e)) ((16 : ZMod (pM s)) ^ E) := by
  have := ZR_pw (A := A) (u := u) h (sixteen_lt_pM s) he
  simpa using this

theorem ZR_pwi {e : Ex} {E : ℕ} (he : eval σ A e = E) :
    ZR (pM s) (eval σ A (pwi u vs e)) (ωi s ^ E) := by
  have := ZR_pw16 (A := A) (u := u) h (e := .mul (.sub (.mul (AE u vs) (AE u vs)) (.lit 1)) e)
    (E := (pA s * pA s - 1) * E) (by simp only [Ex.eval, eval_AE h, he])
  rwa [pow_mul, pA_sq] at this

theorem ZR_tE : ZR (pM s) (eval σ A (tE u vs)) (tInv s) := by
  have := ZR_pw (A := A) (u := u) h (b := 2) (by have := sixteen_lt_pM s; omega)
    (e := .mul (.sub (.mul (.lit 2) (.mul (.lit 4) (LLE u vs))) (.lit 1)) (.add (.mul (.lit 2) (.var vs)) (.lit 2)))
    (E := (2 * pm s - 1) * (2 * s + 2)) (by simp only [Ex.eval, eval_LLE h, h, pm])
  unfold tE; simpa [tInv] using this

theorem eval_dD (hvs : vs < u) {z i : Ex} {I : ℕ} (hi : eval σ A i = I) :
    eval σ A (dD u vs z i) = eval σ A z / pp (fun _ => 2 ^ pL s) I % 2 ^ pL s := by
  simp only [dD, Ex.eval, eval_TLE h]
  rw [eval_nprodK (c := 2 ^ pL s) fun _ => eval_TLE (by rw [upd_lt _ (by omega), h]), hi]

theorem eval_dZ (hvs : vs < u) {z i : Ex} {I : ℕ} (hi : eval σ A i = I) :
    eval σ A (dZ u vs z i) = eval σ A z / pp (fun _ => pM s) I % pM s := by
  simp only [dZ, Ex.eval, eval_ME h]
  rw [eval_nprodK (c := pM s) fun _ => eval_ME (by rw [upd_lt _ (by omega), h]), hi]

end Res

/-! ### The messages -/

section Msg

variable (h : σ vs = s) (hvs : vs < u)
include h hvs

theorem eval_z1E : eval σ A (z1E u vs) = σ (u + 2) / pZ s % pZ s := by
  simp only [z1E, zv, Ex.eval, eval_PZE h hvs]

theorem eval_z2E : eval σ A (z2E u vs) = σ (u + 2) % pZ s := by
  simp only [z2E, zv, Ex.eval, eval_PZE h hvs]

omit hvs in
theorem eval_cyE : eval σ A (cyE u vs) = σ (u + 2) / 2 ^ fw s % pM s := by
  simp only [cyE, zv, Ex.eval, eval_PfE h, eval_ME h]

omit hvs in
theorem eval_ccE : eval σ A (ccE u vs) = σ (u + 2) % 2 ^ fw s := by
  simp only [ccE, zv, Ex.eval, eval_PfE h]

omit hvs in
theorem upd_vs {x : ℕ} (hx : vs < x) (v : ℕ) : Function.update σ x v vs = s := by rw [upd_lt _ hx, h]

theorem faMsg_ZR {va vb : ℕ} (hvb : vb < u + 4) (r : ℕ) (hr : σ va % pA s = r) {k : ℕ}
    (hk : σ vb - 2 * pA s = k) (w : Fin (ph s) → Fin (2 ^ pL s)) (hz : σ (u + 2) = dCode s w) :
    ZR (pM s) (eval σ A (faMsg u vs va vb)) (faV s r w k) := by
  unfold faMsg faV faOut digZ ω16
  refine ZR_mM h (ZR_pw16 h (by simp only [Ex.eval, eval_AE h, eval_kA h, hr, hk])) ?_
  refine ZR_sM h (u + 5) (eval_AE h) _ fun j _ => ?_
  have h' := upd_vs h (show vs < u + 5 by omega) j
  refine ZR_mM h' ?_ (ZR_pw16 h' (by
    simp only [Ex.eval, eval_AE h', eval_kA h', Function.update_self, upd_lt _ (show vb < u + 5 by omega), hk]))
  simp only [Ex.eval, Function.update_self, eval_hE h', ext0]
  by_cases hjh : j < ph s
  · rw [if_pos hjh, dif_pos hjh, eval_dD h' hvs (I := j) (by simp [Ex.eval]), zv, Ex.eval, upd_lt _ (by omega), hz,
      ← dCode_dig s w ⟨j, hjh⟩]
    exact ⟨lt_trans (w _).2 (two_pow_pL_lt_pM s), rfl⟩
  · rw [if_neg hjh, dif_neg hjh]; exact ZR_zero (by positivity)

theorem hat_ZR {zE iE : Ex} (y : Fin (pA s) → ZMod (pM s))
    (hzE : ∀ r, eval (Function.update σ (u + 6) r) A zE = zCode s y) {I : ℕ}
    (hi : ∀ r, eval (Function.update σ (u + 6) r) A iE = I) :
    ZR (pM s) (eval σ A (hat u vs zE iE)) (hatOut (pA s) (ω16 s) (ext0 y) I) := by
  unfold hat hatOut ω16
  refine ZR_sM h (u + 6) (eval_AE h) _ fun j hj => ?_
  have h' := upd_vs h (show vs < u + 6 by omega) j
  refine ZR_mM h' ?_ (ZR_pw16 h' (by simp only [Ex.eval, eval_AE h', Function.update_self, hi]))
  rw [eval_dZ h' hvs (I := j) (by simp [Ex.eval]), hzE, ext0, dif_pos hj, ← zCode_dig s y ⟨j, hj⟩]
  exact ZR_val _

theorem midMsg_ZR {va vb : ℕ} (hvb : vb < u + 4) {k j : ℕ} (hk : σ va - 2 * pA s = k)
    (hj : σ vb - 3 * pA s = j) (z : (Fin (pA s) → ZMod (pM s)) × (Fin (pA s) → ZMod (pM s)))
    (h1 : σ (u + 2) / pZ s % pZ s = zCode s z.1) (h2 : σ (u + 2) % pZ s = zCode s z.2) :
    ZR (pM s) (eval σ A (midMsg u vs va vb)) (midV s k z j) := by
  unfold midMsg midV midOut faOut
  refine ZR_mM h (ZR_pwi h (by simp only [Ex.eval, eval_kA h, hk, hj])) ?_
  refine ZR_sM h (u + 5) (eval_AE h) _ fun i _ => ?_
  have h' := upd_vs h (show vs < u + 5 by omega) i
  have hz6 : ∀ r, Function.update (Function.update σ (u + 5) i) (u + 6) r (u + 2) = σ (u + 2) := fun r => by
    rw [upd_lt _ (by omega), upd_lt _ (by omega)]
  have hi6 : ∀ r, eval (Function.update (Function.update σ (u + 5) i) (u + 6) r) A (.var (u + 5)) = i := fun r => by
    simp only [Ex.eval]; rw [upd_lt _ (by omega), Function.update_self]
  refine ZR_mM h' (ZR_mM h' (hat_ZR h' hvs z.1 (fun r => ?_) hi6) (hat_ZR h' hvs z.2 (fun r => ?_) hi6))
    (ZR_pwi h' (by simp only [Ex.eval, eval_AE h', Function.update_self, upd_lt _ (show vb < u + 5 by omega),
      eval_kA h', hj]))
  · rw [eval_z1E (upd_vs h' (by omega) r) hvs, hz6, h1]
  · rw [eval_z2E (upd_vs h' (by omega) r) hvs, hz6, h2]

theorem ibMsg_ZR {j2 : Ex} {J : ℕ} (hj2 : ∀ r, eval (Function.update σ (u + 6) r) A j2 = J)
    (y : Fin (pA s) → ZMod (pM s)) (hz : σ (u + 2) = zCode s y) :
    ZR (pM s) (eval σ A (ibMsg u vs j2)) (ibV s y J) := by
  unfold ibMsg ibV ibOut hatOut
  refine ZR_mM h (ZR_tE h) (ZR_sM h (u + 6) (eval_AE h) _ fun r hr => ?_)
  have h' := upd_vs h (show vs < u + 6 by omega) r
  refine ZR_mM h' ?_ (ZR_pwi h' (by simp only [Ex.eval, eval_AE h', Function.update_self, hj2]))
  rw [eval_dZ h' hvs (I := r) (by simp [Ex.eval]), zv, Ex.eval, upd_lt _ (by omega), hz, ext0, dif_pos hr,
    ← zCode_dig s y ⟨r, hr⟩]
  exact ZR_val _

/-- **The message expression is the message**, at every pair of gates. -/
theorem msg_val {va vb : ℕ} (_hva : va < u + 4) (hvb : vb < u + 4) (i j : MG (pA s)) (z : mS s i)
    (ha : σ va = MG.enum (pA s) i) (hb : σ vb = MG.enum (pA s) j) (hz : σ (u + 2) = gcode s i z) :
    eval σ A (msg u vs va vb) = mV s i j z := by
  have hA := pA_pos s
  cases i with
  | faP r =>
    have ha' : σ va = r := ha
    rw [msg, eval_sel_faP h r.2 ha']
    cases j with
    | faP r' => rw [eval_sel_faP h r'.2 hb]; rfl
    | faQ r' => rw [eval_sel_faQ h r'.2 hb]; rfl
    | mid k =>
      have hb' : σ vb = pA s + (pA s + k) := hb
      rw [eval_sel_mid h k.2 hb']
      exact ((faMsg_ZR h hvs hvb r (by rw [ha', Nat.mod_eq_of_lt r.2]) (k := k) (by omega) z hz).val_eq).symm
    | ib r' => rw [eval_sel_ib h r'.2 hb]; rfl
    | carry r' => rw [eval_sel_carry h hb]; rfl
  | faQ r =>
    have ha' : σ va = pA s + r := ha
    rw [msg, eval_sel_faQ h r.2 ha']
    cases j with
    | faP r' => rw [eval_sel_faP h r'.2 hb]; rfl
    | faQ r' => rw [eval_sel_faQ h r'.2 hb]; rfl
    | mid k =>
      have hb' : σ vb = pA s + (pA s + k) := hb
      rw [eval_sel_mid h k.2 hb']
      exact ((faMsg_ZR h hvs hvb r (by rw [ha', Nat.add_mod_left, Nat.mod_eq_of_lt r.2]) (k := k) (by omega) z
        hz).val_eq).symm
    | ib r' => rw [eval_sel_ib h r'.2 hb]; rfl
    | carry r' => rw [eval_sel_carry h hb]; rfl
  | mid k =>
    have ha' : σ va = pA s + (pA s + k) := ha
    rw [msg, eval_sel_mid h k.2 ha']
    have h1 : σ (u + 2) / pZ s % pZ s = zCode s z.1 := by rw [hz]; exact mid_dig1 s k z
    have h2 : σ (u + 2) % pZ s = zCode s z.2 := by rw [hz]; exact mid_dig2 s k z
    cases j with
    | faP r =>
      have hb' : σ vb = r := hb
      rw [eval_sel_faP h r.2 hb', eval_dZ h hvs (I := r) (by simp [Ex.eval, hb']), eval_z1E h hvs, h1,
        ← zCode_dig]
      rfl
    | faQ r =>
      have hb' : σ vb = pA s + r := hb
      rw [eval_sel_faQ h r.2 hb', eval_dZ h hvs (I := r) (by simp only [Ex.eval, eval_kA h, hb']; omega),
        eval_z2E h hvs, h2, ← zCode_dig]
      rfl
    | mid r => rw [eval_sel_mid h r.2 hb]; rfl
    | ib j =>
      have hb' : σ vb = pA s + (pA s + (pA s + j)) := hb
      rw [eval_sel_ib h j.2 hb']
      exact ((midMsg_ZR h hvs hvb (k := k) (j := j) (by omega) (by omega) z h1 h2).val_eq).symm
    | carry r => rw [eval_sel_carry h hb]; rfl
  | ib j₁ =>
    have ha' : σ va = pA s + (pA s + (pA s + j₁)) := ha
    have hz' : σ (u + 2) = zCode s z := hz
    rw [msg, eval_sel_ib h j₁.2 ha']
    cases j with
    | faP r => rw [eval_sel_faP h r.2 hb]; rfl
    | faQ r => rw [eval_sel_faQ h r.2 hb]; rfl
    | mid k =>
      have hb' : σ vb = pA s + (pA s + k) := hb
      rw [eval_sel_mid h k.2 hb', eval_dZ h hvs (I := k) (by simp only [Ex.eval, eval_kA h, hb']; omega), zv,
        Ex.eval, hz', ← zCode_dig]
      rfl
    | ib r => rw [eval_sel_ib h r.2 hb]; rfl
    | carry j =>
      have hb' : σ vb = pA s + (pA s + (pA s + (pA s + j))) := hb
      rw [eval_sel_carry h hb', eval_ifEq]
      have e1 : eval σ A (.mod (.sub (.var vb) (kA u vs 4)) (AE u vs)) = j % pA s := by
        simp only [Ex.eval, eval_kA h, eval_AE h, hb']; congr 1; omega
      have e2 : eval σ A (.sub (.var va) (kA u vs 3)) = j₁ := by simp only [Ex.eval, eval_kA h, ha']; omega
      rw [e1, e2]
      show _ = if (j : ℕ) % pA s = j₁ then (ibV s z ((j : ℕ) / pA s)).val else 0
      by_cases hc : (j : ℕ) % pA s = j₁
      · rw [if_pos hc, if_pos hc]
        refine ((ibMsg_ZR h hvs (fun r => ?_) z hz').val_eq).symm
        simp only [Ex.eval, eval_kA (upd_vs h (show vs < u + 6 by omega) r), eval_AE (upd_vs h (show vs < u + 6 by omega) r),
          upd_lt _ (show vb < u + 6 by omega), hb']
        congr 1; omega
      · rw [if_neg hc, if_neg hc]; rfl
  | carry jc =>
    have ha' : σ va = pA s + (pA s + (pA s + (pA s + jc))) := ha
    have hy : eval σ A (cyE u vs) = z.1.val := by rw [eval_cyE h, hz]; exact carry_y s jc z
    have hc : eval σ A (ccE u vs) = z.2 := by rw [eval_ccE h, hz]; exact carry_c s jc z
    have ej : eval σ A (.sub (.var va) (kA u vs 4)) = jc := by simp only [Ex.eval, eval_kA h, ha']; omega
    rw [msg, eval_sel_carry h ha']
    cases j with
    | faP r => rw [eval_sel_faP h r.2 hb]; rfl
    | faQ r => rw [eval_sel_faQ h r.2 hb]; rfl
    | mid r => rw [eval_sel_mid h r.2 hb]; rfl
    | ib j₁ =>
      have hb' : σ vb = pA s + (pA s + (pA s + j₁)) := hb
      rw [eval_sel_ib h j₁.2 hb', eval_ifEq]
      have e1 : eval σ A (.mod (.sub (.var va) (kA u vs 4)) (AE u vs)) = jc % pA s := by
        simp only [Ex.eval, eval_AE h]; rw [← ej]; rfl
      have e2 : eval σ A (.sub (.var vb) (kA u vs 3)) = j₁ := by simp only [Ex.eval, eval_kA h, hb']; omega
      rw [e1, e2, hy]
      rfl
    | carry j'' =>
      have hb' : σ vb = pA s + (pA s + (pA s + (pA s + j''))) := hb
      have ej' : eval σ A (.sub (.var vb) (kA u vs 4)) = j'' := by simp only [Ex.eval, eval_kA h, hb']; omega
      rw [eval_sel_carry h hb', eval_ifEq, eval_ifEq]
      simp only [Ex.eval] at ej ej' ⊢
      simp only [ej, ej', hy, hc, eval_TLE h]
      rfl

end Msg

/-! ### Links and widths -/

section Lnk

variable (h : σ vs = s)
include h

theorem lnk_val (i j : MG (pA s)) (ha : σ u = MG.enum (pA s) i) (hb : σ (u + 1) = MG.enum (pA s) j) :
    eval σ A (lnk u vs) = if mLink s i j then 1 else 0 := by
  cases i with
  | faP r =>
    rw [lnk, eval_sel_faP h r.2 ha]
    cases j with
    | faP r' => rw [eval_sel_faP h r'.2 hb]; rfl
    | faQ r' => rw [eval_sel_faQ h r'.2 hb]; rfl
    | mid k => rw [eval_sel_mid h k.2 hb]; rfl
    | ib r' => rw [eval_sel_ib h r'.2 hb]; rfl
    | carry r' => rw [eval_sel_carry h hb]; rfl
  | faQ r =>
    rw [lnk, eval_sel_faQ h r.2 ha]
    cases j with
    | faP r' => rw [eval_sel_faP h r'.2 hb]; rfl
    | faQ r' => rw [eval_sel_faQ h r'.2 hb]; rfl
    | mid k => rw [eval_sel_mid h k.2 hb]; rfl
    | ib r' => rw [eval_sel_ib h r'.2 hb]; rfl
    | carry r' => rw [eval_sel_carry h hb]; rfl
  | mid k =>
    rw [lnk, eval_sel_mid h k.2 ha]
    cases j with
    | faP r' => rw [eval_sel_faP h r'.2 hb]; rfl
    | faQ r' => rw [eval_sel_faQ h r'.2 hb]; rfl
    | mid k => rw [eval_sel_mid h k.2 hb]; rfl
    | ib r' => rw [eval_sel_ib h r'.2 hb]; rfl
    | carry r' => rw [eval_sel_carry h hb]; rfl
  | ib j₁ =>
    have ha' : σ u = pA s + (pA s + (pA s + j₁)) := ha
    rw [lnk, eval_sel_ib h j₁.2 ha']
    cases j with
    | faP r' => rw [eval_sel_faP h r'.2 hb]; rfl
    | faQ r' => rw [eval_sel_faQ h r'.2 hb]; rfl
    | mid k => rw [eval_sel_mid h k.2 hb]; rfl
    | ib r' => rw [eval_sel_ib h r'.2 hb]; rfl
    | carry j =>
      have hb' : σ (u + 1) = pA s + (pA s + (pA s + (pA s + j))) := hb
      rw [eval_sel_carry h hb', eval_eqE]
      have e1 : eval σ A (.mod (.sub (.var (u + 1)) (kA u vs 4)) (AE u vs)) = j % pA s := by
        simp only [Ex.eval, eval_kA h, eval_AE h, hb']; congr 1; omega
      have e2 : eval σ A (.sub (.var u) (kA u vs 3)) = j₁ := by simp only [Ex.eval, eval_kA h, ha']; omega
      rw [e1, e2]
      by_cases hc : (j : ℕ) % pA s = j₁ <;> simp [hc, mLink]
  | carry jc =>
    have ha' : σ u = pA s + (pA s + (pA s + (pA s + jc))) := ha
    have ej : eval σ A (.sub (.var u) (kA u vs 4)) = jc := by simp only [Ex.eval, eval_kA h, ha']; omega
    rw [lnk, eval_sel_carry h ha']
    cases j with
    | faP r' => rw [eval_sel_faP h r'.2 hb]; rfl
    | faQ r' => rw [eval_sel_faQ h r'.2 hb]; rfl
    | mid k => rw [eval_sel_mid h k.2 hb]; rfl
    | ib j₁ =>
      have hb' : σ (u + 1) = pA s + (pA s + (pA s + j₁)) := hb
      rw [eval_sel_ib h j₁.2 hb', eval_eqE]
      have e1 : eval σ A (.mod (.sub (.var u) (kA u vs 4)) (AE u vs)) = jc % pA s := by
        simp only [Ex.eval, eval_AE h]; rw [← ej]; rfl
      have e2 : eval σ A (.sub (.var (u + 1)) (kA u vs 3)) = j₁ := by
        simp only [Ex.eval, eval_kA h, hb']; omega
      rw [e1, e2]
      by_cases hc : (jc : ℕ) % pA s = j₁ <;> simp [hc, mLink]
    | carry j' =>
      have hb' : σ (u + 1) = pA s + (pA s + (pA s + (pA s + j'))) := hb
      have ej' : eval σ A (.sub (.var (u + 1)) (kA u vs 4)) = j' := by simp only [Ex.eval, eval_kA h, hb']; omega
      rw [eval_sel_carry h hb', eval_ifEq, eval_eqE]
      simp only [Ex.eval] at ej ej' ⊢
      simp only [ej, ej']
      by_cases h1 : (j' : ℕ) = jc + 1
      · rw [if_pos h1]; simp [mLink, h1]
      · by_cases h2 : (jc : ℕ) = j' + 1
        · rw [if_neg h1, if_pos h2]; simp [mLink, h2]
        · rw [if_neg h1, if_neg h2]; simp [mLink, h1, h2]

theorem cE_val (i j : MG (pA s)) (ha : σ u = MG.enum (pA s) i) (hb : σ (u + 1) = MG.enum (pA s) j) :
    eval σ A (cE u vs) = mC s i j := by
  rw [cE, Ex.eval, lnk_val h i j ha hb, eval_fwE h, mC]
  split_ifs <;> simp

end Lnk

/-! ### Weights -/

theorem pp_ind (P : ℕ → Prop) [DecidablePred P] :
    ∀ n, pp (fun i => if P i then 1 else 0) n = if ∀ i < n, P i then 1 else 0
  | 0 => by simp [pp]
  | n + 1 => by
      rw [pp, pp_ind P n]
      by_cases h1 : ∀ i < n, P i
      · by_cases h2 : P n
        · have h3 : ∀ i < n + 1, P i := fun i hi => by
            rcases (show i < n ∨ i = n by omega) with h | h
            · exact h1 i h
            · exact h ▸ h2
          rw [if_pos h1, if_pos h2, if_pos h3]
        · have h3 : ¬ ∀ i < n + 1, P i := fun h' => h2 (h' n (by omega))
          rw [if_neg h2, if_neg h3, mul_zero]
      · have h3 : ¬ ∀ i < n + 1, P i := fun h' => h1 (fun i hi => h' i (by omega))
        rw [if_neg h1, if_neg h3, zero_mul]

theorem mod_two_pow_sum (X : ℕ) : ∀ b, X % 2 ^ b = ∑ t ∈ range b, (X.testBit t).toNat * 2 ^ t
  | 0 => by simp [Nat.mod_one]
  | b + 1 => by
      rw [Nat.mod_pow_succ, sum_range_succ, ← mod_two_pow_sum X b, ← bitN_eq, bitN, mul_comm (2 ^ b)]

theorem dgt_sum (b d i : ℕ) : dgt b d i = ∑ t ∈ range b, (d.testBit (b * i + t)).toNat * 2 ^ t := by
  rw [dgt, mod_two_pow_sum]
  refine sum_congr rfl fun t _ => ?_
  rw [Nat.testBit_div_two_pow, Nat.add_comm t]

theorem toNat_eq_iff {a b : Bool} : a.toNat = b.toNat ↔ a = b := by cases a <;> cases b <;> simp

theorem ind3 (p q1 q2 r1 r2 : Prop) [Decidable p] [Decidable q1] [Decidable q2] [Decidable r1] [Decidable r2] :
    ((if p then 1 else 0) * ((if q1 then (if q2 then 1 else 0) else 1) * (if r1 then (if r2 then 1 else 0) else 1)) : ℕ) =
      if p ∧ (q1 → q2) ∧ (r1 → r2) then 1 else 0 := by
  by_cases hp : p <;> by_cases h1 : q1 <;> by_cases h2 : q2 <;> by_cases h3 : r1 <;> by_cases h4 : r2 <;> simp [*]

section W

variable {n k : ℕ} (h : σ vs = s) (hvs : vs < u) (h2u : 2 < u) (h0 : σ 0 = n) (h2 : σ 2 = k)
include h hvs h2u h0 h2

theorem eval_dgE {j : ℕ} (hj : σ u - 4 * pA s = j) :
    eval σ A (dgE u vs) = dgt (pL s) (numCells (A 0) 1 n) j := by
  rw [dgE, eval_nsum, eval_LLE h, dgt_sum]
  refine sum_congr rfl fun t _ => ?_
  have h' := upd_vs h (show vs < u + 5 by omega) t
  simp only [Ex.eval]
  rw [eval_nBit, eval_pow2]
  simp only [Ex.eval, eval_LLE h', jE, eval_kA h', Function.update_self, upd_lt _ (show u < u + 5 by omega),
    upd_lt _ (show 0 < u + 5 by omega), h0, hj]

theorem eval_faW (r : ℕ) (hr : σ u = r) (w : Fin (ph s) → Fin (2 ^ pL s)) (hz : σ (u + 2) = dCode s w) :
    eval σ A (faW u vs) = if preOK s k (numCells (A 1) k (n - k)) r w then 1 else 0 := by
  set x := numCells (A 1) k (n - k)
  let Q : ℕ → ℕ → Prop := fun i t => ∀ (hi : i < ph s) (_ : t < pL s), k ≤ pL s * (r + pA s * i) + t →
    (w ⟨i, hi⟩ : ℕ).testBit t = x.testBit (pL s * (r + pA s * i) + t - k)
  have inner : ∀ i < ph s, eval (Function.update σ (u + 5) i) A (nprod (u + 6) (LLE u vs)
      (.ifLt (posE u vs) (.var 2) (.lit 1)
        (eqE (.mod (.div (dD u vs (zv u) (.var (u + 5))) (pow2 (u + 4) (.var (u + 6)))) (.lit 2))
          (xBit (.sub (posE u vs) (.var 2)))))) = if ∀ t < pL s, Q i t then 1 else 0 := by
    intro i hi
    have h' := upd_vs h (show vs < u + 5 by omega) i
    rw [eval_nprod, eval_LLE h', ← pp_ind]
    refine pp_congr fun t ht => ?_
    set σ2 := Function.update (Function.update σ (u + 5) i) (u + 6) t
    have h'' : σ2 vs = s := upd_vs h' (by omega) t
    have e5 : σ2 (u + 5) = i := by simp [σ2]
    have e6 : σ2 (u + 6) = t := by simp [σ2]
    have eu : σ2 u = r := by simp only [σ2]; rw [upd_lt _ (by omega), upd_lt _ (by omega), hr]
    have e0 : σ2 0 = n := by simp only [σ2]; rw [upd_lt _ (by omega), upd_lt _ (by omega), h0]
    have e2 : σ2 2 = k := by simp only [σ2]; rw [upd_lt _ (by omega), upd_lt _ (by omega), h2]
    have ez : σ2 (u + 2) = dCode s w := by simp only [σ2]; rw [upd_lt _ (by omega), upd_lt _ (by omega), hz]
    have epos : eval σ2 A (posE u vs) = pL s * (r + pA s * i) + t := by
      simp only [posE, Ex.eval, eval_LLE h'', eval_AE h'', eu, e5, e6]
    have ebit : eval σ2 A (.mod (.div (dD u vs (zv u) (.var (u + 5))) (pow2 (u + 4) (.var (u + 6)))) (.lit 2)) =
        ((w ⟨i, hi⟩ : ℕ).testBit t).toNat := by
      simp only [Ex.eval]
      rw [eval_dD h'' hvs (I := i) (by simp [Ex.eval, e5]), eval_pow2, zv]
      simp only [Ex.eval, ez, e6]
      rw [← dCode_dig s w ⟨i, hi⟩, ← bitN_eq]; rfl
    have ex : eval σ2 A (xBit (.sub (posE u vs) (.var 2))) =
        (x.testBit (pL s * (r + pA s * i) + t - k)).toNat := by
      rw [eval_xBit]; simp only [Ex.eval, epos, e0, e2, x]
    rw [eval_ifLt', epos, eval_eqE, ebit, ex]
    simp only [Ex.eval, e2]
    by_cases hpk : pL s * (r + pA s * i) + t < k
    · rw [if_pos hpk, if_pos (fun _ _ h => absurd h (by omega))]
    · rw [if_neg hpk]
      by_cases hb : (w ⟨i, hi⟩ : ℕ).testBit t = x.testBit (pL s * (r + pA s * i) + t - k)
      · rw [if_pos (by rw [hb]), if_pos (fun _ _ _ => hb)]
      · rw [if_neg (fun h => hb (toNat_eq_iff.mp h)), if_neg (fun h => hb (h hi ht (by omega)))]
  rw [faW, eval_nprod, eval_hE h, pp_congr inner, pp_ind]
  refine if_congr ?_ rfl rfl
  constructor
  · intro H i' t hk
    exact H i' i'.2 t t.2 i'.2 t.2 hk
  · intro H i hi t ht _ _ hk
    exact H ⟨i, hi⟩ ⟨t, ht⟩ hk

end W

/-- **The weight expression is the weight**, at every gate. -/
theorem W_val {m n k : ℕ} (hm : 1 < m) (h : σ vs = s) (hvs : vs < u) (h2u : 2 < u) (h0 : σ 0 = n) (h2 : σ 2 = k)
    (hkn : k ≤ n) (hnL : n ≤ pL s * pL s) (i : MG (pA s)) (z : mS s i) (ha : σ u = MG.enum (pA s) i)
    (hz : σ (u + 2) = gcode s i z) :
    ZR m (eval σ A (sel u vs u (faW u vs) (.lit 1) (.lit 1) (.lit 1) (cW u vs)))
      (mW (R := ZMod m) s (numCells (A 0) 1 n) k (numCells (A 1) k (n - k)) i z) := by
  have hx : numCells (A 1) k (n - k) < 2 ^ (pL s * pL s - k) :=
    lt_of_lt_of_le (numCells_lt _ _ _) (Nat.pow_le_pow_right (by norm_num) (by omega))
  cases i with
  | faP r =>
    have ha' : σ u = r := ha
    rw [eval_sel_faP h r.2 ha', eval_faW h hvs h2u h0 h2 r ha' z hz]
    show ZR m _ (if preOK s k _ r z ∧ ((r : ℕ) = 0 → _ < 2 ^ (pL s * pL s - k)) then 1 else 0)
    rw [if_congr (and_iff_left (fun _ => hx)) rfl rfl]
    exact ZR_ite (ZR_one hm) (ZR_zero (by omega))
  | faQ r => rw [eval_sel_faQ h r.2 ha]; exact ZR_one hm
  | mid r => rw [eval_sel_mid h r.2 ha]; exact ZR_one hm
  | ib r => rw [eval_sel_ib h r.2 ha]; exact ZR_one hm
  | carry j =>
    have ha' : σ u = pA s + (pA s + (pA s + (pA s + j))) := ha
    have hj : σ u - 4 * pA s = j := by omega
    have hy : eval σ A (cyE u vs) = z.1.val := by rw [eval_cyE h, hz]; exact carry_y s j z
    have hc : eval σ A (ccE u vs) = z.2 := by rw [eval_ccE h, hz]; exact carry_c s j z
    have ej : eval σ A (jE u vs) = j := by simp only [jE, Ex.eval, eval_kA h, hj]
    rw [eval_sel_carry h ha', cW]
    simp only [Ex.eval]
    rw [eval_eqE, eval_ifEq, eval_ifEq, eval_eqE, eval_eqE]
    simp only [Ex.eval, hy, hc, ej, eval_TLE h, eval_AE h, eval_dgE h hvs h2u h0 h2 hj, ind3]
    exact ZR_ite (ZR_one hm) (ZR_zero (by omega))

/-! ### The representation -/

theorem sz_val (h : σ vs = s) (hvs : vs < u) (i : MG (pA s)) (ha : σ u = MG.enum (pA s) i) :
    eval σ A (mulNEx u vm vs).sz = gsz s i := by
  cases i with
  | faP r => rw [mulNEx, eval_sel_faP h r.2 ha, eval_PDE h hvs]; rfl
  | faQ r => rw [mulNEx, eval_sel_faQ h r.2 ha, eval_PDE h hvs]; rfl
  | mid r => rw [mulNEx, eval_sel_mid h r.2 ha]; simp only [Ex.eval, eval_PZE h hvs]; rfl
  | ib r => rw [mulNEx, eval_sel_ib h r.2 ha, eval_PZE h hvs]; rfl
  | carry r => rw [mulNEx, eval_sel_carry h ha]; simp only [Ex.eval, eval_ME h, eval_PfE h]; rfl

theorem bnum_bdec_mod (c q : ℕ) : bnum (bdec c q) = q % 2 ^ c := by
  have e : bdec c (q % 2 ^ c) = bdec c q := by
    funext i; simp [bdec, Nat.testBit_mod_two_pow, i.2]
  rw [← e, bnum_bdec (Nat.mod_lt _ (by positivity))]

/-- **The expressions represent the multiplication network with its coding.** -/
theorem mul_rep {m B s n k u vm vs : ℕ} {σ₀ : ℕ → ℕ} {A : ℕ → ℕ → ℕ}
    (hm : 1 < m) (h0 : σ₀ vm = m) (hs : σ₀ vs = s) (hn : σ₀ 0 = n) (hk : σ₀ 2 = k) (hkn : k ≤ n)
    (hnL : n ≤ pL s * pL s) (_hvm : vm < B) (hvs : vs < B) (h2 : 2 < B) (hu : B ≤ u) :
    NRep m vm B σ₀ A (NVars.std u) (mulNEx u vm vs)
      (mulNet s (ZMod m) (numCells (A 0) 1 n) k (numCells (A 1) k (n - k)))
      (mulCoding s m (numCells (A 0) 1 n) k (numCells (A 1) k (n - k))) where
  hm := h0
  sz σ hσ a ha := by
    have h : σ vs = s := (hσ vs hvs).trans hs
    rw [sz_val h (by omega) ((MG.enum (pA s)).symm a) (by rw [Equiv.apply_symm_apply]; exact ha)]
    exact (mulSz_fin s a).symm
  W σ hσ a z ha hz := by
    have h : σ vs = s := (hσ vs hvs).trans hs
    exact W_val hm h (by omega) (by omega) ((hσ 0 (by omega)).trans hn) ((hσ 2 h2).trans hk) hkn hnL
      ((MG.enum (pA s)).symm a) z (by rw [Equiv.apply_symm_apply]; exact ha) hz
  c σ hσ a b _ ha hb := by
    have h : σ vs = s := (hσ vs hvs).trans hs
    exact cE_val h _ _ (by rw [Equiv.apply_symm_apply]; exact ha) (by rw [Equiv.apply_symm_apply]; exact hb)
  l σ hσ a b _ z q ha hb hz hq := by
    have h : σ vs = s := (hσ vs hvs).trans hs
    have ha' : σ u = MG.enum (pA s) ((MG.enum (pA s)).symm a) := by rw [Equiv.apply_symm_apply]; exact ha
    have hb' : σ (u + 1) = MG.enum (pA s) ((MG.enum (pA s)).symm b) := by
      rw [Equiv.apply_symm_apply]; exact hb
    show ZR m _ (if mV s _ _ z = bnum (bdec _ q) then 1 else 0)
    rw [bnum_bdec_mod, mulNEx, eval_eqE, msg_val h (by omega) (by omega) (by omega) _ _ z ha' hb' hz]
    simp only [Ex.eval, eval_pow2, cE_val h _ _ ha' hb']
    rw [show σ (u + 3) = q from hq]
    exact ZR_ite (ZR_one hm) (ZR_zero (by omega))
  r σ hσ a b _ z q ha hb hz hq := by
    have h : σ vs = s := (hσ vs hvs).trans hs
    have ha' : σ u = MG.enum (pA s) ((MG.enum (pA s)).symm a) := by rw [Equiv.apply_symm_apply]; exact ha
    have hb' : σ (u + 1) = MG.enum (pA s) ((MG.enum (pA s)).symm b) := by
      rw [Equiv.apply_symm_apply]; exact hb
    show ZR m _ (if mV s _ _ z = bnum (bdec _ q) then 1 else 0)
    rw [bnum_bdec_mod, mulNEx, eval_eqE, msg_val h (by omega) (by omega) (by omega) _ _ z hb' ha' hz]
    simp only [Ex.eval, eval_pow2, cE_val h _ _ ha' hb']
    rw [show σ (u + 3) = q from hq]
    exact ZR_ite (ZR_one hm) (ZR_zero (by omega))

end Factoring.Aux
