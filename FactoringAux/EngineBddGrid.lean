/-
Value bounds of the row and column networks' expressions (`GridEx.nex P tr`).

* `GridBddHyp`: the hypotheses on `V` (with `DecV` for the decoders).
* **`grid_bdd`**: `NBdd V B σ₀ A (NVars.std P.u) (GridEx.nex P tr) P.g`, for both `tr`.

Not an audit surface.
-/
module

public import FactoringAux.EngineBddDec

@[expose] public section

namespace Factoring.Aux

open Finset Ex SB

/-- The bounds needed by a line network (label width `λ`, grid side `g = P.g`, choice code `cc`). -/
structure GridBddHyp (V m lam cc : ℕ) (P : GP) : Prop where
  /-- The decoders: `1 < m`, `2^(7 tB λ) ≤ V`, `(tB λ + 1) m ≤ V`, `m² ≤ V`, `64 ≤ V`. -/
  dec : DecV V m lam
  /-- The line codes. -/
  hS : 2 ^ (lam * (P.g * (P.g * P.g))) ≤ V
  /-- The widths and offsets. -/
  hW : 2 ^ (3 * (lam * (P.g * P.g))) ≤ V
  /-- The digits of the choice code. -/
  hC : (tB lam + 1) ^ (P.g * P.g * (P.g * P.g)) ≤ V
  /-- The quadruple indices. -/
  hg4 : P.g * P.g * (P.g * P.g) ≤ V
  /-- The choice code. -/
  hcc : cc ≤ V

theorem GridBddHyp.facts {V m lam cc : ℕ} {P : GP} (G : GridBddHyp V m lam cc P) (hg : 0 < P.g) :
    P.g * P.g ≤ V ∧ P.g * (P.g * P.g) ≤ V ∧ 2 ^ lam ≤ V ∧ 64 ≤ V ∧ 7 * tB lam < V ∧ lam + 2 ≤ V ∧ P.g ≤ V := by
  have h1 : P.g * P.g ≤ P.g * P.g * (P.g * P.g) := Nat.le_mul_of_pos_right _ (by positivity)
  have h2 : P.g * (P.g * P.g) ≤ P.g * P.g * (P.g * P.g) :=
    calc P.g * (P.g * P.g) = P.g * P.g * P.g := by ring
      _ ≤ P.g * P.g * (P.g * P.g) := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ hg)
  obtain ⟨hl2, -, hpl, h7, -⟩ := lam_facts G.dec.hD G.dec.h64
  have h3 : P.g ≤ P.g * P.g := Nat.le_mul_of_pos_left _ hg
  exact ⟨le_trans h1 G.hg4, le_trans h2 G.hg4, hpl, G.dec.h64, h7, hl2, le_trans h3 (le_trans h1 G.hg4)⟩

namespace GridEx

variable {V m lam cc : ℕ} {P : GP} {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ}

theorem cube_lt {g w i : ℕ} (hw : w < g * g) (hi : i < g) : w + g * g * i < g * (g * g) := by
  have : g * g * i + g * g ≤ g * g * g := by
    have := Nat.mul_le_mul_left (g * g) (show i + 1 ≤ g by omega); rw [Nat.mul_add, Nat.mul_one] at this; exact this
  rw [show g * (g * g) = g * g * g by ring]; omega

theorem B_slcE (G : GridBddHyp V m lam cc P) (hg : 0 < P.g) (hl : σ P.vl = lam) {Q i w : Ex} (BQ : Bdd V σ A Q)
    (Bi : Bdd V σ A i) (Bw : Bdd V σ A w) (hi : eval σ A i < P.g) (hw : eval σ A w < P.g * P.g) :
    Bdd V σ A (slcE P Q i w) := by
  obtain ⟨hgg, hg3, hpl, h64, -, hl2, hgV⟩ := G.facts hg
  have hc := cube_lt hw hi
  have hgi : P.g * P.g * eval σ A i ≤ P.g * (P.g * P.g) := by omega
  have hpow : 2 ^ (lam * (eval σ A w + P.g * P.g * eval σ A i)) ≤ V :=
    le_trans (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ hc.le)) G.hS
  unfold slcE p2
  refine B_mod (B_div BQ (B_pow2 (B_mul (B_var (by omega)) (B_add Bw (B_mul (B_lit hgg) Bi (by simp only [Ex.eval]; omega))
    (by simp only [Ex.eval]; omega)) ?_) (by omega) ?_)) (B_pow2 (B_var (by omega)) (by omega) (by simp only [Ex.eval, hl]; exact hpl))
  · simp only [Ex.eval, hl]; exact le_trans Nat.lt_two_pow_self.le hpow
  · simp only [Ex.eval, hl]; exact hpow

theorem slcE_lt (hl : σ P.vl = lam) (Q i w : Ex) : eval σ A (slcE P Q i w) < 2 ^ lam := by
  rw [eval_slcE hl]; exact slc_lt _ _ _ _ _

theorem B_ptIE (G : GridBddHyp V m lam cc P) (hg : 0 < P.g) (tr : Bool) {n i : Ex} (Bn : Bdd V σ A n)
    (Bi : Bdd V σ A i) (hn : eval σ A n < P.g) (hi : eval σ A i < P.g) :
    Bdd V σ A (ptIE P tr n i) ∧ eval σ A (ptIE P tr n i) < P.g * P.g := by
  obtain ⟨hgg, -, -, -, -, -, hgV⟩ := G.facts hg
  have hlt := ptI_lt hn hi tr
  rw [eval_ptIE]
  refine ⟨?_, hlt⟩
  have h1 : P.g * eval σ A i < P.g * P.g := Nat.mul_lt_mul_of_pos_left hi hg
  have h2 : P.g * eval σ A n < P.g * P.g := Nat.mul_lt_mul_of_pos_left hn hg
  cases tr
  · exact B_add Bi (B_mul (B_lit (by omega)) Bn (by simp only [Ex.eval]; omega))
      (by simp only [ptI, Bool.false_eq_true, if_false] at hlt; simp only [Ex.eval]; omega)
  · exact B_add Bn (B_mul (B_lit (by omega)) Bi (by simp only [Ex.eval]; omega))
      (by simp only [ptI, if_true] at hlt; simp only [Ex.eval]; omega)

theorem quad_lt {g a b c d : ℕ} (ha : a < g) (hb : b < g) (hc : c < g) (hd : d < g) :
    b + g * a + g * g * (d + g * c) < g * g * (g * g) := by
  have h1 : b + g * a < g * g := by nlinarith
  have h2 : d + g * c < g * g := by nlinarith
  have := cube_lt (g := g * g) (w := b + g * a) (i := d + g * c) (by nlinarith) h2
  nlinarith

theorem B_qIdxE (G : GridBddHyp V m lam cc P) (hg : 0 < P.g) (tr : Bool) {n n' i i' : Ex} (Bn : Bdd V σ A n)
    (Bn' : Bdd V σ A n') (Bi : Bdd V σ A i) (Bi' : Bdd V σ A i') (hn : eval σ A n < P.g) (hn' : eval σ A n' < P.g)
    (hi : eval σ A i < P.g) (hi' : eval σ A i' < P.g) :
    Bdd V σ A (qIdxE P tr n n' i i') ∧ eval σ A (qIdxE P tr n n' i i') < P.g * P.g * (P.g * P.g) := by
  obtain ⟨hgg, -, -, -, -, -, hgV⟩ := G.facts hg
  have h4 := G.hg4
  have p1 : ∀ {a b : Ex}, Bdd V σ A a → Bdd V σ A b → eval σ A a < P.g → eval σ A b < P.g →
      Bdd V σ A (.add b (.mul (.lit P.g) a)) ∧ eval σ A (.add b (.mul (.lit P.g) a)) < P.g * P.g := by
    intro a b Ba Bb ha hb
    have : P.g * eval σ A a + P.g ≤ P.g * P.g := by
      have := Nat.mul_le_mul_left P.g (show eval σ A a + 1 ≤ P.g by omega); rw [Nat.mul_add, Nat.mul_one] at this
      exact this
    refine ⟨B_add Bb (B_mul (B_lit (by omega)) Ba (by simp only [Ex.eval]; omega)) (by simp only [Ex.eval]; omega), ?_⟩
    simp only [Ex.eval]; omega
  rw [eval_qIdxE]
  cases tr
  · obtain ⟨B1, l1⟩ := p1 Bi Bi' hi hi'
    obtain ⟨B2, l2⟩ := p1 Bn Bn' hn hn'
    have hq := quad_lt hi hi' hn hn'
    have hm : P.g * P.g * eval σ A (.add n' (.mul (.lit P.g) n)) < P.g * P.g * (P.g * P.g) := by
      simp only [Ex.eval] at l2 hq ⊢; nlinarith
    refine ⟨B_add B1 (B_mul (B_lit hgg) B2 (by simp only [Ex.eval] at hm ⊢; omega)) ?_, ?_⟩
    · simp only [Ex.eval] at hq ⊢; omega
    · simp only [qIdx, Bool.false_eq_true, if_false]; exact hq
  · obtain ⟨B1, l1⟩ := p1 Bn Bn' hn hn'
    obtain ⟨B2, l2⟩ := p1 Bi Bi' hi hi'
    have hq := quad_lt hn hn' hi hi'
    have hm : P.g * P.g * eval σ A (.add i' (.mul (.lit P.g) i)) < P.g * P.g * (P.g * P.g) := by
      simp only [Ex.eval] at l2 hq ⊢; nlinarith
    refine ⟨B_add B1 (B_mul (B_lit hgg) B2 (by simp only [Ex.eval] at hm ⊢; omega)) ?_, ?_⟩
    · simp only [Ex.eval] at hq ⊢; omega
    · simp only [qIdx, if_true]; exact hq

theorem B_phiDE (G : GridBddHyp V m lam cc P) (hg : 0 < P.g) (hl : σ P.vl = lam) (hc : σ P.vc = cc)
    (hvl : P.vl ≠ P.u + 18) {q : Ex} (Bq : Bdd V σ A q) (hq : eval σ A q < P.g * P.g * (P.g * P.g)) :
    Bdd V σ A (phiDE P q) ∧ eval σ A (phiDE P q) ≤ tB lam := by
  obtain ⟨-, -, -, h64, h7, hl2, -⟩ := G.facts hg
  have BT : ∀ σ' : ℕ → ℕ, σ' P.vl = lam → Bdd V σ' A (.add (tBE P.vl) (.lit 1)) ∧
      eval σ' A (.add (tBE P.vl) (.lit 1)) = tB lam + 1 := fun σ' h' =>
    ⟨B_add (B_tBE h' hl2 (by omega)) (B_lit (by omega)) (by simp only [Ex.eval]; rw [eval_tBE h']; omega),
      by simp only [Ex.eval]; rw [eval_tBE h']⟩
  refine ⟨?_, ?_⟩
  · unfold phiDE
    refine B_mod (B_div (B_var (by rw [hc]; exact G.hcc)) ?_) (BT σ hl).1
    exact B_nprodK (x := P.u + 18) Bq (fun j _ => BT _ (by rw [Function.update_of_ne hvl]; exact hl)) (by omega)
      (le_trans (Nat.pow_le_pow_right (by omega) hq.le) G.hC)
  · rw [eval_phiDE hl hc hvl]; unfold phiD; have := Nat.mod_lt (cc / (tB lam + 1) ^ eval σ A q) (show 0 < tB lam + 1 by omega)
    omega

theorem B_cXE (G : GridBddHyp V m lam cc P) (hg : 0 < P.g) (hl : σ P.vl = lam) (tr : Bool) {i : Ex}
    (Bi : Bdd V σ A i) (hi : eval σ A i ≤ tB lam) :
    Bdd V σ A (cXE P tr i) ∧ eval σ A (cXE P tr i) ≤ 2 * lam := by
  obtain ⟨-, -, -, h64, h7, hl2, -⟩ := G.facts hg
  obtain ⟨-, -, -, -, hl21⟩ := lam_facts G.dec.hD G.dec.h64
  have BT := B_tBE (A := A) hl hl2 (by omega)
  have et := eval_tBE (A := A) hl
  have B2 : Bdd V σ A (.mul (.lit 2) (.var P.vl)) := B_mul (B_lit (by omega)) (B_var (by omega))
    (by simp only [Ex.eval, hl]; omega)
  have B4 : Bdd V σ A (.mul (.lit 4) (tBE P.vl)) := B_mul (B_lit (by omega)) BT (by simp only [Ex.eval]; rw [et]; omega)
  cases tr
  · have B3 : Bdd V σ A (.add (.mul (.lit 4) (tBE P.vl)) (.mul (.lit 3) i)) :=
      B_add B4 (B_mul (B_lit (by omega)) Bi (by simp only [Ex.eval]; omega)) (by simp only [Ex.eval]; rw [et]; omega)
    refine ⟨B_ifLt' B2 B3 (fun _ => B2) (fun _ => B3), ?_⟩
    simp only [cXE, Bool.false_eq_true, if_false, eval_minE]
    simp only [Ex.eval, hl]; omega
  · have B3 : Bdd V σ A (.add (.mul (.lit 4) (tBE P.vl)) (.mul (.lit 3) (.sub (tBE P.vl) i))) :=
      B_add B4 (B_mul (B_lit (by omega)) (B_sub BT Bi) (by simp only [Ex.eval]; rw [et]; omega))
        (by simp only [Ex.eval]; rw [et]; omega)
    refine ⟨B_ifLt' B2 B3 (fun _ => B2) (fun _ => B3), ?_⟩
    simp only [cXE, if_true, eval_minE]
    simp only [Ex.eval, hl]; omega

/-- The width of the pair at slots `(x, y)`. -/
theorem B_cwE (G : GridBddHyp V m lam cc P) (hg : 0 < P.g) (hl : σ P.vl = lam) (hc : σ P.vc = cc)
    (hvl : P.vl ≠ P.u + 18) (tr : Bool) {x y : ℕ} (ha : σ P.u < P.g) (hb : σ (P.u + 1) < P.g) (hx : σ x < P.g)
    (hy : σ y < P.g) : Bdd V σ A (cwE P tr x y) ∧ eval σ A (cwE P tr x y) ≤ 2 * lam := by
  obtain ⟨hgg, -, -, -, -, -, hgV⟩ := G.facts hg
  have v : ∀ z, σ z < P.g → Bdd V σ A (.var z) := fun z hz => B_var (by omega)
  obtain ⟨Bq, lq⟩ := B_qIdxE G hg tr (v _ ha) (v _ hb) (v _ hx) (v _ hy) ha hb hx hy
  obtain ⟨Bp, lp⟩ := B_phiDE G hg hl hc hvl Bq lq
  exact B_cXE G hg hl tr Bp lp

section Line

variable {BT B : ℕ} {σ₀ : ℕ → ℕ} {Tab : Clique (ZMod m) (P.g * P.g) lam}

theorem B_gsz (G : GridBddHyp V m lam cc P) (H : GridHyp m BT B σ₀ A P lam cc Tab) (hσ : Ag B σ₀ σ) :
    Bdd V σ A (GridEx.sz P) := by
  obtain ⟨-, hg3, -, h64, -, hl2, -⟩ := G.facts H.hg
  have hl : σ P.vl = lam := by rw [hσ _ H.hl, H.vl]
  unfold GridEx.sz p2
  exact B_pow2 (B_mul (B_var (by omega)) (B_lit hg3) (by simp only [Ex.eval, hl]; exact le_trans Nat.lt_two_pow_self.le G.hS))
    (by omega) (by simp only [Ex.eval, hl]; exact G.hS)

theorem B_gW (G : GridBddHyp V m lam cc P) (H : GridHyp m BT B σ₀ A P lam cc Tab)
    (hT : TBdd V BT σ₀ A P.vγ P.vΘ P.TE (P.g * P.g)) (tr : Bool) (hσ : Ag B σ₀ σ) (ha : σ P.u < P.g)
    (hz : σ (P.u + 2) ≤ V) : Bdd V σ A (GridEx.W P tr) := by
  have hg := H.hg
  obtain ⟨hgg, hg3, hpl, h64, -, hl2, hgV⟩ := G.facts hg
  have hu := H.hu; have hl := H.hl; have hγB := H.hγB; have hΘB := H.hΘB; have hBT := H.hBT
  have hvm := H.hvm; have hγ := H.hγ; have hΘ := H.hΘ
  have hm := G.dec.hm; have hmm := G.dec.hmm; have hmV := G.dec.mV
  have hmσ : σ P.vm = m := by rw [hσ _ (by omega), H.vm]
  have hlσ : σ P.vl = lam := by rw [hσ _ hl, H.vl]
  have P1 : Bdd V σ A (zprod (P.u + 4) (.lit P.g) P.vm
      (ifEq (slcE P (.var (P.u + 2)) (.var (P.u + 4)) (ptIE P tr (.var P.u) (.var (P.u + 4)))) (.lit 0)
        (.lett P.vγ (ptIE P tr (.var P.u) (.var (P.u + 4)))
          (.lett P.vΘ (.div (.var (P.u + 2)) (p2 P (.mul (.var P.vl) (.mul (.lit (P.g * P.g)) (.var (P.u + 4))))))
            P.TE))
        (.lit 0))) := by
    refine B_zprod (by omega) (by omega) (by omega) (B_lit hgV) fun i hi => ?_
    simp only [Ex.eval] at hi
    set σ1 := Function.update σ (P.u + 4) i
    have l1 : σ1 P.vl = lam := by simp only [σ1]; upd; exact hlσ
    have q1 : σ1 (P.u + 2) ≤ V := by simp only [σ1]; upd; exact hz
    have n1 : σ1 P.u < P.g := by simp only [σ1]; upd; exact ha
    have i1 : σ1 (P.u + 4) = i := by simp only [σ1]; upd
    have Bu : Bdd V σ1 A (.var P.u) := B_var (by omega)
    have Bi : Bdd V σ1 A (.var (P.u + 4)) := B_var (by rw [i1]; omega)
    obtain ⟨Bpt, lpt⟩ := B_ptIE G hg tr Bu Bi n1 (by simp only [Ex.eval]; omega)
    refine B_ifEq (B_slcE G hg l1 (B_var q1) Bi Bpt (by simp only [Ex.eval]; omega) lpt) (B_lit (Nat.zero_le _))
      (B_lett Bpt ?_) (B_lit (Nat.zero_le _))
    set σ2 := Function.update σ1 P.vγ (eval σ1 A (ptIE P tr (.var P.u) (.var (P.u + 4))))
    have l2 : σ2 P.vl = lam := by simp only [σ2]; rw [Function.update_of_ne H.hlγ]; exact l1
    have q2 : σ2 (P.u + 2) ≤ V := by simp only [σ2]; upd; exact q1
    have i2 : σ2 (P.u + 4) = i := by simp only [σ2]; upd; exact i1
    have hc : P.g * P.g * i ≤ P.g * (P.g * P.g) := by
      have := Nat.mul_le_mul_left (P.g * P.g) hi.le; rw [show P.g * (P.g * P.g) = P.g * P.g * P.g by ring]; exact this
    have hpow : 2 ^ (lam * (P.g * P.g * i)) ≤ V :=
      le_trans (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ hc)) G.hS
    unfold p2
    refine B_lett (B_div (B_var q2) (B_pow2 (B_mul (B_var (by omega)) (B_mul (B_lit hgg) (B_var (by rw [i2]; omega))
      (by simp only [Ex.eval, i2]; omega)) (by simp only [Ex.eval, i2, l2]; exact le_trans Nat.lt_two_pow_self.le hpow))
      (by omega) (by simp only [Ex.eval, i2, l2]; exact hpow))) ?_
    set σ3 := Function.update σ2 P.vΘ (eval σ2 A (.div (.var (P.u + 2)) (pow2 (P.u + 19)
      (.mul (.var P.vl) (.mul (.lit (P.g * P.g)) (.var (P.u + 4)))))))
    have a3 : Ag BT σ₀ σ3 := (((hσ.mono hBT).upd (by omega) i).upd hγ _).upd hΘ _
    refine hT σ3 a3 ?_ ?_
    · simp only [σ3, σ2]; rw [Function.update_of_ne H.hγΘ]; simp only [Function.update_self]; exact lpt
    · simp only [σ3, Function.update_self, Ex.eval]; exact le_trans (Nat.div_le_self _ _) q2
  have P2 : Bdd V σ A (zprod (P.u + 4) (.lit P.g) P.vm (zprod (P.u + 5) (.lit P.g) P.vm
      (.ifLt (.var (P.u + 4)) (.var (P.u + 5))
        (ifEq (slcE P (.var (P.u + 2)) (.var (P.u + 4)) (ptIE P tr (.var P.u) (.var (P.u + 5))))
          (slcE P (.var (P.u + 2)) (.var (P.u + 5)) (ptIE P tr (.var P.u) (.var (P.u + 4)))) (.lit 1) (.lit 0))
        (.lit 1)))) := by
    refine B_zprod (by omega) (by omega) (by omega) (B_lit hgV) fun i hi => ?_
    refine B_zprod (by upd; omega) (by upd; omega) (by omega) (B_lit hgV) fun i' hi' => ?_
    simp only [Ex.eval] at hi hi'
    set σ2 := Function.update (Function.update σ (P.u + 4) i) (P.u + 5) i'
    have l2 : σ2 P.vl = lam := by simp only [σ2]; upd; exact hlσ
    have q2 : σ2 (P.u + 2) ≤ V := by simp only [σ2]; upd; exact hz
    have n2 : σ2 P.u < P.g := by simp only [σ2]; upd; exact ha
    have i2 : σ2 (P.u + 4) = i := by simp only [σ2]; upd
    have i2' : σ2 (P.u + 5) = i' := by simp only [σ2]; upd
    have Bu : Bdd V σ2 A (.var P.u) := B_var (by omega)
    have Bi : Bdd V σ2 A (.var (P.u + 4)) := B_var (by rw [i2]; omega)
    have Bi' : Bdd V σ2 A (.var (P.u + 5)) := B_var (by rw [i2']; omega)
    obtain ⟨Bp1, lp1⟩ := B_ptIE G hg tr Bu Bi' n2 (by simp only [Ex.eval]; omega)
    obtain ⟨Bp2, lp2⟩ := B_ptIE G hg tr Bu Bi n2 (by simp only [Ex.eval]; omega)
    exact B_ifLt' Bi Bi' (fun _ => B_ifEq (B_slcE G hg l2 (B_var q2) Bi Bp1 (by simp only [Ex.eval]; omega) lp1)
      (B_slcE G hg l2 (B_var q2) Bi' Bp2 (by simp only [Ex.eval]; omega) lp2) (B_lit (by omega))
      (B_lit (Nat.zero_le _))) (fun _ => B_lit (by omega))
  unfold GridEx.W
  have l1 := lt_zprod (σ := σ) (A := A) (vm := P.vm) (x := P.u + 4) (n := .lit P.g)
    (b := ifEq (slcE P (.var (P.u + 2)) (.var (P.u + 4)) (ptIE P tr (.var P.u) (.var (P.u + 4)))) (.lit 0)
        (.lett P.vγ (ptIE P tr (.var P.u) (.var (P.u + 4)))
          (.lett P.vΘ (.div (.var (P.u + 2)) (p2 P (.mul (.var P.vl) (.mul (.lit (P.g * P.g)) (.var (P.u + 4))))))
            P.TE))
        (.lit 0)) (by omega)
  have l2 := lt_zprod (σ := σ) (A := A) (vm := P.vm) (x := P.u + 4) (n := .lit P.g)
    (b := zprod (P.u + 5) (.lit P.g) P.vm
      (.ifLt (.var (P.u + 4)) (.var (P.u + 5))
        (ifEq (slcE P (.var (P.u + 2)) (.var (P.u + 4)) (ptIE P tr (.var P.u) (.var (P.u + 5))))
          (slcE P (.var (P.u + 2)) (.var (P.u + 5)) (ptIE P tr (.var P.u) (.var (P.u + 4)))) (.lit 1) (.lit 0))
        (.lit 1))) (by omega)
  rw [hmσ] at l1 l2
  exact B_zmul P1 P2 (by omega) (le_trans (Nat.mul_le_mul l1.le l2.le) hmm)

theorem B_gc (G : GridBddHyp V m lam cc P) (H : GridHyp m BT B σ₀ A P lam cc Tab) (tr : Bool) (hσ : Ag B σ₀ σ)
    (ha : σ P.u < P.g) (hb : σ (P.u + 1) < P.g) : Bdd V σ A (GridEx.c P tr) := by
  have hg := H.hg
  obtain ⟨hgg, hg3, hpl, h64, -, hl2, hgV⟩ := G.facts hg
  have hu := H.hu; have hl := H.hl; have hc := H.hc
  have hlσ : σ P.vl = lam := by rw [hσ _ hl, H.vl]
  have hcσ : σ P.vc = cc := by rw [hσ _ hc, H.vc]
  have hW : 3 * (lam * (P.g * P.g)) < V := lt_of_lt_of_le Nat.lt_two_pow_self G.hW
  have e1 : P.g * (P.g * (2 * lam)) = 2 * (lam * (P.g * P.g)) := by ring
  have e2 : P.g * lam ≤ lam * (P.g * P.g) := by
    rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ hg)
  have e3 : P.g * (2 * lam) ≤ 2 * (lam * (P.g * P.g)) := by
    rw [show P.g * (2 * lam) = 2 * (P.g * lam) by ring]; omega
  have inner : ∀ i < P.g, Bdd V (Function.update σ (P.u + 4) i) A (nsum (P.u + 5) (.lit P.g)
      (.ifLt (.var (P.u + 4)) (.var (P.u + 5)) (cwE P tr (P.u + 4) (P.u + 5)) (.lit 0))) ∧
      eval (Function.update σ (P.u + 4) i) A (nsum (P.u + 5) (.lit P.g)
        (.ifLt (.var (P.u + 4)) (.var (P.u + 5)) (cwE P tr (P.u + 4) (P.u + 5)) (.lit 0))) ≤ P.g * (2 * lam) := by
    intro i hi
    have body : ∀ i' < P.g, Bdd V (Function.update (Function.update σ (P.u + 4) i) (P.u + 5) i') A
        (.ifLt (.var (P.u + 4)) (.var (P.u + 5)) (cwE P tr (P.u + 4) (P.u + 5)) (.lit 0)) ∧
        eval (Function.update (Function.update σ (P.u + 4) i) (P.u + 5) i') A
          (.ifLt (.var (P.u + 4)) (.var (P.u + 5)) (cwE P tr (P.u + 4) (P.u + 5)) (.lit 0)) ≤ 2 * lam := by
      intro i' hi'
      obtain ⟨Bw, lw⟩ := B_cwE (A := A) (σ := Function.update (Function.update σ (P.u + 4) i) (P.u + 5) i') G hg
        (by upd; exact hlσ) (by upd; exact hcσ) (by omega) tr (x := P.u + 4) (y := P.u + 5) (by upd; exact ha)
        (by upd; exact hb) (by upd; exact hi) (by upd; exact hi')
      exact ⟨B_ifLt' (B_var (by upd; omega)) (B_var (by upd; omega)) (fun _ => Bw) (fun _ => B_lit (Nat.zero_le _)),
        ifLt_le lw (by simp [Ex.eval])⟩
    refine ⟨B_nsum' (c := 2 * lam) (B_lit hgV) (fun i' hi' => body i' hi') (by simp only [Ex.eval]; omega), ?_⟩
    rw [eval_nsum]
    exact le_trans (Ex.sum_le_card_mul fun i' hi' => (body i' hi').2) (by simp [Ex.eval])
  have Bs := B_nsum' (c := P.g * (2 * lam)) (x := P.u + 4) (σ := σ) (A := A) (B_lit hgV) (fun i hi => inner i hi)
    (by simp only [Ex.eval]; omega)
  have ls : eval σ A (nsum (P.u + 4) (.lit P.g) (nsum (P.u + 5) (.lit P.g)
      (.ifLt (.var (P.u + 4)) (.var (P.u + 5)) (cwE P tr (P.u + 4) (P.u + 5)) (.lit 0)))) ≤ P.g * (P.g * (2 * lam)) := by
    rw [eval_nsum]; exact Ex.sum_le_card_mul fun i hi => (inner i hi).2
  unfold GridEx.c
  exact B_add (B_mul (B_lit hgV) (B_var (by omega)) (by simp only [Ex.eval, hlσ]; omega)) Bs
    (by simp only [Ex.eval, hlσ] at ls ⊢; omega)

theorem B_goffE (G : GridBddHyp V m lam cc P) (hg : 0 < P.g) (hlσ : σ P.vl = lam) (hcσ : σ P.vc = cc)
    (hvl : P.vl < P.u) (hvc : P.vc < P.u) (tr : Bool) (ha : σ P.u < P.g) (hb : σ (P.u + 1) < P.g)
    (hk : σ (P.u + 4) ≤ P.g * P.g) :
    Bdd V σ A (GridEx.offE P tr) ∧ eval σ A (GridEx.offE P tr) ≤ 2 * (lam * (P.g * P.g)) := by
  obtain ⟨hgg, hg3, hpl, h64, -, hl2, hgV⟩ := G.facts hg
  have hW : 3 * (lam * (P.g * P.g)) < V := lt_of_lt_of_le Nat.lt_two_pow_self G.hW
  have hk2 : σ (P.u + 4) * (2 * lam) ≤ 2 * (lam * (P.g * P.g)) := by
    have := Nat.mul_le_mul_right (2 * lam) hk; rw [show P.g * P.g * (2 * lam) = 2 * (lam * (P.g * P.g)) by ring] at this
    exact this
  have body : ∀ j < eval σ A (.var (P.u + 4)), Bdd V (Function.update σ (P.u + 7) j) A
      (.lett (P.u + 8) (.mod (.div (.var (P.u + 7)) (.lit P.g)) (.lit P.g))
        (.lett (P.u + 9) (.mod (.var (P.u + 7)) (.lit P.g))
          (.ifLt (.var (P.u + 8)) (.var (P.u + 9)) (cwE P tr (P.u + 8) (P.u + 9)) (.lit 0)))) ∧
      eval (Function.update σ (P.u + 7) j) A
      (.lett (P.u + 8) (.mod (.div (.var (P.u + 7)) (.lit P.g)) (.lit P.g))
        (.lett (P.u + 9) (.mod (.var (P.u + 7)) (.lit P.g))
          (.ifLt (.var (P.u + 8)) (.var (P.u + 9)) (cwE P tr (P.u + 8) (P.u + 9)) (.lit 0)))) ≤ 2 * lam := by
    intro j hj
    simp only [Ex.eval] at hj
    have hjV : j ≤ V := by omega
    set σ1 := Function.update σ (P.u + 7) j
    have e1 : eval σ1 A (.mod (.div (.var (P.u + 7)) (.lit P.g)) (.lit P.g)) = j / P.g % P.g := by
      simp only [Ex.eval, σ1]; upd
    set σ2 := Function.update σ1 (P.u + 8) (eval σ1 A (.mod (.div (.var (P.u + 7)) (.lit P.g)) (.lit P.g)))
    have e2 : eval σ2 A (.mod (.var (P.u + 7)) (.lit P.g)) = j % P.g := by simp only [Ex.eval, σ2, σ1]; upd
    set σ3 := Function.update σ2 (P.u + 9) (eval σ2 A (.mod (.var (P.u + 7)) (.lit P.g)))
    have v8 : σ3 (P.u + 8) < P.g := by simp only [σ3]; upd; simp only [σ2]; upd; rw [e1]; exact Nat.mod_lt _ hg
    have v9 : σ3 (P.u + 9) < P.g := by simp only [σ3]; upd; rw [e2]; exact Nat.mod_lt _ hg
    obtain ⟨Bw, lw⟩ := B_cwE (A := A) (σ := σ3) G hg (by simp only [σ3, σ2, σ1]; upd; exact hlσ)
      (by simp only [σ3, σ2, σ1]; upd; exact hcσ) (by omega) tr (x := P.u + 8) (y := P.u + 9)
      (by simp only [σ3, σ2, σ1]; upd; exact ha) (by simp only [σ3, σ2, σ1]; upd; exact hb) v8 v9
    have hj7 : σ1 (P.u + 7) ≤ V := by simp only [σ1]; upd; exact hjV
    refine ⟨B_lett (B_mod (B_div (B_var hj7) (B_lit hgV)) (B_lit hgV))
      (B_lett (B_mod (B_var (by upd; exact hj7)) (B_lit hgV))
        (B_ifLt' (B_var (le_trans v8.le hgV)) (B_var (le_trans v9.le hgV)) (fun _ => Bw)
          (fun _ => B_lit (Nat.zero_le _)))), ?_⟩
    rw [eval_lett, eval_lett]
    exact ifLt_le lw (by simp [Ex.eval])
  unfold GridEx.offE
  refine ⟨B_nsum' (c := 2 * lam) (B_var (by omega)) body (by simp only [Ex.eval]; omega), ?_⟩
  rw [eval_nsum]
  exact le_trans (Ex.sum_le_card_mul fun j hj => (body j hj).2) (by simp only [Ex.eval]; omega)

theorem B_gF (G : GridBddHyp V m lam cc P) (H : GridHyp m BT B σ₀ A P lam cc Tab) (tr : Bool) (nE fac : Ex)
    (hσ : Ag B σ₀ σ) (hab : σ P.u < σ (P.u + 1)) (hb : σ (P.u + 1) < P.g) (hz : σ (P.u + 2) ≤ V)
    (hq : σ (P.u + 3) ≤ V)
    (hn : ∀ σ', (∀ y, y < P.u + 2 → σ' y = σ y) → Bdd V σ' A nE ∧ eval σ' A nE < P.g)
    (hfac : ∀ σ', σ' P.vm = m → σ' P.vl = lam → σ' (P.u + 10) ≤ tB lam → σ' (P.u + 11) < 2 ^ lam →
      σ' (P.u + 12) < 2 ^ lam → σ' (P.u + 13) ≤ V → Bdd V σ' A fac) :
    Bdd V σ A (GridEx.F P tr nE fac) := by
  have hg := H.hg
  obtain ⟨hgg, hg3, hpl, h64, -, hl2, hgV⟩ := G.facts hg
  have hu := H.hu; have hl := H.hl; have hc := H.hc; have hvm := H.hvm; have hBT := H.hBT
  have hm := G.dec.hm; have hmm := G.dec.hmm; have hmV := G.dec.mV
  have hmσ : σ P.vm = m := by rw [hσ _ (by omega), H.vm]
  have hlσ : σ P.vl = lam := by rw [hσ _ hl, H.vl]
  have hcσ : σ P.vc = cc := by rw [hσ _ hc, H.vc]
  have hW : 3 * (lam * (P.g * P.g)) < V := lt_of_lt_of_le Nat.lt_two_pow_self G.hW
  have e2 : P.g * lam ≤ lam * (P.g * P.g) := by
    rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ hg)
  have hpow : ∀ x, x ≤ 3 * (lam * (P.g * P.g)) → 2 ^ x ≤ V := fun x hx =>
    le_trans (Nat.pow_le_pow_right (by norm_num) hx) G.hW
  have P1 : Bdd V σ A (zprod (P.u + 4) (.lit P.g) P.vm
      (ifEq (slcE P (.var (P.u + 2)) (.var (P.u + 4)) (ptIE P tr nE (.var (P.u + 4))))
        (.mod (.div (.var (P.u + 3)) (p2 P (.mul (.var P.vl) (.var (P.u + 4))))) (p2 P (.var P.vl))) (.lit 1) (.lit 0))) := by
    refine B_zprod (by omega) (by omega) (by omega) (B_lit hgV) fun i hi => ?_
    simp only [Ex.eval] at hi
    set σ1 := Function.update σ (P.u + 4) i
    have e1 : ∀ v, v < P.u + 4 → σ1 v = σ v := fun v hv => by simp only [σ1]; upd
    have i1 : σ1 (P.u + 4) = i := by simp [σ1]
    have l1 : σ1 P.vl = lam := by rw [e1 _ (by omega), hlσ]
    obtain ⟨Bn, ln⟩ := hn σ1 fun y hy => e1 y (by omega)
    have Bi : Bdd V σ1 A (.var (P.u + 4)) := B_var (by rw [i1]; omega)
    obtain ⟨Bpt, lpt⟩ := B_ptIE G hg tr Bn Bi ln (by simp only [Ex.eval, i1]; exact hi)
    have hli : lam * i ≤ 3 * (lam * (P.g * P.g)) := by
      have := Nat.mul_le_mul_left lam (show i ≤ P.g * P.g by nlinarith); omega
    unfold p2
    exact B_ifEq (B_slcE G hg l1 (B_var (by rw [e1 _ (by omega)]; exact hz)) Bi Bpt (by simp only [Ex.eval, i1]; exact hi) lpt)
      (B_mod (B_div (B_var (by rw [e1 _ (by omega)]; exact hq)) (B_pow2 (B_mul (B_var (by rw [l1]; omega)) Bi
        (by simp only [Ex.eval, l1, i1]; exact le_trans Nat.lt_two_pow_self.le (hpow _ hli))) (by omega)
        (by simp only [Ex.eval, l1, i1]; exact hpow _ hli)))
        (B_pow2 (B_var (by rw [l1]; omega)) (by omega) (by simp only [Ex.eval, l1]; exact hpl)))
      (B_lit (by omega)) (B_lit (Nat.zero_le _))
  have P2 : Bdd V σ A (zprod (P.u + 4) (.lit (P.g * P.g)) P.vm
      (.lett (P.u + 5) (.mod (.div (.var (P.u + 4)) (.lit P.g)) (.lit P.g))
        (.lett (P.u + 6) (.mod (.var (P.u + 4)) (.lit P.g))
          (.ifLt (.var (P.u + 5)) (.var (P.u + 6))
            (.lett (P.u + 10) (phiDE P (qIdxE P tr (.var P.u) (.var (P.u + 1)) (.var (P.u + 5)) (.var (P.u + 6))))
              (.lett (P.u + 11) (slcE P (.var (P.u + 2)) (.var (P.u + 5)) (ptIE P tr nE (.var (P.u + 6))))
                (.lett (P.u + 12) (slcE P (.var (P.u + 2)) (.var (P.u + 6)) (ptIE P tr nE (.var (P.u + 5))))
                  (.lett (P.u + 13) (.div (.div (.var (P.u + 3)) (p2 P (.mul (.lit P.g) (.var P.vl)))) (p2 P (offE P tr)))
                    fac))))
            (.lit 1))))) := by
    refine B_zprod (by omega) (by omega) (by omega) (B_lit hgg) fun k hk => ?_
    simp only [Ex.eval] at hk
    set σ1 := Function.update σ (P.u + 4) k
    have e1 : ∀ v, v < P.u + 4 → σ1 v = σ v := fun v hv => by simp only [σ1]; upd
    have k1 : σ1 (P.u + 4) = k := by simp [σ1]
    refine B_lett (B_mod (B_div (B_var (by rw [k1]; omega)) (B_lit hgV)) (B_lit hgV)) ?_
    rw [show eval σ1 A (.mod (.div (.var (P.u + 4)) (.lit P.g)) (.lit P.g)) = k / P.g % P.g by simp only [Ex.eval, k1]]
    set σ2 := Function.update σ1 (P.u + 5) (k / P.g % P.g)
    have e2' : ∀ v, v < P.u + 5 → σ2 v = σ1 v := fun v hv => by simp only [σ2]; upd
    refine B_lett (B_mod (B_var (by rw [e2' _ (by omega), k1]; omega)) (B_lit hgV)) ?_
    rw [show eval σ2 A (.mod (.var (P.u + 4)) (.lit P.g)) = k % P.g by simp only [Ex.eval, e2' _ (show P.u + 4 < P.u + 5 by omega), k1]]
    set σ3 := Function.update σ2 (P.u + 6) (k % P.g)
    have e3 : ∀ v, v < P.u + 4 → σ3 v = σ v := fun v hv => by simp only [σ3]; upd; rw [e2' v (by omega), e1 v hv]
    have v5 : σ3 (P.u + 5) = k / P.g % P.g := by simp only [σ3, σ2]; upd
    have v6 : σ3 (P.u + 6) = k % P.g := by simp only [σ3]; upd
    have v4 : σ3 (P.u + 4) = k := by simp only [σ3, σ2]; upd; exact k1
    have h5 : k / P.g % P.g < P.g := Nat.mod_lt _ hg
    have h6 : k % P.g < P.g := Nat.mod_lt _ hg
    refine B_ifLt' (B_var (by rw [v5]; omega)) (B_var (by rw [v6]; omega)) (fun hlt => ?_) (fun _ => B_lit (by omega))
    have ha3 : σ3 P.u < P.g := by rw [e3 _ (by omega)]; omega
    have hb3 : σ3 (P.u + 1) < P.g := by rw [e3 _ (by omega)]; exact hb
    obtain ⟨Bq, lq⟩ := B_qIdxE (σ := σ3) (A := A) G hg tr (B_var (by omega)) (B_var (by omega))
      (B_var (by rw [v5]; omega)) (B_var (by rw [v6]; omega)) ha3 hb3 (by simp only [Ex.eval, v5]; exact h5)
      (by simp only [Ex.eval, v6]; exact h6)
    obtain ⟨Bφ, lφ⟩ := B_phiDE G hg (by rw [e3 _ (by omega), hlσ]) (by rw [e3 _ (by omega), hcσ]) (by omega) Bq lq
    refine B_lett Bφ ?_
    set σ4 := Function.update σ3 (P.u + 10) (eval σ3 A (phiDE P (qIdxE P tr (.var P.u) (.var (P.u + 1)) (.var (P.u + 5))
      (.var (P.u + 6)))))
    have e4 : ∀ v, v < P.u + 4 → σ4 v = σ v := fun v hv => by simp only [σ4]; upd; exact e3 v hv
    have w5 : σ4 (P.u + 5) = k / P.g % P.g := by simp only [σ4]; upd; exact v5
    have w6 : σ4 (P.u + 6) = k % P.g := by simp only [σ4]; upd; exact v6
    obtain ⟨Bn4, ln4⟩ := hn σ4 fun y hy => e4 y (by omega)
    obtain ⟨Bp4, lp4⟩ := B_ptIE (σ := σ4) (A := A) G hg tr Bn4 (B_var (by rw [w6]; omega)) ln4
      (by simp only [Ex.eval, w6]; exact h6)
    have l4 : σ4 P.vl = lam := by rw [e4 _ (by omega), hlσ]
    refine B_lett (B_slcE G hg l4 (B_var (by rw [e4 _ (by omega)]; exact hz)) (B_var (by rw [w5]; omega)) Bp4
      (by simp only [Ex.eval, w5]; exact h5) lp4) ?_
    set σ5 := Function.update σ4 (P.u + 11) (eval σ4 A (slcE P (.var (P.u + 2)) (.var (P.u + 5)) (ptIE P tr nE (.var (P.u + 6)))))
    have e5 : ∀ v, v < P.u + 4 → σ5 v = σ v := fun v hv => by simp only [σ5]; upd; exact e4 v hv
    have x5 : σ5 (P.u + 5) = k / P.g % P.g := by simp only [σ5]; upd; exact w5
    have x6 : σ5 (P.u + 6) = k % P.g := by simp only [σ5]; upd; exact w6
    obtain ⟨Bn5, ln5⟩ := hn σ5 fun y hy => e5 y (by omega)
    obtain ⟨Bp5, lp5⟩ := B_ptIE (σ := σ5) (A := A) G hg tr Bn5 (B_var (by rw [x5]; omega)) ln5
      (by simp only [Ex.eval, x5]; exact h5)
    have l5 : σ5 P.vl = lam := by rw [e5 _ (by omega), hlσ]
    refine B_lett (B_slcE G hg l5 (B_var (by rw [e5 _ (by omega)]; exact hz)) (B_var (by rw [x6]; omega)) Bp5
      (by simp only [Ex.eval, x6]; exact h6) lp5) ?_
    set σ6 := Function.update σ5 (P.u + 12) (eval σ5 A (slcE P (.var (P.u + 2)) (.var (P.u + 6)) (ptIE P tr nE (.var (P.u + 5)))))
    have e6 : ∀ v, v < P.u + 4 → σ6 v = σ v := fun v hv => by simp only [σ6]; upd; exact e5 v hv
    have l6 : σ6 P.vl = lam := by rw [e6 _ (by omega), hlσ]
    have k6 : σ6 (P.u + 4) = k := by simp only [σ6, σ5, σ4]; upd; exact v4
    obtain ⟨Boff, loff⟩ := B_goffE (σ := σ6) (A := A) G hg l6 (by rw [e6 _ (by omega), hcσ]) (by omega) (by omega) tr
      (by rw [e6 _ (by omega)]; omega) (by rw [e6 _ (by omega)]; exact hb) (by rw [k6]; omega)
    have hq6 : σ6 (P.u + 3) ≤ V := by rw [e6 _ (by omega)]; exact hq
    unfold p2
    refine B_lett (B_div (B_div (B_var hq6) (B_pow2 (B_mul (B_lit hgV) (B_var (by rw [l6]; omega))
      (by simp only [Ex.eval, l6]; omega)) (by omega) (by simp only [Ex.eval, l6]; exact hpow _ (by omega))))
      (B_pow2 Boff (by omega) (hpow _ (by omega)))) ?_
    set σ7 := Function.update σ6 (P.u + 13) (eval σ6 A (.div (.div (.var (P.u + 3)) (pow2 (P.u + 19) (.mul (.lit P.g) (.var P.vl))))
      (pow2 (P.u + 19) (offE P tr))))
    have e7 : ∀ v, v < P.u + 4 → σ7 v = σ v := fun v hv => by simp only [σ7]; upd; exact e6 v hv
    refine hfac σ7 (by rw [e7 _ (by omega), hmσ]) (by rw [e7 _ (by omega), hlσ]) ?_ ?_ ?_ ?_
    · simp only [σ7, σ6, σ5]; upd; simp only [σ4, Function.update_self]; exact lφ
    · simp only [σ7, σ6]; upd; simp only [σ5, Function.update_self]; exact slcE_lt l4 _ _ _
    · simp only [σ7]; upd; simp only [σ6, Function.update_self]; exact slcE_lt l5 _ _ _
    · simp only [σ7, Function.update_self, Ex.eval]
      exact le_trans (Nat.div_le_self _ _) (le_trans (Nat.div_le_self _ _) hq6)
  unfold GridEx.F
  have l1 := lt_zprod (σ := σ) (A := A) (vm := P.vm) (x := P.u + 4) (n := .lit P.g)
    (b := ifEq (slcE P (.var (P.u + 2)) (.var (P.u + 4)) (ptIE P tr nE (.var (P.u + 4))))
        (.mod (.div (.var (P.u + 3)) (p2 P (.mul (.var P.vl) (.var (P.u + 4))))) (p2 P (.var P.vl))) (.lit 1) (.lit 0))
    (by omega)
  have l2 := lt_zprod (σ := σ) (A := A) (vm := P.vm) (x := P.u + 4) (n := .lit (P.g * P.g))
    (b := .lett (P.u + 5) (.mod (.div (.var (P.u + 4)) (.lit P.g)) (.lit P.g))
        (.lett (P.u + 6) (.mod (.var (P.u + 4)) (.lit P.g))
          (.ifLt (.var (P.u + 5)) (.var (P.u + 6))
            (.lett (P.u + 10) (phiDE P (qIdxE P tr (.var P.u) (.var (P.u + 1)) (.var (P.u + 5)) (.var (P.u + 6))))
              (.lett (P.u + 11) (slcE P (.var (P.u + 2)) (.var (P.u + 5)) (ptIE P tr nE (.var (P.u + 6))))
                (.lett (P.u + 12) (slcE P (.var (P.u + 2)) (.var (P.u + 6)) (ptIE P tr nE (.var (P.u + 5))))
                  (.lett (P.u + 13) (.div (.div (.var (P.u + 3)) (p2 P (.mul (.lit P.g) (.var P.vl)))) (p2 P (offE P tr)))
                    fac))))
            (.lit 1)))) (by omega)
  rw [hmσ] at l1 l2
  exact B_zmul P1 P2 (by omega) (le_trans (Nat.mul_le_mul l1.le l2.le) hmm)

/-- **The row (`tr = false`) and column (`tr = true`) networks: every value is at most `V`.** -/
theorem grid_bdd (G : GridBddHyp V m lam cc P) (H : GridHyp m BT B σ₀ A P lam cc Tab)
    (hT : TBdd V BT σ₀ A P.vγ P.vΘ P.TE (P.g * P.g)) (tr : Bool) :
    NBdd V B σ₀ A (NVars.std P.u) (GridEx.nex P tr) P.g where
  sz σ hσ _ := B_gsz G H hσ
  W σ hσ ha hz := B_gW G H hT tr hσ ha hz
  c σ hσ hab hb := B_gc G H tr hσ (by simp only [NVars.std] at hab hb ⊢; omega) hb
  l σ hσ hab hb hz hq := by
    have hu := H.hu; have hl := H.hl; have hvm := H.hvm; have hBT := H.hBT
    obtain ⟨-, -, -, -, -, -, hgV⟩ := G.facts H.hg
    simp only [NVars.std] at hab hb hz hq
    exact B_gF G H tr _ _ hσ hab hb hz hq
      (fun σ' h' => ⟨B_var (by rw [h' _ (by omega)]; omega), by simp only [Ex.eval]; rw [h' _ (by omega)]; exact hb⟩)
      (fun σ' hm' hl' h10 h11 h12 h13 => B_facLE tr G.dec (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) hm' hl' h10 h11 h12 h13)
  r σ hσ hab hb hz hq := by
    have hu := H.hu; have hl := H.hl; have hvm := H.hvm; have hBT := H.hBT
    obtain ⟨-, -, -, -, -, -, hgV⟩ := G.facts H.hg
    simp only [NVars.std] at hab hb hz hq
    exact B_gF G H tr _ _ hσ hab hb hz hq
      (fun σ' h' => ⟨B_var (by rw [h' _ (by omega)]; omega), by simp only [Ex.eval]; rw [h' _ (by omega)]; omega⟩)
      (fun σ' hm' hl' h10 h11 h12 h13 => B_facRE tr G.dec (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) hm' hl' h10 h11 h12 h13)

end Line

end GridEx

end Factoring.Aux
