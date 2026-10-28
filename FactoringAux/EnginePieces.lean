/-
Lemma 2's factorizations read at codes, for the engine.

* `coefFac_l_succ`, `coefFac_r_succ`: one step of the sequential decoder of `coefFac` (the selector bit of the top
  block is bit `4t + 3j + 3` of the code; its data start at `4t + 3j`, resp. `4t + 3(j−1)` for an expensive block).
* `cfStep` (on numbers `j·m + acc`), **`coefFac_l_fold`**, `coefFac_r_fold`: the left (right) function of
  `coefFac t j` at a code is the result of `t` decoder steps from `j·m + 1` (as an element of `ZMod m`).
* `blk_bdec`: the blocks of a string given by a code `X < 2^λ` are `bdec 3 (X / 2^(3s))`.

Not an audit surface.
-/
module

public import FactoringAux.EngineRep
public import FactoringAux.Pieces

@[expose] public section

namespace Factoring.Aux

open Finset

namespace Fac

variable {R : Type*} [CommSemiring R] {X Y : Type*}

theorem l_add_bdec {a : ℕ} (f g : Fac R X Y a) (x : X) (q : ℕ) :
    (f.add g).l x (bdec (a + 1) q) = if q.testBit a then f.l x (bdec a q) else g.l x (bdec a q) := by
  simp only [add, bdec, Fin.val_last]
  rfl

theorem r_add_bdec {a : ℕ} (f g : Fac R X Y a) (y : Y) (q : ℕ) :
    (f.add g).r y (bdec (a + 1) q) = if q.testBit a then f.r y (bdec a q) else g.r y (bdec a q) := by
  simp only [add, bdec, Fin.val_last]
  rfl

end Fac

section Coef

variable {α β : Type*} (cF : Fac ℤ α β 3) (eF : Fac ℤ α β 6)

/-- One decoder step of `coefFac`, left side. -/
theorem coefFac_l_succ (t j : ℕ) (x : Fin (t + 1) → α) (q : ℕ) :
    (coefFac cF eF (t + 1) j).l x (bdec _ q) =
      if q.testBit (4 * t + 3 * j + 3) then
        (coefFac cF eF t j).l (Fin.init x) (bdec _ q) * cF.l (x (Fin.last t)) (bdec 3 (q / 2 ^ (4 * t + 3 * j)))
      else if j = 0 then 0 else
        (coefFac cF eF t (j - 1)).l (Fin.init x) (bdec _ q) *
          eF.l (x (Fin.last t)) (bdec 6 (q / 2 ^ (4 * t + 3 * (j - 1)))) := by
  rcases j with _ | j
  · simp only [coefFac]
    rw [Fac.l_cast, Fac.bdec_cast, Fac.l_add_bdec, Fac.l_mul_bdec]
    simp [Fac.comp, Fac.zero]
  · simp only [coefFac]
    rw [Fac.l_cast, Fac.bdec_cast, Fac.l_add_bdec, Fac.l_cast, Fac.bdec_cast, Fac.l_mul_bdec, Fac.l_mul_bdec]
    simp only [Fac.comp, Nat.add_one_sub_one, Nat.succ_ne_zero, if_false,
      show 4 * t + 3 * (j + 1) + 3 = 4 * t + 3 * j + 6 by ring]

/-- One decoder step of `coefFac`, right side. -/
theorem coefFac_r_succ (t j : ℕ) (y : Fin (t + 1) → β) (q : ℕ) :
    (coefFac cF eF (t + 1) j).r y (bdec _ q) =
      if q.testBit (4 * t + 3 * j + 3) then
        (coefFac cF eF t j).r (Fin.init y) (bdec _ q) * cF.r (y (Fin.last t)) (bdec 3 (q / 2 ^ (4 * t + 3 * j)))
      else if j = 0 then 0 else
        (coefFac cF eF t (j - 1)).r (Fin.init y) (bdec _ q) *
          eF.r (y (Fin.last t)) (bdec 6 (q / 2 ^ (4 * t + 3 * (j - 1)))) := by
  rcases j with _ | j
  · simp only [coefFac]
    rw [Fac.r_cast, Fac.bdec_cast, Fac.r_add_bdec, Fac.r_mul_bdec]
    simp [Fac.comp, Fac.zero]
  · simp only [coefFac]
    rw [Fac.r_cast, Fac.bdec_cast, Fac.r_add_bdec, Fac.r_cast, Fac.bdec_cast, Fac.r_mul_bdec, Fac.r_mul_bdec]
    simp only [Fac.comp, Nat.add_one_sub_one, Nat.succ_ne_zero, if_false,
      show 4 * t + 3 * (j + 1) + 3 = 4 * t + 3 * j + 6 by ring]

/-- One step of the decoder on numbers `j·m + acc`, for block `s`. -/
def cfAt (m Q : ℕ) (cv ev : ℕ → ℕ → ℕ) (s st : ℕ) : ℕ :=
  if Q.testBit (4 * s + 3 * (st / m) + 3) then
    st / m * m + st % m * cv s (Q / 2 ^ (4 * s + 3 * (st / m))) % m
  else if st / m = 0 then 0 else
    (st / m - 1) * m + st % m * ev s (Q / 2 ^ (4 * s + 3 * (st / m - 1))) % m

/-- The decoder over blocks `t − 1, …, 0`. -/
def cfRun (m Q : ℕ) (cv ev : ℕ → ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, st => st
  | t + 1, st => cfRun m Q cv ev t (cfAt m Q cv ev t st)

/-- The decoder's answer. -/
def cfOut (m st : ℕ) : ℕ := if st / m = 0 then st % m else 0

theorem div_mod_pack {m j r : ℕ} (hm : 0 < m) (hr : r < m) : (j * m + r) / m = j ∧ (j * m + r) % m = r := by
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hm, Nat.div_eq_of_lt hr, zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]

/-- The decoder run is the state fold (block `T − 1 − i` at step `i`). -/
theorem iterF_cfAt (m Q : ℕ) (cv ev : ℕ → ℕ → ℕ) (T st : ℕ) :
    iterF (fun i => cfAt m Q cv ev (T - 1 - i)) st T = cfRun m Q cv ev T st := by
  have : ∀ k ≤ T, cfRun m Q cv ev (T - k) (iterF (fun i => cfAt m Q cv ev (T - 1 - i)) st k) =
      cfRun m Q cv ev T st := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih =>
        intro hk
        rw [← ih (by omega)]
        obtain ⟨r, hr⟩ : ∃ r, T - k = r + 1 := ⟨T - k - 1, by omega⟩
        rw [hr, show T - (k + 1) = r by omega, cfRun]
        show cfRun m Q cv ev r (cfAt m Q cv ev (T - 1 - k) _) = _
        rw [show T - 1 - k = r by omega]
  have h := this T le_rfl
  rwa [Nat.sub_self] at h

/-- **The left function of `coefFac` is the decoder.** -/
theorem coefFac_l_run {m : ℕ} (hm : 0 < m) (Q : ℕ) (x : ℕ → α) (cv ev : ℕ → ℕ → ℕ)
    (hcv : ∀ s Qs, ((cv s Qs : ℕ) : ZMod m) = ((cF.l (x s) (bdec 3 Qs) : ℤ) : ZMod m))
    (hev : ∀ s Qs, ((ev s Qs : ℕ) : ZMod m) = ((eF.l (x s) (bdec 6 Qs) : ℤ) : ZMod m)) :
    ∀ t st, ((cfOut m (cfRun m Q cv ev t st) : ℕ) : ZMod m) =
      ((st % m : ℕ) : ZMod m) * (((coefFac cF eF t (st / m)).l (fun k : Fin t => x k) (bdec _ Q) : ℤ) : ZMod m)
  | 0, st => by
      unfold cfRun cfOut
      rcases h : st / m with _ | j
      · simp [coefFac, Fac.l_cast, Fac.one]
      · simp [coefFac, Fac.zero]
  | t + 1, st => by
      rw [cfRun, coefFac_l_run hm Q x cv ev hcv hev t, coefFac_l_succ]
      simp only [show Fin.init (fun k : Fin (t + 1) => x k) = fun k : Fin t => x k from rfl,
        show (fun k : Fin (t + 1) => x k) (Fin.last t) = x t from rfl]
      unfold cfAt
      by_cases hb : Q.testBit (4 * t + 3 * (st / m) + 3)
      · rw [if_pos hb, if_pos hb]
        obtain ⟨d1, d2⟩ := div_mod_pack (j := st / m) hm (Nat.mod_lt (st % m * cv t (Q / 2 ^ (4 * t + 3 * (st / m)))) hm)
        rw [d1, d2, ZMod.natCast_mod, Nat.cast_mul, hcv, Int.cast_mul]
        ring
      · rw [if_neg hb, if_neg hb]
        by_cases hj : st / m = 0
        · rw [if_pos hj, if_pos hj]
          simp
        · rw [if_neg hj, if_neg hj]
          obtain ⟨d1, d2⟩ := div_mod_pack (j := st / m - 1) hm
            (Nat.mod_lt (st % m * ev t (Q / 2 ^ (4 * t + 3 * (st / m - 1)))) hm)
          rw [d1, d2, ZMod.natCast_mod, Nat.cast_mul, hev, Int.cast_mul]
          ring

/-- The right function of `coefFac` is the decoder. -/
theorem coefFac_r_run {m : ℕ} (hm : 0 < m) (Q : ℕ) (y : ℕ → β) (cv ev : ℕ → ℕ → ℕ)
    (hcv : ∀ s Qs, ((cv s Qs : ℕ) : ZMod m) = ((cF.r (y s) (bdec 3 Qs) : ℤ) : ZMod m))
    (hev : ∀ s Qs, ((ev s Qs : ℕ) : ZMod m) = ((eF.r (y s) (bdec 6 Qs) : ℤ) : ZMod m)) :
    ∀ t st, ((cfOut m (cfRun m Q cv ev t st) : ℕ) : ZMod m) =
      ((st % m : ℕ) : ZMod m) * (((coefFac cF eF t (st / m)).r (fun k : Fin t => y k) (bdec _ Q) : ℤ) : ZMod m)
  | 0, st => by
      unfold cfRun cfOut
      rcases h : st / m with _ | j
      · simp [coefFac, Fac.r_cast, Fac.one]
      · simp [coefFac, Fac.zero]
  | t + 1, st => by
      rw [cfRun, coefFac_r_run hm Q y cv ev hcv hev t, coefFac_r_succ]
      simp only [show Fin.init (fun k : Fin (t + 1) => y k) = fun k : Fin t => y k from rfl,
        show (fun k : Fin (t + 1) => y k) (Fin.last t) = y t from rfl]
      unfold cfAt
      by_cases hb : Q.testBit (4 * t + 3 * (st / m) + 3)
      · rw [if_pos hb, if_pos hb]
        obtain ⟨d1, d2⟩ := div_mod_pack (j := st / m) hm (Nat.mod_lt (st % m * cv t (Q / 2 ^ (4 * t + 3 * (st / m)))) hm)
        rw [d1, d2, ZMod.natCast_mod, Nat.cast_mul, hcv, Int.cast_mul]
        ring
      · rw [if_neg hb, if_neg hb]
        by_cases hj : st / m = 0
        · rw [if_pos hj, if_pos hj]
          simp
        · rw [if_neg hj, if_neg hj]
          obtain ⟨d1, d2⟩ := div_mod_pack (j := st / m - 1) hm
            (Nat.mod_lt (st % m * ev t (Q / 2 ^ (4 * t + 3 * (st / m - 1)))) hm)
          rw [d1, d2, ZMod.natCast_mod, Nat.cast_mul, hev, Int.cast_mul]
          ring

end Coef

end Factoring.Aux
