/-
FactoringAux/Trial/Bits.lean — bit lists for trial division: values, fixed-width encodings, Mathlib's
`encodeNat`, and the bit-serial subtraction and increment used by the stack routines.

Not audited.

Conventions: an LSB-first list `l` has value `valL l`; `bitsW w x` is `x mod 2^w` in exactly `w`
bits, LSB first; `valFrom v ms` reads an MSB-first list `ms` after the prefix value `v`.
-/
module

public import Mathlib.Computability.Encoding
public import Mathlib.Data.Num.Lemmas
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace Factoring.Aux.Trial

open Computability

/-! ### Values of bit lists -/

/-- Value of an LSB-first bit list. -/
def valL : List Bool → ℕ
  | [] => 0
  | b :: l => b.toNat + 2 * valL l

@[simp] theorem valL_nil : valL [] = 0 := rfl
@[simp] theorem valL_cons (b : Bool) (l : List Bool) : valL (b :: l) = b.toNat + 2 * valL l := rfl

theorem valL_lt : ∀ l : List Bool, valL l < 2 ^ l.length
  | [] => by simp
  | b :: l => by
      have := valL_lt l
      have hb := Bool.toNat_le b
      simp only [valL_cons, List.length_cons, pow_succ]
      omega

/-- `x mod 2^w`, in `w` bits, LSB first. -/
def bitsW : ℕ → ℕ → List Bool
  | 0, _ => []
  | w + 1, x => (x % 2 == 1) :: bitsW w (x / 2)

@[simp] theorem bitsW_zero (x : ℕ) : bitsW 0 x = [] := rfl
theorem bitsW_succ (w x : ℕ) : bitsW (w + 1) x = (x % 2 == 1) :: bitsW w (x / 2) := rfl

@[simp] theorem length_bitsW : ∀ w x, (bitsW w x).length = w
  | 0, _ => rfl
  | w + 1, x => by simp [bitsW_succ, length_bitsW w]

theorem toNat_mod_two (x : ℕ) : (x % 2 == 1).toNat = x % 2 := by
  rcases Nat.mod_two_eq_zero_or_one x with h | h <;> simp [h]

theorem valL_bitsW : ∀ w x, valL (bitsW w x) = x % 2 ^ w
  | 0, x => by simp [Nat.mod_one]
  | w + 1, x => by
      rw [bitsW_succ, valL_cons, valL_bitsW w, toNat_mod_two, pow_succ, Nat.mul_comm (2 ^ w) 2,
        Nat.mod_mul]

theorem bitsW_valL : ∀ l : List Bool, bitsW l.length (valL l) = l
  | [] => rfl
  | b :: l => by
      rw [List.length_cons, bitsW_succ, valL_cons]
      have h1 : (b.toNat + 2 * valL l) % 2 = b.toNat := by
        have := Bool.toNat_le b; omega
      have h2 : (b.toNat + 2 * valL l) / 2 = valL l := by
        have := Bool.toNat_le b; omega
      rw [h1, h2, bitsW_valL l]
      cases b <;> rfl

theorem bitsW_eq_of_valL {w x : ℕ} {l : List Bool} (hl : l.length = w) (hv : valL l = x) :
    l = bitsW w x := by
  subst hl hv; exact (bitsW_valL l).symm

theorem bitsW_mod (w x : ℕ) : bitsW w (x % 2 ^ w) = bitsW w x := by
  have := bitsW_valL (bitsW w x)
  rw [length_bitsW, valL_bitsW] at this
  exact this

/-! ### MSB-first values -/

/-- Value of an MSB-first list read after a prefix of value `v`. -/
def valFrom : ℕ → List Bool → ℕ
  | v, [] => v
  | v, b :: l => valFrom (2 * v + b.toNat) l

theorem valFrom_append_single (v : ℕ) (b : Bool) :
    ∀ l : List Bool, valFrom v (l ++ [b]) = 2 * valFrom v l + b.toNat := by
  intro l
  induction l generalizing v with
  | nil => rfl
  | cons a l ih => exact ih _

theorem valFrom_reverse : ∀ (l : List Bool) (v : ℕ), valFrom v l.reverse = 2 ^ l.length * v + valL l
  | [], v => by simp [valFrom]
  | b :: l, v => by
      rw [List.reverse_cons, valFrom_append_single, valFrom_reverse l, List.length_cons, valL_cons,
        pow_succ]
      ring

theorem valFrom_falses (v : ℕ) (l : List Bool) :
    valFrom v (false :: l) = valFrom (2 * v) l := by simp [valFrom]

/-! ### Mathlib's `encodeNat` -/

theorem encodeNum_bit1 (m : Num) : encodeNum (Num.bit1 m) = true :: encodeNum m := by
  cases m <;> rfl

theorem encodeNum_bit0 (m : Num) :
    encodeNum (Num.bit0 m) = if m = 0 then [] else false :: encodeNum m := by
  cases m
  · rfl
  · simp only [Num.bit0, encodeNum, encodePosNum, reduceCtorEq, if_false]

theorem encodeNat_eq_nil_iff (n : ℕ) : encodeNat n = [] ↔ n = 0 := by
  constructor
  · intro h
    have := decode_encodeNat n
    rw [h] at this
    rw [← this]; rfl
  · rintro rfl; rfl

theorem encodeNat_bit (b : Bool) (n : ℕ) :
    encodeNat (Nat.bit b n) = if b = false ∧ n = 0 then [] else b :: encodeNat n := by
  unfold encodeNat
  rw [← Num.ofNat'_eq, Num.ofNat'_bit, ← Num.ofNat'_eq n]
  cases b
  · simp only [cond_false, encodeNum_bit0, true_and]
    by_cases hn : n = 0
    · subst hn; simp
    · have : Num.ofNat' n ≠ 0 := by
        rw [Num.ofNat'_eq]; exact_mod_cast hn
      simp [this, hn]
  · simp [encodeNum_bit1]

/-- `encodeNat` of `2 n + b`. -/
theorem encodeNat_two_mul_add (b : Bool) (n : ℕ) :
    encodeNat (2 * n + b.toNat) = if b = false ∧ n = 0 then [] else b :: encodeNat n := by
  rw [← encodeNat_bit]; congr 1; cases b <;> simp [Nat.bit] <;> ring

theorem valL_encodeNat (n : ℕ) : valL (encodeNat n) = n := by
  induction n using Nat.binaryRec with
  | zero => rfl
  | bit b n ih =>
      rw [encodeNat_bit]
      split_ifs with h
      · obtain ⟨rfl, rfl⟩ := h; rfl
      · rw [valL_cons, ih]; cases b <;> simp [Nat.bit] <;> ring

theorem lt_two_pow_length (n : ℕ) : n < 2 ^ (encodeNat n).length := by
  have := valL_lt (encodeNat n); rwa [valL_encodeNat] at this

/-! ### Stripping leading zeros, MSB first (the output routine) -/

/-- What the output loop leaves on the output stack: skip leading `false`s of the MSB-first list,
pushing the rest (`seen` says a `true` was met). -/
def stripAux : Bool → List Bool → List Bool → List Bool
  | _, [], acc => acc
  | _, true :: ms, acc => stripAux true ms (true :: acc)
  | seen, false :: ms, acc => stripAux seen ms (if seen then false :: acc else acc)

theorem stripAux_encodeNat :
    ∀ (ms : List Bool) (v : ℕ), stripAux (decide (0 < v)) ms (encodeNat v) = encodeNat (valFrom v ms)
  | [], v => rfl
  | true :: ms, v => by
      simp only [stripAux, valFrom]
      have h := stripAux_encodeNat ms (2 * v + 1)
      have hpos : decide (0 < 2 * v + 1) = true := by simp
      rw [hpos, show (2 * v + 1) = 2 * v + true.toNat from rfl, encodeNat_two_mul_add] at h
      simpa using h
  | false :: ms, v => by
      simp only [stripAux, valFrom]
      have h := stripAux_encodeNat ms (2 * v + false.toNat)
      rw [encodeNat_two_mul_add] at h
      by_cases hv : v = 0
      · subst hv
        simp only [Nat.mul_zero, Nat.zero_add, Bool.toNat_false, lt_self_iff_false,
          decide_false, Bool.false_eq_true, if_false, and_self, if_true] at h ⊢
        exact h
      · have hpos : decide (0 < v) = true := by simp; omega
        have hpos' : decide (0 < 2 * v + false.toNat) = true := by simp; omega
        rw [hpos'] at h
        rw [hpos]
        simpa [hv] using h

/-! ### Bit-serial subtraction (one pass of the division step) -/

/-- Difference bit of `x - d - c`. -/
def zbit (x d c : Bool) : Bool := xor (xor x d) c

/-- Borrow out of `x - d - c`. -/
def bbit (x d c : Bool) : Bool := (!x && (d || c)) || (x && d && c)

theorem sub_bit (x d c : Bool) :
    (zbit x d c).toNat + d.toNat + c.toNat = x.toNat + 2 * (bbit x d c).toNat := by
  cases x <;> cases d <;> cases c <;> rfl

/-- One pass: the `x` bits are `prev` followed by `rs` shifted (the bit-serial `2 r + prev`), and the
pass subtracts `ds` from them with borrow `c`.  Returns the difference bits, the `x` bits, the last
bit of `rs` (shifted out), and the borrow out. -/
def passSpec : Bool → Bool → List Bool → List Bool → List Bool × List Bool × Bool × Bool
  | prev, c, [], _ => ([], [], prev, c)
  | prev, c, r :: rs, ds =>
      let d := ds.headD false
      let t := passSpec r (bbit prev d c) rs ds.tail
      (zbit prev d c :: t.1, prev :: t.2.1, t.2.2.1, t.2.2.2)

theorem passSpec_length (prev c : Bool) :
    ∀ (rs ds : List Bool), (passSpec prev c rs ds).1.length = rs.length ∧
      (passSpec prev c rs ds).2.1.length = rs.length
  | [], _ => by simp [passSpec]
  | r :: rs, ds => by
      have := passSpec_length r (bbit prev (ds.headD false) c) rs ds.tail
      simp only [passSpec, List.length_cons]
      exact ⟨congrArg (· + 1) this.1, congrArg (· + 1) this.2⟩

/-- The `x` bits are `2 r + prev` with the top bit shifted out. -/
theorem passSpec_x (prev c : Bool) :
    ∀ (rs ds : List Bool), valL (passSpec prev c rs ds).2.1 +
      2 ^ rs.length * (passSpec prev c rs ds).2.2.1.toNat = prev.toNat + 2 * valL rs
  | [], _ => by simp [passSpec]
  | r :: rs, ds => by
      have := passSpec_x r (bbit prev (ds.headD false) c) rs ds.tail
      simp only [passSpec, valL_cons, List.length_cons, pow_succ] at this ⊢
      nlinarith [this]

/-- The difference bits and the borrow. -/
theorem passSpec_sub (prev c : Bool) :
    ∀ (rs ds : List Bool), ds.length = rs.length →
      valL (passSpec prev c rs ds).1 + valL ds + c.toNat =
        valL (passSpec prev c rs ds).2.1 + 2 ^ rs.length * (passSpec prev c rs ds).2.2.2.toNat
  | [], [], _ => by simp [passSpec]
  | r :: rs, d :: ds, h => by
      have := passSpec_sub r (bbit prev d c) rs ds (by simpa using h)
      have hb := sub_bit prev d c
      simp only [passSpec, List.headD_cons, List.tail_cons, valL_cons, List.length_cons,
        pow_succ] at this ⊢
      nlinarith [this, hb]

/-- The division step on values: with `r < d ≤ 2^(w-1)`, the pass on `bitsW w r` and `bitsW w d`
from `prev = b` and no borrow yields `x = 2 r + b`, and the borrow says `x < d`. -/
theorem passSpec_step (w r d : ℕ) (b : Bool) (hw : 1 ≤ w) (hrd : r < d) (hd : d ≤ 2 ^ (w - 1)) :
    let t := passSpec b false (bitsW w r) (bitsW w d)
    t.2.1 = bitsW w (2 * r + b.toNat) ∧ t.1.length = w ∧
      (t.2.2.2 = true → t.2.1 = bitsW w ((2 * r + b.toNat) % d)) ∧
      (t.2.2.2 = false → t.1 = bitsW w ((2 * r + b.toNat) % d)) := by
  intro t
  have hl := passSpec_length b false (bitsW w r) (bitsW w d)
  simp only [length_bitsW] at hl
  have hx := passSpec_x b false (bitsW w r) (bitsW w d)
  have hs := passSpec_sub b false (bitsW w r) (bitsW w d) (by simp)
  simp only [length_bitsW, valL_bitsW] at hx hs
  have hpow : 2 ^ w = 2 * 2 ^ (w - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hr : r < 2 ^ w := by omega
  have hd2 : d < 2 ^ w := by omega
  rw [Nat.mod_eq_of_lt hr] at hx
  rw [Nat.mod_eq_of_lt hd2] at hs
  have hb := Bool.toNat_le b
  -- the shifted-out bit is 0, since 2 r + b < 2^w
  have hlast : t.2.2.1 = false := by
    by_contra hc
    have : t.2.2.1.toNat = 1 := by simpa using hc
    have hv := valL_lt t.2.1
    rw [hl.2] at hv
    change valL t.2.1 + 2 ^ w * t.2.2.1.toNat = _ at hx
    rw [this] at hx
    omega
  have hxv : valL t.2.1 = 2 * r + b.toNat := by
    change valL t.2.1 + 2 ^ w * t.2.2.1.toNat = _ at hx
    rw [hlast] at hx; simp only [Bool.toNat_false, mul_zero, add_zero] at hx; omega
  have hxw : t.2.1 = bitsW w (2 * r + b.toNat) := bitsW_eq_of_valL hl.2 hxv
  refine ⟨hxw, hl.1, fun hc => ?_, fun hc => ?_⟩
  · -- borrow: x < d
    change valL t.1 + d + 0 = valL t.2.1 + 2 ^ w * t.2.2.2.toNat at hs
    rw [hc] at hs
    have hz := valL_lt t.1
    rw [hl.1] at hz
    simp only [Bool.toNat_true, mul_one] at hs
    have hlt : 2 * r + b.toNat < d := by omega
    rw [Nat.mod_eq_of_lt hlt]; exact hxw
  · -- no borrow: x ≥ d, and x < 2 d
    change valL t.1 + d + 0 = valL t.2.1 + 2 ^ w * t.2.2.2.toNat at hs
    rw [hc] at hs
    simp only [Bool.toNat_false, mul_zero, add_zero] at hs
    have hge : d ≤ 2 * r + b.toNat := by omega
    have hmod : (2 * r + b.toNat) % d = 2 * r + b.toNat - d := by
      rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)]
    rw [hmod]
    exact bitsW_eq_of_valL hl.1 (by omega)

/-! ### Bit-serial increment -/

/-- Add the carry `c` to the LSB-first list `ds`: the sum bits and the carry out. -/
def incSpec : Bool → List Bool → List Bool × Bool
  | c, [] => ([], c)
  | c, d :: ds =>
      let t := incSpec (d && c) ds
      (xor d c :: t.1, t.2)

theorem incSpec_val (c : Bool) : ∀ ds : List Bool,
    valL (incSpec c ds).1 + 2 ^ ds.length * (incSpec c ds).2.toNat = valL ds + c.toNat ∧
      (incSpec c ds).1.length = ds.length
  | [] => by simp [incSpec]
  | d :: ds => by
      have := incSpec_val (d && c) ds
      have hb : (xor d c).toNat + 2 * (d && c).toNat = d.toNat + c.toNat := by
        cases d <;> cases c <;> rfl
      simp only [incSpec, valL_cons, List.length_cons, pow_succ] at this ⊢
      refine ⟨?_, by simp [this.2]⟩
      nlinarith [this.1, hb]

theorem incSpec_bitsW (w d : ℕ) (hd : d + 1 < 2 ^ w) :
    (incSpec true (bitsW w d)).1 = bitsW w (d + 1) := by
  have h := incSpec_val true (bitsW w d)
  simp only [length_bitsW, valL_bitsW, Bool.toNat_true] at h
  rw [Nat.mod_eq_of_lt (by omega)] at h
  have hc : (incSpec true (bitsW w d)).2 = false := by
    by_contra hc
    have : (incSpec true (bitsW w d)).2.toNat = 1 := by simpa using hc
    rw [this] at h
    omega
  rw [hc] at h
  exact bitsW_eq_of_valL h.2 (by simpa using h.1)

end Factoring.Aux.Trial
