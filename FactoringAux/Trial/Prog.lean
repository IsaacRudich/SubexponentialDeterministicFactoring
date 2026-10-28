/-
FactoringAux/Trial/Prog.lean — L5: trial division written in `SProg`.

Not audited.

Input `N` on stack 0 (`encodeNat N`, LSB on top, `n` bits).  Numbers are kept in `w = n + 3` bits.
1. `setup`: `NR` := the bits of `N`, MSB on top, padded to `w` bits; `W` := `w` marks;
   `CTR` := `2 ^ ⌈n/2⌉` marks (by doubling); `D` := `2`.
2. `loop CTR body`: while no divisor is recorded, `R := N mod d` (long division, one bit-serial
   subtraction pass per bit of `N`), record `d` if `R = 0`, then `d := d + 1`.
3. `finish`: the answer is the recorded `d`, or `N` if none; strip its leading zeros onto stack 0;
   empty every other stack.
The search tries `d = 2, …, 2^⌈n/2⌉ + 1`, which passes `√N`, so the answer is `Nat.minFac N`
(`minFac 0 = 2` and `minFac 1 = 1` included).
-/
module

public import FactoringAux.SProg.Lib
public import FactoringAux.Trial.Bits

@[expose] public section

namespace Factoring.Aux.Trial

open SProg

/-! Stack names (scoped notations for numerals, so that `simp` decides index (in)equalities). -/
/-- input / output -/
scoped notation "sIO" => (0 : ℕ)
/-- `w` marks (the width) -/
scoped notation "sW" => (1 : ℕ)
/-- `N`, MSB on top, `w` bits -/
scoped notation "sNR" => (2 : ℕ)
/-- the trial divisor `d`, `w` bits -/
scoped notation "sD" => (3 : ℕ)
/-- found flag -/
scoped notation "sFD" => (4 : ℕ)
/-- the recorded divisor -/
scoped notation "sANS" => (5 : ℕ)
/-- the outer counter -/
scoped notation "sCTR" => (6 : ℕ)
/-- `⌈n/2⌉` marks -/
scoped notation "sH" => (7 : ℕ)
/-- toggle, doubling and output temporary -/
scoped notation "sT" => (8 : ℕ)
/-- the remainder -/
scoped notation "sR" => (9 : ℕ)
/-- a counter copy of `W` -/
scoped notation "sCNT" => (10 : ℕ)
/-- `NR` reversed during the division -/
scoped notation "sNT" => (11 : ℕ)
/-- the previous bit of the shifting remainder -/
scoped notation "sPREV" => (12 : ℕ)
/-- the borrow -/
scoped notation "sBOR" => (13 : ℕ)
/-- difference bits -/
scoped notation "sS" => (14 : ℕ)
/-- shifted remainder bits -/
scoped notation "sX" => (15 : ℕ)
/-- `D` reversed -/
scoped notation "sDT" => (16 : ℕ)
/-- zero test / seen flag -/
scoped notation "sZ" => (17 : ℕ)
/-- copy temporary -/
scoped notation "sTMP" => (18 : ℕ)
/-- the carry -/
scoped notation "sCAR" => (19 : ℕ)

/-- Number of stacks. -/
def nStacks : ℕ := 20

/-! ### The division step: `R := (2 R + b) mod d` -/

/-- One iteration of the subtraction pass, on the bit `r` popped from `R`. -/
def bodyDiv (r : Bool) : SProg :=
  readBit sPREV fun x => seq (push sPREV r) (readBit sD fun d => seq (push sDT d)
    (readBit sBOR fun c =>
      seqs [push sS (zbit x d c), push sX x, if bbit x d c then push sBOR true else skip]))

/-- `R := (2 R + b) mod d`, for `R < d`. -/
def divstep (b : Bool) : SProg :=
  seqs [push sPREV b, loop sR (bodyDiv true) (bodyDiv false), clear sPREV, move sDT sD,
    read sBOR (seq (move sX sR) (clear sS)) skip (seq (move sS sR) (clear sX))]

/-- `R := N mod d` (long division over the bits of `NR`, which is restored). -/
def modD : SProg :=
  seqs [copy sW sCNT sTMP, loop sCNT (push sR false) (push sR false),
    loop sNR (seq (push sNT true) (divstep true)) (seq (push sNT false) (divstep false)),
    move sNT sNR]

/-- If `R = 0`: set the found flag and record `d`.  Empties `R`. -/
def testZ : SProg :=
  seqs [loop sR (push sZ true) skip,
    read sZ (clear sZ) skip (seq (push sFD true) (copy sD sANS sTMP))]

/-- One iteration of the increment, on the bit `x` popped from `D`. -/
def incBody (x : Bool) : SProg :=
  readBit sCAR fun c => seq (push sDT (xor x c)) (if x && c then push sCAR true else skip)

/-- `d := d + 1`. -/
def incD : SProg :=
  seqs [push sCAR true, loop sD (incBody true) (incBody false), move sDT sD, clear sCAR]

/-- One turn of the main loop: nothing once a divisor is recorded. -/
def body : SProg :=
  read sFD (push sFD true) skip (seqs [modD, testZ, incD])

/-! ### Setup and output -/

/-- On each input bit: keep it (MSB will be on top of `NR`), count it in `W`, and count every
other bit in `H` (toggle `T`). -/
def bodyIn (x : Bool) : SProg :=
  seqs [push sNR x, push sW true, read sT skip skip (seq (push sT true) (push sH true))]

/-- Double the counter `CTR`. -/
def dbl : SProg :=
  seq (loop sCTR (seq (push sT true) (push sT true)) (seq (push sT true) (push sT true)))
    (move sT sCTR)

/-- Read the input: `NR`, `W`, `H`; pad `NR` and `W` by three; `CTR := 1`. -/
def setupA : SProg :=
  seqs [loop sIO (bodyIn true) (bodyIn false), clear sT,
    push sNR false, push sNR false, push sNR false, push sW true, push sW true, push sW true,
    push sCTR true]

/-- `CTR := 2 ^ H`. -/
def setupB : SProg := loop sH dbl dbl

/-- `D := 2` in `w` bits. -/
def setupC : SProg :=
  seqs [copy sW sCNT sTMP, loop sCNT (push sD false) (push sD false),
    pop sD, pop sD, push sD true, push sD false]

def setup : SProg := seqs [setupA, setupB, setupC]

/-- Output: answer `N` if nothing was recorded; strip leading zeros onto stack 0; clean up. -/
def finish : SProg :=
  seqs [read sFD (clear sNR) skip (move sNR sANS), move sANS sT,
    loop sT (seqs [clear sZ, push sZ true, push sIO true])
      (read sZ (seq (push sZ true) (push sIO false)) skip skip),
    clear sZ, clear sW, clear sD]

/-- Trial division. -/
def trialProg : SProg :=
  seqs [setup, loop sCTR body body, finish]

end Factoring.Aux.Trial

namespace Factoring.Aux.Trial

theorem trialProg_WF : trialProg.WF = true := by decide

theorem trialProg_stacks : trialProg.StacksBelow nStacks = true := by decide

end Factoring.Aux.Trial
