/-
The multiplication network: a gate network whose good settings are the divisors of `N` with
prescribed high bits.

Parameters (from `Transform.lean`): `A = 2^(s+1)` gates per layer, `T = A·A = 2L` coefficients, digits of
`L = 2^(2s+1)` bits, `h = 2^s` digits per input gate (`L = A·h`), the ring `ZMod (2^m+1)`, `m = 4L`, messages of
`m + 1` bits.  The numbers are `p, q < 2^(L·L)`.

Gates (`MG A`) and their settings (`mS`):
* `faP r`, `faQ r` (`r < A`): the digits `r + A i'` (`i' < h`) of `p`, resp. `q`;
* `mid k₁`: the residues `y_p[r][k₁]`, `y_q[r][k₁]` (`r < A`) it receives;
* `ib j₁`: the residues `z[r'][j₁]` (`r' < A`) it receives;
* `carry j` (`j < T`): the coefficient `c_j` it receives and its incoming carry.
Each gate stores only what it receives; what it sends (`mV`) is computed from its setting: `FA → MID` (`faOut`),
`MID → IB` (`midOut`), `IB → CARRY` (`ibOut`), `CARRY j → CARRY (j+1)` (the carry).  The weights (`mW`): `faP r`
checks the bits of `p` at positions `≥ k` against `x` (and `faP 0` checks `x < 2^(L·L - k)`); `carry j` checks its
digit of `N`, the first carry `0` and the last carry `0`.  All other weights are `1`.

`mulNet R s N k x`: the network (`GNet.toNet`), on `4A + A·A` nodes.

Not an audit surface.
-/
module

public import FactoringAux.Gates
public import FactoringAux.Digits

@[expose] public section

namespace Factoring.Aux

open Finset

instance (m : ℕ) : NeZero (2 ^ m + 1) := ⟨Nat.succ_ne_zero _⟩

/-- The gates of the multiplication network, `A` per layer. -/
inductive MG (A : ℕ) where
  | faP (r : Fin A)
  | faQ (r : Fin A)
  | mid (k : Fin A)
  | ib (j : Fin A)
  | carry (j : Fin (A * A))
  deriving DecidableEq

namespace MG

variable {A : ℕ}

/-- The gates as a sum type. -/
def toSum : MG A → Fin A ⊕ (Fin A ⊕ (Fin A ⊕ (Fin A ⊕ Fin (A * A))))
  | faP r => .inl r
  | faQ r => .inr (.inl r)
  | mid k => .inr (.inr (.inl k))
  | ib j => .inr (.inr (.inr (.inl j)))
  | carry j => .inr (.inr (.inr (.inr j)))

/-- Back from the sum type. -/
def ofSum : Fin A ⊕ (Fin A ⊕ (Fin A ⊕ (Fin A ⊕ Fin (A * A)))) → MG A
  | .inl r => faP r
  | .inr (.inl r) => faQ r
  | .inr (.inr (.inl k)) => mid k
  | .inr (.inr (.inr (.inl j))) => ib j
  | .inr (.inr (.inr (.inr j))) => carry j

/-- The gates are the sum type. -/
def sumEquiv : MG A ≃ Fin A ⊕ (Fin A ⊕ (Fin A ⊕ (Fin A ⊕ Fin (A * A)))) where
  toFun := toSum
  invFun := ofSum
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with x | x | x | x | x <;> rfl

/-- The enumeration of the gates: `faP`, `faQ`, `mid`, `ib`, `carry`. -/
def enum (A : ℕ) : MG A ≃ Fin (A + (A + (A + (A + A * A)))) :=
  sumEquiv.trans <| (Equiv.sumCongr (Equiv.refl _) <| (Equiv.sumCongr (Equiv.refl _) <|
    (Equiv.sumCongr (Equiv.refl _) finSumFinEquiv).trans finSumFinEquiv).trans finSumFinEquiv).trans
    finSumFinEquiv

instance : Fintype (MG A) := Fintype.ofEquiv _ (enum A).symm

end MG

section Params

variable (s : ℕ)

/-- `h = 2^s` digits per input gate. -/
def ph : ℕ := 2 ^ s

/-- The width of a message: `m + 1` bits. -/
def fw : ℕ := pm s + 1

theorem pA_eq : pA s = 2 * ph s := by unfold pA ph; rw [pow_succ]; ring

theorem pL_eq : pL s = pA s * ph s := by unfold pL pA ph; rw [← pow_add]; ring_nf

theorem ph_pos : 0 < ph s := Nat.pow_pos (by norm_num)

theorem pA_pos : 0 < pA s := Nat.pow_pos (by norm_num)

/-- Gate settings. -/
@[reducible] def mS : MG (pA s) → Type
  | .faP _ => Fin (ph s) → Fin (2 ^ pL s)
  | .faQ _ => Fin (ph s) → Fin (2 ^ pL s)
  | .mid _ => (Fin (pA s) → ZMod (pM s)) × (Fin (pA s) → ZMod (pM s))
  | .ib _ => Fin (pA s) → ZMod (pM s)
  | .carry _ => ZMod (pM s) × Fin (2 ^ fw s)

instance mS_fintype : ∀ i, Fintype (mS s i) := by
  intro i; cases i <;> (unfold mS; infer_instance)

instance mS_deq : ∀ i, DecidableEq (mS s i) := by
  intro i; cases i <;> (unfold mS; infer_instance)

/-- A finite family read as a sequence, `0` past the end. -/
def ext0 {R : Type*} [Zero R] {n : ℕ} (f : Fin n → R) : ℕ → R := fun i => if h : i < n then f ⟨i, h⟩ else 0

/-- `ω = 16`. -/
def ω16 : ZMod (pM s) := 16

/-- `ω' = ω^(T-1)`. -/
def ωi : ZMod (pM s) := 16 ^ (2 ^ (2 * s + 1 + 1) - 1)

/-- The digits of an input gate, as residues. -/
def digZ (u : Fin (ph s) → Fin (2 ^ pL s)) : ℕ → ZMod (pM s) := ext0 fun t => ((u t : ℕ) : ZMod (pM s))

/-- What input gate `r` sends to `MID[k₁]`. -/
def faV (r : ℕ) (u : Fin (ph s) → Fin (2 ^ pL s)) (k₁ : ℕ) : ZMod (pM s) := faOut (pA s) (ω16 s) r (digZ s u) k₁

/-- What `MID[k₁]` sends to `IB[j₁]`. -/
def midV (k₁ : ℕ) (z : (Fin (pA s) → ZMod (pM s)) × (Fin (pA s) → ZMod (pM s))) (j₁ : ℕ) : ZMod (pM s) :=
  midOut (pA s) (ω16 s) (ωi s) k₁ (ext0 z.1) (ext0 z.2) j₁

/-- What `IB[j₁]` sends to `CARRY[j₁ + A j₂]`. -/
def ibV (z : Fin (pA s) → ZMod (pM s)) (j₂ : ℕ) : ZMod (pM s) := ibOut (pA s) (ωi s) (tInv s) (ext0 z) j₂

/-- Which gates talk. -/
def mLink : MG (pA s) → MG (pA s) → Bool
  | .faP _, .mid _ => true
  | .faQ _, .mid _ => true
  | .mid _, .faP _ => true
  | .mid _, .faQ _ => true
  | .mid _, .ib _ => true
  | .ib _, .mid _ => true
  | .ib j₁, .carry j => j.val % pA s = j₁.val
  | .carry j, .ib j₁ => j.val % pA s = j₁.val
  | .carry j, .carry j' => j'.val = j.val + 1 ∨ j.val = j'.val + 1
  | _, _ => false

/-- Message widths. -/
def mC (i j : MG (pA s)) : ℕ := if mLink s i j then fw s else 0

/-- The messages. -/
def mV : ∀ i : MG (pA s), MG (pA s) → mS s i → ℕ
  | .faP r, .mid k, u => (faV s r (u : Fin (ph s) → Fin (2 ^ pL s)) k).val
  | .faQ r, .mid k, u => (faV s r (u : Fin (ph s) → Fin (2 ^ pL s)) k).val
  | .mid _, .faP r, z => ((z : (Fin (pA s) → ZMod (pM s)) × (Fin (pA s) → ZMod (pM s))).1 r).val
  | .mid _, .faQ r, z => ((z : (Fin (pA s) → ZMod (pM s)) × (Fin (pA s) → ZMod (pM s))).2 r).val
  | .mid k, .ib j, z => (midV s k z j).val
  | .ib _, .mid k, z => ((z : Fin (pA s) → ZMod (pM s)) k).val
  | .ib j₁, .carry j, z => if j.val % pA s = j₁.val then (ibV s z (j.val / pA s)).val else 0
  | .carry j, .ib j₁, z =>
      if j.val % pA s = j₁.val then (z : ZMod (pM s) × Fin (2 ^ fw s)).1.val else 0
  | .carry j, .carry j', z =>
      if j'.val = j.val + 1 then
        ((z : ZMod (pM s) × Fin (2 ^ fw s)).2.val + (z : ZMod (pM s) × Fin (2 ^ fw s)).1.val) / 2 ^ pL s
      else if j.val = j'.val + 1 then (z : ZMod (pM s) × Fin (2 ^ fw s)).2.val else 0
  | _, _, _ => 0

/-- Input gate `r` agrees with the pattern: bit `t` of digit `r + A i'` is bit `L(r + A i') + t - k` of `x` when
that position is at least `k`. -/
def preOK (k x r : ℕ) (u : Fin (ph s) → Fin (2 ^ pL s)) : Prop :=
  ∀ i' : Fin (ph s), ∀ t : Fin (pL s), k ≤ pL s * (r + pA s * i') + t →
    (u i').val.testBit t = x.testBit (pL s * (r + pA s * i') + t - k)

instance (k x r : ℕ) (u : Fin (ph s) → Fin (2 ^ pL s)) : Decidable (preOK s k x r u) := by
  unfold preOK; infer_instance

variable {R : Type*} [CommRing R]

/-- The weights. -/
def mW (N k x : ℕ) : ∀ i : MG (pA s), mS s i → R
  | .faP r, u => if preOK s k x r u ∧ (r.val = 0 → x < 2 ^ (pL s * pL s - k)) then 1 else 0
  | .carry j, z =>
      if ((z : ZMod (pM s) × Fin (2 ^ fw s)).2.val + (z : ZMod (pM s) × Fin (2 ^ fw s)).1.val) % 2 ^ pL s =
          dgt (pL s) N j ∧ (j.val = 0 → (z : ZMod (pM s) × Fin (2 ^ fw s)).2.val = 0) ∧
          (j.val + 1 = pA s * pA s →
            ((z : ZMod (pM s) × Fin (2 ^ fw s)).2.val + (z : ZMod (pM s) × Fin (2 ^ fw s)).1.val) / 2 ^ pL s = 0)
      then 1 else 0
  | _, _ => 1

variable (R)

/-- The multiplication network as a gate network. -/
def mulG (N k x : ℕ) : GNet R (MG (pA s)) where
  S := mS s
  fS := mS_fintype s
  dS := mS_deq s
  W := mW s N k x
  c := mC s
  v := mV s

/-- **The multiplication network.** -/
def mulNet (N k x : ℕ) : Net R (pA s + (pA s + (pA s + (pA s + pA s * pA s)))) :=
  (mulG s R N k x).toNet (MG.enum (pA s))

end Params

end Factoring.Aux
