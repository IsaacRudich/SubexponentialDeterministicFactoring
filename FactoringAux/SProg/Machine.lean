/-
FactoringAux/SProg/Machine.lean — L1′, second half: an `SProg` program as a Mathlib `FinTM2`, and the
bridge to the audited `FactoringInTime`.

Not audited.

`tmOf P nK hK` has stacks `Fin nK` (all with alphabet `Bool`; input and output on stack `0`), labels
`Fin (size P + 1)` (the flat code of `P`, then `halt`), and internal state `Option Bool` (the symbol
just popped, reset to `none` before every jump).  It runs `P` in exactly `cost P s` steps, then halts
in one more step (`outputsInTime`).  `factoringInTime_of_sprog` turns an `SProg` program for
`Nat.minFac` (input `encodeNat N` on stack 0, output `encodeNat (minFac N)` on stack 0, every other
stack empty at the end) into the audited `FactoringInTime`.
-/
module

public import FactoringAux.SProg.Compile
public import FactoringAux.Definitions

@[expose] public section

namespace Factoring.Aux
namespace SProg

open Function Turing Computability StateTransition

/-- The stack bound of a flat instruction. -/
def Instr.StackLt (n : ℕ) : Instr → Prop
  | .push k _ _ => k < n
  | .read k _ _ _ => k < n
  | .halt => True

theorem code_stackLt {n : ℕ} :
    ∀ (p : SProg) (start next i : ℕ), p.StacksBelow n = true → (code p start next i).StackLt n
  | skip, _, _, _, _ => trivial
  | push k b, _, _, _, h => by simpa [StacksBelow, code, Instr.StackLt] using h
  | read k pt pf pe, start, next, i, h => by
      simp only [StacksBelow, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨hk, h1⟩, h2⟩, h3⟩ := h
      simp only [code]
      split_ifs
      · exact hk
      · exact code_stackLt pt _ _ _ h1
      · exact code_stackLt pf _ _ _ h2
      · exact code_stackLt pe _ _ _ h3
  | seq p q, start, next, i, h => by
      simp only [StacksBelow, Bool.and_eq_true] at h
      simp only [code]
      split_ifs
      · exact code_stackLt p _ _ _ h.1
      · exact code_stackLt q _ _ _ h.2
  | loop k pt pf, start, next, i, h => by
      simp only [StacksBelow, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨hk, h1⟩, h2⟩ := h
      simp only [code]
      split_ifs
      · exact hk
      · exact code_stackLt pt _ _ _ h1
      · exact code_stackLt pf _ _ _ h2

/-- The whole flat code: `P` at `0 … size P - 1`, leaving to `size P`, where it halts. -/
def flatCode (P : SProg) (i : ℕ) : Instr :=
  if i < size P then code P 0 (size P) i else .halt

/-- Labels of the machine. -/
def lab (P : SProg) (n : ℕ) : Fin (size P + 1) := ⟨min n (size P), by omega⟩

/-- One flat instruction as one `TM2` statement. -/
def instrStmt {nK : ℕ} (hK : 0 < nK) {Λ : Type} (lb : ℕ → Λ) :
    Instr → TM2.Stmt (fun _ : Fin nK => Bool) Λ (Option Bool)
  | .push k b n => .push ⟨k % nK, Nat.mod_lt _ hK⟩ (fun _ => b) (.goto fun _ => lb n)
  | .read k t f e =>
      .pop ⟨k % nK, Nat.mod_lt _ hK⟩ (fun _ x => x)
        (.branch (fun v => v == some true) (.load (fun _ => none) (.goto fun _ => lb t))
          (.branch (fun v => v == some false) (.load (fun _ => none) (.goto fun _ => lb f))
            (.load (fun _ => none) (.goto fun _ => lb e))))
  | .halt => .halt

/-- Configurations of the machine running `P` with `nK` stacks. -/
abbrev CfgOf (P : SProg) (nK : ℕ) : Type :=
  TM2.Cfg (fun _ : Fin nK => Bool) (Fin (size P + 1)) (Option Bool)

/-- The program of the machine: label `i` runs flat instruction `i`. -/
def mOf (P : SProg) {nK : ℕ} (hK : 0 < nK) :
    Fin (size P + 1) → TM2.Stmt (fun _ : Fin nK => Bool) (Fin (size P + 1)) (Option Bool) :=
  fun i => instrStmt hK (lab P) (flatCode P i.val)

/-- The Mathlib machine running `P`, with `nK` stacks. -/
@[reducible] def tmOf (P : SProg) (nK : ℕ) (hK : 0 < nK) : FinTM2 where
  K := Fin nK
  k₀ := ⟨0, hK⟩
  k₁ := ⟨0, hK⟩
  Γ := fun _ => Bool
  Λ := Fin (size P + 1)
  main := lab P (entry P 0 (size P))
  σ := Option Bool
  initialState := none
  m := mOf P hK

/-- The machine configuration at address `pc` with stacks `s`. -/
def enc (P : SProg) (nK : ℕ) (_hK : 0 < nK) (pc : ℕ) (s : Stacks) : CfgOf P nK :=
  ⟨some (lab P pc), none, fun k => s k.val⟩

theorem lab_val {P : SProg} {pc : ℕ} (h : pc ≤ size P) : (lab P pc).val = pc := by
  simp [lab, h]

theorem update_fin {nK k : ℕ} (hk : k < nK) (hK : 0 < nK) (s : Stacks) (v : List Bool) :
    update (fun j : Fin nK => s j.val) ⟨k % nK, Nat.mod_lt _ hK⟩ v =
      fun j : Fin nK => update s k v j.val := by
  funext j
  have hk' : k % nK = k := Nat.mod_eq_of_lt hk
  by_cases hj : j.val = k
  · have : j = ⟨k % nK, Nat.mod_lt _ hK⟩ := Fin.ext (by simp [hj, hk'])
    subst this
    simp [hk']
  · have : j ≠ ⟨k % nK, Nat.mod_lt _ hK⟩ := fun h => hj (by rw [h]; exact hk')
    rw [update_of_ne this, update_of_ne hj]

theorem simulates (P : SProg) (nK : ℕ) (hK : 0 < nK) (hst : P.StacksBelow nK = true) :
    Simulates (flatCode P) (TM2.step (mOf P hK)) (enc P nK hK) := by
  constructor
  · intro pc s k b n hC
    have hpc : pc < size P := by
      by_contra h; simp [flatCode, h] at hC
    have hk : k < nK := by
      have := code_stackLt P 0 (size P) pc hst
      simp only [flatCode, hpc, if_true] at hC
      rw [hC] at this; exact this
    have hm : mOf P hK (lab P pc) = instrStmt hK (lab P) (.push k b n) := by
      show instrStmt hK (lab P) (flatCode P (lab P pc).val) = _
      rw [lab_val hpc.le, hC]
    simp only [enc, TM2.step]
    rw [hm]
    simp only [instrStmt, TM2.stepAux, Option.some.injEq]
    rw [update_fin hk hK s]
    simp [Nat.mod_eq_of_lt hk]
  · intro pc s k t f e hC
    have hpc : pc < size P := by
      by_contra h; simp [flatCode, h] at hC
    have hk : k < nK := by
      have := code_stackLt P 0 (size P) pc hst
      simp only [flatCode, hpc, if_true] at hC
      rw [hC] at this; exact this
    have hm : mOf P hK (lab P pc) = instrStmt hK (lab P) (.read k t f e) := by
      show instrStmt hK (lab P) (flatCode P (lab P pc).val) = _
      rw [lab_val hpc.le, hC]
    have hk' : k % nK = k := Nat.mod_eq_of_lt hk
    simp only [enc, TM2.step]
    rw [hm]
    simp only [instrStmt, TM2.stepAux]
    rcases hs : s k with _ | ⟨x, l⟩
    · have hl : (fun j : Fin nK => s j.val) ⟨k % nK, Nat.mod_lt _ hK⟩ = [] := by simp [hk', hs]
      simp only [hl, List.head?_nil, List.tail_nil, readNext, hs]
      have hu : update (fun j : Fin nK => s j.val) ⟨k % nK, Nat.mod_lt _ hK⟩ [] =
          fun j => s j.val := by
        rw [update_fin hk hK s]
        funext j
        by_cases hj : j.val = k
        · simp [hj, hs]
        · simp [update_of_ne hj]
      rw [hu]
      rfl
    · have hl : (fun j : Fin nK => s j.val) ⟨k % nK, Nat.mod_lt _ hK⟩ = x :: l := by simp [hk', hs]
      cases x
      · simp only [hl, List.head?_cons, List.tail_cons, readNext, hs]
        simp only [update_fin hk hK s]
        simp
      · simp only [hl, List.head?_cons, List.tail_cons, readNext, hs]
        simp only [update_fin hk hK s]
        simp

theorem loaded_flat (P : SProg) : Loaded (flatCode P) P 0 (size P) :=
  loaded_of_code P 0 (size P) fun i _ h => by simp only [flatCode]; rw [if_pos (by omega)]

/-- The machine runs `P` and halts: `cost + 1` steps from the input `l` to the output `out`. -/
def outputsInTime (P : SProg) (nK : ℕ) (hK : 0 < nK) (hwf : P.WF = true)
    (hst : P.StacksBelow nK = true) (l out : List Bool)
    (hout : P.exec (initStacks l) = initStacks out) :
    TM2OutputsInTime (tmOf P nK hK) l (some out) (P.cost (initStacks l) + 1) where
  steps := P.cost (initStacks l) + 1
  evals_in_steps := by
    have hinit : (initList (tmOf P nK hK) l : CfgOf P nK) =
        enc P nK hK (entry P 0 (size P)) (initStacks l) := by
      simp only [initList, enc]
      congr 1
      funext k
      by_cases hk : k = ⟨0, hK⟩
      · subst hk; simp [initStacks]
      · have : k.val ≠ 0 := fun h => hk (Fin.ext h)
        simp [hk, initStacks, update_of_ne this]
    have hhalt : (haltList (tmOf P nK hK) out : CfgOf P nK) = ⟨none, none, fun k => initStacks out k.val⟩ := by
      simp only [haltList]
      congr 1
      funext k
      by_cases hk : k = ⟨0, hK⟩
      · subst hk; simp [initStacks]
      · have : k.val ≠ 0 := fun h => hk (Fin.ext h)
        simp [hk, initStacks, update_of_ne this]
    show (flip Option.bind (TM2.step (mOf P hK)))^[P.cost (initStacks l) + 1]
      (some (initList (tmOf P nK hK) l : CfgOf P nK)) =
      some (haltList (tmOf P nK hK) out : CfgOf P nK)
    rw [Function.iterate_succ_apply', hinit,
      iterate_cost (simulates P nK hK hst) P 0 (size P) _ (loaded_flat P) hwf, hout, hhalt]
    have hm : mOf P hK (lab P (size P)) = .halt := by
      show instrStmt hK (lab P) (flatCode P (lab P (size P)).val) = _
      rw [lab_val (Nat.le_refl _)]; simp [flatCode, instrStmt]
    simp only [flip, Option.bind_some, enc, TM2.step, hm, TM2.stepAux]
    rfl
  steps_le_m := le_rfl

/-- A time bound can be raised. -/
def outputsInTime_mono {tm : FinTM2} {l : List (tm.Γ tm.k₀)} {o : Option (List (tm.Γ tm.k₁))}
    {m m' : ℕ} (h : TM2OutputsInTime tm l o m) (hm : m ≤ m') : TM2OutputsInTime tm l o m' :=
  ⟨h.toEvalsTo, h.steps_le_m.trans hm⟩

/-- **The bridge.**  An `SProg` program for `Nat.minFac` in the stack convention (input
`encodeNat N` on stack 0, output `encodeNat (minFac N)` on stack 0, every other stack empty), with
cost `+ 1` at most `T` of the input length, gives `FactoringInTime T`. -/
theorem factoringInTime_of_sprog (P : SProg) (nK : ℕ) (hK : 0 < nK) (hwf : P.WF = true)
    (hst : P.StacksBelow nK = true) (T : ℕ → ℕ)
    (hexec : ∀ N, P.exec (initStacks (encodeNat N)) = initStacks (encodeNat (Nat.minFac N)))
    (hcost : ∀ N, P.cost (initStacks (encodeNat N)) + 1 ≤ T (encodeNat N).length) :
    FactoringInTime T := by
  let M : FactoringMachine :=
    { tm := tmOf P nK hK
      inputAlphabet := Equiv.refl Bool
      outputAlphabet := Equiv.refl Bool
      time := T
      outputsFun := fun a => by
        have e1 : List.map (Equiv.refl Bool).invFun (encodeNat a) = encodeNat a := List.map_id _
        have e2 : List.map (Equiv.refl Bool).invFun (encodeNat (factor a)) =
            encodeNat (factor a) := List.map_id _
        exact cast (by rw [e1, e2]) (outputsInTime_mono
          (outputsInTime P nK hK hwf hst (encodeNat a) (encodeNat (factor a)) (hexec a))
          (hcost a)) }
  exact ⟨M, fun _ => inferInstanceAs (Finite Bool), fun _ => le_rfl⟩

end SProg

end Factoring.Aux
