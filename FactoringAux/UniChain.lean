/-
The uniform engine: the chain along one path of choice codes.

The per-`k` engine sums over the choice codes of every level by nesting (`deepVal`).  The uniform engine runs over
all paths `R < NPof d L` (the codes of the levels are the mixed-radix digits of `R`, the top level first) and, for
each path, computes the tables one level after the other (`chainVal`).  The sum over the paths is `deepVal`.

* `Nc` (choice codes of one level), `chainVal`, `NPof`; `sum_range_mul`; **`sum_chainVal`**.

Not an audit surface.
-/
module

public import FactoringAux.EngineGroup

@[expose] public section

namespace Factoring.Aux

open Finset

/-- The number of choice codes of the step from depth `d + 1` (label width `L`). -/
def Nc (K0 d L : ℕ) : ℕ := (tB L + 1) ^ (Gs K0 d * Gs K0 d * (Gs K0 d * Gs K0 d))

theorem Nc_pos (K0 d L : ℕ) : 0 < Nc K0 d L := Nat.pow_pos (Nat.succ_pos _)

variable {m : ℕ}

/-- The bottom value along the path `R` (digits `R % N`, `R / N`, the top level first). -/
def chainVal (K0 : ℕ) (hK : 2 ≤ K0) : (d L : ℕ) → Clique (ZMod m) (Kb K0 d) L → ℕ → ZMod m
  | 0, _, T, _ => T.value
  | d + 1, L, T, R => chainVal K0 hK d (Lnext (Kb K0 d) (Gs K0 d) L)
      (nextT (Kb K0 d) (by have := Kb_ge K0 hK d; omega) T ⟨R % Nc K0 d L, Nat.mod_lt _ (Nc_pos K0 d L)⟩)
      (R / Nc K0 d L)

/-- The number of paths. -/
def NPof (K0 : ℕ) : (d L : ℕ) → ℕ
  | 0, _ => 1
  | d + 1, L => Nc K0 d L * NPof K0 d (Lnext (Kb K0 d) (Gs K0 d) L)

theorem sum_range_mul {R : Type*} [AddCommMonoid R] (N M : ℕ) (f : ℕ → R) :
    ∑ x ∈ range (N * M), f x = ∑ c ∈ range N, ∑ y ∈ range M, f (c + N * y) := by
  induction M with
  | zero => simp
  | succ M ih =>
      rw [show N * (M + 1) = N * M + N by ring, sum_range_add, ih]
      simp only [sum_range_succ, sum_add_distrib]
      congr 1
      exact sum_congr rfl fun c _ => by rw [add_comm]

/-- **The sum over the paths is the nested sum.** -/
theorem sum_chainVal (K0 : ℕ) (hK : 2 ≤ K0) :
    ∀ (d L : ℕ) (T : Clique (ZMod m) (Kb K0 d) L),
      ∑ R ∈ range (NPof K0 d L), chainVal K0 hK d L T R = deepVal K0 hK d L T
  | 0, L, T => by simp [NPof, chainVal, deepVal]
  | d + 1, L, T => by
      rw [NPof, sum_range_mul, deepVal, ← Fin.sum_univ_eq_sum_range (fun c => ∑ y ∈ range _, _)]
      refine sum_congr rfl fun c _ => ?_
      have hN := Nc_pos K0 d L
      have e1 : ∀ y, (c.1 + Nc K0 d L * y) % Nc K0 d L = c.1 := fun y => by
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt c.2]
      have e2 : ∀ y, (c.1 + Nc K0 d L * y) / Nc K0 d L = y := fun y => by
        rw [Nat.add_mul_div_left _ _ hN, Nat.div_eq_of_lt c.2, zero_add]
      simp only [chainVal, e2]
      rw [← sum_chainVal K0 hK d]
      refine sum_congr rfl fun y _ => ?_
      congr 2
      exact Fin.ext (e1 y)

end Factoring.Aux
