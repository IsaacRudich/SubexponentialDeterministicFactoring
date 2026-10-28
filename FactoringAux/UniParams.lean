/-
The uniform engine: the parameters computed at run time.

The bottom group count is the constant `K0 = 48`; the number of levels `ℓ = ellOf n` is the largest `ℓ ≤ n` (found
step by step) with `Kb 48 ℓ ^ 40 ≤ n`; the group count at height `d` is `Kb 48 d`.  Internal binders of these
expressions are `900 …`.

* `powE` (`e^k`), `kbE` (`Kb 48 d`), `ellOf`, `ellE`, `gE` (`3 K^8`), `g4E`, `NcE` (`Nc`), `rcN`, `multV` (`mult`);
  their `eval_*` lemmas; `card_rects`, `nonRects_eq`.

Not an audit surface.
-/
module

public import FactoringAux.UniChain
public import FactoringAux.EngineGridEx

@[expose] public section

namespace Factoring.Aux

open Finset Ex

/-- The bottom group count of the uniform engine. -/
abbrev K0u : ℕ := 48

variable {σ : ℕ → ℕ} {A : ℕ → ℕ → ℕ}

/-- `e ^ k` (`x` a binder not read by `e`). -/
def powE (x : ℕ) (e : Ex) (k : ℕ) : Ex := .prod x (.lit k) (.lit 0) e

theorem foldProd_zero_pow (f : ℕ → ℕ) (c : ℕ) (hf : ∀ i, f i = c) : ∀ k, foldProd f 0 k = c ^ k
  | 0 => rfl
  | k + 1 => by rw [foldProd, Nat.mod_zero, foldProd_zero_pow f c hf k, hf, pow_succ]

theorem eval_powE (x : ℕ) (e : Ex) (k : ℕ) (hx : ∀ i, eval (Function.update σ x i) A e = eval σ A e) :
    eval σ A (powE x e k) = eval σ A e ^ k := by
  simp only [powE, Ex.eval]
  exact foldProd_zero_pow _ _ hx k

/-- `Kb 48 (var vd)`. -/
def kbE (vd : ℕ) : Ex := .iter 900 901 (.var vd) (.lit K0u) (.mul (.lit 9) (powE 902 (.var 901) 16))

theorem Kb_succ (K0 d : ℕ) : Kb K0 (d + 1) = 9 * Kb K0 d ^ 16 := by
  show (3 * Kb K0 d ^ 8) * (3 * Kb K0 d ^ 8) = _; ring

theorem iterF_Kb (K0 : ℕ) : ∀ d, iterF (fun _ s => 9 * s ^ 16) K0 d = Kb K0 d
  | 0 => rfl
  | d + 1 => by rw [iterF, iterF_Kb K0 d, Kb_succ]

theorem eval_kbE (vd : ℕ) : eval σ A (kbE vd) = Kb K0u (σ vd) := by
  rw [kbE, eval_iter]
  show iterF _ K0u (σ vd) = _
  rw [← iterF_Kb]
  congr 1
  funext j s
  simp only [Ex.eval]
  rw [eval_powE 902 _ 16 (fun i => by simp [Ex.eval])]
  simp [Ex.eval]

/-- One step of the search for `ℓ`. -/
def ellStep (n : ℕ) (_ y : ℕ) : ℕ := if n < Kb K0u (y + 1) ^ 40 then y else y + 1

/-- The number of levels: the largest `ℓ` reached step by step with `Kb 48 ℓ ^ 40 ≤ n`. -/
def ellOf (n : ℕ) : ℕ := iterF (ellStep n) 0 n

/-- `ellOf (var 0)`. -/
def ellE : Ex :=
  .iter 903 904 (.var 0) (.lit 0) (.lett 905 (.add (.var 904) (.lit 1))
    (.ifLt (.var 0) (powE 909 (kbE 905) 40) (.var 904) (.var 905)))

theorem eval_ellE : eval σ A ellE = ellOf (σ 0) := by
  rw [ellE, eval_iter]
  show iterF _ 0 (σ 0) = _
  unfold ellOf
  congr 1
  funext j y
  rw [eval_lett]
  have e1 : eval (Function.update (Function.update σ 903 j) 904 y) A (.add (.var 904) (.lit 1)) = y + 1 := by
    simp [Ex.eval]
  rw [e1, eval_ifLt']
  rw [eval_powE 909 _ 40 (fun i => by rw [eval_kbE, eval_kbE]; simp)]
  rw [eval_kbE]
  simp [Ex.eval, ellStep]

/-- `3 K^8` (`K` in `vK`). -/
def gE (vK : ℕ) : Ex := .mul (.lit 3) (powE 906 (.var vK) 8)

theorem eval_gE {vK : ℕ} (h : vK ≠ 906) : eval σ A (gE vK) = 3 * σ vK ^ 8 := by
  simp only [gE, Ex.eval]
  rw [eval_powE 906 _ 8 (fun i => by simp [Ex.eval, Function.update_of_ne h])]
  rfl

/-- `(3 K^8)^4`. -/
def g4E (vK : ℕ) : Ex := powE 907 (gE vK) 4

theorem eval_g4E {vK : ℕ} (h : vK ≠ 906) (h' : vK ≠ 907) : eval σ A (g4E vK) = (3 * σ vK ^ 8) ^ 4 := by
  rw [g4E, eval_powE 907 _ 4 (fun i => by rw [eval_gE h, eval_gE h, Function.update_of_ne h'])]
  rw [eval_gE h]

theorem Gs_eq (K0 d : ℕ) : Gs K0 d = 3 * Kb K0 d ^ 8 := rfl

/-- `Nc 48 d λ` (`Kb 48 d` in `vK`, `λ` in `vl`). -/
def NcE (vK vl : ℕ) : Ex := .prod 908 (g4E vK) (.lit 0) (.add (tBE vl) (.lit 1))

theorem eval_NcE {vK vl d L : ℕ} (h1 : vK ≠ 906) (h2 : vK ≠ 907) (h3 : vl ≠ 908) (hK : σ vK = Kb K0u d)
    (hl : σ vl = L) : eval σ A (NcE vK vl) = Nc K0u d L := by
  simp only [NcE, Ex.eval]
  rw [eval_g4E h1 h2, hK]
  rw [foldProd_zero_pow _ (tB L + 1) (fun i => by
    rw [eval_tBE (lam := L) (by rw [Function.update_of_ne h3]; exact hl)])]
  rw [Nc, Gs_eq]; ring

theorem card_rects (G : ℕ) : (rects G).card = (G * (G - 1) / 2) * (G * (G - 1) / 2) := by
  rw [rects, card_product]
  have := card_pairs G
  have h : (pairs G).card = G * (G - 1) / 2 := by omega
  rw [h]

theorem nonRects_eq (G : ℕ) : nonRects G = G ^ 4 - (rects G).card := by
  unfold nonRects
  rw [filter_not, card_sdiff, filter_mem_eq_inter, univ_inter]
  simp [Fintype.card_prod]; ring_nf

/-- `mult (3 K^8) λ` (`K` in `vK`, `λ` in `vl`). -/
def multV (vK vl : ℕ) : Ex :=
  .lett 910 (gE vK) (.lett 911 (.div (.mul (.var 910) (.sub (.var 910) (.lit 1))) (.lit 2))
    (.lett 912 (.mul (.var 911) (.var 911))
      (.mul (.prod 913 (.sub (powE 914 (.var 910) 4) (.var 912)) (.lit 0) (.add (tBE vl) (.lit 1)))
        (.prod 913 (.mul (tBE vl) (.var 912)) (.lit 0) (.lit 2)))))

theorem eval_multV {vK vl d L : ℕ} (h1 : vK ≠ 906) (h3 : vl < 910) (hK : σ vK = Kb K0u d) (hl : σ vl = L) :
    eval σ A (multV vK vl) = mult (Gs K0u d) L := by
  rw [multV, eval_lett, eval_gE h1, hK]
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
  simp only [Ex.eval]
  rw [eval_powE 914 _ 4 (fun i => by simp [Ex.eval]), show eval σ3 A (.var 910) = G from v910, v912]
  rw [foldProd_zero_pow _ (tB L + 1) (fun i => by
      rw [t3 _ (fun y hy => by rw [Function.update_of_ne (by omega)]; exact a3 y hy)]),
    foldProd_zero_pow _ 2 (fun i => rfl), t3 _ a3]
  rw [mult, nonRects_eq, card_rects, Gs_eq]

end Factoring.Aux
