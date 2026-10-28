/-
FactoringAux/Trial/Main.lean — trial division is correct and runs in `O((n+1)^2 · 2^(n/2))` steps;
hence `trialDivisionRate`.

Not audited.
-/
module

public import FactoringAux.Trial.Setup
public import FactoringAux.SProg.Machine
public import Mathlib.Data.Nat.Prime.Basic

@[expose] public section

namespace Factoring.Aux.Trial

open SProg Function Computability

/-! ### What the search finds -/

theorem search_some (N : ℕ) : ∀ (m d a : ℕ), (search N d m (some a)).2 = some a
  | 0, _, _ => rfl
  | m + 1, d, a => search_some N m d a

theorem search_none (N : ℕ) : ∀ (m d : ℕ),
    ((search N d m none).2 = none → ∀ b, d ≤ b → b < d + m → N % b ≠ 0) ∧
    (∀ a, (search N d m none).2 = some a →
      d ≤ a ∧ a < d + m ∧ N % a = 0 ∧ ∀ b, d ≤ b → b < a → N % b ≠ 0)
  | 0, d => by
      refine ⟨fun _ b h1 h2 => by omega, fun a h => ?_⟩
      simp [search] at h
  | m + 1, d => by
      by_cases hd : N % d = 0
      · have e : (search N d (m + 1) none).2 = some d := by
          simp only [search, if_pos hd]; exact search_some N m (d + 1) d
        rw [e]
        refine ⟨fun h => by simp at h, fun a h => ?_⟩
        simp only [Option.some.injEq] at h
        subst h
        exact ⟨le_rfl, by omega, hd, fun b h1 h2 => by omega⟩
      · have e : search N d (m + 1) none = search N (d + 1) m none := by
          simp only [search, if_neg hd]
        rw [e]
        obtain ⟨ih1, ih2⟩ := search_none N m (d + 1)
        refine ⟨fun h b h1 h2 => ?_, fun a h => ?_⟩
        · rcases Nat.eq_or_lt_of_le h1 with rfl | h1
          · exact hd
          · exact ih1 h b h1 (by omega)
        · obtain ⟨a1, a2, a3, a4⟩ := ih2 a h
          refine ⟨by omega, by omega, a3, fun b h1 h2 => ?_⟩
          rcases Nat.eq_or_lt_of_le h1 with rfl | h1
          · exact hd
          · exact a4 b h1 h2

/-- The answer of trial division is `Nat.minFac N`, as soon as the search passes `√N`. -/
theorem search_minFac (N M : ℕ) (hM : 1 ≤ M) (hN : N < M * M) :
    ((search N 2 M none).2).elim N id = Nat.minFac N := by
  obtain ⟨h1, h2⟩ := search_none N M 2
  cases hs : (search N 2 M none).2 with
  | some a =>
      obtain ⟨a1, a2, a3, a4⟩ := h2 a hs
      simp only [Option.elim, id]
      have hdvd : a ∣ N := Nat.dvd_of_mod_eq_zero a3
      have hN1 : N ≠ 1 := by
        rintro rfl
        have := Nat.le_of_dvd one_pos hdvd; omega
      have hle : Nat.minFac N ≤ a := Nat.minFac_le_of_dvd a1 hdvd
      have hp := Nat.minFac_prime hN1
      by_contra hne
      have hlt : Nat.minFac N < a := lt_of_le_of_ne hle (Ne.symm hne)
      exact a4 (Nat.minFac N) hp.two_le hlt (Nat.mod_eq_zero_of_dvd (Nat.minFac_dvd N))
  | none =>
      have hno := h1 hs
      simp only [Option.elim]
      rcases Nat.lt_or_ge N 2 with hN2 | hN2
      · obtain rfl | rfl : N = 0 ∨ N = 1 := by omega
        · exact absurd (Nat.zero_mod 2) (hno 2 le_rfl (by omega))
        · rw [Nat.minFac_one]
      · have hN1 : N ≠ 1 := by omega
        have hp := Nat.minFac_prime hN1
        have hbig : 2 + M ≤ Nat.minFac N := by
          by_contra h
          exact hno (Nat.minFac N) hp.two_le (by omega)
            (Nat.mod_eq_zero_of_dvd (Nat.minFac_dvd N))
        by_contra hne
        have hnp : ¬ N.Prime := fun hpr => hne (hpr.minFac_eq).symm
        have hsq := Nat.minFac_sq_le_self (by omega) hnp
        have : M * M < Nat.minFac N * Nat.minFac N := Nat.mul_lt_mul'' (by omega) (by omega)
        rw [sq] at hsq
        omega

/-! ### Correctness of the program -/

theorem valFrom_nr (l : List Bool) :
    valFrom 0 (false :: false :: false :: l.reverse) = valL l := by
  simp only [valFrom, Nat.mul_zero, Bool.toNat_false, Nat.add_zero]
  rw [valFrom_reverse]; simp

theorem setup_exec_eq (s : Stacks) :
    setup.exec s = setupC.exec (setupB.exec (setupA.exec s)) := rfl

theorem setup_cost_eq (s : Stacks) :
    setup.cost s = setupA.cost s + (setupB.cost (setupA.exec s) +
      (setupC.cost (setupB.exec (setupA.exec s)) + 0)) := rfl

theorem trial_split (s : Stacks) :
    trialProg.exec s = finish.exec ((loop sCTR body body).exec (setup.exec s)) ∧
    trialProg.cost s = setup.cost s + ((loop sCTR body body).cost (setup.exec s) +
      (finish.cost ((loop sCTR body body).exec (setup.exec s)) + 0)) := ⟨rfl, rfl⟩

/-- Everything about one run, on input `l = encodeNat N`. -/
theorem trial_run (N : ℕ) :
    trialProg.exec (initStacks (encodeNat N)) = initStacks (encodeNat (Nat.minFac N)) ∧
      trialProg.cost (initStacks (encodeNat N)) ≤
        (6 * (encodeNat N).length + 10) + (7 * 2 ^ (((encodeNat N).length + 1) / 2) +
          3 * (((encodeNat N).length + 1) / 2) + 1) + (7 * ((encodeNat N).length + 1) + 25) +
        ((14 * ((encodeNat N).length + 3) * ((encodeNat N).length + 3) +
          34 * ((encodeNat N).length + 3) + 18) * 2 ^ (((encodeNat N).length + 1) / 2) + 1) +
        (12 * ((encodeNat N).length + 3) + 12) := by
  set l := encodeNat N with hl
  set n := l.length with hn
  set H := (n + 1) / 2 with hH
  set nr := false :: false :: false :: l.reverse with hnr
  have hnrl : nr.length = n + 3 := by simp [nr, n]
  have hA := setupA_spec l
  rw [← hn, ← hH, ← hnr] at hA
  have hB := setupB_spec (n + 3) H nr
  have hC := setupC_spec (n + 1) nr (List.replicate (2 ^ H) true)
  rw [show n + 1 + 2 = n + 3 from rfl] at hC
  have hsetup : setup.exec (initStacks l) = mainSt (n + 3) nr 2 none (List.replicate (2 ^ H) true) := by
    rw [setup_exec_eq, hA.1, hB.1, hC.1]
  -- the search range passes √N
  have hNlt : N < 2 ^ n := by have := lt_two_pow_length N; simpa [l, n] using this
  have hHn : H ≤ n := by omega
  have hsq : 2 ^ n ≤ 2 ^ H * 2 ^ H := by
    rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hpowH : 2 + 2 ^ H ≤ 2 ^ (n + 3 - 1) := by
    have : 2 ^ H ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hHn
    have : 2 ^ (n + 3 - 1) = 4 * 2 ^ n := by
      rw [show n + 3 - 1 = n + 2 by omega, pow_add]; ring
    have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    omega
  have hloop := mainLoop (n + 3) nr (by omega) hnrl (List.replicate (2 ^ H) true) 2 none (by norm_num)
    (by simpa using hpowH)
  rw [List.length_replicate] at hloop
  have hloopE : (loop sCTR body body).exec (mainSt (n + 3) nr 2 none (List.replicate (2 ^ H) true)) =
      mainSt (n + 3) nr (search (valFrom 0 nr) 2 (2 ^ H) none).1
        (search (valFrom 0 nr) 2 (2 ^ H) none).2 [] := by
    rw [exec_loop, show mainSt (n + 3) nr 2 none (List.replicate (2 ^ H) true) sCTR =
      List.replicate (2 ^ H) true by simp [mainSt]]
    exact hloop.1
  have hloopC : (loop sCTR body body).cost (mainSt (n + 3) nr 2 none (List.replicate (2 ^ H) true)) ≤
      (14 * (n + 3) * (n + 3) + 34 * (n + 3) + 18) * 2 ^ H + 1 := by
    rw [cost_loop, show mainSt (n + 3) nr 2 none (List.replicate (2 ^ H) true) sCTR =
      List.replicate (2 ^ H) true by simp [mainSt]]
    exact hloop.2
  have hF := finish_spec (n + 3) (search (valFrom 0 nr) 2 (2 ^ H) none).1 nr
    (search (valFrom 0 nr) 2 (2 ^ H) none).2 hnrl
  have hval : valFrom 0 nr = N := by rw [valFrom_nr, hl, valL_encodeNat]
  rw [hval] at hF hloopE
  have hans : ((search N 2 (2 ^ H) none).2).elim N (fun a => valL (bitsW (n + 3) a)) =
      Nat.minFac N := by
    rw [← search_minFac N (2 ^ H) Nat.one_le_two_pow (by omega)]
    cases hs : (search N 2 (2 ^ H) none).2 with
    | none => rfl
    | some a =>
        obtain ⟨_, a2, _, _⟩ := (search_none N (2 ^ H) 2).2 a hs
        simp only [Option.elim, id, valL_bitsW]
        apply Nat.mod_eq_of_lt
        have : 2 ^ (n + 3 - 1) ≤ 2 ^ (n + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
  refine ⟨?_, ?_⟩
  · rw [(trial_split _).1, hsetup, hloopE, hF.1, hans]
  · rw [(trial_split _).2, hsetup, hloopE, setup_cost_eq, hA.1, hB.1]
    have := hA.2; have := hB.2; have := hC.2; have := hF.2
    omega

/-- The cost bound in the shape of the claim. -/
theorem trial_cost (N : ℕ) :
    trialProg.cost (initStacks (encodeNat N)) + 1 ≤
      1000 * ((encodeNat N).length + 1) ^ 2 * 2 ^ ((encodeNat N).length / 2) := by
  have h := (trial_run N).2
  generalize (encodeNat N).length = n at h ⊢
  set P := 2 ^ (n / 2) with hP
  set H := (n + 1) / 2 with hH
  have hP1 : 1 ≤ P := Nat.one_le_two_pow
  have hHP : 2 ^ H ≤ 2 * P := by
    rw [hP, ← pow_succ']; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hq : (14 * (n + 3) * (n + 3) + 34 * (n + 3) + 18) ≤ 246 * ((n + 1) * (n + 1)) := by
    nlinarith
  have hloop : (14 * (n + 3) * (n + 3) + 34 * (n + 3) + 18) * 2 ^ H ≤
      492 * ((n + 1) * (n + 1) * P) := by
    calc (14 * (n + 3) * (n + 3) + 34 * (n + 3) + 18) * 2 ^ H
        ≤ 246 * ((n + 1) * (n + 1)) * (2 * P) := Nat.mul_le_mul hq hHP
      _ = 492 * ((n + 1) * (n + 1) * P) := by ring
  have hX1 : P ≤ (n + 1) * (n + 1) * P := by
    have : 1 ≤ (n + 1) * (n + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    nlinarith
  have hX2 : n + 1 ≤ (n + 1) * (n + 1) * P := by
    have : n + 1 ≤ (n + 1) * (n + 1) := Nat.le_mul_of_pos_right _ (by omega)
    nlinarith
  rw [sq, show 1000 * ((n + 1) * (n + 1)) * P = 1000 * ((n + 1) * (n + 1) * P) by ring]
  generalize (n + 1) * (n + 1) * P = X at *
  omega

end Factoring.Aux.Trial

namespace Factoring.Aux

/-- **Trial division.**  Some Mathlib machine factors within `1000 · (n+1)^2 · 2^(n/2)` steps. -/
theorem trialDivisionRate :
    ∃ C d : ℕ, FactoringInTime (fun n => C * (n + 1) ^ d * 2 ^ (n / 2)) :=
  ⟨1000, 2, SProg.factoringInTime_of_sprog Trial.trialProg Trial.nStacks (by decide)
    Trial.trialProg_WF Trial.trialProg_stacks _ (fun N => (Trial.trial_run N).1)
    Trial.trial_cost⟩

end Factoring.Aux
