/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OrderedOpExp08.MainResults.TaylorRemainder

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open Matrix
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
open Qatlib.Concepts.TrotterFormula.GeneralOrder
open Qatlib.Concepts.TrotterFormula.RecursiveSuzuki
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open scoped Classical BigOperators Matrix.Norms.L2Operator
set_option warningAsError false

namespace Qatlib.Papers.OrderedOpExp08.MainResults

def taylorRemainder {I : Type} [Fintype I] [DecidableEq I]
    (V : List (Matrix I I ℂ)) (t : ℝ) (k : ℕ) : ℝ :=
  ‖suzukiExponentialWord V t -
    ∑ n ∈ Finset.range (2 * k + 1), t ^ n • suzukiSeries V n‖

theorem exp_factorial_tail_le_two_mul_pow (a : ℝ) (m : ℕ)
    (ha0 : 0 ≤ a) (ha : a ≤ 1 / 2) :
    Real.exp a * a ^ m / (m.factorial : ℝ) ≤ 2 * a ^ m := by
  have hexp_half : Real.exp (1 / 2 : ℝ) < 2 := by
    have hsq : Real.exp (1 / 2 : ℝ) * Real.exp (1 / 2 : ℝ) = Real.exp 1 := by
      rw [← Real.exp_add]
      norm_num
    have hpos : 0 < Real.exp (1 / 2 : ℝ) := Real.exp_pos _
    have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    nlinarith
  have hexp : Real.exp a ≤ 2 := (Real.exp_le_exp.mpr ha).trans hexp_half.le
  have hpow : 0 ≤ a ^ m := pow_nonneg ha0 m
  have hmpos : (0 : ℝ) < (m.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos m
  have hfac : (1 : ℝ) ≤ (m.factorial : ℝ) := by
    have h1 : (1 : ℕ) ≤ m.factorial :=
      Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero m)
    exact_mod_cast h1
  have hdiv : a ^ m / (m.factorial : ℝ) ≤ a ^ m := by
    rw [div_le_iff₀ hmpos]
    calc a ^ m = a ^ m * 1 := by ring
      _ ≤ a ^ m * (m.factorial : ℝ) := mul_le_mul_of_nonneg_left hfac hpow
  calc
    Real.exp a * a ^ m / (m.factorial : ℝ) =
        Real.exp a * (a ^ m / (m.factorial : ℝ)) := by ring
    _ ≤ 2 * (a ^ m / (m.factorial : ℝ)) :=
      mul_le_mul_of_nonneg_right hexp (by positivity)
    _ ≤ 2 * a ^ m := mul_le_mul_of_nonneg_left hdiv (by norm_num)

theorem sum_ofFn_eq {m : ℕ} (g : Fin m → ℝ) :
    (List.ofFn g).sum = ∑ j, g j := by
  induction m with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.sum_cons, ih, Fin.sum_univ_succ]

theorem lemma3_remainder_bound {I : Type} [Fintype I] [DecidableEq I]
    (xs : List (Matrix I I ℂ)) (t : ℝ) (k : ℕ)
    (hshort : |t| * suzukiMass xs ≤ 1 / 2) :
    taylorRemainder xs t k ≤ 2 * (|t| * suzukiMass xs) ^ (2 * k + 1) := by
  unfold taylorRemainder
  refine (general_trotter_taylor_tail xs t (2 * k + 1)).trans ?_
  exact exp_factorial_tail_le_two_mul_pow _ _
    (mul_nonneg (abs_nonneg _) (general_trotter_mass_nonneg xs)) hshort

theorem lemma3_lts_remainder_bound {I : Type} [Fintype I] [DecidableEq I] {m : ℕ}
    (H : Fin m → ℝ → Matrix I I ℂ) (μ dlam Λ : ℝ) (k : ℕ)
    (_hk : 1 ≤ k) (hdlam : 0 ≤ dlam) (_hΛ : 0 ≤ Λ)
    (hsmooth : LambdaSmooth H Λ μ (μ + dlam) (2 * k))
    (hshort : |dlam| * ((3 : ℝ) ^ (k - 1) * Λ) ≤ 1 / 2) :
    taylorRemainder (ltsGenerators H μ dlam (k - 1)) dlam k ≤
      2 * (|dlam| * ((3 : ℝ) ^ (k - 1) * Λ)) ^ (2 * k + 1) := by
  have hmem : μ + dlam / 2 ∈ Set.Icc μ (μ + dlam) := by
    refine ⟨by linarith, by linarith⟩
  have hbase : suzukiMass (List.ofFn (fun j : Fin m => H j (μ + dlam / 2))) ≤ Λ := by
    have h0 := hsmooth 0 (Nat.zero_le _) (μ + dlam / 2) hmem
    have h0' : ∑ j : Fin m, ‖H j (μ + dlam / 2)‖ ≤ Λ := by
      simpa [iteratedDeriv_zero] using! h0
    simpa [suzukiMass, sum_ofFn_eq] using! h0'
  have hmass : suzukiMass (ltsGenerators H μ dlam (k - 1)) ≤ (3 : ℝ) ^ (k - 1) * Λ := by
    have h := (recursive_suzuki_length_and_mass I
      (List.ofFn (fun j : Fin m => H j (μ + dlam / 2))) (k - 1)).2
    have h' : suzukiMass (ltsGenerators H μ dlam (k - 1)) ≤
        (3 : ℝ) ^ (k - 1) *
          suzukiMass (List.ofFn (fun j : Fin m => H j (μ + dlam / 2))) := h
    exact h'.trans (mul_le_mul_of_nonneg_left hbase (by positivity))
  have hshort' : |dlam| * suzukiMass (ltsGenerators H μ dlam (k - 1)) ≤ 1 / 2 := by
    calc |dlam| * suzukiMass (ltsGenerators H μ dlam (k - 1))
        ≤ |dlam| * ((3 : ℝ) ^ (k - 1) * Λ) :=
          mul_le_mul_of_nonneg_left hmass (abs_nonneg _)
      _ ≤ 1 / 2 := hshort
  have hmono : |dlam| * suzukiMass (ltsGenerators H μ dlam (k - 1)) ≤
      |dlam| * ((3 : ℝ) ^ (k - 1) * Λ) :=
    mul_le_mul_of_nonneg_left hmass (abs_nonneg _)
  have hnn : 0 ≤ |dlam| * suzukiMass (ltsGenerators H μ dlam (k - 1)) :=
    mul_nonneg (abs_nonneg _) (general_trotter_mass_nonneg _)
  refine (lemma3_remainder_bound _ _ k hshort').trans ?_
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hnn hmono _) (by norm_num)

theorem theorem3_short_interval_error {I : Type} [Fintype I] [DecidableEq I]
    (hs : List (Matrix I I ℂ)) (k : ℕ) (hk : 1 ≤ k) (t : ℝ)
    (hhs : ∀ X ∈ hs, Xᴴ = -X)
    (hshort : ((3 : ℝ) ^ (k - 1) * suzukiMass hs + ‖hs.sum‖) * |t| ≤ 1 / 2) :
    ‖suzukiExponentialWord (recursiveSuzukiGenerators hs (k - 1)) t -
        NormedSpace.exp (t • hs.sum)‖ ≤
      4 * (((3 : ℝ) ^ (k - 1) * suzukiMass hs + ‖hs.sum‖) * |t|) ^ (2 * k + 1) := by
  have hp : 2 * (k - 1) + 3 = 2 * k + 1 := by omega
  obtain ⟨-, -, herr⟩ :=
    recursive_suzuki_actual_simulation_and_cost I hs (k - 1) 1 t hhs (by norm_num)
  have hw : (recursiveSuzukiWord hs (k - 1) t 1).prod =
      suzukiExponentialWord (recursiveSuzukiGenerators hs (k - 1)) t := by
    simp [recursiveSuzukiWord, suzukiExponentialWord]
  rw [hw] at herr
  have hL : 0 ≤ (3 : ℝ) ^ (k - 1) * suzukiMass hs + ‖hs.sum‖ := by
    have h1 : (0 : ℝ) ≤ (3 : ℝ) ^ (k - 1) := by positivity
    have h2 : 0 ≤ suzukiMass hs := general_trotter_mass_nonneg hs
    have h3 : (0 : ℝ) ≤ ‖hs.sum‖ := norm_nonneg _
    nlinarith
  have herrEq : recursiveSuzukiError hs (k - 1) t 1 =
      2 * (Real.exp (((3 : ℝ) ^ (k - 1) * suzukiMass hs + ‖hs.sum‖) * |t|) *
        (((3 : ℝ) ^ (k - 1) * suzukiMass hs + ‖hs.sum‖) * |t|) ^ (2 * k + 1) /
        ((2 * k + 1).factorial : ℝ)) := by
    simp only [recursiveSuzukiError, Nat.cast_one, div_one, hp]
    ring
  rw [herrEq] at herr
  have hstep := exp_factorial_tail_le_two_mul_pow
    (((3 : ℝ) ^ (k - 1) * suzukiMass hs + ‖hs.sum‖) * |t|) (2 * k + 1)
    (mul_nonneg hL (abs_nonneg _)) hshort
  calc
    ‖suzukiExponentialWord (recursiveSuzukiGenerators hs (k - 1)) t -
        NormedSpace.exp (t • hs.sum)‖ ≤
      2 * (Real.exp (((3 : ℝ) ^ (k - 1) * suzukiMass hs + ‖hs.sum‖) * |t|) *
        (((3 : ℝ) ^ (k - 1) * suzukiMass hs + ‖hs.sum‖) * |t|) ^ (2 * k + 1) /
        ((2 * k + 1).factorial : ℝ)) := herr
    _ ≤ 2 * (2 * (((3 : ℝ) ^ (k - 1) * suzukiMass hs + ‖hs.sum‖) * |t|) ^ (2 * k + 1)) :=
      mul_le_mul_of_nonneg_left hstep (by norm_num)
    _ = 4 * (((3 : ℝ) ^ (k - 1) * suzukiMass hs + ‖hs.sum‖) * |t|) ^ (2 * k + 1) := by ring

end Qatlib.Papers.OrderedOpExp08.MainResults
