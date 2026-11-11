/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TrotterFormula.GeneralOrder.GeneralTrotterOrderConsumers

/-!
# Taylor certificates for multi-product formulas

This module defines finite weighted exponential words as `multiProduct`, their Taylor
`coefficient`, and an explicit `localCertificate` combining coefficient mismatch with
exponential remainder bounds. Matching the target coefficients removes the finite mismatch term,
yielding local error estimates for the multi-product setting of [AftabAnTrivisa2026].

The concrete fourth-order construction combines one Strang step and two half-steps with weights
-1/3 and 4/3, matches degrees below five, and has an explicit fifth-order local bound.

## Main statements

* `local_error_from_coefficients`: bounds local error by coefficient mismatch and Taylor tails.
* `matched_local_error`: uses exact coefficient matching.
* `fourth_local_error`: specializes to the fourth-order two-branch construction.

## References

* [Aftab et al., 2026][AftabAnTrivisa2026]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CommutLCHS26.MainResults.MPFRemainder

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.TrotterFormula.GeneralOrder

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J]

/-- The finite real-weighted sum of the exponential words in a family. -/
def multiProduct (ws : J → List (Matrix I I ℂ)) (a : J → ℝ) (t : ℝ) : Matrix I I ℂ :=
  ∑ j, a j • suzukiExponentialWord (ws j) t

/-- The finite weighted sum of the degree-n series coefficients of the word family. -/
def coefficient (ws : J → List (Matrix I I ℂ)) (a : J → ℝ) (n : ℕ) : Matrix I I ℂ :=
  ∑ j, a j • suzukiSeries (ws j) n

/-- The sum of finite Taylor coefficient mismatches and weighted exponential tail bounds for the
word family and target generator. -/
def localCertificate (ws : J → List (Matrix I I ℂ)) (a : J → ℝ)
    (Z : Matrix I I ℂ) (t : ℝ) (d : ℕ) : ℝ :=
  (∑ n ∈ Finset.range d, |t| ^ n *
    ‖coefficient ws a n - ((n.factorial : ℝ)⁻¹) • Z ^ n‖) +
  (∑ j, |a j| * (Real.exp (|t| * suzukiMass (ws j)) *
    (|t| * suzukiMass (ws j)) ^ d / (d.factorial : ℝ))) +
  Real.exp (|t| * ‖Z‖) * (|t| * ‖Z‖) ^ d / (d.factorial : ℝ)

/-- The error after truncating the multi-product Taylor series below degree d is bounded by the
sum of the absolute-weighted word tail estimates. -/
theorem multiProduct_taylor_error (ws : J → List (Matrix I I ℂ)) (a : J → ℝ)
    (t : ℝ) (d : ℕ) :
    ‖multiProduct ws a t - ∑ n ∈ Finset.range d, t ^ n • coefficient ws a n‖ ≤
      ∑ j, |a j| * (Real.exp (|t| * suzukiMass (ws j)) *
        (|t| * suzukiMass (ws j)) ^ d / (d.factorial : ℝ)) := by
  have hp : (∑ n ∈ Finset.range d, t ^ n • coefficient ws a n) =
      ∑ j, a j • (∑ n ∈ Finset.range d, t ^ n • suzukiSeries (ws j) n) := by
    simp only [coefficient, Finset.smul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro n _
    rw [smul_smul, smul_smul, mul_comm]
  rw [hp, multiProduct, ← Finset.sum_sub_distrib]
  simp_rw [← smul_sub]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (general_trotter_taylor_tail (ws j) t d) (abs_nonneg _)

/-- The multi-product error against exp(tZ) is bounded by the finite coefficient mismatch and
the word and target exponential Taylor tails. -/
theorem local_error_from_coefficients (ws : J → List (Matrix I I ℂ)) (a : J → ℝ)
    (Z : Matrix I I ℂ) (t : ℝ) (d : ℕ) :
    ‖multiProduct ws a t - NormedSpace.exp (t • Z)‖ ≤
      (∑ n ∈ Finset.range d, |t| ^ n *
        ‖coefficient ws a n - ((n.factorial : ℝ)⁻¹) • Z ^ n‖) +
      (∑ j, |a j| * (Real.exp (|t| * suzukiMass (ws j)) *
        (|t| * suzukiMass (ws j)) ^ d / (d.factorial : ℝ))) +
      Real.exp (|t| * ‖Z‖) * (|t| * ‖Z‖) ^ d / (d.factorial : ℝ) := by
  let P := ∑ n ∈ Finset.range d, t ^ n • coefficient ws a n
  let Q := ∑ n ∈ Finset.range d, t ^ n • (((n.factorial : ℝ)⁻¹) • Z ^ n)
  have hmiddle : ‖P - Q‖ ≤ ∑ n ∈ Finset.range d, |t| ^ n *
      ‖coefficient ws a n - ((n.factorial : ℝ)⁻¹) • Z ^ n‖ := by
    dsimp [P, Q]
    rw [← Finset.sum_sub_distrib]
    simp_rw [← smul_sub]
    simpa only [norm_smul, Real.norm_eq_abs, abs_pow] using!
      norm_sum_le (s := Finset.range d)
        (f := fun n => t ^ n • (coefficient ws a n - ((n.factorial : ℝ)⁻¹) • Z ^ n))
  have htarget : ‖NormedSpace.exp (t • Z) - Q‖ ≤
      Real.exp (|t| * ‖Z‖) * (|t| * ‖Z‖) ^ d / (d.factorial : ℝ) := by
    simpa only [suzukiExponentialWord, suzukiSeries_singleton, suzukiMass,
      List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      List.sum_cons, List.sum_nil, add_zero, Q] using! general_trotter_taylor_tail [Z] t d
  have hsplit : multiProduct ws a t - NormedSpace.exp (t • Z) =
      (P - Q) + (multiProduct ws a t - P) - (NormedSpace.exp (t • Z) - Q) := by abel
  rw [hsplit]
  exact (norm_sub_le _ _).trans ((_root_.add_le_add
    (norm_add_le (P - Q) (multiProduct ws a t - P)) le_rfl).trans
    (_root_.add_le_add (_root_.add_le_add hmiddle (multiProduct_taylor_error ws a t d)) htarget))

/-- When all coefficients below degree d match the target exponential, the local error is
bounded by the weighted word tails plus the target tail. -/
theorem matched_local_error (ws : J → List (Matrix I I ℂ)) (a : J → ℝ)
    (Z : Matrix I I ℂ) (t : ℝ) (d : ℕ)
    (hc : ∀ n, n < d → coefficient ws a n = ((n.factorial : ℝ)⁻¹) • Z ^ n) :
    ‖multiProduct ws a t - NormedSpace.exp (t • Z)‖ ≤
      (∑ j, |a j| * (Real.exp (|t| * suzukiMass (ws j)) *
        (|t| * suzukiMass (ws j)) ^ d / (d.factorial : ℝ))) +
      Real.exp (|t| * ‖Z‖) * (|t| * ‖Z‖) ^ d / (d.factorial : ℝ) := by
  have hz : (∑ n ∈ Finset.range d, |t| ^ n *
      ‖coefficient ws a n - ((n.factorial : ℝ)⁻¹) • Z ^ n‖) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    simp [hc n (Finset.mem_range.mp hn)]
  simpa only [hz, zero_add] using! local_error_from_coefficients ws a Z t d

/-- The two generator words consisting of one Strang step and two half-sized Strang steps. -/
def fourthWords (X Y : Matrix I I ℂ) (j : Fin 2) : List (Matrix I I ℂ) :=
  if j = 0 then [(1 / 2 : ℝ) • X, Y, (1 / 2 : ℝ) • X]
  else [(1 / 4 : ℝ) • X, (1 / 2 : ℝ) • Y, (1 / 4 : ℝ) • X,
    (1 / 4 : ℝ) • X, (1 / 2 : ℝ) • Y, (1 / 4 : ℝ) • X]

/-- The two fourth-order extrapolation weights -1/3 and 4/3. -/
def fourthWeights : Fin 2 → ℝ := ![-1 / 3, 4 / 3]

/-- The flattened generator list for q Strang steps with X scaled by 1/(2q) and Y by 1/q. -/
def strangRepeats (X Y : Matrix I I ℂ) (q : ℕ) : List (Matrix I I ℂ) :=
  (List.replicate q [(1 / (2 * (q : ℝ))) • X, (1 / (q : ℝ)) • Y,
    (1 / (2 * (q : ℝ))) • X]).flatten

/-- The exponential word of the repeated Strang generator list equals the q-th power of the
single scaled Strang word. -/
theorem strangRepeats_actual (X Y : Matrix I I ℂ) (q : ℕ) (t : ℝ) :
    suzukiExponentialWord (strangRepeats X Y q) t =
      (suzukiExponentialWord [(1 / (2 * (q : ℝ))) • X, (1 / (q : ℝ)) • Y,
        (1 / (2 * (q : ℝ))) • X] t) ^ q := by
  simp [strangRepeats, suzukiExponentialWord, List.map_flatten, List.prod_flatten]

omit [Fintype I] [DecidableEq I] in

/-- The j-th fourth-order word is the Strang word with j + 1 subdivisions. -/
theorem fourthWords_eq_subdivisions (X Y : Matrix I I ℂ) (j : Fin 2) :
    fourthWords X Y j = strangRepeats X Y (j.val + 1) := by
  fin_cases j <;> norm_num [fourthWords, strangRepeats, List.replicate_succ]

/-- The fourth-order multi-product equals -1/3 times one Strang word plus 4/3 times the square
of a half-sized Strang word. -/
theorem fourth_actual_words (X Y : Matrix I I ℂ) (t : ℝ) :
    multiProduct (fourthWords X Y) fourthWeights t =
      (-1 / 3 : ℝ) • suzukiExponentialWord [(1 / 2 : ℝ) • X, Y, (1 / 2 : ℝ) • X] t +
      (4 / 3 : ℝ) • (suzukiExponentialWord
        [(1 / 4 : ℝ) • X, (1 / 2 : ℝ) • Y, (1 / 4 : ℝ) • X] t) ^ 2 := by
  simp [multiProduct, fourthWeights, fourthWords, Fin.sum_univ_two,
    suzukiExponentialWord, pow_two, Matrix.mul_assoc]

set_option maxHeartbeats 4000000 in

/-- The fourth-order two-branch construction matches the coefficients of exp(t(X + Y)) through
degree four. -/
theorem fourth_coefficients (X Y : Matrix I I ℂ) (n : ℕ) (hn : n < 5) :
    coefficient (fourthWords X Y) fourthWeights n = ((n.factorial : ℝ)⁻¹) • (X + Y) ^ n := by
  unfold coefficient
  rw [Fin.sum_univ_two]
  change (-1 / 3 : ℝ) • suzukiSeries [(1 / 2 : ℝ) • X, Y, (1 / 2 : ℝ) • X] n +
    (4 / 3 : ℝ) • suzukiSeries [(1 / 4 : ℝ) • X, (1 / 2 : ℝ) • Y, (1 / 4 : ℝ) • X,
      (1 / 4 : ℝ) • X, (1 / 2 : ℝ) • Y, (1 / 4 : ℝ) • X] n = _
  interval_cases n
  all_goals simp only [suzukiSeries_zero, suzukiSeries_cons_one, suzukiSeries_cons_two,
    suzukiSeries_cons_three, suzukiSeries_cons_four, suzukiSeries_nil_succ,
    Nat.factorial, Nat.cast_one, inv_one, one_smul]
  all_goals simp only [pow_succ, pow_zero, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.mul_assoc,
    smul_add, Matrix.one_mul, Matrix.mul_zero, add_zero, zero_add]
  all_goals match_scalars <;> ring

/-- The fourth-order multi-product error is bounded by its weighted word Taylor tails and the
target Taylor tail, all starting at degree five. -/
theorem fourth_local_error (X Y : Matrix I I ℂ) (t : ℝ) :
    ‖multiProduct (fourthWords X Y) fourthWeights t - NormedSpace.exp (t • (X + Y))‖ ≤
      (∑ j : Fin 2, |fourthWeights j| * (Real.exp (|t| * suzukiMass (fourthWords X Y j)) *
        (|t| * suzukiMass (fourthWords X Y j)) ^ 5 / (Nat.factorial 5 : ℝ))) +
      Real.exp (|t| * ‖X + Y‖) * (|t| * ‖X + Y‖) ^ 5 / (Nat.factorial 5 : ℝ) :=
  matched_local_error _ _ _ _ _ (fourth_coefficients X Y)

end Qatlib.Papers.CommutLCHS26.MainResults.MPFRemainder
