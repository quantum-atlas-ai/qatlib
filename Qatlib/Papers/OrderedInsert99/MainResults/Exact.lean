/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OrderedInsert99.MainResults.LowerBound

/-!
# Normalized exact stages for ordered insertion

This module counts the odd and even index classes and proves normalization of `targetAmp`. An
`ExactStage` therefore has `successProbability` equal to one. These finite normalization results
support the exact invariant ordered-insertion algorithms of [FarhiEtAl1999].

## Main statements

* `card_filter_parity`: For positive `N` and parity zero or one, exactly `N` indices have the
  specified parity.
* `targetAmp_sum_sq`: For positive `N` and parity zero or one, the squared moduli of the target
  amplitudes sum to one.
* `exactStage_prob`: An exact stage of an invariant ordered-insertion algorithm with positive
  `N` has success probability one.

## References

* [Farhi et al., 1999][FarhiEtAl1999]
-/

set_option warningAsError false

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.OrderedInsert99.MainResults

open scoped BigOperators

/-- For positive `N`, the odd index set has cardinality `N`. -/
lemma oddIdx_card (N : ℕ) (hN : 0 < N) : (oddIdx N).card = N := by
  have h := test_sum hN (fun _ => (1 : ℝ))
  have h1 : (↑(oddIdx N).card : ℝ) = (N : ℝ) := by
    simpa using h
  exact_mod_cast h1

/-- For positive `N` and parity zero or one, exactly `N` indices have the specified parity. -/
lemma card_filter_parity (N parity : ℕ) (hN : 0 < N) (hpar : parity < 2) :
    (Finset.univ.filter (fun p : Idx N => p.val % 2 = parity)).card = N := by
  have hcode : parity = 0 ∨ parity = 1 := by omega
  rcases hcode with rfl | rfl
  · have hsum := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Idx N))) (p := fun p : Idx N => p.val % 2 = 0)
    have hcompl : (Finset.univ.filter (fun p : Idx N => ¬ p.val % 2 = 0)) = oddIdx N := by
      apply Finset.filter_congr
      intro p _
      constructor <;> intro h <;> omega
    have huniv : (Finset.univ : Finset (Idx N)).card = 2 * N := by
      simp [Idx]
    have hodd : (oddIdx N).card = N := oddIdx_card N hN
    rw [hcompl, huniv, hodd] at hsum
    omega
  · have heq : (Finset.univ.filter (fun p : Idx N => p.val % 2 = 1)) = oddIdx N := by
      apply Finset.filter_congr
      intro p _
      rfl
    rw [heq]
    exact oddIdx_card N hN

/-- For positive `N` and parity zero or one, the squared moduli of the target amplitudes sum to
one. -/
lemma targetAmp_sum_sq (N parity : ℕ) (hN : 0 < N) (hpar : parity < 2) :
    ∑ p : Idx N, ‖targetAmp N parity p‖ ^ 2 = 1 := by
  have hsq : ((Real.sqrt (N : ℝ))⁻¹) ^ 2 = (1 : ℝ) / N := by
    rw [inv_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ N), one_div]
  have hterm : ∀ p : Idx N,
      ‖targetAmp N parity p‖ ^ 2 =
        if p.val % 2 = parity then (1 : ℝ) / N else 0 := by
    intro p
    rw [targetAmp_norm N parity hN p]
    split_ifs with h
    · rw [hsq]
    · simp
  rw [Finset.sum_congr rfl (fun p _ => hterm p)]
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero]
  rw [card_filter_parity N parity hN hpar, nsmul_eq_mul]
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  field_simp

/-- An exact stage of an invariant ordered-insertion algorithm with positive `N` has success
probability one. -/
lemma exactStage_prob (N k : ℕ) (hN : 0 < N) (α : ℕ → Idx N → ℝ)
    (h : ExactStage N k α) : successProbability N k α = 1 := by
  have hψ : ∀ p, psi N α k p = targetAmp N (k % 2) p := h
  have hsum : successAmplitude N k α =
      (((∑ p : Idx N, ‖targetAmp N (k % 2) p‖ ^ 2 : ℝ)) : ℂ) := by
    unfold successAmplitude
    rw [Finset.sum_congr rfl (fun p _ => by rw [hψ p])]
    push_cast
    apply Finset.sum_congr rfl
    intro p _
    rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    rfl
  unfold successProbability
  rw [hsum, targetAmp_sum_sq N (k % 2) hN (by omega)]
  norm_num

end Qatlib.Papers.OrderedInsert99.MainResults
