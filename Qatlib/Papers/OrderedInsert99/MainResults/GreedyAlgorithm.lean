/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OrderedInsert99.MainResults.InvariantDefs

/-!
# Monotonicity and fixed points of the greedy update

The scalar update `greedyProbStep` squares the average of the square roots of `P + (c i)^2`. For
positive `N` and nonnegative `P`, the update cannot decrease `P`, and zero correction data leave
it unchanged. These identities formalize the greedy-step monotonicity and fixed-point
calculation of [FarhiEtAl1999].

## Main statements

* `greedyProbStep_mono`: For positive `N` and nonnegative `P`, the greedy update is at least `P`
  for every correction vector.
* `greedyProbStep_zero_cot`: For positive `N` and nonnegative `P`, zero correction values leave
  the greedy update equal to `P`.
* `greedy_prob_monotone_and_fixed`: For positive `N`, the greedy update does not decrease any
  nonnegative input for arbitrary correction data, fixes one for zero corrections, and fixes
  every nonnegative input for zero corrections.

## References

* [Farhi et al., 1999][FarhiEtAl1999]
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.OrderedInsert99.MainResults

open scoped BigOperators

/-- The square of the average of `sqrt (P + (c i)^2)` over the `N` correction values. -/
noncomputable def greedyProbStep (N : ℕ) (P : ℝ) (c : Fin N → ℝ) : ℝ :=
  ((1 / (N : ℝ)) * ∑ i : Fin N, Real.sqrt (P + (c i) ^ 2)) ^ 2

/-- The greedy scalar update is nonnegative. -/
theorem greedyProbStep_nonneg (N : ℕ) (P : ℝ) (c : Fin N → ℝ) :
    0 ≤ greedyProbStep N P c := by
  unfold greedyProbStep
  positivity

/-- For positive `N` and nonnegative `P`, the greedy update is at least `P` for every correction
vector. -/
theorem greedyProbStep_mono (N : ℕ) (hN : 0 < N) (P : ℝ) (hP : 0 ≤ P)
    (c : Fin N → ℝ) : P ≤ greedyProbStep N P c := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hterm : ∀ i : Fin N, Real.sqrt P ≤ Real.sqrt (P + (c i) ^ 2) := by
    intro i
    apply Real.sqrt_le_sqrt
    nlinarith [sq_nonneg (c i)]
  have hsum : (N : ℝ) * Real.sqrt P ≤ ∑ i : Fin N, Real.sqrt (P + (c i) ^ 2) := by
    calc (N : ℝ) * Real.sqrt P = ∑ _i : Fin N, Real.sqrt P := by
          simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ ∑ i : Fin N, Real.sqrt (P + (c i) ^ 2) := Finset.sum_le_sum (fun i _ => hterm i)
  have hstep : Real.sqrt P ≤ (1 / (N : ℝ)) * ∑ i : Fin N, Real.sqrt (P + (c i) ^ 2) := by
    have h := mul_le_mul_of_nonneg_left hsum (by positivity : (0 : ℝ) ≤ 1 / (N : ℝ))
    have h2 : (1 / (N : ℝ)) * ((N : ℝ) * Real.sqrt P) = Real.sqrt P := by
      field_simp
    rwa [h2] at h
  calc P = (Real.sqrt P) ^ 2 := (Real.sq_sqrt hP).symm
    _ ≤ ((1 / (N : ℝ)) * ∑ i : Fin N, Real.sqrt (P + (c i) ^ 2)) ^ 2 :=
        pow_le_pow_left₀ (Real.sqrt_nonneg P) hstep 2

/-- For positive `N` and nonnegative `P`, zero correction values leave the greedy update equal
to `P`. -/
theorem greedyProbStep_zero_cot (N : ℕ) (hN : 0 < N) (P : ℝ) (hP : 0 ≤ P) :
    greedyProbStep N P (fun _ => 0) = P := by
  have hsum :
      (∑ i : Fin N, Real.sqrt (P + (fun _ : Fin N => (0 : ℝ)) i ^ 2)) =
        (N : ℝ) * Real.sqrt P := by
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  unfold greedyProbStep
  rw [hsum]
  have h : (1 / (N : ℝ)) * ((N : ℝ) * Real.sqrt P) = Real.sqrt P := by
    field_simp
  rw [h, Real.sq_sqrt hP]

/-- For positive `N`, the greedy update does not decrease any nonnegative input for arbitrary
correction data, fixes one for zero corrections, and fixes every nonnegative input for zero
corrections [FarhiEtAl1999]. -/
theorem greedy_prob_monotone_and_fixed (N : ℕ) (hN : 0 < N) :
    (∀ P : ℝ, 0 ≤ P → ∀ c : Fin N → ℝ, P ≤ greedyProbStep N P c) ∧
      greedyProbStep N 1 (fun _ => 0) = 1 ∧
      (∀ P : ℝ, 0 ≤ P → greedyProbStep N P (fun _ => 0) = P) := by
  refine ⟨fun P hP c => greedyProbStep_mono N hN P hP c, ?_, ?_⟩
  · have h := greedyProbStep_zero_cot N hN 1 (by norm_num)
    simpa using h
  · exact fun P hP => greedyProbStep_zero_cot N hN P hP

end Qatlib.Papers.OrderedInsert99.MainResults
