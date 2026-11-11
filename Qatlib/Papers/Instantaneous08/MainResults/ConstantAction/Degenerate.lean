/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Instantaneous08.MainResults.XProgram
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic

/-!
# Degenerate action angles in X-programs

This module defines the collision probability `collisionProb` and total row sum `totalRow` of an
X-program. It proves deterministic output and unit collision probability when each angle is an
integer multiple of π or an odd multiple of π/2, covering the corresponding cases of Lemma 2 in
[ShepherdBremner2009].

## Main statements

* `prob_eq_one_zero_of_multiple_pi`: gives deterministic zero output for integer multiples of π.
* `prob_eq_one_totalRow_of_odd_pi_div_two`: gives deterministic total-row output for odd
  multiples of π/2.
* `collisionProb_eq_one_of_odd_pi_div_two`: evaluates the collision probability in the latter
  case.

## References

* [Shepherd and Bremner, 2009][ShepherdBremner2009]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.Instantaneous08.MainResults.ConstantAction

open Qatlib.Papers.Instantaneous08.MainResults.XProgram

/-- The collision probability of an X-program, defined as the sum of squared output
probabilities. -/
def collisionProb {n k : ℕ} (p : Fin k → F2Vec n) (θ : Fin k → ℝ) : ℝ :=
  ∑ x : F2Vec n, prob p θ x ^ 2

/-- The sum of all rows of the binary program matrix. -/
def totalRow {n k : ℕ} (p : Fin k → F2Vec n) : F2Vec n :=
  ∑ i, p i

/-- The sine of an integer multiple of π vanishes. -/
theorem sin_eq_zero_of_int_mul_pi {θ : ℝ} (h : ∃ m : ℤ, θ = m * Real.pi) :
    Real.sin θ = 0 := by
  obtain ⟨m, rfl⟩ := h
  exact Real.sin_int_mul_pi m

/-- The squared cosine of an integer multiple of π equals one. -/
theorem cos_sq_eq_one_of_int_mul_pi {θ : ℝ} (h : ∃ m : ℤ, θ = m * Real.pi) :
    Real.cos θ ^ 2 = 1 := by
  obtain ⟨m, rfl⟩ := h
  have hsin : Real.sin ((m : ℝ) * Real.pi) = 0 := Real.sin_int_mul_pi m
  have h := Real.cos_sq_add_sin_sq ((m : ℝ) * Real.pi)
  rw [hsin] at h
  nlinarith

/-- The cosine of an odd integer multiple of π/2 vanishes. -/
theorem cos_eq_zero_of_odd_mul_pi_div_two {θ : ℝ}
    (h : ∃ m : ℤ, θ = (2 * (m : ℝ) + 1) * (Real.pi / 2)) : Real.cos θ = 0 := by
  obtain ⟨m, rfl⟩ := h
  have hrewrite : (2 * (m : ℝ) + 1) * (Real.pi / 2) =
      (m : ℝ) * Real.pi + Real.pi / 2 := by ring
  rw [hrewrite, Real.cos_add_pi_div_two, Real.sin_int_mul_pi]
  ring

/-- The squared sine of an odd integer multiple of π/2 equals one. -/
theorem sin_sq_eq_one_of_odd_mul_pi_div_two {θ : ℝ}
    (h : ∃ m : ℤ, θ = (2 * (m : ℝ) + 1) * (Real.pi / 2)) : Real.sin θ ^ 2 = 1 := by
  have hcos := cos_eq_zero_of_odd_mul_pi_div_two h
  have h := Real.sin_sq_add_cos_sq θ
  rw [hcos] at h
  nlinarith

/-- When every angle is an integer multiple of π, the path sum is supported at zero and equals
the product of the cosines there. -/
theorem pathSum_eq_single_of_multiple_pi {n k : ℕ} (p : Fin k → F2Vec n)
    (θ : Fin k → ℝ) (hθ : ∀ i, ∃ m : ℤ, θ i = m * Real.pi) (x : F2Vec n) :
    pathSum p θ x = if x = 0 then ∏ i, (Real.cos (θ i) : ℂ) else 0 := by
  rw [pathSum]
  rw [Finset.sum_eq_single (fun _ : Fin k => false)]
  · have hsample : pathSample p (fun _ : Fin k => false) = 0 := by
      simp [pathSample]
    rw [hsample]
    by_cases hx : x = 0
    · simp [hx, pathWeight, pathCoeff]
    · rw [if_neg (Ne.symm hx), if_neg hx]
      simp
  · intro b _ hb
    have hex : ∃ i, b i = true := by
      by_contra h
      apply hb
      funext i
      by_cases hi : b i
      · exact absurd ⟨i, hi⟩ h
      · simpa using hi
    obtain ⟨i, hi⟩ := hex
    have hz : pathCoeff (θ i) (b i) = 0 := by
      have hsin := sin_eq_zero_of_int_mul_pi (hθ i)
      simp [hi, pathCoeff_true, hsin]
    have hweight : pathWeight θ b = 0 := by
      rw [pathWeight]
      exact Finset.prod_eq_zero (Finset.mem_univ i) hz
    simp [hweight]
  · intro h
    exact absurd (Finset.mem_univ (fun _ : Fin k => false)) h

/-- When every angle is an integer multiple of π, the output is zero with probability one. See
[ShepherdBremner2009]. -/
theorem prob_eq_one_zero_of_multiple_pi {n k : ℕ} (p : Fin k → F2Vec n)
    (θ : Fin k → ℝ) (hθ : ∀ i, ∃ m : ℤ, θ i = m * Real.pi) :
    prob p θ 0 = 1 := by
  rw [prob, circuit_eq_pathSum, pathSum_eq_single_of_multiple_pi p θ hθ 0, if_pos rfl]
  rw [map_prod Complex.normSq]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [Complex.normSq_ofReal, ← sq]
  exact cos_sq_eq_one_of_int_mul_pi (hθ i)

/-- When every angle is an integer multiple of π, every nonzero output has probability zero. -/
theorem prob_eq_zero_of_ne_zero_of_multiple_pi {n k : ℕ} (p : Fin k → F2Vec n)
    (θ : Fin k → ℝ) (hθ : ∀ i, ∃ m : ℤ, θ i = m * Real.pi) {x : F2Vec n}
    (hx : x ≠ 0) : prob p θ x = 0 := by
  rw [prob, circuit_eq_pathSum, pathSum_eq_single_of_multiple_pi p θ hθ x, if_neg hx]
  simp

/-- When every angle is an integer multiple of π, the collision probability equals one. See
[ShepherdBremner2009]. -/
theorem collisionProb_eq_one_of_multiple_pi {n k : ℕ} (p : Fin k → F2Vec n)
    (θ : Fin k → ℝ) (hθ : ∀ i, ∃ m : ℤ, θ i = m * Real.pi) :
    collisionProb p θ = 1 := by
  rw [collisionProb, Finset.sum_eq_single 0]
  · rw [prob_eq_one_zero_of_multiple_pi p θ hθ]
    norm_num
  · intro x _ hx
    rw [prob_eq_zero_of_ne_zero_of_multiple_pi p θ hθ hx]
    norm_num
  · intro h
    exact absurd (Finset.mem_univ (0 : F2Vec n)) h

/-- When every angle is an odd multiple of π/2, the path sum is supported at `totalRow p` and
equals the product of `I * sin (θ i)` there. -/
theorem pathSum_eq_single_of_odd_pi_div_two {n k : ℕ} (p : Fin k → F2Vec n)
    (θ : Fin k → ℝ)
    (hθ : ∀ i, ∃ m : ℤ, θ i = (2 * (m : ℝ) + 1) * (Real.pi / 2)) (x : F2Vec n) :
    pathSum p θ x =
      if x = totalRow p then ∏ i, (Complex.I * (Real.sin (θ i) : ℂ)) else 0 := by
  rw [pathSum]
  rw [Finset.sum_eq_single (fun _ : Fin k => true)]
  · have hsample : pathSample p (fun _ : Fin k => true) = totalRow p := by
      simp [pathSample, totalRow]
    rw [hsample]
    by_cases hx : x = totalRow p
    · simp [hx, pathWeight, pathCoeff]
    · rw [if_neg (Ne.symm hx), if_neg hx]
      simp
  · intro b _ hb
    have hex : ∃ i, b i = false := by
      by_contra h
      apply hb
      funext i
      cases hbi : b i with
      | false => exact absurd ⟨i, hbi⟩ h
      | true => rfl
    obtain ⟨i, hi⟩ := hex
    have hz : pathCoeff (θ i) (b i) = 0 := by
      have hcos := cos_eq_zero_of_odd_mul_pi_div_two (hθ i)
      simp [hi, pathCoeff_false, hcos]
    have hweight : pathWeight θ b = 0 := by
      rw [pathWeight]
      exact Finset.prod_eq_zero (Finset.mem_univ i) hz
    simp [hweight]
  · intro h
    exact absurd (Finset.mem_univ (fun _ : Fin k => true)) h

/-- When every angle is an odd multiple of π/2, the output equals `totalRow p` with probability
one. See [ShepherdBremner2009]. -/
theorem prob_eq_one_totalRow_of_odd_pi_div_two {n k : ℕ} (p : Fin k → F2Vec n)
    (θ : Fin k → ℝ)
    (hθ : ∀ i, ∃ m : ℤ, θ i = (2 * (m : ℝ) + 1) * (Real.pi / 2)) :
    prob p θ (totalRow p) = 1 := by
  rw [prob, circuit_eq_pathSum,
    pathSum_eq_single_of_odd_pi_div_two p θ hθ (totalRow p), if_pos rfl]
  rw [map_prod Complex.normSq]
  refine Finset.prod_eq_one fun i _ => ?_
  have hsin := sin_sq_eq_one_of_odd_mul_pi_div_two (hθ i)
  simp only [Complex.normSq_mul, Complex.normSq_I, Complex.normSq_ofReal, one_mul,
    ← sq]
  exact hsin

/-- When every angle is an odd multiple of π/2, every output distinct from `totalRow p` has
probability zero. -/
theorem prob_eq_zero_of_ne_totalRow_of_odd_pi_div_two {n k : ℕ}
    (p : Fin k → F2Vec n) (θ : Fin k → ℝ)
    (hθ : ∀ i, ∃ m : ℤ, θ i = (2 * (m : ℝ) + 1) * (Real.pi / 2)) {x : F2Vec n}
    (hx : x ≠ totalRow p) : prob p θ x = 0 := by
  rw [prob, circuit_eq_pathSum,
    pathSum_eq_single_of_odd_pi_div_two p θ hθ x, if_neg hx]
  simp

/-- When every angle is an odd multiple of π/2, the collision probability equals one. See
[ShepherdBremner2009]. -/
theorem collisionProb_eq_one_of_odd_pi_div_two {n k : ℕ} (p : Fin k → F2Vec n)
    (θ : Fin k → ℝ)
    (hθ : ∀ i, ∃ m : ℤ, θ i = (2 * (m : ℝ) + 1) * (Real.pi / 2)) :
    collisionProb p θ = 1 := by
  rw [collisionProb, Finset.sum_eq_single (totalRow p)]
  · rw [prob_eq_one_totalRow_of_odd_pi_div_two p θ hθ]
    norm_num
  · intro x _ hx
    rw [prob_eq_zero_of_ne_totalRow_of_odd_pi_div_two p θ hθ hx]
    norm_num
  · intro h
    exact absurd (Finset.mem_univ (totalRow p)) h

end Qatlib.Papers.Instantaneous08.MainResults.ConstantAction
