/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Instantaneous08.MainResults.ConstantAction.CodeWeight

/-!
# Directional differences and X-program bias

This module defines `fdiff` as the signed action at `a` minus the signed action at `a + s`. It
rewrites the π/8 X-program bias using this finite difference, following the
directional-difference formulation of Lemma 5 in [ShepherdBremner2009].

## Main statements

* `fdiff_eq`: expresses the finite difference through selected-row weights.
* `bias_eq_cosSq_fdiff`: gives the bias as a cosine-squared average.
* `bias_eq_one_iff`: characterizes unit bias by pointwise unit cosine squares.

## References

* [Shepherd and Bremner, 2009][ShepherdBremner2009]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.Instantaneous08.MainResults.ConstantAction

open Qatlib.Papers.Instantaneous08.MainResults.XProgram

attribute [local instance] Classical.propDecidable

/-- The finite difference `actSum p a - actSum p (a + s)` of the signed action in direction `s`. -/
def fdiff {n k : ℕ} (p : Fin k → F2Vec n) (s a : F2Vec n) : ℝ :=
  actSum p a - actSum p (a + s)

/-- The finite difference equals twice the selected-row count minus four times the induced code
weight. See [ShepherdBremner2009]. -/
theorem fdiff_eq {n k : ℕ} (p : Fin k → F2Vec n) (s a : F2Vec n) :
    fdiff p s a = 2 * ((nSub p s : ℝ) - 2 * (codeWeight p s a : ℝ)) := by
  unfold fdiff
  rw [actSum_shift]
  ring

/-- At action π/8, the bias in direction `s` is the uniform average of `cos (π / 16 * fdiff p s
a) ^ 2`, following [Shepherd and Bremner, Lemma 5][ShepherdBremner2009]. -/
theorem bias_eq_cosSq_fdiff {n k : ℕ} (p : Fin k → F2Vec n) (s : F2Vec n) :
    (∑ x : F2Vec n,
        (if dot x s = 0 then prob p (fun _ => Real.pi / 8) x else 0)) =
      ((Fintype.card (F2Vec n) : ℝ))⁻¹ *
        ∑ a : F2Vec n, Real.cos (Real.pi / 16 * fdiff p s a) ^ 2 := by
  rw [show (∑ x : F2Vec n,
        (if dot x s = 0 then prob p (fun _ => Real.pi / 8) x else 0)) =
      (1 / 2) * (1 + ((Fintype.card (F2Vec n) : ℝ))⁻¹ *
        ∑ a : F2Vec n, Real.cos (2 * (Real.pi / 8) *
          ((nSub p s : ℝ) - 2 * (codeWeight p s a : ℝ)))) by
    simpa using bias_eq_cos p (Real.pi / 8) s]
  have hcos : ∀ a : F2Vec n,
      Real.cos (2 * (Real.pi / 8) * ((nSub p s : ℝ) - 2 * (codeWeight p s a : ℝ))) =
        2 * Real.cos (Real.pi / 16 * fdiff p s a) ^ 2 - 1 := by
    intro a
    have hx : Real.pi / 16 * fdiff p s a =
        Real.pi / 8 * ((nSub p s : ℝ) - 2 * (codeWeight p s a : ℝ)) := by
      rw [fdiff_eq]; ring
    rw [hx]
    have hsq := Real.cos_sq (Real.pi / 8 * ((nSub p s : ℝ) - 2 * (codeWeight p s a : ℝ)))
    have harg : 2 * (Real.pi / 8) * ((nSub p s : ℝ) - 2 * (codeWeight p s a : ℝ)) =
        2 * (Real.pi / 8 * ((nSub p s : ℝ) - 2 * (codeWeight p s a : ℝ))) := by ring
    rw [harg]
    linarith
  simp only [hcos]
  have hS : (∑ a : F2Vec n,
        (2 * Real.cos (Real.pi / 16 * fdiff p s a) ^ 2 - 1)) =
      2 * (∑ a : F2Vec n, Real.cos (Real.pi / 16 * fdiff p s a) ^ 2) -
        (Fintype.card (F2Vec n) : ℝ) := by
    rw [Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_const, Finset.card_univ]
    simp
  rw [hS]
  have hN : (Fintype.card (F2Vec n) : ℝ) ≠ 0 := by
    rw [ClassicalApprox.card_f2vec]; positivity
  field_simp
  ring

/-- The π/8 X-program bias equals one if and only if every cosine-square term in its
finite-difference average equals one. -/
theorem bias_eq_one_iff {n k : ℕ} (p : Fin k → F2Vec n) (s : F2Vec n) :
    (∑ x : F2Vec n,
        (if dot x s = 0 then prob p (fun _ => Real.pi / 8) x else 0)) = 1 ↔
      ∀ a : F2Vec n, Real.cos (Real.pi / 16 * fdiff p s a) ^ 2 = 1 := by
  rw [bias_eq_cosSq_fdiff]
  set N : ℝ := (Fintype.card (F2Vec n) : ℝ) with hN
  have hNpos : 0 < N := by
    rw [hN, ClassicalApprox.card_f2vec]; positivity
  have hNne : N ≠ 0 := ne_of_gt hNpos
  have hcosle : ∀ a : F2Vec n, Real.cos (Real.pi / 16 * fdiff p s a) ^ 2 ≤ 1 :=
    fun a => Real.cos_sq_le_one _
  constructor
  · intro h
    have hsum : N⁻¹ * (∑ a : F2Vec n, Real.cos (Real.pi / 16 * fdiff p s a) ^ 2) = 1 := h
    have hEq : (∑ a : F2Vec n, Real.cos (Real.pi / 16 * fdiff p s a) ^ 2) = N := by
      have : (∑ a : F2Vec n, Real.cos (Real.pi / 16 * fdiff p s a) ^ 2) = N * 1 := by
        rw [← hsum]; field_simp
      rw [this, mul_one]
    have hall : ∀ a ∈ (Finset.univ : Finset (F2Vec n)),
        Real.cos (Real.pi / 16 * fdiff p s a) ^ 2 = (1 : ℝ) := by
      refine (Finset.sum_eq_sum_iff_of_le (fun a _ => hcosle a)).mp ?_
      rw [hEq, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    intro a
    exact hall a (Finset.mem_univ a)
  · intro h
    rw [Finset.sum_congr rfl (fun a _ => h a)]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    rw [← hN]
    exact inv_mul_cancel₀ hNne

end Qatlib.Papers.Instantaneous08.MainResults.ConstantAction
