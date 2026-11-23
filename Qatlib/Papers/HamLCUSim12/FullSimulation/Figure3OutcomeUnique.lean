/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Algebra.Star.BigOperators
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# Coefficientwise uniqueness of the successful outcome in Figure 3

This module isolates the row-orthogonality step of [ChildsWiebe2012], Appendix A, Eq. (A9).
Success here means coefficientwise agreement up to scale, not merely equality of the
resulting data operators; linearly dependent SELECT terms can hide coefficient differences.
Full support is needed for cancellation: zero-padded terms are not covered by this statement.
Under the coefficientwise hypotheses below, two successful rows would be proportional:
given a preparation matrix `A`, a unitary measurement gate `B`, coefficients `C` with
full support, and scales `K₀` and `K₁ ≠ 0` with `B j₀ m * A m jin = K₀ * C m` and
`B j₁ m * A m jin = K₁ * C m` for every `m`, distinct outcomes `j₀ ≠ j₁` are impossible.
The statement covers the orthogonality step for coefficientwise success in Theorem 13.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.HamLCUSim12.FullSimulation

open Matrix
open scoped BigOperators

/-- For coefficients with full support, two distinct outcomes of the unitary measurement
gate cannot both realize the same coefficient family up to scale when the second scale
is nonzero. This is the row-orthogonality step in [ChildsWiebe2012], Appendix A, Eq. (A9). -/
theorem figure3_success_outcome_unique {J : Type} [Fintype J] [DecidableEq J]
    (A B : Matrix J J ℂ) (hB : B ∈ Matrix.unitaryGroup J ℂ)
    (j₀ j₁ jin : J) (hj : j₀ ≠ j₁) (C : J → ℂ) (hC : ∀ m, C m ≠ 0)
    (K₀ K₁ : ℂ) (hK₁ : K₁ ≠ 0)
    (h₀ : ∀ m, B j₀ m * A m jin = K₀ * C m)
    (h₁ : ∀ m, B j₁ m * A m jin = K₁ * C m) :
    False := by
  have hB' : B * star B = 1 := (Matrix.mem_unitaryGroup_iff).mp hB
  -- The right factors `A m jin` are nonzero because `K₁ * C m ≠ 0`.
  have hA0 : ∀ m, A m jin ≠ 0 := fun m =>
    (mul_ne_zero_iff.mp (by rw [h₁ m]; exact mul_ne_zero hK₁ (hC m))).2
  -- Row proportionality forced by the two success conditions.
  have hprop : ∀ m, K₀ * B j₁ m = K₁ * B j₀ m := fun m => by
    have e1 : (K₀ * B j₁ m) * A m jin = (K₁ * B j₀ m) * A m jin := by
      rw [mul_assoc, h₁ m, mul_assoc, h₀ m]
      ring
    exact mul_right_cancel₀ (hA0 m) e1
  -- Orthogonality of rows `j₀` and `j₁` of `B`.
  have hortho : ∑ m : J, B j₁ m * star (B j₀ m) = 0 := by
    simpa [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply, Ne.symm hj]
      using congrArg (fun M : Matrix J J ℂ => M j₁ j₀) hB'
  have hrow : ∑ m : J, B j₀ m * star (B j₀ m) = 1 := by
    simpa [Matrix.mul_apply, Matrix.star_apply]
      using congrArg (fun M : Matrix J J ℂ => M j₀ j₀) hB'
  -- Combine proportionality with orthogonality and the unit norm.
  have hcombine : K₀ * (∑ m : J, B j₁ m * star (B j₀ m))
      = K₁ * (∑ m : J, B j₀ m * star (B j₀ m)) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    have hp := hprop m
    rw [← mul_assoc, hp, mul_assoc]
  rw [hortho, hrow] at hcombine
  simp at hcombine
  exact hK₁ hcombine.symm

end Qatlib.Papers.HamLCUSim12.FullSimulation
