/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.AdversaryHam11.MainResults.ProgressReduction

@[expose] public section


/-! # The genuine initial spectral-progress identity

This preserves the complete old closed mathematical identity. The public
mean-value reduction remains genuine conditional analysis; neither identity
supplies the missing physical oracle-block or terminal-measurement bridge.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
namespace Qatlib.Papers.AdversaryHam11.MainResults.SourceMath
open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.AdversaryHam11.MainResults
/-- The actual initial progress equals the principal spectral eigenvalue. -/
theorem initialValue {X H : Type} [Fintype X] [DecidableEq X] [Fintype H] [DecidableEq H]
    {Γ : Matrix X X ℝ} {δ : X → ℝ} {state : X → ℝ → QState H} {initial : QState H}
    (hinit : ∀ x, state x 0 = initial) (hnorm : Normalized initial)
    (hδunit : ∑ x, δ x ^ 2 = 1)
    (hδeig : Γ.mulVec δ = (‖Γ‖) • δ) :
    progressMeasure Γ δ state 0 = ((‖Γ‖) : ℂ) := by
  have hinner : ∀ x y, Qatlib.Foundations.PureStateMath.Inner (state x 0) (state y 0) = 1 := by
    intro x y
    rw [hinit x, hinit y]
    exact (normalized_iff_inner_self initial).mp hnorm
  unfold progressMeasure
  simp only [hinner, mul_one]
  have hsum : (∑ x, ∑ y, Γ x y * δ x * δ y) = ‖Γ‖ := by
    have hmv : ∀ x, (∑ y, Γ x y * δ y) = (Γ.mulVec δ) x := by
      intro x
      rw [Matrix.mulVec, dotProduct]
    calc ∑ x, ∑ y, Γ x y * δ x * δ y
        = ∑ x, δ x * (∑ y, Γ x y * δ y) := by
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro y _
          ring
      _ = ∑ x, δ x * (Γ.mulVec δ) x := by simp only [hmv]
      _ = ∑ x, δ x * (‖Γ‖ * δ x) := by
          rw [hδeig]
          simp only [Pi.smul_apply, smul_eq_mul]
      _ = ‖Γ‖ * ∑ x, δ x ^ 2 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _
          ring
      _ = ‖Γ‖ := by rw [hδunit]; ring
  have hcast : (∑ x, ∑ y, ((Γ x y : ℝ) : ℂ) * ((δ x : ℝ) : ℂ) * ((δ y : ℝ) : ℂ))
      = ((∑ x, ∑ y, Γ x y * δ x * δ y : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hcast, hsum]
end Qatlib.Papers.AdversaryHam11.MainResults.SourceMath
