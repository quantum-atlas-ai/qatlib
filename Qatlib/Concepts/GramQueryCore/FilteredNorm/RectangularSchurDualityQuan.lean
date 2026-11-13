/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GramQueryCore.FilteredNorm.RectangularSchurDualityStat
import Qatlib.Concepts.GramQueryCore.FilteredNorm.RectangularBudgetRealizationQuan

/-!
# Rectangular Schur multiplier duality

This module transfers filtered γ₂ duality through the rectangular lift. Norm preservation by
`sourceRectLift_norm` and the corner identity `sourceRectLift_hadamard_corner` yield
`rectangularSchurDuality`, including attainment of finite values and unbounded objectives for
infinite values [LeeEtAl2011].

## Main statements

* `sourceRectLift_norm`: The rectangular lift preserves the operator norm.

* `sourceRectDual_eq_lift`: The rectangular dual value equals the filtered γ₂ dual value of the
  rectangular lifts.

* `rectangularSchurDuality`: The rectangular filtered value equals its Schur multiplier dual,
  with attainment for finite values and arbitrarily large feasible objectives for infinite
  values [Lee et al., Lemma A.1][LeeEtAl2011].

## References

* [Lee et al., 2011][LeeEtAl2011]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.GramQueryCore.GammaDuality
open Qatlib.Concepts.GramQueryCore.LowerBoundTools

namespace Qatlib.Concepts.GramQueryCore.FilteredNorm
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ENNReal ComplexOrder

/-- The squared Euclidean norm of a vector on a sum type is the sum of the squared norms of its
two components. -/
theorem rectangularSumState_norm_sq {R S : Type} [Fintype R] [Fintype S]
    (a : QState R) (b : QState S) :
    ‖toEuclidean_fromVec (Sum.elim a b)‖^2 =
      ‖toEuclidean_fromVec a‖^2+‖toEuclidean_fromVec b‖^2 := by
  simp only [norm_toEuclidean_fromVec_sq, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]

/-- The rectangular lift maps a sum-indexed vector to the target matrix applied to its right
component, with zero output in the right component. -/
theorem sourceRectLift_mulVec {R S : Type} [Fintype R] [Fintype S]
    (A : Matrix R S ℂ) (v : QState (R ⊕ S)) :
    sourceRectLift A *ᵥ v = Sum.elim (A *ᵥ (v ∘ Sum.inr)) (fun _ => 0) := by
  ext z
  cases z <;> simp [sourceRectLift, Matrix.mulVec, dotProduct, Fintype.sum_sum_type]

/-- The rectangular lift preserves the operator norm. -/
theorem sourceRectLift_norm {R S : Type} [Fintype R] [DecidableEq R]
    [Fintype S] [DecidableEq S] (A : Matrix R S ℂ) : ‖sourceRectLift A‖ = ‖A‖ := by
  have houtput (v : QState (R ⊕ S)) :
      ‖toEuclidean_fromVec (sourceRectLift A *ᵥ v)‖ =
        ‖toEuclidean_fromVec (A *ᵥ (v ∘ Sum.inr))‖ := by
    have hs : ‖toEuclidean_fromVec (sourceRectLift A *ᵥ v)‖^2 =
        ‖toEuclidean_fromVec (A *ᵥ (v ∘ Sum.inr))‖^2 := by
      rw [sourceRectLift_mulVec, rectangularSumState_norm_sq]
      simp [norm_toEuclidean_fromVec_sq]
    nlinarith [norm_nonneg (toEuclidean_fromVec (sourceRectLift A *ᵥ v)),
      norm_nonneg (toEuclidean_fromVec (A *ᵥ (v ∘ Sum.inr)))]
  apply le_antisymm
  · apply l2_opNorm_le_of_mulVec_le (norm_nonneg A)
    intro v
    have hinput : ‖toEuclidean_fromVec (v ∘ Sum.inr)‖ ≤ ‖toEuclidean_fromVec v‖ := by
      have hv : v = Sum.elim (v ∘ Sum.inl) (v ∘ Sum.inr) := by
        ext z
        cases z <;> rfl
      have hs : ‖toEuclidean_fromVec v‖^2 =
          ‖toEuclidean_fromVec (v ∘ Sum.inl)‖^2+‖toEuclidean_fromVec (v ∘ Sum.inr)‖^2 := by
        conv_lhs => rw [hv]
        exact rectangularSumState_norm_sq _ _
      nlinarith [sq_nonneg ‖toEuclidean_fromVec (v ∘ Sum.inl)‖,
        norm_nonneg (toEuclidean_fromVec (v ∘ Sum.inr)), norm_nonneg (toEuclidean_fromVec v)]
    rw [houtput]
    exact (l2_norm_mulVec_fromVec_le A _).trans
      (mul_le_mul_of_nonneg_left hinput (norm_nonneg A))
  · apply l2_opNorm_le_of_mulVec_le (norm_nonneg (sourceRectLift A))
    intro v
    let pad : QState (R ⊕ S) := Sum.elim (fun _ => 0) v
    have hpad : ‖toEuclidean_fromVec pad‖ = ‖toEuclidean_fromVec v‖ := by
      have hs : ‖toEuclidean_fromVec pad‖^2 = ‖toEuclidean_fromVec v‖^2 := by
        dsimp only [pad]
        rw [rectangularSumState_norm_sq]
        simp [norm_toEuclidean_fromVec_sq]
      nlinarith [norm_nonneg (toEuclidean_fromVec pad), norm_nonneg (toEuclidean_fromVec v)]
    have hright : pad ∘ Sum.inr = v := rfl
    have h := l2_norm_mulVec_fromVec_le (sourceRectLift A) pad
    rw [houtput, hright, hpad] at h
    exact h

/-- The upper-right rectangular block of a matrix indexed by a sum type. -/
def sourceRectCorner {R S : Type} (M : Matrix (R ⊕ S) (R ⊕ S) ℂ) : Matrix R S ℂ :=
  fun r s => M (.inl r) (.inr s)

/-- Entrywise multiplying a rectangular lift uses only the upper-right block of the multiplier. -/
theorem sourceRectLift_hadamard_corner {R S : Type}
    (A : Matrix R S ℂ) (M : Matrix (R ⊕ S) (R ⊕ S) ℂ) :
    sourceRectLift A ⊙ M = sourceRectLift (A ⊙ sourceRectCorner M) := by
  ext r s
  cases r <;> cases s <;> simp [sourceRectLift, sourceRectCorner, Matrix.hadamard_apply]

/-- The rectangular lift preserves entrywise products. -/
theorem sourceRectLift_hadamard {R S : Type} (A M : Matrix R S ℂ) :
    sourceRectLift A ⊙ sourceRectLift M = sourceRectLift (A ⊙ M) := by
  ext r s
  cases r <;> cases s <;> simp [sourceRectLift, Matrix.hadamard_apply]

/-- The rectangular dual value equals the filtered γ₂ dual value of the rectangular lifts. -/
theorem sourceRectDual_eq_lift {R S : Type} [Fintype R] [DecidableEq R]
    [Fintype S] [DecidableEq S] {n : ℕ} (A : Matrix R S ℂ) (Z : Fin n → Matrix R S ℂ) :
    sourceRectDual A Z = filteredGamma2DualValue (sourceRectLift A) (fun j => sourceRectLift (Z j)) := by
  apply le_antisymm
  · unfold sourceRectDual
    apply iSup_le
    intro M
    have hfilters : ∀ j, ‖sourceRectLift (Z j) ⊙ sourceRectLift M.val‖ ≤ 1 := by
      intro j
      rw [sourceRectLift_hadamard, sourceRectLift_norm]
      exact M.property j
    apply le_iSup_of_le ⟨sourceRectLift M.val,hfilters⟩
    rw [sourceRectLift_hadamard, sourceRectLift_norm]
  · unfold filteredGamma2DualValue
    apply iSup_le
    intro M
    have hfilters : ∀ j, ‖Z j ⊙ sourceRectCorner M.val‖ ≤ 1 := by
      intro j
      have h := M.property j
      rw [sourceRectLift_hadamard_corner, sourceRectLift_norm] at h
      exact h
    apply le_iSup_of_le ⟨sourceRectCorner M.val,hfilters⟩
    rw [sourceRectLift_hadamard_corner, sourceRectLift_norm]

/-- The rectangular filtered value equals its Schur multiplier dual, with attainment for finite
values and arbitrarily large feasible objectives for infinite values [Lee et al., Lemma
A.1][LeeEtAl2011]. -/
theorem rectangularSchurDuality :
    ∀ (R S : Type) [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
      (n : ℕ) (A : Matrix R S ℂ) (Z : Fin n → Matrix R S ℂ),
      sourceRectValue A Z = sourceRectDual A Z ∧
      (sourceRectValue A Z < ⊤ → ∃ M : Matrix R S ℂ,
        (∀ j, ‖Z j ⊙ M‖ ≤ 1) ∧ sourceRectValue A Z=ENNReal.ofReal ‖A ⊙ M‖) ∧
      (sourceRectValue A Z = ⊤ → ∀ t : ℝ, ∃ M : Matrix R S ℂ,
        (∀ j, ‖Z j ⊙ M‖ ≤ 1) ∧ t ≤ ‖A ⊙ M‖) := by
  intro R S _ _ _ _ n A Z
  have hstrong := filteredGamma2_strong_duality (R ⊕ S) n (sourceRectLift A)
    (fun j => sourceRectLift (Z j))
  have hvalue : sourceRectValue A Z = sourceRectDual A Z := by
    rw [sourceRectValue_eq_lift, sourceRectDual_eq_lift]
    exact hstrong.1
  refine ⟨hvalue, ?_, ?_⟩
  · intro hfinite
    obtain ⟨M, hM, hmax⟩ := hstrong.2 (by rwa [← sourceRectValue_eq_lift])
    refine ⟨sourceRectCorner M, ?_, ?_⟩
    · intro j
      have h := hM j
      rwa [sourceRectLift_hadamard_corner, sourceRectLift_norm] at h
    · rw [sourceRectValue_eq_lift, hmax, sourceRectLift_hadamard_corner, sourceRectLift_norm]
  · intro htop t
    by_contra hnone
    have hbounded : sourceRectDual A Z ≤ ENNReal.ofReal t := by
      unfold sourceRectDual
      apply iSup_le
      intro M
      apply ENNReal.ofReal_le_ofReal
      have ht : ‖A ⊙ M.val‖ < t := by
        by_contra! ht
        exact hnone ⟨M.val, M.property, ht⟩
      exact ht.le
    rw [← hvalue, htop] at hbounded
    exact ENNReal.ofReal_ne_top (top_le_iff.mp hbounded)

end Qatlib.Concepts.GramQueryCore.FilteredNorm
