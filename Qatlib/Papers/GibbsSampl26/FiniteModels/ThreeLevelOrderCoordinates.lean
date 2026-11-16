/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelPermutations
public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelCoordinateMetric
public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelCollisionSourceTables

@[expose] public section


/-! Exact reordered projector and complete source-coordinate identities.
Both population coordinates and every fast matrix coordinate are retained. -/


/-!
# The ordered projector family 201

The permutation assigns the original projectors P2, P0, P1 in that order.
The concrete projector identities are used to attach both collision-face
literal sources to the original physical operators.
-/

open Qatlib.Foundations.PureStateMath
open Matrix
open scoped BigOperators

namespace Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelOrder201
open ThreeLevelCluster ThreeLevelWordDual ThreeLevelCollisionRelabeling

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000
noncomputable section

/-- Order201 low Swap for the stated finite source data. -/
theorem order201_lowSwap : lowSwap order201 = order021 := by
  ext i
  fin_cases i <;> decide

/-- Spectral Projectors order201 zero for the stated finite source data. -/
theorem spectralProjectors_order201_zero : spectralProjectors order201 0 = pTwo := by
  simp [spectralProjectors, order201_apply, projectors]

/-- Spectral Projectors order201 one for the stated finite source data. -/
theorem spectralProjectors_order201_one : spectralProjectors order201 1 = pZero := by
  simp [spectralProjectors, order201_apply, projectors]

/-- Spectral Projectors order201 two for the stated finite source data. -/
theorem spectralProjectors_order201_two : spectralProjectors order201 2 = pOne := by
  simp [spectralProjectors, order201_apply, projectors]

open ThreeLevelGramCertificateCorner ThreeLevelCoordinateMetric
open ThreeLevelCollisionSourceTables

/-- Both population entries and every fast coordinate are transported at once. -/
theorem twoSided_two_edges_stack_mulVec (S : Matrix (Fin 96) (Fin 15) ℂ)
    (A B E F : Fin 6 → Operator 4)
    (hS : ∀ a l, S a l =
      ((if l = 0 then E (sourceIndex a) else 0) +
      (if l = 1 then F (sourceIndex a) else 0) +
      (A (sourceIndex a) * maskedLiteralInput l -
        maskedLiteralInput l * B (sourceIndex a))) (rowIndex a) (columnIndex a))
    (σ : Perm) (c d : ℂ) (Y : Operator 4) (hY : ThreeLevelInvariant.IsFast σ Y)
    (a : Fin 96) :
    (S *ᵥ fullCoordinates c d Y) a =
      (c • E (sourceIndex a) + d • F (sourceIndex a) +
      (A (sourceIndex a) * Y - Y * B (sourceIndex a)))
        (rowIndex a) (columnIndex a) := by
  rw [← twoSided_maskedLiteralInput σ c d Y hY
    (A (sourceIndex a)) (B (sourceIndex a))]
  simp only [Matrix.mulVec, dotProduct, hS, Matrix.add_apply, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib]
  congr 1
  · congr 1
    · simp only [Matrix.ite_apply, Matrix.zero_apply, ite_mul, zero_mul,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true, fullCoordinates_zero]
      ring
    · simp only [Matrix.ite_apply, Matrix.zero_apply, ite_mul, zero_mul,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true, fullCoordinates_one]
      ring
  · apply Finset.sum_congr rfl
    intro l _
    ring



end
end Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelOrder201


/-!
# The ordered projector family 120

The order assigns the original projectors P1, P2, P0. Swapping coincident
low levels gives order210; swapping coincident high levels gives order102.
These identities concern physical relabeling, not coordinate metric equality.
-/

open Qatlib.Foundations.PureStateMath
open Matrix

namespace Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelOrder120
open ThreeLevelCluster ThreeLevelWordDual ThreeLevelCollisionRelabeling ThreeLevelOrder201

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000
noncomputable section

/-- Order120 low Swap for the stated finite source data. -/
theorem order120_lowSwap : lowSwap order120 = order210 := by
  ext i
  fin_cases i <;> decide

/-- Order120 high Swap for the stated finite source data. -/
theorem order120_highSwap : highSwap order120 = order102 := by
  ext i
  fin_cases i <;> decide

/-- Spectral Projectors order120 zero for the stated finite source data. -/
theorem spectralProjectors_order120_zero : spectralProjectors order120 0 = pOne := by
  simp [spectralProjectors, order120_apply, projectors]

/-- Spectral Projectors order120 one for the stated finite source data. -/
theorem spectralProjectors_order120_one : spectralProjectors order120 1 = pTwo := by
  simp [spectralProjectors, order120_apply, projectors]

/-- Spectral Projectors order120 two for the stated finite source data. -/
theorem spectralProjectors_order120_two : spectralProjectors order120 2 = pZero := by
  simp [spectralProjectors, order120_apply, projectors]


end
end Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelOrder120
