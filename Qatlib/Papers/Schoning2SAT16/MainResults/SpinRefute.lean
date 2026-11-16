/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.Schoning2SAT16.MainResults.SourceSpinModel
public import Mathlib.Tactic

@[expose] public section


set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.Schoning2SAT16.MainResults.ContractRefute

open Matrix
open scoped BigOperators
open Qatlib.Papers.Schoning2SAT16.MainResults

/-- An empty clause family has no coefficients. -/
def emptyCoeff : Fin 0 → ℂ := Fin.elim0

/-- An empty clause family has no qubit indices. -/
def emptyIndex : Fin 0 → Fin 1 := Fin.elim0

/-- The distinct-support hypothesis is satisfied vacuously by the empty family. -/
theorem emptyDistinct : ∀ α : Fin 0, emptyIndex α ≠ emptyIndex α := by
  intro α
  exact Fin.elim0 α

/-- The all-zero basis index of a one-qubit register. -/
def zeroIndex : QIdx 1 := fun _ => 0

/-- The matrix unit projecting onto the all-zero basis vector. -/
def zeroProjector : NOp 1 := Matrix.single zeroIndex zeroIndex 1

/-- The selected matrix unit has first-spin expectation one. -/
theorem first_expect : Matrix.trace (totalSpin 1 * zeroProjector) = 1 := by
  rw [zeroProjector, Matrix.trace_mul_single]
  simp [totalSpin, sigmaZAt, zeroIndex, hz]

/-- The selected matrix unit has squared-spin expectation one. -/
theorem second_expect : Matrix.trace (totalSpinSq 1 * zeroProjector) = 1 := by
  have hspin : totalSpin 1 = sigmaZAt (0 : Fin 1) := by
    simp [totalSpin]
  have hdiag : (totalSpinSq 1) zeroIndex zeroIndex = 1 := by
    rw [totalSpinSq, hspin, sigmaZ_mul_sigmaZ_apply]
    simp [zeroIndex, hz]
  simpa [zeroProjector, Matrix.trace_mul_single] using hdiag

/-- With no clauses the legacy averaged channel is the zero map. -/
theorem emptyChannel :
    familyChannel emptyCoeff emptyCoeff emptyIndex emptyIndex emptyDistinct zeroProjector = 0 := by
  simp [familyChannel]

/-- The legacy first-spin identity fails for an allowed empty clause family. -/
theorem spin_first_zero :
    Matrix.trace (totalSpin 1 *
      familyChannel emptyCoeff emptyCoeff emptyIndex emptyIndex emptyDistinct zeroProjector) ≠
      Matrix.trace (totalSpin 1 * zeroProjector) := by
  rw [emptyChannel, Matrix.mul_zero, Matrix.trace_zero, first_expect]
  norm_num

/-- The legacy second-spin identity also fails for the same empty clause family. -/
theorem spin_second_zero :
    Matrix.trace (totalSpinSq 1 *
      familyChannel emptyCoeff emptyCoeff emptyIndex emptyIndex emptyDistinct zeroProjector) -
      Matrix.trace (totalSpinSq 1 * zeroProjector) ≠
      (2 / (0 : ℂ)) * ∑ α : Fin 0,
        Matrix.trace (clauseProj (emptyCoeff α) (emptyCoeff α)
          (emptyIndex α) (emptyIndex α) (emptyDistinct α) * zeroProjector) := by
  rw [emptyChannel, Matrix.mul_zero, Matrix.trace_zero, second_expect]
  norm_num

end Qatlib.Papers.Schoning2SAT16.MainResults.ContractRefute
