/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QuantumSVM13.MinusReadout
import Qatlib.Papers.QuantumSVM13.MinusReadout.SwapTest

/-!
# A finite Frozen consumer for the minus branch (QuantumSVM13)

This module consumes the `realQState`/`minusBranchState` bridge at the two
computational basis states of `Fin 2`.  It computes the coordinate Born
probabilities and the all-coordinate event probability.  The resulting branch
has mass `1/2`, so it is intentionally not a normalized state; no SWAP circuit
or state-preparation claim is made here.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open scoped BigOperators

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Papers.QuantumSVM13.MinusReadout

open Qatlib.Papers.QuantumSVM13.MinusReadout


/-- The finite minus branch obtained from the two computational basis states. -/
noncomputable def classicalBasisMinus2 : QState (Fin 2) :=
  minusBranchState classicalZero2 classicalOne2

/-- The zero coordinate of the finite minus branch has Born probability `1/4`. -/
theorem classicalBasisMinus2_bornProb_zero :
    BornProb classicalBasisMinus2 (0 : Fin 2) = (1 / 4 : ℝ) := by
  rw [classicalBasisMinus2, bornProb_minusBranchState]
  norm_num [classicalZero2, classicalOne2]

/-- The one coordinate of the finite minus branch has Born probability `1/4`. -/
theorem classicalBasisMinus2_bornProb_one :
    BornProb classicalBasisMinus2 (1 : Fin 2) = (1 / 4 : ℝ) := by
  rw [classicalBasisMinus2, bornProb_minusBranchState]
  norm_num [classicalZero2, classicalOne2]

/-- The finite minus branch has total event probability `1/2`. -/
theorem classicalBasisMinus2_measureProb_univ :
    MeasureProb classicalBasisMinus2 Finset.univ = (1 / 2 : ℝ) := by
  rw [classicalBasisMinus2, ← minusBranchWeight_eq_measureProb_univ]
  exact classical_basis_minusBranchWeight

/-- The finite minus branch is not normalized because its mass is `1/2`. -/
theorem not_normalized_classicalBasisMinus2 :
    ¬ Normalized classicalBasisMinus2 := by
  intro hnorm
  have huniv := measureProb_univ hnorm
  rw [classicalBasisMinus2_measureProb_univ] at huniv
  norm_num at huniv

end Qatlib.Papers.QuantumSVM13.MinusReadout
