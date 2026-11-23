/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic

@[expose] public section

/-!
# A normalization counterexample for the QPCA nearest-centroid readout

Theorem 2 of [Tang2021], Theorem 2 reports the projection probability as
`lambda / Z` after forming the augmented normalized matrix `M`.  The real
one-dimensional instance `u = 1`, `V = -1` already makes that printed value
equal to `2`, so it cannot be a probability.  The missing factor is the
Frobenius mass of `M`.

This file keeps the scalar witness explicit and states the repaired readout as
`lambda / (Z * frobNormSq M)`.  Working over `ℝ` is a faithful specialization
of the source's complex statement, so the witness refutes the literal source
formula without adding any modelling assumptions.

References:

* [Tang2021], Theorem 2. <https://arxiv.org/abs/1811.00414v3>, pp. 2, 3, 6.
* The source's augmented matrix is `M = [u/‖u‖; V/(sqrt n ‖V_i‖)]` and
  `Z = ‖u‖² + ‖V‖_F²/n`.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators Matrix

namespace Qatlib.Papers.QPCAAssume18.QuantumCentroid

/-- The squared centroid distance in the one-row real specialization. -/
def centroidLambda (u v : ℝ) : ℝ := (u - v) ^ 2

/-- The source's average-norm parameter `Z` for one data row. -/
def centroidZ (u v : ℝ) : ℝ := u ^ 2 + v ^ 2

/-- The projection probability printed in the source statement. -/
def printedProjectionProbability (lambda Z : ℝ) : ℝ := lambda / Z

/-- Squared Frobenius mass of a finite real matrix. -/
def frobNormSq {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  ∑ i, ∑ j, (M i j) ^ 2

/-- The two-row matrix used by the scalar `u,V` witness. -/
def scalarAugmentedMatrix (u v : ℝ) : Matrix (Fin 2) (Fin 1) ℝ :=
  fun i _ => if i = 0 then u else v

/-- The repaired probability, retaining the Frobenius normalization of `M`. -/
def correctedProjectionProbability {m n : ℕ}
    (lambda Z : ℝ) (M : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  lambda / (Z * frobNormSq M)

/-- The scalar augmented matrix for `u = 1`, `V = -1`. -/
def witnessMatrix : Matrix (Fin 2) (Fin 1) ℝ :=
  scalarAugmentedMatrix 1 (-1)

/-- The source's distance parameter is `4` on the explicit `u = 1`, `V = -1`
witness. -/
theorem witness_lambda : centroidLambda 1 (-1) = 4 := by
  norm_num [centroidLambda]

/-- The source's average-norm parameter is `Z = 2` on the witness. -/
theorem witness_z : centroidZ 1 (-1) = 2 := by
  norm_num [centroidZ]

/-- The augmented normalized matrix has squared Frobenius mass `2` on the
one-dimensional witness. -/
theorem witness_frobNormSq : frobNormSq witnessMatrix = 2 := by
  simp [witnessMatrix, scalarAugmentedMatrix, frobNormSq]

/-- The literal source formula reports the impossible value `2`. -/
theorem witness_printed_value :
    printedProjectionProbability (centroidLambda 1 (-1)) (centroidZ 1 (-1)) = 2 := by
  norm_num [printedProjectionProbability, centroidLambda, centroidZ]

/-- The literal source formula is outside the probability interval on the
explicit witness. -/
theorem witness_printed_value_not_probability :
    ¬ (0 ≤ printedProjectionProbability (centroidLambda 1 (-1)) (centroidZ 1 (-1)) ∧
      printedProjectionProbability (centroidLambda 1 (-1)) (centroidZ 1 (-1)) ≤ 1) := by
  norm_num [printedProjectionProbability, centroidLambda, centroidZ]

/-- The repaired formula gives the normalized value `1` on the same witness. -/
theorem witness_corrected_value :
    correctedProjectionProbability (centroidLambda 1 (-1)) (centroidZ 1 (-1)) witnessMatrix = 1 := by
  unfold correctedProjectionProbability
  rw [witness_frobNormSq]
  norm_num [correctedProjectionProbability, centroidLambda, centroidZ]

/-- The repaired readout is exactly `lambda / (Z * ‖M‖²_F)`. -/
theorem corrected_projection_probability_eq (lambda Z : ℝ)
    {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) :
    correctedProjectionProbability lambda Z M = lambda / (Z * frobNormSq M) := rfl

/-- If the augmented matrix is Frobenius-normalized, the repaired formula
reduces to the source quotient. -/
theorem corrected_projection_probability_eq_printed_of_frobNormSq_eq_one
    (lambda Z : ℝ) {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ)
    (hM : frobNormSq M = 1) :
    correctedProjectionProbability lambda Z M = printedProjectionProbability lambda Z := by
  simp [correctedProjectionProbability, printedProjectionProbability, hM]

end Qatlib.Papers.QPCAAssume18.QuantumCentroid
