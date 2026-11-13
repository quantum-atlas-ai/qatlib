/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HadamardAnn19.NativeReduction.Actual

/-!
# Small Hadamard Ground Configurations

This module gives explicit Boolean encodings of order-two and order-four orthogonal sign
matrices for the search model of [SuksmonoMinato2019]. The declarations `exampleTwo_frame` and
`exampleFour_frame` verify their column Gram identities.

`completed_frame_ground` extends any orthogonal sign frame with its correct AND ancillas and
proves that the resulting configuration minimizes the paper energy at coefficient `4 * M ^ 2`,
provided there are at least two rows. The concrete examples use coefficients 16 and 64.

## Main statements

* `exampleTwo_frame` and `exampleFour_frame` certify the explicit orthogonal frames.
* `completed_frame_ground` proves minimality of the valid completion of any orthogonal frame.
* `exampleTwo_ground` and `exampleFour_ground` specialize this result to the two explicit
  matrices.

## References

* [Suksmono and Minato, 2019][SuksmonoMinato2019]
-/

set_option autoImplicit false
namespace Qatlib.Papers.HadamardAnn19.NativeReduction.Examples
open Qatlib.Foundations.BooleanEnergy.HadamardGram
open Qatlib.Foundations.BooleanEnergy.PenaltyExact
open Qatlib.Foundations.BooleanEnergy.QuboForms

/-- The two-by-two Boolean matrix with rows `(false, true)` and `(true, true)`, whose associated
sign columns are orthogonal. -/
def exampleTwo : Fin 2 → Fin 2 → Bool := ![![false,true],![true,true]]

/-- The sign matrix encoded by `exampleTwo` has column Gram matrix equal to twice the identity. -/
theorem exampleTwo_frame : IsOrthogonalFrame exampleTwo := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [gram,signMatrix,Matrix.mul_apply,Matrix.transpose_apply,
      Fin.sum_univ_two,exampleTwo,spin,bit]

/-- An explicit four-by-four Boolean matrix encoding an order-four Hadamard sign matrix. -/
def exampleFour : Fin 4 → Fin 4 → Bool :=
  ![![true,true,false,false],![false,true,false,true],
    ![true,true,true,true],![true,false,false,true]]

/-- The sign matrix encoded by `exampleFour` has column Gram matrix equal to four times the
identity. -/
theorem exampleFour_frame : IsOrthogonalFrame exampleFour := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [gram,signMatrix,Matrix.mul_apply,Matrix.transpose_apply,
      Fin.sum_univ_succ,exampleFour,spin,bit]

/-- For at least two rows, completing an orthogonal sign frame with its correct AND ancillas
gives a ground configuration of the paper energy at coefficient `4 * M ^ 2`. -/
theorem completed_frame_ground {M N : ℕ} (hM : 2 ≤ M)
    (q : Fin M → Fin N → Bool) (hq : IsOrthogonalFrame q) :
    IsGround (paperEnergy (4*(M:ℝ)^2)) (complete q) := by
  apply (source_ground_iff hM _).mpr
  refine ⟨complete_pair_valid q,?_⟩
  intro y
  change energy q ≤ energy y
  rw [(energy_zero_iff q).mpr hq]
  exact energy_nonneg y

/-- The valid completion of `exampleTwo` minimizes the paper energy with penalty coefficient 16. -/
theorem exampleTwo_ground : IsGround (paperEnergy 16) (complete exampleTwo) := by
  convert completed_frame_ground (by decide) exampleTwo exampleTwo_frame using 1
  norm_num

/-- The valid completion of `exampleFour` minimizes the paper energy with penalty coefficient
64. -/
theorem exampleFour_ground : IsGround (paperEnergy 64) (complete exampleFour) := by
  convert completed_frame_ground (by decide) exampleFour exampleFour_frame using 1
  norm_num

end Qatlib.Papers.HadamardAnn19.NativeReduction.Examples
