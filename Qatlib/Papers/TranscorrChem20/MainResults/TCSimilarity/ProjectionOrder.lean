/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.TranscorrChem20.MainResults.TCSimilarity.Basic

/-!
# Compression and transcorrelation need not commute

This module gives explicit two-dimensional matrices exhibiting a failure of compatibility
between compression and transcorrelated similarity. Compressing the original Hamiltonian to the
first coordinate gives zero, whereas compressing its transformed matrix gives the scalar `-1/3`,
precluding similarity in the compressed space. See [McArdleTew2020].

## Main statements

* `projectionCorrelator_exp`: Explicit exponential of the Hermitian correlator.
* `transformed_compression_entry`: The transformed compressed entry is `-1/3`.
* `projection_order_not_similar`: No scalar conjugation relates the two compressions.

## References

* [McArdle and Tew, 2020][McArdleTew2020]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section
open Matrix NormedSpace
open Qatlib.Papers.TranscorrChem20.MainResults.ImaginaryTime

namespace Qatlib.Papers.TranscorrChem20.MainResults.TCSimilarity

/-- The two-dimensional matrix with rows `(1, 1)` and `(1, -1)` used to diagonalize the
correlator. -/
def reflection : Op 2 := !![1,1;1,-1]

/-- One half of `reflection`, serving as its inverse. -/
def reflectionInv : Op 2 := !![1/2,1/2;1/2,-1/2]

/-- Multiplying `reflectionInv` by `reflection` gives the identity. -/
theorem reflectionInv_mul : reflectionInv * reflection = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [reflection, reflectionInv, Matrix.mul_apply, Fin.sum_univ_two]

/-- The two-dimensional correlator obtained by conjugating `diagonal ![Real.log 3, 0]` by
`reflection`. -/
def projectionCorrelator : Op 2 :=
  reflectionInv * diagonal ![(Real.log 3 : ℂ),0] * reflection

/-- The explicit projection-order correlator is Hermitian. See [McArdleTew2020]. -/
theorem projectionCorrelator_hermitian : projectionCorrelator.IsHermitian := by
  have he : projectionCorrelator =
      !![(Real.log 3 : ℂ)/2,(Real.log 3 : ℂ)/2;
         (Real.log 3 : ℂ)/2,(Real.log 3 : ℂ)/2] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [projectionCorrelator, reflection, reflectionInv, Matrix.mul_apply,
        Matrix.vecMul, dotProduct, Fin.sum_univ_two] <;> ring
  rw [he]
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    change (starRingEnd ℂ) ((Real.log 3 : ℂ)/2) = (Real.log 3 : ℂ)/2
    rw [map_div₀, Complex.conj_ofReal, map_ofNat]

/-- The exponential of the correlator is the matrix with diagonal entries two and off-diagonal
entries one. -/
theorem projectionCorrelator_exp : exp projectionCorrelator = !![2,1;1,2] := by
  have hr : IsUnit reflection := by
    rw [Matrix.isUnit_iff_isUnit_det]
    norm_num [reflection, Matrix.det_fin_two, isUnit_iff_ne_zero]
  have hi : reflection⁻¹ = reflectionInv := Matrix.inv_eq_left_inv reflectionInv_mul
  have hd : exp (diagonal ![(Real.log 3 : ℂ),0]) = diagonal ![3,1] := by
    rw [Matrix.exp_diagonal]
    congr 1
    funext i
    rw [Pi.coe_exp]
    fin_cases i
    · change exp (Real.log 3 : ℂ) = (3 : ℂ)
      rw [← Complex.exp_eq_exp_ℂ, ← Complex.ofReal_exp, Real.exp_log (by norm_num : (0:ℝ)<3)]
      rfl
    · simp
  have h := Matrix.exp_conj' reflection (diagonal ![(Real.log 3 : ℂ),0]) hr
  rw [hi, hd] at h
  change exp projectionCorrelator = _ at h
  rw [h]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [reflection, reflectionInv, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

/-- The exponential of the negative correlator has diagonal entries `2/3` and off-diagonal
entries `-1/3`. -/
theorem projectionCorrelator_exp_neg : exp (-projectionCorrelator) = !![2/3,-1/3;-1/3,2/3] := by
  rw [Matrix.exp_neg, projectionCorrelator_exp]
  apply Matrix.inv_eq_left_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two]

/-- The two-dimensional Hamiltonian with diagonal entries zero and one. -/
def projectionHamiltonian : Op 2 := !![0,0;0,1]

/-- Compression of a two-dimensional matrix to its first diagonal entry, viewed as a
one-dimensional matrix. -/
def compressFirst (A : Op 2) : Op 1 := fun _ _ => A 0 0

/-- The first diagonal entry of the transcorrelated example Hamiltonian is `-1/3`. -/
theorem transformed_compression_entry :
    compressFirst (tc projectionHamiltonian projectionCorrelator) 0 0 = -(1/3:ℂ) := by
  norm_num [compressFirst, tc, projectionHamiltonian, projectionCorrelator_exp,
    projectionCorrelator_exp_neg, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

/-- For every one-dimensional matrix `S`, conjugating the compressed original Hamiltonian by `S`
cannot equal the compression of the transcorrelated Hamiltonian. See [McArdleTew2020]. -/
theorem projection_order_not_similar (S : Op 1) :
    S⁻¹ * compressFirst projectionHamiltonian * S ≠
      compressFirst (tc projectionHamiltonian projectionCorrelator) := by
  have hz : compressFirst projectionHamiltonian = 0 := by
    ext i j
    norm_num [compressFirst, projectionHamiltonian]
  intro h
  rw [hz, Matrix.mul_zero, Matrix.zero_mul] at h
  have he := congrArg (fun A : Op 1 => A 0 0) h
  change (0 : ℂ) = compressFirst (tc projectionHamiltonian projectionCorrelator) 0 0 at he
  rw [transformed_compression_entry] at he
  norm_num at he

end Qatlib.Papers.TranscorrChem20.MainResults.TCSimilarity
