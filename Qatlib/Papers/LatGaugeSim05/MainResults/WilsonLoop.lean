/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.Diagonal
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic

/-!
# Wilson loop traces and unitary phases

The identities `u6_wilson_transcription` and `u6_wilson_transcription_three` expand traces of
matrix products as cyclic sums over internal labels. The phase function `u6Eigenphase` has unit
modulus, yielding the unitary identity for a diagonal matrix of real-angle phases. See
[ByrnesYamamoto2006] for the paper context.

## Main statements

* `u6_wilson_transcription_three`: The trace of a product of three matrices is the cyclic triple
  sum of their entries.
* `u6_diagonal_phase_unitary`: A diagonal matrix whose entries are `u6Eigenphase` at real angles
  has adjoint-times-matrix product equal to the identity.

## References

* [Byrnes and Yamamoto, 2006][ByrnesYamamoto2006]
-/

set_option autoImplicit false

noncomputable section

open Matrix

namespace Qatlib.Papers.LatGaugeSim05.MainResults

/-- The trace of a product of two matrices is the cyclic double sum of their entries
[ByrnesYamamoto2006]. -/
theorem u6_wilson_transcription {β : Type} [Fintype β] [DecidableEq β]
    (V0 V1 : Matrix β β ℂ) :
    (V0 * V1).trace = ∑ m1, ∑ m2, V0 m1 m2 * V1 m2 m1 := by

  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]

/-- The trace of a product of three matrices is the cyclic triple sum of their entries
[ByrnesYamamoto2006]. -/
theorem u6_wilson_transcription_three {β : Type} [Fintype β] [DecidableEq β]
    (V0 V1 V2 : Matrix β β ℂ) :
    (V0 * V1 * V2).trace =
      ∑ m1, ∑ m2, ∑ m3, V0 m1 m2 * V1 m2 m3 * V2 m3 m1 := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.sum_comm]

/-- The complex phase `exp (-θ * I)` associated with a real angle. -/
def u6Eigenphase (θ : ℝ) : ℂ := Complex.exp ((-(θ : ℂ)) * Complex.I)

/-- Multiplying the conjugate of `u6Eigenphase θ` by the phase itself gives one
[ByrnesYamamoto2006]. -/
theorem u6Eigenphase_unit (θ : ℝ) : star (u6Eigenphase θ) * u6Eigenphase θ = 1 := by
  unfold u6Eigenphase
  rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  have h : (starRingEnd ℂ) ((-(θ : ℂ)) * Complex.I) + (-(θ : ℂ)) * Complex.I = 0 := by
    simp only [map_mul, map_neg, Complex.conj_ofReal, Complex.conj_I]
    ring
  rw [h, Complex.exp_zero]

/-- A diagonal matrix whose entries are `u6Eigenphase` at real angles has adjoint-times-matrix
product equal to the identity [ByrnesYamamoto2006]. -/
theorem u6_diagonal_phase_unitary {ι : Type} [Fintype ι] [DecidableEq ι]
    (W : ι → ℝ) :
    (Matrix.diagonal (fun i => u6Eigenphase (W i)))ᴴ *
      Matrix.diagonal (fun i => u6Eigenphase (W i)) = 1 := by
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  convert Matrix.diagonal_one using 2
  funext i
  exact u6Eigenphase_unit (W i)

end Qatlib.Papers.LatGaugeSim05.MainResults
