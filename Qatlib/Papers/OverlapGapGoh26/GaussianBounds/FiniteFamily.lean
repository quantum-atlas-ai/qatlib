/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OverlapGapGoh26.GaussianBounds.LinearTail

/-!
# Gaussian tails for finite families of unit tensors

`finite_unit_family_tail` bounds the probability that any member of a finite family of
multilinear evaluations exceeds a nonnegative threshold in absolute value. Each slot has unit
Euclidean norm, so the Gaussian tail bound acquires only the cardinality of the family. This is
a finite union estimate for the Gaussian model associated with [GohMuller2026].

## Main statements

* `finite_unit_family_tail`: For a finite family of unit slot vectors and `ε ≥ 0`, the
  probability that some multilinear evaluation has absolute value at least `ε` is at most the
  family cardinality times `2 exp(-ε²/(2N⁻ʳ))`, with the variance parameter interpreted as in
  the displayed formula.

## References

* [Goh and Müller, 2026][GohMuller2026]
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators
open Qatlib.Papers.OverlapGapGoh26.GaussianModel.Interpolation
open Qatlib.Papers.OverlapGapGoh26.GaussianBounds.Linear

namespace Qatlib.Papers.OverlapGapGoh26.GaussianBounds.FiniteFamily

/-- For a finite family of unit slot vectors and `ε ≥ 0`, the probability that some multilinear
evaluation has absolute value at least `ε` is at most the family cardinality times `2
exp(-ε²/(2N⁻ʳ))`, with the variance parameter interpreted as in the displayed formula. -/
theorem finite_unit_family_tail {r N : ℕ} {I : Type} [Fintype I]
    (z : I → Fin (r+1) → Fin N → ℝ) (hz : ∀ j a, ∑ i,z j a i^2=1)
    (ε : ℝ) (hε : 0≤ε) :
    (gaussianTensorLaw r N).real {A | ∃ j, ε≤|multilinearEval A (z j)|}≤
      (Fintype.card I:ℝ)*2*Real.exp (-ε^2/(2*(((N:NNReal)^r)⁻¹:ℝ))) := by
  have he : {A : Qatlib.Foundations.MatrixAlgebra.TensorDiff.Tensor (r+1) N | ∃ j, ε≤|multilinearEval A (z j)|}=
      ⋃ j:I, {A | ε≤|multilinearEval A (z j)|} := by ext A; simp
  rw [he]
  apply (measureReal_iUnion_fintype_le _).trans
  calc
    _ ≤ ∑ _j:I, 2*Real.exp (-ε^2/(2*(((N:NNReal)^r)⁻¹:ℝ))) :=
      Finset.sum_le_sum (fun j _ => unit_multilinear_abs_tail (z j) (hz j) ε hε)
    _ = _ := by simp [mul_assoc]

end Qatlib.Papers.OverlapGapGoh26.GaussianBounds.FiniteFamily
