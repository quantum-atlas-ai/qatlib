/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OverlapGapGoh26.GaussianBounds.LinearTail
set_option warningAsError false

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators
open Qatlib.Papers.OverlapGapGoh26.GaussianModel.Interpolation
open Qatlib.Papers.OverlapGapGoh26.GaussianBounds.Linear

namespace Qatlib.Papers.OverlapGapGoh26.GaussianBounds.FiniteFamily

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
