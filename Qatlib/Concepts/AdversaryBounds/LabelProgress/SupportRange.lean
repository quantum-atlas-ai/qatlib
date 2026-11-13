/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.LabelProgress.PureState

/-!
# Support as the amplitude range

The support defined by the range of `C * Cᴴ` equals the range of the amplitude matrix `C`
itself. The proof uses equality of their ranks together with the immediate range inclusion, a
finite-dimensional Gram-matrix fact in the linear-algebraic framework of [Watrous2018].

In particular, every amplitude column lies in the support used by the label-progress
constructions.

## Main statements

* `support_eq_amplitude_range`: identify the Gram support with the amplitude range.
* `amplitude_column_mem_support`: place every amplitude column in that support.

## References

* [Watrous, 2018][Watrous2018]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Matrix Module
open scoped Classical BigOperators ComplexOrder
namespace Qatlib.Concepts.AdversaryBounds.LabelProgress
variable {I A : Type*} [Fintype I] [Fintype A]

/-- The range of `reducedInput C = C * Cᴴ` equals the range of the amplitude matrix `C`. -/
theorem support_eq_amplitude_range (C : Matrix I A ℂ) : support C=C.mulVecLin.range := by
  have hle : support C ≤ C.mulVecLin.range := by
    change (C*Cᴴ).mulVecLin.range ≤ C.mulVecLin.range
    rw [Matrix.mulVecLin_mul]
    exact LinearMap.range_comp_le_range _ _
  apply Submodule.eq_of_le_of_finrank_eq hle
  exact Matrix.rank_self_mul_conjTranspose C

/-- Every column of the amplitude matrix belongs to its reduced input support. -/
theorem amplitude_column_mem_support (C : Matrix I A ℂ) (a : A) : (fun i => C i a) ∈ support C := by
  rw [support_eq_amplitude_range]
  refine ⟨Pi.single a (1 : ℂ),?_⟩
  ext i
  classical
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]
end Qatlib.Concepts.AdversaryBounds.LabelProgress
