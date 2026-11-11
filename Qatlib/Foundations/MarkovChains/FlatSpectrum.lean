/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MarkovChains.ReverseKernel.Discriminant

/-!
# Symmetry and reversal of the flat discriminant

The flat discriminant of a real matrix has entries given by the square roots of products of
opposite entries. `flat_transpose` proves symmetry, and `flat_reverse` shows invariance under
reversal weighted by a strictly positive function.

These identities concern the discriminants used in quantum walks for nonreversible Markov
chains; see [ClaudonPiquemalMonmarche2025].

## Main statements

* `flat_reverse`: Invariance under positively weighted reversal.
* `flat_transpose`: Symmetry of the flat discriminant.

## References

* [Claudon et al., 2025][ClaudonPiquemalMonmarche2025]
-/

set_option autoImplicit false
noncomputable section
open Matrix
namespace Qatlib.Foundations.MarkovChains.FlatSpectrum

/-- Reversing a real matrix with strictly positive weights leaves its flat discriminant
unchanged. -/
theorem flat_reverse {I : Type*} (P : Matrix I I ℝ) (π : I → ℝ) (hπ : ∀ x,0<π x) :
    ReverseKernel.flat (ReverseKernel.reverse P π)=ReverseKernel.flat P := by
  ext x y
  unfold ReverseKernel.flat ReverseKernel.reverse
  congr 1
  field_simp [ne_of_gt (hπ x),ne_of_gt (hπ y)]

/-- The flat discriminant of any real matrix is symmetric. -/
theorem flat_transpose {I : Type*} (P : Matrix I I ℝ) :
    (ReverseKernel.flat P)ᵀ=ReverseKernel.flat P := by
  ext x y
  exact congrArg Real.sqrt (mul_comm (P y x) (P x y))
end Qatlib.Foundations.MarkovChains.FlatSpectrum
