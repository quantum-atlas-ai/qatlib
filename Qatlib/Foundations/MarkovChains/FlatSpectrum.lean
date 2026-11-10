/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MarkovChains.ReverseKernel.Discriminant

set_option autoImplicit false
noncomputable section
open Matrix
namespace Qatlib.Foundations.MarkovChains.FlatSpectrum

theorem flat_reverse {I : Type*} (P : Matrix I I ℝ) (π : I → ℝ) (hπ : ∀ x,0<π x) :
    ReverseKernel.flat (ReverseKernel.reverse P π)=ReverseKernel.flat P := by
  ext x y
  unfold ReverseKernel.flat ReverseKernel.reverse
  congr 1
  field_simp [ne_of_gt (hπ x),ne_of_gt (hπ y)]

theorem flat_transpose {I : Type*} (P : Matrix I I ℝ) :
    (ReverseKernel.flat P)ᵀ=ReverseKernel.flat P := by
  ext x y
  exact congrArg Real.sqrt (mul_comm (P y x) (P x y))
end Qatlib.Foundations.MarkovChains.FlatSpectrum
