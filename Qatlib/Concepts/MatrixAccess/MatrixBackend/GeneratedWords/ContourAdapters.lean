/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixContour.ContourCalc.ContourModel
import Qatlib.Concepts.CopyEvolution.Discriminate.ParallelQSVT

open Qatlib.Concepts.BlockEncoding.LCU

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.Reflection

/-!
# Contour Adapters

The canonical normalized joint shift is the same label-first SELECT used by the existing common-oracle word, for every matrix and scale.
-/

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords
open Qatlib.Concepts.MatrixContour.ContourCalc
open Qatlib.Concepts.CopyEvolution.Discriminate

/-- The canonical normalized joint shift is the same label-first SELECT used
by the existing common-oracle word, for every matrix and scale. -/
theorem normalized_shift_as_select {I L : Type*} [Fintype I] [DecidableEq I]
    [Fintype L] [DecidableEq L] (A : Matrix I I ℂ) (z : L → ℂ) (B : ℝ) :
    jointNormalizedShift A z B = select (fun j => ((B⁻¹ : ℝ) : ℂ) • matrixShift A (z j)) := rfl

/-- The canonical joint pseudoinverse resolvent agrees with the historical
label-first SELECT, including singular shifts. -/
theorem matrix_resolvent_as_select {I L : Type*} [Fintype I] [DecidableEq I]
    [Fintype L] [DecidableEq L] (A : Matrix I I ℂ) (z : L → ℂ) :
    jointMatrixResolvent A z = select (fun j => matrixResolvent A (z j)) := rfl

end Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords
