/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order

set_option autoImplicit false
namespace Qatlib.Concepts.MpsAdaptation.MpsTransfer
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder
variable {N : Type*} [Fintype N] [DecidableEq N]

noncomputable def positiveComplementSqrt (E : Matrix N N ℂ) : Matrix N N ℂ :=
  CFC.sqrt (1 - E)

end Qatlib.Concepts.MpsAdaptation.MpsTransfer
