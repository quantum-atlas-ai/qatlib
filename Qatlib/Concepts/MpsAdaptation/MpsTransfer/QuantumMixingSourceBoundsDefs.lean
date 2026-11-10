/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.DirichletForm.KmsDirichlet.Basic
import Mathlib.Analysis.Normed.Algebra.Exponential
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.MpsAdaptation.MpsTransfer

open scoped Matrix.Norms.L2Operator

def matrixFlow {I : Type*} [Fintype I] [DecidableEq I]
    (L : Matrix I I ℂ) (t : ℝ) : Matrix I I ℂ := NormedSpace.exp (t • L)

end Qatlib.Concepts.MpsAdaptation.MpsTransfer
