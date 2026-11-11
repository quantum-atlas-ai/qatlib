/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.DirichletForm.KmsDirichlet.Basic
import Mathlib.Analysis.Normed.Algebra.Exponential

/-!
# Matrix exponential flow

`matrixFlow` defines the exponential of a real-time multiple of a finite complex matrix. The
definition applies to an arbitrary matrix; the companion module establishes identities for rate
and clock rescaling.

Matrix exponentials provide the finite-dimensional evolution framework used in open quantum
systems; see [BreuerPetruccione2007].

## Main statements

* `matrixFlow`: The matrix exponential of `t • L`.

## References

* [Breuer and Petruccione, 2007][BreuerPetruccione2007]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.MpsAdaptation.MpsTransfer

open scoped Matrix.Norms.L2Operator

/-- The matrix exponential `NormedSpace.exp (t • L)` of the real-time-scaled matrix generator. -/
def matrixFlow {I : Type*} [Fintype I] [DecidableEq I]
    (L : Matrix I I ℂ) (t : ℝ) : Matrix I I ℂ := NormedSpace.exp (t • L)

end Qatlib.Concepts.MpsAdaptation.MpsTransfer
