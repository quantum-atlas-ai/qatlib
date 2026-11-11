/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order

/-!
# Positive complement square root

`positiveComplementSqrt` defines the continuous-functional-calculus square root of the
complement of a complex square matrix. Its positivity, square identity, and quantitative bounds
under positive contraction hypotheses are established in the companion module.

The positive-matrix functional calculus used in this construction has background in
[Bhatia1997].

## Main statements

* `positiveComplementSqrt`: The functional-calculus square root of the identity minus the input
  matrix.

## References

* [Bhatia, 1997][Bhatia1997]
-/

set_option autoImplicit false
namespace Qatlib.Concepts.MpsAdaptation.MpsTransfer
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder
variable {N : Type*} [Fintype N] [DecidableEq N]

/-- The continuous-functional-calculus square root `CFC.sqrt (1 - E)` of the complement of `E`. -/
noncomputable def positiveComplementSqrt (E : Matrix N N ℂ) : Matrix N N ℂ :=
  CFC.sqrt (1 - E)

end Qatlib.Concepts.MpsAdaptation.MpsTransfer
