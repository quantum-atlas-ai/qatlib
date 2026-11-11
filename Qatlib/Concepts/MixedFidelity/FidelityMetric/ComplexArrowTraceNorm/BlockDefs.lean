/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import QuantumInfo.ForMathlib.MatrixNorm.TraceNorm
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Complex arrow block definitions

`arrow` is a Hermitian two-dimensional block with a complex coupling. `fullBlock` adds a scalar
identity tail, and `errorNumerator` records the scalar expression used in balanced trace-norm
formulas. See [Bhatia1997].

## Main statements

* `arrow`: the two-dimensional matrix with diagonals `ell` and `-ell - mass`.
* `fullBlock`: the arrow matrix together with a scalar identity tail.
* `errorNumerator`: the balanced trace-norm numerator.

## References

* [Bhatia, 1997][Bhatia1997]
-/

set_option warningAsError false

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MixedFidelity.FidelityMetric.ComplexArrowTraceNorm

/-- The two-by-two matrix with diagonal entries `ell` and `-ell - mass`, and off-diagonal
entries `z` and its conjugate. -/
def arrow (ell mass : ℝ) (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(ell : ℂ), z; star z, ((-ell - mass : ℝ) : ℂ)]

/-- The block-diagonal sum of `arrow ell mass z` and `tail` times the `n`-dimensional identity. -/
def fullBlock (n : ℕ) (ell mass tail : ℝ) (z : ℂ) :
    Matrix (Fin 2 ⊕ Fin n) (Fin 2 ⊕ Fin n) ℂ :=
  Matrix.fromBlocks (Qatlib.Concepts.MixedFidelity.FidelityMetric.ComplexArrowTraceNorm.arrow ell mass z) 0 0
    ((tail : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ))

/-- The scalar `max mass ((mass + Real.sqrt ((2 * ell + mass) ^ 2 + 4 * z2)) / 2)` used for
balanced arrow blocks. -/
def errorNumerator (ell mass z2 : ℝ) : ℝ :=
  max mass ((mass + Real.sqrt ((2 * ell + mass)^2 + 4*z2))/2)

end Qatlib.Concepts.MixedFidelity.FidelityMetric.ComplexArrowTraceNorm
