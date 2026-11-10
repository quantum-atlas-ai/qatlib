/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import QuantumInfo.ForMathlib.MatrixNorm.TraceNorm
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Notation
set_option warningAsError false

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MixedFidelity.FidelityMetric.ComplexArrowTraceNorm

def arrow (ell mass : ℝ) (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(ell : ℂ), z; star z, ((-ell - mass : ℝ) : ℂ)]

def fullBlock (n : ℕ) (ell mass tail : ℝ) (z : ℂ) :
    Matrix (Fin 2 ⊕ Fin n) (Fin 2 ⊕ Fin n) ℂ :=
  Matrix.fromBlocks (Qatlib.Concepts.MixedFidelity.FidelityMetric.ComplexArrowTraceNorm.arrow ell mass z) 0 0
    ((tail : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ))

def errorNumerator (ell mass z2 : ℝ) : ℝ :=
  max mass ((mass + Real.sqrt ((2 * ell + mass)^2 + 4*z2))/2)

end Qatlib.Concepts.MixedFidelity.FidelityMetric.ComplexArrowTraceNorm
