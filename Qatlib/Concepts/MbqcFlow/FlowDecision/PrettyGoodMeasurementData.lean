/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge
import QuantumInfo.ForMathlib.HermitianMat.Sqrt

/-!
# Gram data for pretty-good measurements

Defines the positive Gram matrix `ensembleGram W`, its reciprocal square root
`ensembleGramInvSqrt W`, and the normalized matrix frame `prettyGoodFrame W`. The reciprocal
square root is formed by functional calculus, with the scalar inverse taking value zero at zero.

These Gram-matrix constructions use the finite-dimensional matrix analysis described in
[Bhatia1997].

## Main statements

* `ensembleGram_nonneg`: positivity of the ensemble Gram matrix.
* `prettyGoodFrame`: the matrix `W` multiplied by the reciprocal square root of its Gram matrix.

## References

* [Bhatia, 1997][Bhatia1997]
-/

open Qatlib.Foundations.PureStateMath
set_option warningAsError false

namespace Qatlib.Concepts.MbqcFlow.FlowDecision

open Matrix
open scoped ComplexOrder MatrixOrder

variable {I : Type} [Fintype I] [DecidableEq I] {D : ℕ}

/-- The Hermitian Gram matrix `Wᴴ * W` of the columns of `W`. -/
noncomputable def ensembleGram (W : Matrix (Fin D) I ℂ) : HermitianMat I ℂ :=
  ⟨Wᴴ * W, Matrix.isHermitian_conjTranspose_mul_self W⟩

omit [DecidableEq I] in

/-- The ensemble Gram matrix is nonnegative. -/
theorem ensembleGram_nonneg (W : Matrix (Fin D) I ℂ) : 0 ≤ ensembleGram W := by
  rw [HermitianMat.zero_le_iff]
  exact Matrix.posSemidef_conjTranspose_mul_self W

/-- The reciprocal square root of the ensemble Gram matrix, defined by functional calculus and
equal to zero on its kernel. -/
noncomputable def ensembleGramInvSqrt (W : Matrix (Fin D) I ℂ) : HermitianMat I ℂ :=
  (ensembleGram W).cfc (fun x : ℝ => (Real.sqrt x)⁻¹)

/-- The frame matrix obtained by multiplying `W` by the reciprocal square root of its Gram
matrix. -/
noncomputable def prettyGoodFrame (W : Matrix (Fin D) I ℂ) : Matrix (Fin D) I ℂ :=
  W * (ensembleGramInvSqrt W).mat

end Qatlib.Concepts.MbqcFlow.FlowDecision
