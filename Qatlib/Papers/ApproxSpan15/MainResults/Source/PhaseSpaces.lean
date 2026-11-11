/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Phase spaces of the span program unitaries (Section 3.1, p. 13)

Ito--Jeffery, *Approximate Span Programs*, arXiv:1507.00432v1.

The source defines, for `Θ ∈ [0, π)`, `Π^x_Θ` as the orthogonal projector onto
the `e^{iθ}`-eigenspaces of `U(P,x)` with `|θ| ≤ Θ` (p. 13).  Over `ℂ` the
θ-phase space of a unitary is the eigenspace of `U + U†` with eigenvalue
`2 cos θ`; since `U(P,x)` in this model is a *real* orthogonal operator, the
union of the `±θ` phase spaces is exactly the sum of the real eigenspaces of the
self-adjoint operator `U + U†` with eigenvalue at least `2 cos Θ`.  We take this
as the definition of the phase space, which is the faithful real form of the
source's complex definition (the source only uses the *spans* of the small-phase
eigenspaces, and `Π^x_Θ = Π^x_{−Θ}`).
-/


set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.ApproxSpan15.MainResults

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

/-- The spectral threshold `2 cos Θ` cutting off phases `|θ| ≤ Θ`. -/
def phaseThreshold (Θ : ℝ) : ℝ := 2 * Real.cos Θ

/-- The `≤ Θ` phase subspace of an orthogonal operator `U`: the sum of the real
eigenspaces of `U + U†` with eigenvalue at least `2 cos Θ`.  This is the real
form of the source's `e^{iθ}`-eigenspaces with `|θ| ≤ Θ` (p. 13). -/
noncomputable def phaseSpace (U : H →L[ℝ] H) (Θ : ℝ) : Submodule ℝ H :=
  ⨆ (μ : ℝ), ⨆ (_ : phaseThreshold Θ ≤ μ),
    Module.End.eigenspace ((U + U.adjoint : H →L[ℝ] H) : H →ₗ[ℝ] H) μ

/-- The source's projector `Π^x_Θ` (p. 13) in the real model: the orthogonal
projection onto `phaseSpace U Θ`. -/
noncomputable def phaseProjector (U : H →L[ℝ] H) (Θ : ℝ) : H →L[ℝ] H :=
  (phaseSpace U Θ).starProjection

end Qatlib.Papers.ApproxSpan15.MainResults
