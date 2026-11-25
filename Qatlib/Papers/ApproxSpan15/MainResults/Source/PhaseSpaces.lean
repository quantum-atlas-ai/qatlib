/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

@[expose] public section


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

The projector is an orthogonal projection, hence idempotent and self-adjoint, and the phase
space is monotone in the angle `Θ` because the spectral threshold `2 cos Θ` decreases.
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

/-- The phase-space projector is idempotent: `Π^x_Θ` is an orthogonal projection
(Section 3.1, p. 13). -/
theorem phaseProjector_isIdempotent (U : H →L[ℝ] H) (Θ : ℝ) :
    phaseProjector U Θ ∘ phaseProjector U Θ = phaseProjector U Θ := by
  funext v
  show (phaseSpace U Θ).starProjection ((phaseSpace U Θ).starProjection v) =
    (phaseSpace U Θ).starProjection v
  exact Submodule.starProjection_eq_self_iff.mpr (Submodule.coe_mem _)

/-- The phase-space projector is self-adjoint, as an orthogonal projection
(Section 3.1, p. 13). -/
theorem phaseProjector_isSelfAdjoint (U : H →L[ℝ] H) (Θ : ℝ) :
    IsSelfAdjoint (phaseProjector U Θ) :=
  isSelfAdjoint_starProjection (phaseSpace U Θ)

/-- The phase space grows with the angle: `Π^x_Θ` projects onto the phases `|θ| ≤ Θ`, so a
larger `Θ ∈ [0, π]` gives a larger subspace (Section 3.1, p. 13).  In the model this is
the antitone threshold `2 cos Θ` composed with the supremum of eigenspaces. -/
theorem phaseSpace_monotone (U : H →L[ℝ] H) {Θ₁ Θ₂ : ℝ} (h0 : 0 ≤ Θ₁) (hΘ : Θ₁ ≤ Θ₂)
    (hπ : Θ₂ ≤ Real.pi) : phaseSpace U Θ₁ ≤ phaseSpace U Θ₂ := by
  have hcos : Real.cos Θ₂ ≤ Real.cos Θ₁ := Real.cos_le_cos_of_nonneg_of_le_pi h0 hπ hΘ
  unfold phaseSpace
  refine iSup_le fun μ => iSup_le fun hμ => ?_
  have hμ' : phaseThreshold Θ₂ ≤ μ := by
    have hμ1 : 2 * Real.cos Θ₁ ≤ μ := hμ
    show 2 * Real.cos Θ₂ ≤ μ
    linarith
  exact le_iSup_of_le μ (le_iSup_of_le hμ' le_rfl)

end Qatlib.Papers.ApproxSpan15.MainResults
