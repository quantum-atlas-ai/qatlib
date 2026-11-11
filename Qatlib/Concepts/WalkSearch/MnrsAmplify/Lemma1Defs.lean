/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Complex.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Definitions for recursive amplitude amplification

`lineProj` and `markProj` supply the projections used to define marked mass in a finite
dimensional complex inner product space. `raaUnitary` recursively composes the previous iterate
with a marked phase flip and a level reflection, while `betaAt`, `raaState`, and `raaCost`
specify the error schedule, iterated state, and recursive cost ledger. For background on search
via quantum walks, see [MagniezNayakRolandSantha2011].

## Main statements

* `lineProj`: The orthogonal projection onto the complex span of `u`, regarded as a continuous
  linear endomorphism of the ambient space.
* `raaCost`: The cost recurrence with value zero at level zero and next value three times the
  previous cost plus the level reflection cost and marking cost.

## References

* [Magniez et al., 2011][MagniezNayakRolandSantha2011]
-/

open scoped Real

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]

namespace Qatlib.Concepts.WalkSearch.MnrsAmplify

/-- The orthogonal projection onto the complex span of `u`, regarded as a continuous linear
endomorphism of the ambient space. -/
noncomputable def lineProj (u : W) : W →L[ℂ] W :=
  (Submodule.subtypeL (Submodule.span ℂ {u})).comp
    (Submodule.orthogonalProjection (Submodule.span ℂ {u}))

/-- The orthogonal projection onto the marked subspace `M`, followed by its inclusion in the
ambient space. -/
noncomputable def markProj (M : Submodule ℂ W) : W →L[ℂ] W :=
  M.subtypeL.comp M.orthogonalProjection

/-- The squared norm of the projection of `x₀` onto the marked subspace `M`. -/
noncomputable def markedMass (M : Submodule ℂ W) (x₀ : W) : ℝ :=
  ‖markProj M x₀‖ ^ 2

/-- The error schedule `18 / (4 * π^3) * γ / i^2` used for approximate recursive amplitude
amplification in [MagniezNayakRolandSantha2011]. -/
noncomputable def betaAt (γ : ℝ) (i : ℕ) : ℝ :=
  18 / (4 * Real.pi ^ 3) * γ / (i : ℝ) ^ 2

/-- Start with the identity at level zero, then apply the previous iterate, `unmarkRefl`, and `R
(i + 1)` at the next level; see [MagniezNayakRolandSantha2011]. -/
def raaUnitary (unmarkRefl : W ≃ₗᵢ[ℂ] W) (R : ℕ → (W ≃ₗᵢ[ℂ] W)) : ℕ → (W ≃ₗᵢ[ℂ] W)
  | 0 => LinearIsometryEquiv.refl ℂ W
  | i + 1 => ((raaUnitary unmarkRefl R i).trans unmarkRefl).trans (R (i + 1))

/-- The result of applying the level `i` recursive amplification isometry to the initial vector
`x₀`. -/
def raaState (unmarkRefl : W ≃ₗᵢ[ℂ] W) (R : ℕ → (W ≃ₗᵢ[ℂ] W)) (x₀ : W) (i : ℕ) : W :=
  (raaUnitary unmarkRefl R i) x₀

/-- The cost recurrence with value zero at level zero and next value three times the previous
cost plus the level reflection cost and marking cost. -/
noncomputable def raaCost (costR : ℕ → ℝ) (costMark : ℝ) : ℕ → ℝ
  | 0 => 0
  | i + 1 => 3 * raaCost costR costMark i + costR (i + 1) + costMark
end Qatlib.Concepts.WalkSearch.MnrsAmplify
