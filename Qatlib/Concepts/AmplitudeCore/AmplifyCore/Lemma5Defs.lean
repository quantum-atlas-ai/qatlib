/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Span.Defs
import Qatlib.Concepts.AEMeanReadout.RankOneSubspace.Lemma3RestrictedQuan
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Good subspaces and generalized phase iterates

`amplitudeEstimationGoodSubspace` forms the closed span of marked basis vectors.
`amplitudeEstimationPhaseIterate` combines a phase on this subspace with a conjugated phase
about the initial vector and an overall minus sign. See [BrassardEtAl2002] for background.

## Main statements

* `amplitudeEstimationGoodSubspace`: The closed subspace spanned by basis vectors whose indices
  are marked by `χ`.
* `amplitudeEstimationPhaseIterate`: The generalized amplitude amplification iterate with phase
  `ϕ` on `G`, phase `φ` about the initial vector transported by `A`, and an overall minus sign.

## References

* [Brassard et al., 2002][BrassardEtAl2002]
-/

namespace Qatlib.Concepts.AmplitudeCore.AmplifyCore

/-- The closed subspace spanned by basis vectors whose indices are marked by `χ`. -/
noncomputable def amplitudeEstimationGoodSubspace
    {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (basis : HilbertBasis ι ℂ H) (χ : ι → Bool) : ClosedSubmodule ℂ H :=
  (Submodule.span ℂ (basis '' {i | χ i = true})).closure
/-- The generalized amplitude amplification iterate with phase `ϕ` on `G`, phase `φ` about the
initial vector transported by `A`, and an overall minus sign. -/
noncomputable def amplitudeEstimationPhaseIterate
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H ≃ₗᵢ[ℂ] H) (e₀ : H) (G : ClosedSubmodule ℂ H)
    (φ ϕ : ℝ) (v : H) : H :=
  let w : H := v +
    (Complex.exp ((ϕ : ℂ) * Complex.I) - 1) • G.toSubmodule.starProjection v;
  let u : H := A.symm w;
  -(A (u +
    ((Complex.exp ((φ : ℂ) * Complex.I) - 1) * inner ℂ e₀ u) • e₀))

end Qatlib.Concepts.AmplitudeCore.AmplifyCore
