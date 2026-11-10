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

namespace Qatlib.Concepts.AmplitudeCore.AmplifyCore

noncomputable def amplitudeEstimationGoodSubspace
    {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (basis : HilbertBasis ι ℂ H) (χ : ι → Bool) : ClosedSubmodule ℂ H :=
  (Submodule.span ℂ (basis '' {i | χ i = true})).closure
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
