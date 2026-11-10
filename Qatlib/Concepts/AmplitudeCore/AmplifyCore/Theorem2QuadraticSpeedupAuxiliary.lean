/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.Span.Defs
import Qatlib.Concepts.AEMeanReadout.RankOneSubspace.Theorem2QuadraticSpeedupRestrictedQuan
import Qatlib.Concepts.AmplitudeCore.AmplifyCore.Lemma1Quan
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.InnerProductSpace.l2Space
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

namespace Qatlib.Concepts.AmplitudeCore.AmplifyCore.AmplitudeAmplificationCore
noncomputable def goodProjection {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {S : Set ℤ} (basis : HilbertBasis S ℂ E) (χ : ℤ → Bool) : E →L[ℂ] E :=
  (Submodule.span ℂ
    (Set.image (fun i : S => basis i) {i : S | χ i.1 = true})).topologicalClosure.starProjection
noncomputable def zeroSign {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (e₀ v : E) : E :=
  v - ((2 : ℂ) * inner ℂ e₀ v) • e₀
noncomputable def step {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (A : E ≃ₗᵢ[ℂ] E) (e₀ : E) (P : E →L[ℂ] E) (v : E) : E :=
  -(A (zeroSign e₀ (A.symm (v - (2 : ℂ) • P v))))
end Qatlib.Concepts.AmplitudeCore.AmplifyCore.AmplitudeAmplificationCore
