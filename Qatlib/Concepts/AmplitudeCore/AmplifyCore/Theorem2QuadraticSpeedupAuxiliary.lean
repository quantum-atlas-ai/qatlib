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

/-!
# Operators for amplitude amplification

`goodProjection` selects the closed span of marked basis vectors, while `zeroSign` defines the
reflection expression about an initial vector. `step` combines these operations with state
preparation and its inverse to form the Grover iterate. See [BrassardEtAl2002] for background.

## Main statements

* `goodProjection`: The orthogonal projection onto the closed span of basis vectors marked by
  `χ`.
* `step`: The Grover step obtained by composing the good component sign change, inverse
  preparation, initial vector sign change, preparation, and an overall minus sign.

## References

* [Brassard et al., 2002][BrassardEtAl2002]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

namespace Qatlib.Concepts.AmplitudeCore.AmplifyCore.AmplitudeAmplificationCore
/-- The orthogonal projection onto the closed span of basis vectors marked by `χ`. -/
noncomputable def goodProjection {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {S : Set ℤ} (basis : HilbertBasis S ℂ E) (χ : ℤ → Bool) : E →L[ℂ] E :=
  (Submodule.span ℂ
    (Set.image (fun i : S => basis i) {i : S | χ i.1 = true})).topologicalClosure.starProjection
/-- The map sending `v` to `v - 2 * ⟪e₀, v⟫ • e₀`, which is the reflection about the orthogonal
complement of `e₀` when `e₀` is a unit vector. -/
noncomputable def zeroSign {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (e₀ v : E) : E :=
  v - ((2 : ℂ) * inner ℂ e₀ v) • e₀
/-- The Grover step obtained by composing the good component sign change, inverse preparation,
initial vector sign change, preparation, and an overall minus sign. -/
noncomputable def step {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (A : E ≃ₗᵢ[ℂ] E) (e₀ : E) (P : E →L[ℂ] E) (v : E) : E :=
  -(A (zeroSign e₀ (A.symm (v - (2 : ℂ) • P v))))
end Qatlib.Concepts.AmplitudeCore.AmplifyCore.AmplitudeAmplificationCore
