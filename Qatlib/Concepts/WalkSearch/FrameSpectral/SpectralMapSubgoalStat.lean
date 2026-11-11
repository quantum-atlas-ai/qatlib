/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.Spectral.SzegedySpectral

/-!
# Specification of the Szegedy spectral rotation

The proposition `SpectralMapSubgoal` states the finite discriminant-to-walk rotation
correspondence. It requires two normalized orthogonal walk states associated with each
normalized real discriminant eigenvector of eigenvalue `cos θ` when `sin θ` is nonzero. The
quantum walk spectral framework is developed in [Szegedy2004].

## Main statements

* `SpectralMapSubgoal`: The prescribed angle-doubling action on an orthonormal pair.

## References

* [Szegedy, 2004][Szegedy2004]
-/

set_option warningAsError false

open Matrix

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.WalkSearch.Spectral

open Qatlib.Concepts.WalkSearch.TwoLevelLower

namespace Qatlib.Concepts.WalkSearch.FrameSpectral

/-- The requirement that a normalized real discriminant eigenvector of eigenvalue `cos θ`, with
`sin θ ≠ 0`, determines an orthonormal pair carrying the stated Szegedy walk rotation at
angle `2 * θ` [Szegedy2004]. -/
def SpectralMapSubgoal : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (P : I → I → ℝ), IsTransitionMatrix P →
    ∀ (v : I → ℝ), (∑ i, v i ^ 2 = 1) →
    ∀ (θ : ℝ), Real.sin θ ≠ 0 →
    SzegedyDiscriminant P *ᵥ v = (Real.cos θ) • v →
    ∃ (w₀ w₁ : QState (I × I)), Normalized w₀ ∧ Normalized w₁ ∧ Inner w₀ w₁ = 0 ∧
      SzegedyWalk P *ᵥ w₀
        = (((Real.cos (2 * θ) : ℝ)) : ℂ) • w₀ + (((Real.sin (2 * θ) : ℝ)) : ℂ) • w₁ ∧
      SzegedyWalk P *ᵥ w₁
        = (-(((Real.sin (2 * θ) : ℝ)) : ℂ)) • w₀ + (((Real.cos (2 * θ) : ℝ)) : ℂ) • w₁

end Qatlib.Concepts.WalkSearch.FrameSpectral
