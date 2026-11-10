/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.Spectral.SzegedySpectral
set_option warningAsError false

open Matrix

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.WalkSearch.Spectral

open Qatlib.Concepts.WalkSearch.TwoLevelLower

namespace Qatlib.Concepts.WalkSearch.FrameSpectral

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
