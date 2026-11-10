/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.FrameSpectral.SzegedyLemma5NormBoundQuan
import Qatlib.Concepts.WalkSearch.FrameSpectral.SpectralMapSubgoalQuan
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CommuteTest05.MainResults.Theorem211

open Qatlib.Concepts.WalkSearch.FrameSpectral
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.Execution.WorkspaceCP (IsIsometry)
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralFilter.BusySpectrum
open Qatlib.Concepts.WalkSearch.TwoLevelLower
open Matrix

theorem theorem211_a_discriminant_singular_bound
    {H I J : Type} [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (A : Matrix H I ℂ) (B : Matrix H J ℂ)
    (hA : IsIsometry A) (hB : IsIsometry B) :
    (∀ x : QState (I ⊕ J),
      ∑ p, ‖(bipartiteDiscriminant A B *ᵥ x) p‖ ^ 2 ≤ ∑ p, ‖x p‖ ^ 2) ∧
    (∀ a : QState I, ∀ b : QState J,
      bipartiteDiscriminant A B *ᵥ (Sum.elim a b) = Sum.elim a b →
        A *ᵥ a = B *ᵥ b) := by
  simpa only [SzegedyLemma5NormBound] using!
    szegedyLemma5NormBound H I J A B hA hB

theorem theorem211_b_invariant_rotation_plane
    {I : Type} [Fintype I] [DecidableEq I] (P : I → I → ℝ)
    (hP : IsTransitionMatrix P) (v : I → ℝ) (hv : ∑ i, v i ^ 2 = 1)
    (θ : ℝ) (hs : Real.sin θ ≠ 0)
    (hvD : SzegedyDiscriminant P *ᵥ v = (Real.cos θ) • v) :
    ∃ (w₀ w₁ : QState (I × I)), Normalized w₀ ∧ Normalized w₁ ∧
      Inner w₀ w₁ = 0 ∧
      SzegedyWalk P *ᵥ w₀
        = (((Real.cos (2 * θ) : ℝ)) : ℂ) • w₀ +
          (((Real.sin (2 * θ) : ℝ)) : ℂ) • w₁ ∧
      SzegedyWalk P *ᵥ w₁
        = (-(((Real.sin (2 * θ) : ℝ)) : ℂ)) • w₀ +
          (((Real.cos (2 * θ) : ℝ)) : ℂ) • w₁ := by
  simpa only [SpectralMapSubgoal] using!
    spectralMapSubgoal I P hP v hv θ hs hvD

end Qatlib.Papers.CommuteTest05.MainResults.Theorem211
