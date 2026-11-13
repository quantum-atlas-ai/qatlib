/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.FrameSpectral.SzegedyLemma5NormBoundQuan
import Qatlib.Concepts.WalkSearch.FrameSpectral.SpectralMapSubgoalQuan

/-!
# Discriminant contractions and invariant walk planes

This module establishes two spectral ingredients associated with Theorem 2.1.1 of [Itakura2005].
Isometric embeddings give a contractive bipartite discriminant, while a normalized eigenvector
of a Szegedy discriminant with nonzero sine yields an orthonormal invariant rotation plane for
the walk.

## Main statements

* `theorem211_a_discriminant_singular_bound`: Proves contraction and compatibility of fixed
  discriminant vectors.
* `theorem211_b_invariant_rotation_plane`: Constructs an orthonormal plane on which the walk
  rotates by `2 * θ`.

## References

* [Itakura, 2005][Itakura2005]
-/

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

/-- For isometric `A` and `B`, the bipartite discriminant does not increase the sum of squared
coordinate norms, and a fixed vector `Sum.elim a b` satisfies `A *ᵥ a = B *ᵥ b`. These are
the discriminant bounds associated with [Itakura, Theorem 2.1.1][Itakura2005]. -/
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

/-- A normalized real eigenvector of the Szegedy discriminant with eigenvalue `cos θ` and `sin θ
≠ 0` yields orthonormal states spanning an invariant plane on which `SzegedyWalk P` has the
displayed rotation action of angle `2 * θ`. See [Itakura, Theorem 2.1.1][Itakura2005]. -/
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
