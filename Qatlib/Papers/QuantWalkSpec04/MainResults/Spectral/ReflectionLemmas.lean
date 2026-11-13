/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.FrameSpectral.SzegedyLemma4FrameReflectionQuan
import Qatlib.Concepts.WalkSearch.FrameSpectral.SzegedyLemma5NormBoundQuan
import Qatlib.Concepts.WalkSearch.FrameSpectral.SzegedyLemma6BlockActionQuan
import Qatlib.Concepts.WalkSearch.FrameSpectral.SzegedyLemma7EigenSymmetryQuan

/-!
# Reflection and discriminant identities

This module collects the orthogonal projection and reflection properties of orthonormal frames
used in the walk spectral analysis. It also proves contraction, block action, and sign symmetry
statements for the bipartite discriminant. See [Szegedy2004].

## Main statements

* `szegedyLemma4_frame_reflections`: For each of two orthonormal frames, the frame operator is
  an orthogonal projector that fixes frame vectors and kills their orthogonal complement, while
  its reflection fixes frame vectors and negates that complement.
* `szegedyLemma5_norm_bound`: The discriminant of two isometries contracts the squared Euclidean
  norm, and a discriminant fixed vector has equal images under the two isometries.
* `szegedyLemma7_eigen_symmetry`: Applying `paperSourceFlip` to a discriminant eigenvector with
  real eigenvalue `lam` yields an eigenvector with eigenvalue `-lam`.

## References

* [Szegedy, 2004][Szegedy2004]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralFilter.BusySpectrum
open Qatlib.Concepts.WalkSearch.FrameSpectral

namespace Qatlib.Papers.QuantWalkSpec04.MainResults.Spectral

/-- For each of two orthonormal frames, the frame operator is an orthogonal projector that fixes
frame vectors and kills their orthogonal complement, while its reflection fixes frame
vectors and negates that complement. -/
theorem szegedyLemma4_frame_reflections
    {H ι κ : Type} [Fintype H] [DecidableEq H] [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (v : ι → QState H) (w : κ → QState H)
    (hv : ∀ i j, Inner (v i) (v j) = if i = j then 1 else 0)
    (hw : ∀ i j, Inner (w i) (w j) = if i = j then 1 else 0) :
    (IsOrthogonalProjector (paperFrameProjection v) ∧
      (∀ l, paperFrameProjection v *ᵥ v l = v l) ∧
      (∀ u, (∀ l, Inner (v l) u = 0) → paperFrameProjection v *ᵥ u = 0) ∧
      (∀ l, ReflectionAbout (paperFrameProjection v) *ᵥ v l = v l) ∧
      (∀ u, (∀ l, Inner (v l) u = 0) →
        ReflectionAbout (paperFrameProjection v) *ᵥ u = -u)) ∧
    (IsOrthogonalProjector (paperFrameProjection w) ∧
      (∀ l, paperFrameProjection w *ᵥ w l = w l) ∧
      (∀ u, (∀ l, Inner (w l) u = 0) → paperFrameProjection w *ᵥ u = 0) ∧
      (∀ l, ReflectionAbout (paperFrameProjection w) *ᵥ w l = w l) ∧
      (∀ u, (∀ l, Inner (w l) u = 0) →
        ReflectionAbout (paperFrameProjection w) *ᵥ u = -u)) :=
  ⟨szegedyLemma4FrameReflection H ι v hv, szegedyLemma4FrameReflection H κ w hw⟩

/-- The discriminant of two isometries contracts the squared Euclidean norm, and a discriminant
fixed vector has equal images under the two isometries. -/
theorem szegedyLemma5_norm_bound
    {H I J : Type} [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (A : Matrix H I ℂ) (B : Matrix H J ℂ)
    (hA : IsIsometry A) (hB : IsIsometry B) :
    (∀ x : QState (I ⊕ J),
      ∑ p, ‖(bipartiteDiscriminant A B *ᵥ x) p‖ ^ 2 ≤ ∑ p, ‖x p‖ ^ 2) ∧
    (∀ a : QState I, ∀ b : QState J,
      bipartiteDiscriminant A B *ᵥ (Sum.elim a b) = Sum.elim a b →
      A *ᵥ a = B *ᵥ b) :=
  szegedyLemma5NormBound H I J A B hA hB

/-- If the discriminant maps `Sum.elim a b` to `Sum.elim a' b'`, its actions on the separate
input blocks give the corresponding opposite output blocks. -/
theorem szegedyLemma6_block_action
    {H I J : Type} [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (A : Matrix H I ℂ) (B : Matrix H J ℂ)
    (a a' : QState I) (b b' : QState J)
    (h : bipartiteDiscriminant A B *ᵥ Sum.elim a b = Sum.elim a' b') :
    bipartiteDiscriminant A B *ᵥ Sum.elim a (0 : QState J) =
      Sum.elim (0 : QState I) b' ∧
    bipartiteDiscriminant A B *ᵥ Sum.elim (0 : QState I) b =
      Sum.elim a' (0 : QState J) :=
  szegedyLemma6BlockAction H I J A B a a' b b' h

/-- Applying `paperSourceFlip` to a discriminant eigenvector with real eigenvalue `lam` yields
an eigenvector with eigenvalue `-lam`. -/
theorem szegedyLemma7_eigen_symmetry
    {H I J : Type} [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (A : Matrix H I ℂ) (B : Matrix H J ℂ)
    (v : QState (I ⊕ J)) (lam : ℝ)
    (hv : bipartiteDiscriminant A B *ᵥ v = (lam : ℂ) • v) :
    bipartiteDiscriminant A B *ᵥ paperSourceFlip v = (-(lam : ℂ)) • paperSourceFlip v :=
  szegedyLemma7EigenSymmetry H I J A B v lam hv

end Qatlib.Papers.QuantWalkSpec04.MainResults.Spectral
