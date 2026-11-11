/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QWalkSpectra04.WalkDefinition.SzegedyDefOneQuantizedWalkStat
import Qatlib.Concepts.WalkSearch.Spectral.SzegedySpectral
import Qatlib.Papers.QWalkSpectra04.WalkDefinition.SzegedyDefTwoDiscriminantDefs

/-!
# Statement of the bipartite discriminant correspondence

This module packages the identities associated with Definition 2 of [Szegedy2004] as
`SzegedyDefTwoDiscriminant`. The statement includes isometric frames for stochastic bipartite
kernels, their cross Gram entries, the tilde Gram identity, and the block form of the
discriminant for a transition matrix.

## Main statements

* `SzegedyDefTwoDiscriminant`: the combined bipartite and transition-matrix discriminant
  statement.

## References

* [Szegedy, 2004][Szegedy2004]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding

open Matrix

namespace Qatlib.Papers.QWalkSpectra04.WalkDefinition

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.SpectralFilter.BusySpectrum
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.WalkSearch.TwoLevelLower

/-- The proposition combining isometric frames, square-root cross Gram entries, and the tilde
Gram identity for stochastic bipartite kernels, together with the block discriminant
specialization for a transition matrix. -/
def SzegedyDefTwoDiscriminant : Prop :=
  ∀ (I J : Type) [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
      (c : I → J → ℝ) (r : J → I → ℝ), IsPaperBipartiteWalk c r →
    IsIsometry (paperFrameA c) ∧
    IsIsometry (paperFrameB r) ∧
    (∀ i j, ((paperFrameA c)ᴴ * paperFrameB r) i j =
      ((Real.sqrt (c i j * r j i) : ℂ))) ∧
    (bipartiteTilde (paperFrameA c) (paperFrameB r))ᴴ *
      bipartiteTilde (paperFrameA c) (paperFrameB r) =
      1 + bipartiteDiscriminant (paperFrameA c) (paperFrameB r) ∧
    ∀ (K : Type) [Fintype K] [DecidableEq K] (P : K → K → ℝ),
      IsTransitionMatrix P →
      paperFrameA P = SzegedyIsometry P ∧
      paperFrameB P = SzegedyIsometryB P ∧
      bipartiteDiscriminant (SzegedyIsometry P) (SzegedyIsometryB P) =
        Matrix.fromBlocks 0 ((SzegedyDiscriminant P).map Complex.ofReal)
          ((SzegedyDiscriminant P).map Complex.ofReal) 0

end Qatlib.Papers.QWalkSpectra04.WalkDefinition
