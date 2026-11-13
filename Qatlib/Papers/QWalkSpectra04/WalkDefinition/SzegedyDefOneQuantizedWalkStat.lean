/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.TwoLevelLower
import Qatlib.Concepts.SpectralFilter.BusySpectrum.BipartiteDiscriminantSpectrum
import Qatlib.Papers.QWalkSpectra04.WalkDefinition.SzegedyDefOneQuantizedWalkDefs

/-!
# Quantized walk identification

This module states the identification of the product of reflections in Definition 1 of
[Szegedy2004] with the abstract bipartite walk. `SzegedyDefOneQuantizedWalk` also includes the
specialization of `paperMu` to `SzegedyWalk` for a single finite kernel, without stochasticity
assumptions.

## Main statements

* `SzegedyDefOneQuantizedWalk`: the bipartite and single-kernel operator identifications.

## References

* [Szegedy, 2004][Szegedy2004]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.SpectralFilter.BusySpectrum
open Qatlib.Concepts.WalkSearch.TwoLevelLower
open Matrix

namespace Qatlib.Papers.QWalkSpectra04.WalkDefinition

/-- The proposition that `paperMu` equals the bipartite walk of the two paper frames for
arbitrary finite real kernels, and that `paperMu P P` equals `SzegedyWalk P` for every
finite real kernel `P`. -/
def SzegedyDefOneQuantizedWalk : Prop :=
  ∀ (I J : Type) [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
      (c : I → J → ℝ) (r : J → I → ℝ),
    paperMu c r = bipartiteWalk (paperFrameA c) (paperFrameB r) ∧
    ∀ (K : Type) [Fintype K] [DecidableEq K] (P : K → K → ℝ),
      paperMu P P = SzegedyWalk P

end Qatlib.Papers.QWalkSpectra04.WalkDefinition
