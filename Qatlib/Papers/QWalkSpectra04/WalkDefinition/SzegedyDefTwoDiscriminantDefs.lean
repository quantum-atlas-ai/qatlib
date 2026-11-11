/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QWalkSpectra04.WalkDefinition.SzegedyDefOneQuantizedWalkStat
import Qatlib.Concepts.WalkSearch.Spectral.SzegedySpectral

/-!
# Stochastic kernels for a bipartite walk

This module defines the kernel hypotheses used for the bipartite walk and its discriminant in
[Szegedy2004]. `IsPaperBipartiteWalk` requires each of the two real kernels to have nonnegative
entries and row sums equal to one.

## Main statements

* `IsPaperBipartiteWalk`: the nonnegativity and normalization conditions for the two kernels.

## References

* [Szegedy, 2004][Szegedy2004]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding

open Matrix

open Qatlib.Concepts.Execution.WorkspaceCP (IsIsometry)

namespace Qatlib.Papers.QWalkSpectra04.WalkDefinition

/-- The condition that both bipartite kernels have nonnegative entries and each of their rows
sums to one. -/
def IsPaperBipartiteWalk {I J : Type} [Fintype I] [Fintype J]
    (c : I → J → ℝ) (r : J → I → ℝ) : Prop :=
  (∀ i j, 0 ≤ c i j) ∧ (∀ i, ∑ j, c i j = 1) ∧
  (∀ j i, 0 ≤ r j i) ∧ (∀ j, ∑ i, r j i = 1)
end Qatlib.Papers.QWalkSpectra04.WalkDefinition
