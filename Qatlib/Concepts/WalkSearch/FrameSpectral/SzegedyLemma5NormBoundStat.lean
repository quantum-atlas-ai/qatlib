/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpectralFilter.BusySpectrum.BipartiteDiscriminantSpectrum

/-!
# Specification of the bipartite discriminant norm bound

The proposition `SzegedyLemma5NormBound` records two consequences of frame isometry. The
bipartite discriminant contracts the squared Euclidean norm, and a source vector fixed by it has
matching images under the two frames. The quantum walk spectral framework is developed in
[Szegedy2004].

## Main statements

* `SzegedyLemma5NormBound`: Discriminant contraction and matching endpoint images.

## References

* [Szegedy, 2004][Szegedy2004]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding

open Matrix

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.SpectralFilter.BusySpectrum

namespace Qatlib.Concepts.WalkSearch.FrameSpectral

open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.Execution.WorkspaceCP (IsIsometry)

/-- The requirement that the bipartite discriminant of two isometric frames contracts the
squared coordinate norm and that a fixed source pair has equal frame images [Szegedy, Lemma
5][Szegedy2004]. -/
def SzegedyLemma5NormBound : Prop :=
  ∀ (H I J : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
      [Fintype J] [DecidableEq J] (A : Matrix H I ℂ) (B : Matrix H J ℂ),
    IsIsometry A → IsIsometry B →
    (∀ x : QState (I ⊕ J),
      ∑ p, ‖(bipartiteDiscriminant A B *ᵥ x) p‖ ^ 2 ≤ ∑ p, ‖x p‖ ^ 2) ∧
    (∀ a : QState I, ∀ b : QState J,
      bipartiteDiscriminant A B *ᵥ (Sum.elim a b) = Sum.elim a b →
      A *ᵥ a = B *ᵥ b)

end Qatlib.Concepts.WalkSearch.FrameSpectral
