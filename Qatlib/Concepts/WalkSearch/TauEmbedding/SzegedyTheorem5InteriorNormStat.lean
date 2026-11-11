/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.TauEmbedding.SzegedyTauScaledIsometryStat

/-!
# Normalized τ-image norm contract

`SzegedyTheorem5InteriorNorm` records the exact norm of signed τ images for two isometric
frames. A normalized discriminant eigenvector at any `0 ≤ lam < 1` maps to a vector with squared
norm `1 - lam^2` for either sign.

The inclusion of `lam = 0` makes this norm contract applicable at the zero source endpoint in
the spectral framework of [Szegedy2004].

## Main statements

* `SzegedyTheorem5InteriorNorm`: the normalized source-image norm requirement.

## References

* [Szegedy, 2004][Szegedy2004]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Matrix

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.SpectralFilter.BusySpectrum

namespace Qatlib.Concepts.WalkSearch.TauEmbedding

/-- The contract that either signed τ image of a normalized discriminant eigenvector with `0 ≤
lam < 1` has self-inner-product `1 - lam^2` [Szegedy2004]. -/
def SzegedyTheorem5InteriorNorm : Prop :=
  ∀ (H I J : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
      [Fintype J] [DecidableEq J] (A : Matrix H I ℂ) (B : Matrix H J ℂ) (lam : ℝ),
    Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry A → Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry B → 0 ≤ lam → lam < 1 →
    ∀ u : QState (I⊕J),
      Normalized u → bipartiteDiscriminant A B *ᵥu = (lam:ℂ)•u →
      ∀ s : Bool,
      Qatlib.Foundations.PureStateMath.Inner (bipartiteTauLinear A B lam s u) (bipartiteTauLinear A B lam s u) =
        ((1 - lam^2 : ℝ) : ℂ)

end Qatlib.Concepts.WalkSearch.TauEmbedding
