/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.TauEmbedding.SzegedyLemma10PairingStat

/-!
# τ-map scaled-isometry contract

`SzegedyTauScaledIsometry` specifies the inner-product scaling of the signed linear τ maps on an
interior positive discriminant eigenspace. For two isometric frames and `0 < lam < 1`, the image
pairing equals `1 - lam^2` times the source pairing for either sign.

This contract refines the source spectral correspondence by recording its metric scaling
[Szegedy2004].

## Main statements

* `SzegedyTauScaledIsometry`: the signed τ-map inner-product identity.

## References

* [Szegedy, 2004][Szegedy2004]
-/

set_option backward.isDefEq.respectTransparency false

open Matrix

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.SpectralFilter.BusySpectrum

namespace Qatlib.Concepts.WalkSearch.TauEmbedding

/-- The contract that either signed τ map multiplies inner products by `1 - lam^2` on each
discriminant eigenspace with `0 < lam < 1` for two isometric frames [Szegedy2004]. -/
def SzegedyTauScaledIsometry : Prop :=
  ∀ (H I J : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
      [Fintype J] [DecidableEq J] (A : Matrix H I ℂ) (B : Matrix H J ℂ) (lam : ℝ),
    Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry A → Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry B → 0 < lam → lam < 1 →
    ∀ u v : QState (I⊕J),
      bipartiteDiscriminant A B *ᵥu = (lam:ℂ)•u →
      bipartiteDiscriminant A B *ᵥv = (lam:ℂ)•v →
      ∀ s : Bool,
      Qatlib.Foundations.PureStateMath.Inner (bipartiteTauLinear A B lam s u) (bipartiteTauLinear A B lam s v) =
        ((1 - lam^2 : ℝ) : ℂ) * Qatlib.Foundations.PureStateMath.Inner u v

end Qatlib.Concepts.WalkSearch.TauEmbedding
