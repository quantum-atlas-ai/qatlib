/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.TauEmbedding.SzegedyLemma10PairingStat
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Matrix

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.SpectralFilter.BusySpectrum

namespace Qatlib.Concepts.WalkSearch.TauEmbedding

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
