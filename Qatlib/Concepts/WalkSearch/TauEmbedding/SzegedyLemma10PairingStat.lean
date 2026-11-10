/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.TauEmbedding.BipartiteTauCorrespondence
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Matrix

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.SpectralFilter.BusySpectrum

namespace Qatlib.Concepts.WalkSearch.TauEmbedding

def SzegedyLemma10Pairing : Prop :=
  ∀ (H I J : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
      [Fintype J] [DecidableEq J] (A : Matrix H I ℂ) (B : Matrix H J ℂ) (lam : ℝ),
    Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry A → Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry B → 0 < lam → lam < 1 →
    ∀ u v : QState (I⊕J),
      bipartiteDiscriminant A B *ᵥu = (lam:ℂ)•u →
      bipartiteDiscriminant A B *ᵥv = (lam:ℂ)•v →
      Qatlib.Foundations.PureStateMath.Inner (A*ᵥfun i => u (.inl i)) (A*ᵥfun i => v (.inl i)) =
        Qatlib.Foundations.PureStateMath.Inner (B*ᵥfun j => u (.inr j)) (B*ᵥfun j => v (.inr j)) ∧
      Qatlib.Foundations.PureStateMath.Inner (A*ᵥfun i => u (.inl i)) (B*ᵥfun j => v (.inr j)) =
        (lam:ℂ) * Qatlib.Foundations.PureStateMath.Inner (A*ᵥfun i => u (.inl i)) (A*ᵥfun i => v (.inl i))

end Qatlib.Concepts.WalkSearch.TauEmbedding
