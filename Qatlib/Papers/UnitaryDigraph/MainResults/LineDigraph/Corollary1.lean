/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.UnitaryDigraph.MainResults.Specular
import Qatlib.Papers.UnitaryDigraph.MainResults.LineDigraph.Theorem2
set_option warningAsError false

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

namespace Qatlib.Papers.UnitaryDigraph.MainResults.LineDigraph

open Qatlib.Papers.UnitaryDigraph.MainResults.Defs
open Qatlib.Papers.UnitaryDigraph.MainResults.Specular

theorem corollary1 {W : Type} (D₀ : Defs.Digraph W) [Fintype (Arc D₀)]
    [DecidableEq (Arc D₀)]
    (hT1 : ∀ {V : Type} [Fintype V] [DecidableEq V] (D : Defs.Digraph V),
      Specular D → StronglyQuadrangular D → IsUnitaryDigraph D)
    (hsq : StronglyQuadrangular (lineDigraph D₀)) :
    IsUnitaryDigraph (lineDigraph D₀) :=
  hT1 (lineDigraph D₀) (lineDigraph_specular D₀) hsq

theorem corollary1_onesided {W : Type} [Fintype W] [DecidableEq W] (D₀ : Defs.Digraph W)
    [Fintype (Arc D₀)] [DecidableEq (Arc D₀)]
    (houtSQ : OutStronglyQuadrangular (lineDigraph D₀))
    (hinSQ : InStronglyQuadrangular (lineDigraph D₀))
    (hout : ∀ a, ((lineDigraph D₀).outNbrs a).Nonempty)
    (hin : ∀ a, ((lineDigraph D₀).inNbrs a).Nonempty) :
    IsUnitaryDigraph (lineDigraph D₀) :=
  theorem1 (lineDigraph D₀) (lineDigraph_specular D₀) houtSQ hinSQ hout hin

end Qatlib.Papers.UnitaryDigraph.MainResults.LineDigraph
