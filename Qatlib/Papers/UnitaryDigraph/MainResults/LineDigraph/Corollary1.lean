/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.UnitaryDigraph.MainResults.Specular
import Qatlib.Papers.UnitaryDigraph.MainResults.LineDigraph.Theorem2

/-!
# Unitary realizations of strongly quadrangular line digraphs

This module gives two formulations of Corollary 1 of [Severini2003]. The theorem `corollary1`
assumes the general specular realization implication, while `corollary1_onesided` uses incoming
and outgoing strong quadrangularity together with nonempty neighborhoods.

## Main statements

* `corollary1`: Deduce unitary realizability from the supplied specular realization theorem.
* `corollary1_onesided`: Construct a unitary realization under the stated one-sided and
  nonemptiness hypotheses.

## References

* [Severini, 2003][Severini2003]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.UnitaryDigraph.MainResults.LineDigraph

open Qatlib.Papers.UnitaryDigraph.MainResults.Defs
open Qatlib.Papers.UnitaryDigraph.MainResults.Specular

/-- Assuming every finite specular strongly quadrangular digraph is unitary, a finite strongly
quadrangular line digraph is unitary [Severini2003]. -/
theorem corollary1 {W : Type} (D₀ : Defs.Digraph W) [Fintype (Arc D₀)]
    [DecidableEq (Arc D₀)]
    (hT1 : ∀ {V : Type} [Fintype V] [DecidableEq V] (D : Defs.Digraph V),
      Specular D → StronglyQuadrangular D → IsUnitaryDigraph D)
    (hsq : StronglyQuadrangular (lineDigraph D₀)) :
    IsUnitaryDigraph (lineDigraph D₀) :=
  hT1 (lineDigraph D₀) (lineDigraph_specular D₀) hsq

/-- A finite line digraph is unitary when it is both incoming and outgoing strongly quadrangular
and every arc has nonempty incoming and outgoing neighborhoods [Severini2003]. -/
theorem corollary1_onesided {W : Type} [Fintype W] [DecidableEq W] (D₀ : Defs.Digraph W)
    [Fintype (Arc D₀)] [DecidableEq (Arc D₀)]
    (houtSQ : OutStronglyQuadrangular (lineDigraph D₀))
    (hinSQ : InStronglyQuadrangular (lineDigraph D₀))
    (hout : ∀ a, ((lineDigraph D₀).outNbrs a).Nonempty)
    (hin : ∀ a, ((lineDigraph D₀).inNbrs a).Nonempty) :
    IsUnitaryDigraph (lineDigraph D₀) :=
  theorem1 (lineDigraph D₀) (lineDigraph_specular D₀) houtSQ hinSQ hout hin

end Qatlib.Papers.UnitaryDigraph.MainResults.LineDigraph
