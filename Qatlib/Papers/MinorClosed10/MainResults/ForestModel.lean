/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.MinorClosed10.MainResults.Model.GraphAndQueryModel

@[expose] public section


/-! # The preserved acyclicity decision property

Demand: Childs--Kothari, arXiv1011.1443v2 Theorem 3.4. This is the exact
closed historical graph-property definition, retained independently of
the deferred adversary lower bound. A named predicate is not a proof of
that query bound.
-/

set_option autoImplicit false
namespace Qatlib.Papers.MinorClosed10.MainResults.ForestModel
open Qatlib.Papers.MinorClosed10.MainResults

/-- The actual historical property that the input simple graph contains no cycle. -/
def ForestProperty : GraphProperty := fun _ _ _ G => G.IsAcyclic

end Qatlib.Papers.MinorClosed10.MainResults.ForestModel
