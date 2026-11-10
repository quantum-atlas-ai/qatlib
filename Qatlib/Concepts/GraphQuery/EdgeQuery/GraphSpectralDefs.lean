/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.Clique
import Qatlib.Concepts.QueryWordCore.QueryMachinery.Oracle
import Qatlib.Concepts.GraphQuery.EdgeQuery.GraphCollision
open Qatlib.Foundations.QueryWordCore.Circuit

set_option autoImplicit false

namespace Qatlib.Concepts.GraphQuery.EdgeQuery

open Qatlib

def edgeBit {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] (e : V × V) : Bool :=
  decide (G.Adj e.1 e.2)

def triangleBit {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] : Bool :=
  decide (∃ x y z : V, G.Adj x y ∧ G.Adj y z ∧ G.Adj z x)

def edgeQuery {V : Type*} : Circuit ((V × V) × Bool) := [Step.query]

def preservesEdges {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj] (e : V ≃ W) : Prop :=
  ∀ u v, edgeBit G (u,v) = edgeBit H (e u,e v)

end Qatlib.Concepts.GraphQuery.EdgeQuery
