/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GraphQuery.EdgeQuery.GraphCollision
import Qatlib.Concepts.QueryComplexity.DegreeMethod.Complexity
import Qatlib.Concepts.QueryWordCore.QueryMachinery.Oracle

set_option backward.isDefEq.respectTransparency false

/-!
# Graph collision query model (shared paper-layer vocabulary)

Fixed arXiv:1305.1021v1.  This file fixes the query-model vocabulary used by every
Theorem/Lemma of the paper *Parameterized Quantum Query Complexity of Graph Collision*.

The decision function is the frozen `graphCollision` of
`QuantumAlgorithm.Foundations.GraphQuery.EdgeQuery`: the graph `adj` is a known
parameter and the queried input is only the vertex labelling `x : Fin n → Bool`.
The oracle family is the library's textbook bit oracle `BitOracleOn x` on the
register `Fin n × Bool` (main register plus oracle target qubit).  A bounded-error
algorithm is represented by the frozen fixed-space certificate
`FixedSpaceQueryUpperBound` with error `1/3`; its acceptance event is "the target
qubit of the final state reads the correct COL decision".

The paper's asymptotic statements (Theorems 1, 4, 5) are stated against
`GraphCollisionQueryUpperBound`, so they quantify over one fixed circuit and one
fixed normalized start state, exactly the library's query-model discipline.
-/

set_option autoImplicit false

namespace Qatlib.Papers.GraphCollis13.QueryBound.Model

open Matrix
open Qatlib.Concepts.GraphQuery.EdgeQuery
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.QueryWordCore.QueryMachinery

/-- The oracle family for graph collision: the bit oracle of the labelling `x` on the
fixed register `Fin n × Bool`.  Access to the graph `adj` is preprocessing and is not
charged as a query. -/
noncomputable def graphCollisionOracle {n : ℕ} (x : Fin n → Bool) :
    Matrix (Fin n × Bool) (Fin n × Bool) ℂ :=
  BitOracleOn x

/-- The graph-collision oracle is unitary, so the frozen fixed-space model applies. -/
theorem graphCollisionOracle_mem_unitaryGroup {n : ℕ} (x : Fin n → Bool) :
    graphCollisionOracle x ∈ Matrix.unitaryGroup (Fin n × Bool) ℂ :=
  bitOracleOn_unitary x

/-- Readout set: the oracle target qubit holds `b`. -/
def readoutSet {n : ℕ} (b : Bool) : Finset (Fin n × Bool) :=
  Finset.univ.filter (fun p => p.2 = b)

/-- Acceptance event for the labelling `x`: the target qubit reads the COL decision. -/
noncomputable def graphCollisionAccept {n : ℕ} (adj : Fin n → Fin n → Bool)
    (x : Fin n → Bool) : Finset (Fin n × Bool) :=
  readoutSet (graphCollision adj x)

/-- **Bounded-error quantum query upper bound for graph collision.**  There is one
unitary fixed-gate circuit on `Fin n × Bool` with one normalized start state that,
for every labelling `x`, uses at most `q` bit-oracle queries and reads the correct
graph-collision decision with probability at least `1 - 1/3`. -/
def GraphCollisionQueryUpperBound {n : ℕ} (adj : Fin n → Fin n → Bool) (q : ℕ) : Prop :=
  FixedSpaceQueryUpperBound (graphCollisionOracle (n := n)) (graphCollisionAccept adj)
    (1 / 3) q

/-- The oracle-unitarity conjunct of the model is automatic. -/
theorem graphCollisionQueryUpperBound_oracle {n : ℕ} (adj : Fin n → Fin n → Bool) (q : ℕ) :
    GraphCollisionQueryUpperBound adj q →
      ∀ x, graphCollisionOracle x ∈ Matrix.unitaryGroup (Fin n × Bool) ℂ :=
  fun h => h.2.1

end Qatlib.Papers.GraphCollis13.QueryBound.Model
