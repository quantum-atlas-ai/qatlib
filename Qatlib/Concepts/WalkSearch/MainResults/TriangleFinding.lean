/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.MainResults.TriangleFindingDefs

/-!
# Triangle search diagnostic endpoints

This module proves the specifications `clause20Spec` through `clause24Spec`. These endpoints
combine refutations of historical capability contracts with corrected stored data and numerical
statements, injective finite encodings, a zero gate unitary circuit witness, and the low
threshold nonvacuity statement. For background on quantum search and amplitude amplification,
see [BrassardEtAl2002].

## Main statements

* `clause20_endpoint`: The three historical native search capability propositions in
  `clause20Spec` are false.
* `clause24_endpoint`: The low degree threshold nonvacuity statement `DLoNonvacuity` holds.

## References

* [Brassard et al., 2002][BrassardEtAl2002]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.WalkSearch.CollisionSearch
open Qatlib.Concepts.WalkSearch.Primitives
open Qatlib.Concepts.WalkSearch.QuantumAccess
open Qatlib.Concepts.WalkSearch.WalkAlgorithms

namespace Qatlib.Concepts.WalkSearch.MainResults

open Qatlib
open scoped Classical BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- The three historical native search capability propositions in `clause20Spec` are false. -/
theorem clause20_endpoint : clause20Spec := by
  exact ⟨safeGroverNative_obstruction, noisySearchNative_obstruction,
    kCollisionNative_obstruction⟩

/-- The historical stored subgraph proposition is false, and its source corrected replacement
holds. -/
theorem clause21_endpoint : clause21Spec := by
  exact ⟨storedSubgraphSUC_empty_obstruction, storedSubgraphSUCSourceCorrected_answer⟩

/-- Real exponent transport and the polylogarithmic numerical replacement hold, while the
historical numerical proposition is false. -/
theorem clause22_endpoint : clause22Spec := by
  exact ⟨realExponentTransport_answer, th5Numeric_obstruction, th5NumericPolylog_answer⟩

/-- The finite search index and Boolean adjacency table have the specified injective encodings,
and every nonempty finite state space possesses a normalized state and a unitary circuit
with zero gates. -/
theorem clause23_endpoint : clause23Spec := by
  refine ⟨?_, ?_, ?_⟩
  · intro n
    exact search_index_encoding n
  · intro n
    exact adjacency_table_encoding n
  · intro N hN
    exact positive_empty_word_gate_bound N hN

/-- The low degree threshold nonvacuity statement `DLoNonvacuity` holds. -/
theorem clause24_endpoint : clause24Spec := dLoNonvacuity_answer

end Qatlib.Concepts.WalkSearch.MainResults
