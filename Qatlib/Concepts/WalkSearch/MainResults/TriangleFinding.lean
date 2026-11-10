/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.MainResults.TriangleFindingDefs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.WalkSearch.CollisionSearch
open Qatlib.Concepts.WalkSearch.Primitives
open Qatlib.Concepts.WalkSearch.QuantumAccess
open Qatlib.Concepts.WalkSearch.WalkAlgorithms

namespace Qatlib.Concepts.WalkSearch.MainResults

open Qatlib
open scoped Classical BigOperators

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

theorem clause20_endpoint : clause20Spec := by
  exact ⟨safeGroverNative_obstruction, noisySearchNative_obstruction,
    kCollisionNative_obstruction⟩

theorem clause21_endpoint : clause21Spec := by
  exact ⟨storedSubgraphSUC_empty_obstruction, storedSubgraphSUCSourceCorrected_answer⟩

theorem clause22_endpoint : clause22Spec := by
  exact ⟨realExponentTransport_answer, th5Numeric_obstruction, th5NumericPolylog_answer⟩

theorem clause23_endpoint : clause23Spec := by
  refine ⟨?_, ?_, ?_⟩
  · intro n
    exact search_index_encoding n
  · intro n
    exact adjacency_table_encoding n
  · intro N hN
    exact positive_empty_word_gate_bound N hN

theorem clause24_endpoint : clause24Spec := dLoNonvacuity_answer

end Qatlib.Concepts.WalkSearch.MainResults
