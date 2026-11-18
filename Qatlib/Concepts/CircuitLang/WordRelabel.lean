/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.CircuitLang.QueryWords
public import Qatlib.Concepts.CircuitLang.WireReg
public import Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel

@[expose] public section

/-!
# Relabeled words, unitarity transport, and oracle independence

This module completes the query-word semantic bridge on the relabeling side: the matrix denotation of a
word commutes with public circuit relabeling, square matrix reindexing reflects (not just
preserves) unitarity, and words with zero query count have a denotation that is independent of
the oracle. Query counting itself is not redefined here; the public `QueryCount` remains the
single source of query numbers, as proposed for the R4 interface.

## Main statements

* `denoteRelabel`: denotation commutes with `relabelCircuit` gate by gate.
* `reidxUniIff`: square reindexing along an equivalence reflects and preserves unitarity.
* `denoteQOne`: the one-query word denotes the oracle itself.
* `denoteFree`: query-free words denote the same matrix under any two oracles.
-/

set_option autoImplicit false
set_option warningAsError true

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.GateVocabulary.GateVocab
open Qatlib.Concepts.CircuitLang.QueryWords
open Qatlib.Concepts.CircuitLang.WireReg

namespace Qatlib.Concepts.CircuitLang.WordRelabel

/-- Denotation commutes with circuit relabeling: relabeling every gate of a word and denoting
with the relabeled oracle equals relabeling the denotation of the original word. -/
theorem denoteRelabel {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (e : I ≃ J) (oracle : Matrix I I ℂ) (C : Circuit I) :
    Denote (relabelGate e oracle) (relabelCircuit e C) = relabelGate e (Denote oracle C) := by
  induction C with
  | nil => rw [relabelCircuit_nil, denote_nil, denote_nil, CircuitRelabel.relabelGate_one]
  | cons s C ih =>
    cases s with
    | gate U =>
      rw [relabelCircuit_gate, denote_gate, denote_gate, ih, CircuitRelabel.relabelGate_mul]
    | query =>
      rw [relabelCircuit_query, denote_query, denote_query, ih, CircuitRelabel.relabelGate_mul]

/-- Square matrix reindexing along an equivalence preserves and reflects unitarity; this
completes the one-directional `reidxUnitary` to an equivalence. -/
theorem reidxUniIff {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (e : J ≃ I) {M : Matrix J J ℂ} :
    Matrix.reindex e e M ∈ Matrix.unitaryGroup I ℂ ↔ M ∈ Matrix.unitaryGroup J ℂ := by
  refine ⟨fun h => ?_, reidxUnitary e⟩
  have h2 := reidxUnitary e.symm (M := Matrix.reindex e e M) h
  have h3 : Matrix.reindex e.symm e.symm (Matrix.reindex e e M) = M := by
    ext i j
    simp [Matrix.reindex_apply]
  rwa [h3] at h2

/-- The one-query word denotes the oracle matrix itself, so a single query is exactly one
oracle application in matrix semantics. -/
theorem denoteQOne {I : Type*} [Fintype I] [DecidableEq I] (oracle : Matrix I I ℂ) :
    Denote oracle [Step.query] = oracle := by
  rw [denote_query, denote_nil, Matrix.one_mul]

/-- A word with zero query count denotes the same matrix under any two oracles: the public
`QueryCount` on the word controls oracle dependence of the denotation completely. -/
theorem denoteFree {I : Type*} [Fintype I] [DecidableEq I] {C : Circuit I}
    (hC : QueryCount C = 0) (o o' : Matrix I I ℂ) : Denote o C = Denote o' C := by
  induction C with
  | nil => rw [denote_nil, denote_nil]
  | cons s C ih =>
    cases s with
    | gate U => rw [denote_gate, denote_gate, ih hC]
    | query => simp [QueryCount] at hC

end Qatlib.Concepts.CircuitLang.WordRelabel
