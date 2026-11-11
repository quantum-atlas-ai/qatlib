/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GateVocabulary.FiniteGateDescription

set_option backward.isDefEq.respectTransparency false

/-!
# Bridge: the finite-gate circuit model of the BQP side

Fixed source: A. W. Harrow, *Review of Quantum Algorithms for Systems of Linear
Equations*, arXiv:1501.00008v1, §3, Theorem 1 (PDF p. 2). The Theorem 1 circuit
is a sequence of two-qubit unitary gates applied to `|0⟩^{⊗n}` and concluded by
a single-qubit measurement.

The reviewed hardness statement is about *that* circuit model. The repository's
frozen finite-gate vocabulary
`QuantumAlgorithm.Concepts.UniformBqp.FiniteGateWord` (the Concepts block bound
by the claim `c001`) fixes a concrete finite gate set `H, X, T, T†, CNOT`, its
total matrix interpretation, effective legality, and exact syntactic counts. The
lemma below re-exports, at this paper layer, the frozen theorem that legal words
are unitary and have exact query/gate counts — the executable content behind the
`T` gate applications counted by Theorem 1.
-/

set_option autoImplicit false

namespace Qatlib.Papers.QLinearSys15.MainResults.LinearSystemSample

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Concepts.GateVocabulary.FiniteGateDescription
/-- **Finite-gate bridge.** For every `n`-qubit description `gs` of finite gate
tags: an illegal description rejects on every input, and a legal description is
a genuine unitary circuit with zero oracle queries and exactly `gs.length` fixed
gates. This is the frozen
`finite_gate_description_rejection_unitarity_and_counts` restated at the
`QLinearSys15` paper layer; it supplies the gate-count bookkeeping used by the
Theorem 1 circuit on the BQP side. -/
theorem finiteGateWord_model_bridge (n : ℕ) (gs : List FiniteGateCode) :
    (∀ ψ : QState (Reg n), finiteWordLegal n gs = false → finiteWordRun n gs ψ = none) ∧
      (finiteWordLegal n gs = true →
        IsUnitaryCircuit (finiteCodeCircuit n gs) ∧
        QueryCount (finiteCodeCircuit n gs) = 0 ∧
        GateCount (finiteCodeCircuit n gs) = gs.length) :=
  finite_gate_description_rejection_unitarity_and_counts n gs

end Qatlib.Papers.QLinearSys15.MainResults.LinearSystemSample
