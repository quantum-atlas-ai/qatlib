/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.QuantumAccess.ResidualDiagnosticContracts
import Qatlib.Concepts.WalkSearch.QuantumAccess.SafeGroverNative
import Qatlib.Concepts.WalkSearch.QuantumAccess.NoisySearchNative
import Qatlib.Concepts.WalkSearch.Primitives.KCollisionNative
import Qatlib.Concepts.WalkSearch.Primitives.StoredSubgraphSUC
import Qatlib.Concepts.WalkSearch.WalkAlgorithms.StoredSubgraphSUCSourceCorrectedQuan
import Qatlib.Concepts.WalkSearch.Primitives.Th5Numeric
import Qatlib.Concepts.WalkSearch.WalkAlgorithms.Th5NumericPolylogQuan
import Qatlib.Concepts.WalkSearch.CollisionSearch.RealExponentTransportQuan
import Qatlib.Concepts.WalkSearch.Primitives.DLoNonvacuityQuan
import Qatlib.Concepts.WalkSearch.Primitives.FiniteResourceBounds

/-!
# Specifications for triangle search diagnostics

`clause20Spec` through `clause24Spec` state the endpoint obligations for historical contract
refutations, corrected stored data and numerical results, finite encodings, and low degree
threshold nonvacuity. The corresponding residual lists describe constructions and resource
ledgers outside these propositions. For background on quantum search and amplitude
amplification, see [BrassardEtAl2002].

## Main statements

* `clause20Spec`: The conjunction asserting that `SafeGroverNative`, `NoisySearchNative`, and
  `KCollisionNative` are false.
* `clause24Residual`: A description of the finite small graph case analysis not rederived by the
  low degree threshold endpoint.

## References

* [Brassard et al., 2002][BrassardEtAl2002]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.WalkSearch.CollisionSearch
open Qatlib.Concepts.WalkSearch.Primitives
open Qatlib.Concepts.WalkSearch.QuantumAccess
open Qatlib.Concepts.WalkSearch.QuantumAccess.Walk
open Qatlib.Concepts.WalkSearch.WalkAlgorithms

namespace Qatlib.Concepts.WalkSearch.MainResults

open Qatlib
open scoped Classical BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- The conjunction asserting that `SafeGroverNative`, `NoisySearchNative`, and
`KCollisionNative` are false. -/
def clause20Spec : Prop :=
  ¬ SafeGroverNative ∧ ¬ NoisySearchNative ∧ ¬ KCollisionNative

/-- The historical `StoredSubgraphSUC` proposition is false and the corrected
`StoredSubgraphSUCSourceCorrected` proposition holds. -/
def clause21Spec : Prop :=
  ¬ StoredSubgraphSUC ∧ StoredSubgraphSUCSourceCorrected

/-- Real exponent transport holds, the historical numerical Theorem 5 proposition is false, and
its polylogarithmic replacement holds. -/
def clause22Spec : Prop :=
  RealExponentTransport ∧ ¬ Th5Numeric ∧ Th5NumericPolylog

/-- Finite search indices and Boolean adjacency tables possess the specified injective
encodings, and each nonempty finite state space has a normalized state and a unitary zero
gate circuit. -/
def clause23Spec : Prop :=
  (∀ n : ℕ, ∃ qenc : Fin n → Fin (2 ^ Nat.clog 2 n), Function.Injective qenc) ∧
  (∀ n : ℕ, ∃ cenc : (Fin n → Fin n → Bool) → Fin (2 ^ (n * n)), Function.Injective cenc) ∧
  (∀ N : ℕ, 0 < N →
    ∃ (C : Circuit (Fin N)) (ψ : QState (Fin N)),
      IsUnitaryCircuit C ∧ Normalized ψ ∧ GateCount C = 0)

/-- The low degree threshold nonvacuity proposition `DLoNonvacuity`. -/
def clause24Spec : Prop := DLoNonvacuity

/-- Descriptions of the historical capability contracts and native search words not constructed
by the clause 20 endpoint. -/
def clause20Residual : List String :=
  [ "the historical native-capability contracts of the source are refuted by the \
frozen package, so they cannot be discharged as stated; the corrected replacement of \
each of them is not constructed here",
    "the usable native words of the source (the validated Grover word with its Born \
coupling, the coherent test template and the uniform Grover ticket) are not re-derived \
on the Dev side" ]

/-- Descriptions of the historical stored subgraph contract and the checker communication cost
ledger outside the clause 21 endpoint. -/
def clause21Residual : List String :=
  [ "the historical stored-subgraph contract is refuted by the frozen package; only the \
corrected setup/update/replay account of the frozen package is discharged here",
    "the checker-communication cost ledger of the stored subgraph is not derived on the \
Dev side" ]

/-- Descriptions of the historical numerical contract and source exponent transport derivation
outside the clause 22 endpoint. -/
def clause22Residual : List String :=
  [ "the historical numerical Theorem-5 contract is refuted by the frozen package; the \
polylogarithmic replacement of the frozen package is discharged instead",
    "the source real exponent transport is consumed from the frozen package and not \
re-derived on the Dev side" ]

/-- Descriptions of the combined workspace and nontrivial execution gate ledgers outside the
finite encoding endpoint. -/
def clause23Residual : List String :=
  [ "the `O(log n)` quantum workspace and the `O(n^2)` classical workspace of the \
source are not turned into a single Dev-side ledger here; only the injective \
encodings of the search index and of the adjacency table and the zero-gate circuit \
are discharged",
    "the gate-count ledger of a non-trivial run is not derived on the Dev side" ]

/-- A description of the finite small graph case analysis not rederived by the low degree
threshold endpoint. -/
def clause24Residual : List String :=
  [ "the `dLo = 0` branch is discharged through the frozen non-vacuity statement; the \
finite small-`n` case analysis of the branch is not re-derived on the Dev side" ]

end Qatlib.Concepts.WalkSearch.MainResults
