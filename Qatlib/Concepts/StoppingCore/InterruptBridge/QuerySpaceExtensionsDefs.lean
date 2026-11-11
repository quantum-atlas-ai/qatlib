/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.LocalCapability
import Qatlib.Concepts.HspRecovery.CyclicRecovery.AlgebraicOracle
import Qatlib.Concepts.QueryWordCore.QueryMachinery.Oracle
import Qatlib.Concepts.QueryWordCore.QueryMachinery.NegativeAdversary
import Qatlib.Concepts.StoppingCore.InterruptBridge.BitToPhaseSameInput
import Qatlib.Concepts.QueryComplexity.AdversarySearch.WorkspaceQueryMagnitude
import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.AdaptiveQueryPurification
import Qatlib.Concepts.ShadowModels.ShadowChannel.ObservedEvent
import Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedQueryBudget
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.FiniteStoppingTail
import Qatlib.Concepts.StoppingCore.InterruptBridge.WeightedStoppingBudget
import Qatlib.Concepts.StoppingCore.BranchCostCore.UnboundedFiniteExecution

/-!
# Specifications for query-space extensions

This module defines predicates for clean-ancilla circuit transport, adaptive purification,
polynomial and adversary bounds, and oracle simulation with access ledgers. It also specifies
stopping-tail identities, positive-cost termination conditions, and finite versus unbounded
search acceptance.

The circuit and measurement conventions use the standard framework of [NielsenChuang2010]. The
definitions keep normalization, oracle capabilities, and charged resources explicit so later
results can state their precise assumptions.

## Main statements

* `cleanRunTransport`: clean-ancilla circuit, readout, and resource correspondence
* `adaptivePurificationBridge`: unitary deferred-measurement simulation specification
* `AccessLedger`: separate access kinds and fixed-gate charges
* `stopJointLaw`: query-cutoff acceptance and tail specification

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.StoppingCore.BranchCostCore
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.HspRecovery.CyclicRecovery
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.AdaptiveQuery
open Qatlib.Concepts.QueryComplexity.AdversarySearch
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.ShadowModels.ShadowChannel
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CompressedQuery.CompressOracle
open Qatlib.Concepts.QueryWordCore.QueryMachinery

namespace Qatlib.Concepts.StoppingCore.InterruptBridge
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Matrix

open scoped Matrix.Norms.L2Operator ENNReal

section Norms

/-- The operator norm of the difference between two oracle matrices. -/
noncomputable def oracleDistance {K : Type} [Fintype K] [DecidableEq K]
    (O Q : Matrix K K ℂ) : ℝ :=
  ‖O - Q‖

/-- The operator norm of an adversary weight matrix. -/
noncomputable def advWeightNorm {X : Type} [Fintype X] [DecidableEq X]
    (Γ : Matrix X X ℂ) : ℝ :=
  ‖Γ‖

/-- An adversary matrix is valid when it is Hermitian and vanishes on pairs with equal Boolean
outputs. -/
def adversaryValid {X : Type} [Fintype X] [DecidableEq X] (f : X → Bool)
    (Γ : Matrix X X ℂ) : Prop :=
  Γ.IsHermitian ∧ ∀ x y, f x = f y → Γ x y = 0

end Norms

section CleanAncilla

variable {I J F : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- The embedding that appends the fixed ancilla basis value `j₀`. -/
def cleanEmbed (j₀ : J) (x : I) : I × J := (x, j₀)

/-- The readout event on a product space that tests the first register and accepts every ancilla
value. -/
def ancillaReadout (A : Finset I) : Finset (I × J) := A ×ˢ Finset.univ

/-- The diagonal projection onto the basis indices belonging to a finite readout event. -/
noncomputable def readoutEffect {K : Type} [Fintype K] [DecidableEq K] (S : Finset K) :
    Matrix K K ℂ :=
  Matrix.diagonal fun k => if k ∈ S then (1 : ℂ) else 0

/-- The oracle family extended by the identity on an ancilla register. -/
noncomputable def ancillaOracle (O : F → Matrix I I ℂ) (f : F) :
    Matrix (I × J) (I × J) ℂ :=
  TensorGate (O f) 1

/-- The condition that a state factors as an arbitrary data state tensored with the basis state
`j₀`. -/
def cleanInit (j₀ : J) (ψ : QState (I × J)) : Prop :=
  ∃ ψ₀ : QState I, ψ = TensorState ψ₀ (Qatlib.Foundations.PureStateMath.Ket j₀)

/-- The specification of a unitary lifted circuit with a clean ancilla, unchanged resource
counts, factored readout effects, and preserved measurement probabilities. -/
def cleanRunTransport (O : F → Matrix I I ℂ) (Acc : F → Finset I)
    (C : Circuit I) (ψ₀ : QState I) (j₀ : J)
    (C' : Circuit (I × J)) (ψ' : QState (I × J)) : Prop :=
  C' = LiftCircuitTo J C ∧ ψ' = TensorState ψ₀ (Qatlib.Foundations.PureStateMath.Ket j₀) ∧
    QueryCount C' = QueryCount C ∧ GateCount C' = GateCount C ∧ Size C' = Size C ∧
    IsUnitaryCircuit C' ∧
    (∀ f : F, readoutEffect (K := I × J) (ancillaReadout (Acc f)) =
      TensorGate (readoutEffect (Acc f)) (1 : Matrix J J ℂ)) ∧
    ∀ f : F, MeasureProb (Run (ancillaOracle (J := J) O f) C' ψ') (ancillaReadout (Acc f)) =
      MeasureProb (Run (O f) C ψ₀) (Acc f)

/-- The existence of a normalized unitary circuit using at most `Q` queries and achieving event
probability at least `p` for every oracle input. -/
def upperBoundWitness (O : F → Matrix I I ℂ) (Acc : F → Finset I) (Q : ℕ) (p : ℝ) : Prop :=
  ∃ (C : Circuit I) (ψ₀ : QState I), IsUnitaryCircuit C ∧ Normalized ψ₀ ∧
    QueryCount C ≤ Q ∧ ∀ f : F, p ≤ MeasureProb (Run (O f) C ψ₀) (Acc f)

/-- The specification that every normalized unitary upper-bound witness lifts to a clean ancilla
with unchanged counts and success bounds. -/
def cleanUpperTransport (O : F → Matrix I I ℂ) (Acc : F → Finset I) (j₀ : J)
    (Q : ℕ) (p : ℝ) : Prop :=
  ∀ (C : Circuit I) (ψ₀ : QState I),
    IsUnitaryCircuit C → Normalized ψ₀ → QueryCount C ≤ Q →
    (∀ f : F, p ≤ MeasureProb (Run (O f) C ψ₀) (Acc f)) →
    ∃ (C' : Circuit (I × J)) (ψ' : QState (I × J)),
      cleanRunTransport O Acc C ψ₀ j₀ C' ψ' ∧
      QueryCount C' ≤ Q ∧
      ∀ f : F, p ≤ MeasureProb (Run (ancillaOracle O f) C' ψ') (ancillaReadout (Acc f))

end CleanAncilla

section Bridge

variable {n : ℕ} {W : Type} [Fintype W] [DecidableEq W]

/-- The existence of a real polynomial of total degree at most `d`, multilinear in each
variable, representing the acceptance function on Boolean inputs. -/
def multilinearRep {m : ℕ} (accept : (Fin m → Bool) → ℝ) (d : ℕ) : Prop :=
  ∃ p : MvPolynomial (Fin m) ℝ, p.totalDegree ≤ d ∧
    (∀ c : Fin m →₀ ℕ, p.coeff c ≠ 0 → ∀ i, c i ≤ 1) ∧
    ∀ f : Fin m → Bool,
      MvPolynomial.eval (fun i => if f i then (1 : ℝ) else 0) p = accept f

/-- The acceptance function of an observed circuit with a workspace bit oracle, as a function of
the Boolean oracle input. -/
noncomputable def treeAcceptance (P : ObservedCircuit ((Fin n × Bool) × W))
    (ψ : QState ((Fin n × Bool) × W)) : (Fin n → Bool) → ℝ :=
  fun bs => observedAcceptance (workspaceBitOracle (W := W) bs) P ψ

/-- The specification of a unitary deferred-measurement circuit preserving observed acceptance,
with exact query depth and bounds on gates and trace history. -/
def adaptivePurificationBridge (P : ObservedCircuit ((Fin n × Bool) × W))
    (R : ℕ) (C : Circuit ((Fin n × Bool) × (W × Fin (R + 1) × Bool))) : Prop :=
  IsUnitaryCircuit C ∧ QueryCount C = observedQueryDepth P ∧
    GateCount C ≤ 10 * observedTreeNodes P * (observedQueryDepth P + 1) ∧
    ∀ (f : Fin n → Bool) (ψ : QState ((Fin n × Bool) × W)),
      (observedTraces (workspaceBitOracle (W := W) f) P ψ).length ≤ R + 1 ∧
      MeasureProb (Run (workspaceBitOracle (W := W × Fin (R + 1) × Bool) f) C
        (deferredObservedInput (R := R) ψ)) (adaptiveObservedHistoryEvent P R) =
        observedAcceptance (workspaceBitOracle (W := W) f) P ψ

/-- The existence of an adaptive purification bridge and a multilinear acceptance polynomial of
degree at most twice the observed query depth. -/
def bridgePolynomialTransport (P : ObservedCircuit ((Fin n × Bool) × W))
    (ψ : QState ((Fin n × Bool) × W)) : Prop :=
  ∃ (R : ℕ) (C : Circuit ((Fin n × Bool) × (W × Fin (R + 1) × Bool))),
    adaptivePurificationBridge P R C ∧
    multilinearRep (treeAcceptance P ψ) (2 * observedQueryDepth P)

/-- The existence of an adaptive purification bridge together with adversary validity and the
stated adversary bound in terms of observed query depth. -/
def bridgeAdversaryTransport {X : Type} [Fintype X] [DecidableEq X] [Nonempty X]
    (input : X → Fin n → Bool) (f : X → Bool) (Γ : Matrix X X ℂ) (ε : ℝ)
    (P : ObservedCircuit ((Fin n × Bool) × W)) : Prop :=
  ∃ (R : ℕ) (C : Circuit ((Fin n × Bool) × (W × Fin (R + 1) × Bool))),
    adaptivePurificationBridge P R C ∧
    adversaryValid f Γ ∧
    (1 - 2 * Real.sqrt (ε * (1 - ε))) * advWeightNorm Γ ≤
      2 * observedQueryDepth P * advFilterBound input Γ

/-- The adversary lower-bound specification for normalized unitary circuits with a clean ancilla
and bounded-error readout. -/
def cleanAncillaLowerTransport {X : Type} [Fintype X] [DecidableEq X] [Nonempty X]
    (J : Type) [Fintype J] [DecidableEq J]
    (input : X → Fin n → Bool) (f : X → Bool) (Γ : Matrix X X ℂ) (ε : ℝ) : Prop :=
  adversaryValid f Γ → 0 ≤ ε → ε ≤ 1 / 2 →
  ∀ (C' : Circuit ((Fin n × Bool) × J)) (ψ' : QState ((Fin n × Bool) × J)) (j₀ : J)
    (E₀ : Finset (Fin n × Bool)),
    IsUnitaryCircuit C' → Normalized ψ' → cleanInit j₀ ψ' →
    (∀ x : X, 1 - ε ≤ MeasureProb
      (Run (workspaceBitOracle (W := J) (input x)) C' ψ')
      (if f x then ancillaReadout (J := J) E₀ else (ancillaReadout (J := J) E₀)ᶜ)) →
    (1 - 2 * Real.sqrt (ε * (1 - ε))) * advWeightNorm Γ ≤
      2 * QueryCount C' * advFilterBound input Γ

end Bridge

section Ledgers

/-- Natural-valued resource counts for forward, controlled, and inverse accesses, address bits,
per-access fees, and fixed gates. -/
structure AccessLedger where
  forwardAccesses : ℕ
  controlledAccesses : ℕ
  inverseAccesses : ℕ
  addressBits : ℕ
  perAccessCharge : ℕ
  fixedGates : ℕ

namespace AccessLedger

/-- The sum of the forward, controlled, and inverse access counts in a ledger. -/
def totalAccesses (L : AccessLedger) : ℕ :=
  L.forwardAccesses + L.controlledAccesses + L.inverseAccesses

/-- The total access count multiplied by the sum of the address width and the per-access fee. -/
def accessCharge (L : AccessLedger) : ℕ :=
  L.totalAccesses * (L.addressBits + L.perAccessCharge)

/-- The condition that both controlled and inverse access counts are zero. -/
def freeOfControlInverse (L : AccessLedger) : Prop :=
  L.controlledAccesses = 0 ∧ L.inverseAccesses = 0

end AccessLedger

/-- The ledger relation preserving access counts, fees, and fixed gates while adding one address
bit to the target. -/
def phaseToBitLedger (source target : AccessLedger) : Prop :=
  target.forwardAccesses = source.forwardAccesses ∧
    target.controlledAccesses = source.controlledAccesses ∧
    target.inverseAccesses = source.inverseAccesses ∧
    target.addressBits = source.addressBits + 1 ∧
    target.perAccessCharge = source.perAccessCharge ∧
    target.fixedGates = source.fixedGates

/-- The ledger relation preserving access counts, address bits, and fees while adding two fixed
gates per forward access. -/
def bitToPhaseLedger (source target : AccessLedger) : Prop :=
  target.forwardAccesses = source.forwardAccesses ∧
    target.controlledAccesses = source.controlledAccesses ∧
    target.inverseAccesses = source.inverseAccesses ∧
    target.addressBits = source.addressBits ∧
    target.perAccessCharge = source.perAccessCharge ∧
    target.fixedGates = source.fixedGates + 2 * source.forwardAccesses

/-- The condition that each nonzero controlled or inverse access count has a granted capability
and a positive address-plus-access fee. -/
def controlInverseHonest (L : AccessLedger) (grantedControl grantedInverse : Prop) : Prop :=
  (L.controlledAccesses = 0 ∨
    (grantedControl ∧ 0 < L.controlledAccesses ∧ 0 < L.addressBits + L.perAccessCharge)) ∧
  (L.inverseAccesses = 0 ∨
    (grantedInverse ∧ 0 < L.inverseAccesses ∧ 0 < L.addressBits + L.perAccessCharge))

/-- The existence of a controlled implementation of the oracle matrix `U`. -/
def hasControlledCapability {I : Type} [Fintype I] [DecidableEq I]
    (U : Matrix I I ℂ) : Prop :=
  Nonempty (HasControlled U)

/-- The existence of an inverse implementation of the oracle matrix `U`. -/
def hasInverseCapability {I : Type} [Fintype I] [DecidableEq I]
    (U : Matrix I I ℂ) : Prop :=
  Nonempty (HasInverse U)

/-- The specification that honest controlled and inverse accesses have positive per-access
charges and obey the ledger's total-charge formula. -/
def chargedCapabilityLaw {I : Type} [Fintype I] [DecidableEq I]
    (U : Matrix I I ℂ) (L : AccessLedger) : Prop :=
  controlInverseHonest L (hasControlledCapability U) (hasInverseCapability U) →
    L.accessCharge = L.totalAccesses * (L.addressBits + L.perAccessCharge) ∧
      (L.controlledAccesses = 0 ∨ 0 < L.addressBits + L.perAccessCharge) ∧
      (L.inverseAccesses = 0 ∨ 0 < L.addressBits + L.perAccessCharge)

end Ledgers

section Directions

variable {I : Type} [Fintype I] [DecidableEq I]

/-- The encoding of a Boolean as zero or one in `ZMod 2`. -/
def boolToZMod (b : Bool) : ZMod 2 := if b then 1 else 0

/-- The bit-oracle action sending `(x, b)` to `(x, b ^^ f x)`. -/
def bitAction (f : I → Bool) (p : I × Bool) : I × Bool := BitFlip f p

/-- The additive value-oracle action sending `(x, z)` to `(x, z + f x)`. -/
def valueAction {R : Type} [AddGroup R] (f : I → R) (p : I × R) : I × R :=
  addOracleEquiv f p

/-- The condition that Boolean bit-oracle actions agree with additive `ZMod 2` oracle actions
under `boolToZMod`. -/
def bitValueActionsUnify (f : I → Bool) : Prop :=
  ∀ (x : I) (b : Bool),
    boolToZMod (bitAction f (x, b)).2 =
      (valueAction (fun x => if f x then (1 : ZMod 2) else 0) (x, boolToZMod b)).2

/-- The equality of Boolean and `ZMod 2` answer-register readout probabilities after one query
from a zero answer register. -/
def valueBitReadoutUnify (f : I → Bool) : Prop :=
  ∀ (ψ : QState I) (b : Bool),
    MarginalProbRight
      (Run (AddOracle fun x => if f x then (1 : ZMod 2) else 0) [Step.query]
        (TensorState ψ (Qatlib.Foundations.PureStateMath.Ket 0))) ({boolToZMod b} : Finset (ZMod 2)) =
      MarginalProbRight
        (Run (BitOracleOn f) [Step.query] (TensorState ψ (Qatlib.Foundations.PureStateMath.Ket false))) ({b} : Finset Bool)

/-- The equality of all measurement probabilities for the constantly false and constantly true
phase oracles in any fixed circuit. -/
def phaseConstantUnidentifiable : Prop :=
  ∀ (C : Circuit I) (ψ : QState I) (S : Finset I),
    MeasureProb (Run (PhaseOracle (fun _ => false)) C ψ) S =
      MeasureProb (Run (PhaseOracle (fun _ => true)) C ψ) S

/-- The impossibility of separating the two constant phase oracles by one event with the stated
error thresholds from a normalized input. -/
def noBaselinePhaseToBit (ε : ℝ) : Prop :=
  ∀ (C : Circuit I) (ψ : QState I) (S : Finset I),
    Normalized ψ →
    ¬ (1 - ε ≤ MeasureProb (Run (PhaseOracle (fun _ => false)) C ψ) S ∧
      MeasureProb (Run (PhaseOracle (fun _ => true)) C ψ) S ≤ ε)

/-- The normalized equal superposition of two distinct basis states, or their single basis state
when they coincide. -/
noncomputable def spanPlus (x y : I) : QState I :=
  fun z => if z = x then (if x = y then (1 : ℂ) else (1 : ℂ) / (Real.sqrt 2 : ℂ))
    else if z = y then (1 : ℂ) / (Real.sqrt 2 : ℂ) else 0

/-- The specification that a known false baseline enables a unitary circuit with at most one
phase query to distinguish the value at `x` exactly. -/
def baselineExtractsBit (f : I → Bool) (x xstar : I) : Prop :=
  f xstar = false →
    ∃ (C : Circuit I) (S : Finset I), QueryCount C ≤ 1 ∧ IsUnitaryCircuit C ∧
      (f x = false → MeasureProb (Run (PhaseOracle f) C (spanPlus x xstar)) S = 1) ∧
      (f x = true → MeasureProb (Run (PhaseOracle f) C (spanPlus x xstar)) S = 0)

variable {W : Type} [Fintype W] [DecidableEq W]

/-- A bit-to-phase simulation specification preserving same-input measurement probabilities and
query counts, adding two gates per query, and tracking honest access ledgers. -/
def bitToPhaseSimulation (f : I → Bool) (C : Circuit ((I × Bool) × W))
    (ψ : QState ((I × Bool) × W)) (source target : AccessLedger) : Prop :=
  bitToPhaseLedger source target ∧
    source.freeOfControlInverse ∧ target.freeOfControlInverse ∧
    source.accessCharge = source.totalAccesses * (source.addressBits + source.perAccessCharge) ∧
    target.accessCharge = target.totalAccesses * (target.addressBits + target.perAccessCharge) ∧
    source.forwardAccesses = QueryCount C ∧
    source.fixedGates = GateCount C ∧
    target.forwardAccesses = QueryCount C ∧
    target.fixedGates = GateCount C + 2 * QueryCount C ∧
    ∃ C' : Circuit ((I × Bool) × W),
      QueryCount C' = QueryCount C ∧
      GateCount C' = GateCount C + 2 * QueryCount C ∧
      (IsUnitaryCircuit C' ↔ IsUnitaryCircuit C) ∧
      ∀ S : Finset ((I × Bool) × W),
        MeasureProb (Run (workspacePhaseOracle f) C' ψ) S =
          MeasureProb (Run (workspaceBitOracle f) C ψ) S

/-- A phase-to-bit simulation specification using a lifted circuit and a `Minus` ancilla,
preserving measurement probabilities and circuit counts with the corresponding ledgers. -/
def phaseToBitSimulation (f : I → Bool) (C : Circuit I) (ψ : QState I)
    (source target : AccessLedger) : Prop :=
  phaseToBitLedger source target ∧
    source.freeOfControlInverse ∧ target.freeOfControlInverse ∧
    source.accessCharge = source.totalAccesses * (source.addressBits + source.perAccessCharge) ∧
    target.accessCharge = target.totalAccesses * (target.addressBits + target.perAccessCharge) ∧
    source.forwardAccesses = QueryCount C ∧
    source.fixedGates = GateCount C ∧
    target.forwardAccesses = QueryCount C ∧
    target.fixedGates = GateCount C ∧
    ∃ C' : Circuit (I × Bool),
      C' = LiftCircuitTo Bool C ∧
      QueryCount C' = QueryCount C ∧
      GateCount C' = GateCount C ∧
      ∀ S : Finset I,
        MeasureProb (Run (BitOracleOn f) C' (TensorState ψ Minus)) (ancillaReadout (J := Bool) S) =
          MeasureProb (Run (PhaseOracle f) C ψ) S

end Directions

section Stopping

variable {I : Type} [Fintype I] [DecidableEq I]

/-- The Boolean event that a trace accepts using at most `K` queries. -/
def acceptedWithin (K : ℕ) (t : BranchTrace I) : Bool :=
  t.accepted && decide (t.queries ≤ K)

/-- The Boolean event that a trace accepts using more than `K` queries. -/
def acceptedBeyond (K : ℕ) (t : BranchTrace I) : Bool :=
  t.accepted && decide (K < t.queries)

/-- The Boolean event that a trace uses at least `K` queries. -/
def queryTail (K : ℕ) (t : BranchTrace I) : Bool := decide (K ≤ t.queries)

/-- The specification of an acceptance split at every query cutoff, exact truncated acceptance,
and the expected-query tail bound. -/
def stopJointLaw (O : Matrix I I ℂ) (P : ObservedCircuit I) (ψ : QState I) : Prop :=
  ∀ K : ℕ,
    observedAcceptance O P ψ =
      observedEventMass O P ψ (acceptedWithin K) +
        observedEventMass O P ψ (acceptedBeyond K) ∧
    observedAcceptance O (truncateObservedQueries P K) ψ =
      observedEventMass O P ψ (acceptedWithin K) ∧
    (K : ℝ) * observedEventMass O P ψ (queryTail K) ≤ expectedObservedQueries O P ψ

/-- The conditional hybrid-distance inequality for a unitary circuit and normalized input,
without requiring the oracle matrices to be unitary. -/
def hybridDistanceBound {K : Type} [Fintype K] [DecidableEq K]
    (O O' : Matrix K K ℂ) (C : Circuit K) (ψ : QState K) (Q : ℕ) : Prop :=
  IsUnitaryCircuit C → Normalized ψ → QueryCount C ≤ Q →
    ‖toEuclidean_fromVec (Run O C ψ) - toEuclidean_fromVec (Run O' C ψ)‖ ≤
      Q * oracleDistance O O'

end Stopping

section AdaptiveBounds

variable {X : Type} [Fintype X] [DecidableEq X] {n : ℕ} {W : Type}
  [Fintype W] [DecidableEq W]

/-- The bounded-error condition that observed acceptance is at least `1 - ε` on true inputs and
at most `ε` on false inputs. -/
def treeBoundedError (input : X → Fin n → Bool) (f : X → Bool)
    (P : ObservedCircuit ((Fin n × Bool) × W))
    (ψ : QState ((Fin n × Bool) × W)) (ε : ℝ) : Prop :=
  ∀ x : X,
    if f x then 1 - ε ≤ observedAcceptance (workspaceBitOracle (W := W) (input x)) P ψ
    else observedAcceptance (workspaceBitOracle (W := W) (input x)) P ψ ≤ ε

/-- The uniform bound `Tbar` on expected observed queries over the input family. -/
def expectedChargeBound (input : X → Fin n → Bool)
    (P : ObservedCircuit ((Fin n × Bool) × W))
    (ψ : QState ((Fin n × Bool) × W)) (Tbar : ℝ) : Prop :=
  ∀ x : X, expectedObservedQueries (workspaceBitOracle (W := W) (input x)) P ψ ≤ Tbar

end AdaptiveBounds

section Zenos

variable {S O : Type} [Fintype S] [DecidableEq S] [Fintype O] [DecidableEq O]

/-- The nontermination mass of a randomized execution. -/
noncomputable def neverStopMass (next : S → PMF (RandomizedExecution.Configuration S O))
    (cfg : RandomizedExecution.Configuration S O) : ℝ≥0∞ :=
  nonterminationMass next cfg

/-- The probability that a finite randomized run is in a halted configuration after `n` steps. -/
noncomputable def haltedMassWithin (next : S → PMF (RandomizedExecution.Configuration S O))
    (n : ℕ) (cfg : RandomizedExecution.Configuration S O) : ℝ≥0∞ :=
  CostedLaw.event (RandomizedExecution.runFor next n cfg) fun x => ∃ a, x.1 = Sum.inl a

/-- The specification that finite halted and pending masses sum to one and that nontermination
mass is the infimum of pending masses. -/
def stopTailNeverJointLaw (next : S → PMF (RandomizedExecution.Configuration S O))
    (cfg : RandomizedExecution.Configuration S O) : Prop :=
  ∀ n : ℕ,
    haltedMassWithin next n cfg + pendingMass next cfg n = 1 ∧
      neverStopMass next cfg = ⨅ k, pendingMass next cfg k

/-- The condition that the execution has zero nontermination mass. -/
def aeTerminates (next : S → PMF (RandomizedExecution.Configuration S O))
    (cfg : RandomizedExecution.Configuration S O) : Prop :=
  neverStopMass next cfg = 0

/-- The condition that every running state has strictly positive natural cost. -/
def positiveCharge (c : S → ℕ) : Prop := ∀ s : S, 0 < c s

/-- The condition of zero costs at every state, positive nontermination mass from `s`, and zero
expected weighted cost. -/
def zenoZeroCharge (next : S → PMF (O ⊕ S)) (c : S → ℕ) (s : S) : Prop :=
  (∀ t : S, c t = 0) ∧
    0 < neverStopMass (O := O) next (Sum.inr s) ∧
    weightedExpectedCost next c (Sum.inr s) = 0

/-- The deterministic transition kernel that always remains in the unique running state. -/
noncomputable def zenoNext : PUnit → PMF (PUnit ⊕ PUnit) :=
  fun _ => PMF.pure (Sum.inr PUnit.unit)

/-- The identically zero cost function on the singleton state space. -/
def zenoCharge : PUnit → ℕ := fun _ => 0

end Zenos

section PolyRep

/-- The indicator that a Boolean function on natural numbers is true at some index. -/
noncomputable def unboundedSearchAcceptance (f : ℕ → Bool) : ℝ := by
  classical exact if ∃ k, f k = true then 1 else 0

/-- The indicator that a Boolean function is true at some index smaller than `K`. -/
noncomputable def truncatedSearchAcceptance (K : ℕ) (f : ℕ → Bool) : ℝ :=
  if ∃ k, k < K ∧ f k = true then 1 else 0

/-- The existence of a multilinear polynomial of degree at most `K` representing search
acceptance over the first `K` indices. -/
def truncatedSearchPolyRep (K : ℕ) : Prop :=
  ∃ p : MvPolynomial ℕ ℝ, p.totalDegree ≤ K ∧
    (∀ c : ℕ →₀ ℕ, p.coeff c ≠ 0 → ∀ i, c i ≤ 1) ∧
    ∀ f : ℕ → Bool,
      MvPolynomial.eval (fun i => if f i then (1 : ℝ) else 0) p =
        truncatedSearchAcceptance K f

/-- The nonexistence of a multilinear polynomial in countably many variables representing
unbounded search acceptance on every Boolean input. -/
def noUnconditionalPolyRep : Prop :=
  ¬ ∃ p : MvPolynomial ℕ ℝ,
    (∀ c : ℕ →₀ ℕ, p.coeff c ≠ 0 → ∀ i, c i ≤ 1) ∧
      ∀ f : ℕ → Bool,
        MvPolynomial.eval (fun i => if f i then (1 : ℝ) else 0) p =
          unboundedSearchAcceptance f

end PolyRep

end Qatlib.Concepts.StoppingCore.InterruptBridge
