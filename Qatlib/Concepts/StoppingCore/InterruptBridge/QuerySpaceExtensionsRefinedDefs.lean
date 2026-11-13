/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.StoppingCore.InterruptBridge.QuerySpaceExtensions
import Qatlib.Concepts.StoppingCore.InterruptBridge.QuerySpaceExtensionsDefs
import Qatlib.Concepts.QueryWordCore.QueryMachinery.NegativeAdversary
import Qatlib.Concepts.QueryWordCore.QueryMachinery.Oracle
import Qatlib.Concepts.HspRecovery.CyclicRecovery.AlgebraicOracle
import Qatlib.Concepts.QueryComplexity.DegreeMethod.LocalCapability
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.AdaptiveQueryPurification
import Qatlib.Concepts.ReferenceError.RefTraceError.TensorOperatorNorm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Refined assumptions for query-space transport

This module defines refined transport specifications with explicit clean-space structure,
normalized tree inputs, and unitary oracle assumptions. It also introduces general angle-valued
phase oracles, additive value-fiber readout laws, and the query-tail truncation specification.

These definitions make the hypotheses of standard circuit and measurement arguments explicit;
see [NielsenChuang2010].

## Main statements

* `correctedBridgeAdversaryTransport`: normalized adaptive adversary transport specification
* `unitaryHybridDistance`: hybrid-distance specification for unitary oracles
* `generalNoBaselinePhaseToBit`: measurement invariance under constant phase offsets
* `generalValueReadoutLaw`: answer-register readout as value-fiber mass

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.StoppingCore.InterruptBridge
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.HspRecovery.CyclicRecovery
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.AdaptiveQuery
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.ShadowModels.ShadowChannel
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.QueryWordCore.QueryMachinery

set_option autoImplicit false

namespace Qatlib.Concepts.StoppingCore.InterruptBridge

open Qatlib
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator ComplexConjugate

section CleanScope

variable {I J F : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- The specification of a clean circuit lift with a fixed basis ancilla, tensor-identity oracle
and readout extensions, and unchanged resource counts. -/
def cleanSpaceScope (O : F → Matrix I I ℂ) (Acc : F → Finset I) (j₀ : J)
    (C : Circuit I) (ψ₀ : QState I) (C' : Circuit (I × J)) (ψ' : QState (I × J)) : Prop :=
  C' = LiftCircuitTo J C ∧
  ψ' = TensorState ψ₀ (Ket j₀) ∧
    (∀ f : F, ancillaOracle (J := J) O f = TensorGate (O f) (1 : Matrix J J ℂ)) ∧
    (∀ f : F, readoutEffect (K := I × J) (ancillaReadout (Acc f)) =
      TensorGate (readoutEffect (Acc f)) (1 : Matrix J J ℂ)) ∧
    QueryCount C' = QueryCount C ∧ GateCount C' = GateCount C ∧ Size C' = Size C

end CleanScope

section NormalizedTree

variable {X : Type} [Fintype X] [DecidableEq X] {n : ℕ} {W : Type}
  [Fintype W] [DecidableEq W]

/-- The conjunction of input-state normalization and the observed tree's bounded-error
condition. -/
def normalizedTreeBoundedError (input : X → Fin n → Bool) (f : X → Bool)
    (P : ObservedCircuit ((Fin n × Bool) × W))
    (ψ : QState ((Fin n × Bool) × W)) (ε : ℝ) : Prop :=
  Normalized ψ ∧ treeBoundedError input f P ψ ε

/-- The adaptive purification and adversary-bound specification under positive input length,
well-formedness, normalized input, bounded error, and a valid adversary matrix. -/
def correctedBridgeAdversaryTransport (input : X → Fin n → Bool) (f : X → Bool)
    (Γ : Matrix X X ℂ) (ε : ℝ) (P : ObservedCircuit ((Fin n × Bool) × W))
    (ψ : QState ((Fin n × Bool) × W)) : Prop :=
  0 < n → observedWellFormed P → 0 ≤ ε → ε ≤ 1 / 2 → Normalized ψ →
    treeBoundedError input f P ψ ε → adversaryValid f Γ →
    ∃ (R : ℕ) (C : Circuit ((Fin n × Bool) × (W × Fin (R + 1) × Bool))),
      adaptivePurificationBridge P R C ∧
      (1 - 2 * Real.sqrt (ε * (1 - ε))) * advWeightNorm Γ ≤
        2 * observedQueryDepth P * advFilterBound input Γ

/-- The existence of an adaptive purification bridge, a valid adversary matrix, and the stated
query-depth adversary inequality. -/
def unrestrictedAdversaryTransport (input : X → Fin n → Bool) (f : X → Bool)
    (Γ : Matrix X X ℂ) (ε : ℝ) (P : ObservedCircuit ((Fin n × Bool) × W)) : Prop :=
  ∃ (R : ℕ) (C : Circuit ((Fin n × Bool) × (W × Fin (R + 1) × Bool))),
    adaptivePurificationBridge P R C ∧
    adversaryValid f Γ ∧
    (1 - 2 * Real.sqrt (ε * (1 - ε))) * advWeightNorm Γ ≤
      2 * observedQueryDepth P * advFilterBound input Γ

end NormalizedTree

section GeneralPhase

variable {I : Type} [Fintype I] [DecidableEq I]

/-- The diagonal phase oracle with entries `exp (I * θ x)`. -/
noncomputable def phaseOracleOfAngle (θ : I → ℝ) : Matrix I I ℂ :=
  Matrix.diagonal fun x => Complex.exp (Complex.I * (θ x : ℂ))

/-- The phase oracle obtained by adding the same real offset `c` to every phase angle. -/
noncomputable def phaseOracleOffset (θ : I → ℝ) (c : ℝ) : Matrix I I ℂ :=
  phaseOracleOfAngle (fun x => θ x + c)

/-- The specification that adding a constant to all oracle phases preserves every fixed
circuit's measurement probabilities. -/
def generalNoBaselinePhaseToBit (θ : I → ℝ) (c : ℝ) : Prop :=
  ∀ (C : Circuit I) (ψ : QState I) (S : Finset I),
    MeasureProb (Run (phaseOracleOffset θ c) C ψ) S =
      MeasureProb (Run (phaseOracleOfAngle θ) C ψ) S

/-- The total squared amplitude of input indices whose value under `v` equals `z`. -/
noncomputable def valueFiberMass {X R : Type} [Fintype X] [DecidableEq X]
    [AddCommGroup R] [Fintype R] [DecidableEq R] (v : X → R) (ψ : QState X) (z : R) : ℝ :=
  ∑ x : X, if v x = z then ‖ψ x‖ ^ 2 else 0

/-- The equality between a single additive-oracle answer-register probability and the
squared-amplitude mass of the corresponding value fiber. -/
def generalValueReadoutLaw {X R : Type} [Fintype X] [DecidableEq X]
    [AddCommGroup R] [Fintype R] [DecidableEq R] (v : X → R) (ψ : QState X) (z : R) : Prop :=
  MarginalProbRight
      (Run (AddOracle v) [Step.query] (TensorState ψ (Ket (0 : R)))) ({z} : Finset R) =
    valueFiberMass v ψ z

end GeneralPhase

section CorrectedHybrid

variable {K : Type} [Fintype K] [DecidableEq K] [Nonempty K]

/-- The hybrid-distance bound for unitary oracle matrices, a unitary circuit, and a normalized
input with at most `Q` queries. -/
def unitaryHybridDistance (O O' : Matrix K K ℂ) (C : Circuit K) (ψ : QState K)
    (Q : ℕ) : Prop :=
  O ∈ Matrix.unitaryGroup K ℂ → O' ∈ Matrix.unitaryGroup K ℂ →
    IsUnitaryCircuit C → Normalized ψ → QueryCount C ≤ Q →
    ‖toEuclidean_fromVec (Run O C ψ) - toEuclidean_fromVec (Run O' C ψ)‖ ≤
      (Q : ℝ) * oracleDistance O O'

end CorrectedHybrid

section CorrectedCharge

variable {X : Type} [Fintype X] [DecidableEq X] [Nonempty X] {n : ℕ} {W : Type}
  [Fintype W] [DecidableEq W]

/-- The query-depth adversary inequality under positive input length, tree well-formedness,
normalized input, bounded error, and adversary validity. -/
def normalizedTreeAdversaryBound
    (input : X → Fin n → Bool) (f : X → Bool) (Γ : Matrix X X ℂ) (ε : ℝ)
    (P : ObservedCircuit ((Fin n × Bool) × W))
    (ψ : QState ((Fin n × Bool) × W)) : Prop :=
  0 < n → observedWellFormed P → 0 ≤ ε → ε ≤ 1 / 2 → Normalized ψ →
    treeBoundedError input f P ψ ε → adversaryValid f Γ →
    (1 - 2 * Real.sqrt (ε * (1 - ε))) * advWeightNorm Γ ≤
      2 * observedQueryDepth P * advFilterBound input Γ

end CorrectedCharge

section TruncatedTail

variable {I : Type} [Fintype I] [DecidableEq I]

/-- The specification of the acceptance split at each query cutoff, exact truncated acceptance,
and the expected-query tail inequality. -/
def truncatedTailLaw (O : Matrix I I ℂ) (P : ObservedCircuit I) (ψ : QState I) : Prop :=
  ∀ K : ℕ,
    observedAcceptance O P ψ =
      observedEventMass O P ψ (acceptedWithin K) +
        observedEventMass O P ψ (acceptedBeyond K) ∧
    observedAcceptance O (truncateObservedQueries P K) ψ =
      observedEventMass O P ψ (acceptedWithin K) ∧
    (K : ℝ) * observedEventMass O P ψ (queryTail K) ≤ expectedObservedQueries O P ψ

end TruncatedTail

end Qatlib.Concepts.StoppingCore.InterruptBridge
