/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CryptoDisting99.Equivalence.Defs
open Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.LocalReflectionGates Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.MixedFidelity.TraceNormRankBound Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Concepts.PauliClifford.ExactRank Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit

/-!
# Quantum exponential indistinguishability (Definitions 12 and 13)

Fuchs & van de Graaf (1999), Definition 13, §6, p. 22: two families of density
matrices `{ρ0^(n)}`, `{ρ1^(n)}` are exponentially indistinguishable when the
Kolmogorov distance `K(ρ0^(n), ρ1^(n))` decays as `εⁿ` for some `0 < ε < 1`.
Theorem 2 states that the choice of the measure (`K`, `PE`, `B`, `SD`) is
immaterial, so we package all four quantum forms here.

These predicates are used by `Lemma1` (classical form) and `Theorem2`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CryptoDisting99.Equivalence

open Qatlib.Papers.CryptoDisting99.Equivalence

open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath

variable {D : ℕ}

/-- Quantum exponential indistinguishability with respect to `K`
(Definition 13, p. 22). -/
def QuantExpK (P Q : ℕ → Operator D) (hP : ∀ n, IsDensityOperator (P n))
    (hQ : ∀ n, IsDensityOperator (Q n)) : Prop :=
  ExpSmall fun n => quantumKolmogorov (P n) (Q n) (hP n) (hQ n)

/-- Quantum exponential indistinguishability with respect to `PE` (convergence of
the error probability to `1/2`). -/
def QuantExpPE (P Q : ℕ → Operator D) (hP : ∀ n, IsDensityOperator (P n))
    (hQ : ∀ n, IsDensityOperator (Q n)) : Prop :=
  ExpNear (fun n => quantumErrProb (P n) (Q n) (hP n) (hQ n)) (1 / 2)

/-- Quantum exponential indistinguishability with respect to `B` (convergence of
the Bhattacharyya coefficient to `1`). -/
def QuantExpB (P Q : ℕ → Operator D) (hP : ∀ n, IsDensityOperator (P n))
    (hQ : ∀ n, IsDensityOperator (Q n)) : Prop :=
  ExpNear (fun n => quantumBhattacharyya (P n) (Q n) (hP n) (hQ n)) 1

/-- Quantum exponential indistinguishability with respect to `SD`. -/
def QuantExpSD (P Q : ℕ → Operator D) (hP : ∀ n, IsDensityOperator (P n))
    (hQ : ∀ n, IsDensityOperator (Q n)) : Prop :=
  ExpSmall fun n => quantumShannon (P n) (Q n) (hP n) (hQ n)

end Qatlib.Papers.CryptoDisting99.Equivalence
