/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementStatisticsExt
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.FiniteLaws.FiniteInformationDivergence
import Qatlib.Concepts.MixedFidelity.FidelityMetric.MixedFidelity
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CryptoDisting99.Equivalence

open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementStatisticsExt
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FiniteInformationDivergence
open Matrix
open scoped BigOperators

variable {X : Type} [Fintype X]

def classicalErrProb (p0 p1 : FinDist X) : ℝ :=
  (1 / 2) * ∑ x, min (p0.prob x) (p1.prob x)

def classicalKolmogorov (p0 p1 : FinDist X) : ℝ :=
  tv p0 p1

def bhattacharyya (p0 p1 : FinDist X) : ℝ :=
  ∑ x, Real.sqrt (p0.prob x * p1.prob x)

def binaryEntropy (r : ℝ) : ℝ :=
  (Real.log 2)⁻¹ * Real.binEntropy r

def shannonDist (p0 p1 : FinDist X) : ℝ :=
  1 - ∑ x, ((p0.prob x + p1.prob x) / 2) *
    binaryEntropy (p0.prob x / (p0.prob x + p1.prob x))

theorem FinDist.prob_nonneg' (p : FinDist X) (x : X) : 0 ≤ p.prob x := p.nonneg x

variable {D : ℕ}

def quantumErrProb (ρ σ : Operator D) (hρ : IsDensityOperator ρ)
    (hσ : IsDensityOperator σ) : ℝ :=
  sInf { x : ℝ | ∃ (m : ℕ) (E : FinitePOVM (Fin m) D),
    x = classicalErrProb (povmRecordLaw E ρ hρ) (povmRecordLaw E σ hσ) }

def quantumKolmogorov (ρ σ : Operator D) (hρ : IsDensityOperator ρ)
    (hσ : IsDensityOperator σ) : ℝ :=
  sSup { x : ℝ | ∃ (m : ℕ) (E : FinitePOVM (Fin m) D),
    x = classicalKolmogorov (povmRecordLaw E ρ hρ) (povmRecordLaw E σ hσ) }

def quantumBhattacharyya (ρ σ : Operator D) (hρ : IsDensityOperator ρ)
    (hσ : IsDensityOperator σ) : ℝ :=
  sInf { x : ℝ | ∃ (m : ℕ) (E : FinitePOVM (Fin m) D),
    x = bhattacharyya (povmRecordLaw E ρ hρ) (povmRecordLaw E σ hσ) }

def quantumShannon (ρ σ : Operator D) (hρ : IsDensityOperator ρ)
    (hσ : IsDensityOperator σ) : ℝ :=
  sSup { x : ℝ | ∃ (m : ℕ) (E : FinitePOVM (Fin m) D),
    x = shannonDist (povmRecordLaw E ρ hρ) (povmRecordLaw E σ hσ) }

def ExpSmall (d : ℕ → ℝ) : Prop :=
  ∃ (n0 : ℕ) (ε : ℝ), 0 < ε ∧ ε < 1 ∧ ∀ n, n0 ≤ n → d n ≤ ε ^ n

def ExpNear (d : ℕ → ℝ) (L : ℝ) : Prop :=
  ∃ (n0 : ℕ) (ε : ℝ), 0 < ε ∧ ε < 1 ∧ ∀ n, n0 ≤ n → |d n - L| ≤ ε ^ n

def ClassExpK (P Q : ℕ → FinDist X) : Prop :=
  ExpSmall fun n => classicalKolmogorov (P n) (Q n)

def ClassExpPE (P Q : ℕ → FinDist X) : Prop :=
  ExpNear (fun n => classicalErrProb (P n) (Q n)) (1 / 2)

def ClassExpB (P Q : ℕ → FinDist X) : Prop :=
  ExpNear (fun n => bhattacharyya (P n) (Q n)) 1

def ClassExpSD (P Q : ℕ → FinDist X) : Prop :=
  ExpSmall fun n => shannonDist (P n) (Q n)

end Qatlib.Papers.CryptoDisting99.Equivalence
