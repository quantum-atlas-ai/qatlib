/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementStatisticsExt
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.FiniteLaws.FiniteInformationDivergence
import Qatlib.Concepts.MixedFidelity.FidelityMetric.MixedFidelity
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-!
# Classical and quantum distinguishability measures

The definitions `classicalErrProb`, `classicalKolmogorov`, `bhattacharyya`, and `shannonDist`
specify four classical distinguishability quantities from [FuchsVanDeGraaf1999]. Their quantum
counterparts optimize over finite POVM outcome laws, while `ExpSmall`, `ExpNear`, and the
classical family predicates express eventual exponential bounds.

## Main statements

* `quantumErrProb` and `quantumBhattacharyya`: infima over finite measurements.
* `quantumKolmogorov` and `quantumShannon`: suprema over finite measurements.
* `ClassExpK`, `ClassExpPE`, `ClassExpB`, and `ClassExpSD`: exponential indistinguishability
  predicates.

## References

* [Fuchs and van de Graaf, 1999][FuchsVanDeGraaf1999]
-/

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

/-- Defines the equal-prior classical error probability as half the sum of the pointwise minima
of the two probability laws. -/
def classicalErrProb (p0 p1 : FinDist X) : ℝ :=
  (1 / 2) * ∑ x, min (p0.prob x) (p1.prob x)

/-- Defines the classical Kolmogorov distance as total variation distance. -/
def classicalKolmogorov (p0 p1 : FinDist X) : ℝ :=
  tv p0 p1

/-- Defines the Bhattacharyya coefficient as the sum of square roots of the pointwise
probability products. -/
def bhattacharyya (p0 p1 : FinDist X) : ℝ :=
  ∑ x, Real.sqrt (p0.prob x * p1.prob x)

/-- Defines binary entropy in bits by dividing `Real.binEntropy` by `Real.log 2`. -/
def binaryEntropy (r : ℝ) : ℝ :=
  (Real.log 2)⁻¹ * Real.binEntropy r

/-- Defines the equal-prior Shannon distinguishability as one minus the average posterior binary
entropy. -/
def shannonDist (p0 p1 : FinDist X) : ℝ :=
  1 - ∑ x, ((p0.prob x + p1.prob x) / 2) *
    binaryEntropy (p0.prob x / (p0.prob x + p1.prob x))

/-- Every probability in a finite probability distribution is nonnegative. -/
theorem FinDist.prob_nonneg' (p : FinDist X) (x : X) : 0 ≤ p.prob x := p.nonneg x

variable {D : ℕ}

/-- Defines quantum error probability as the infimum of classical error probabilities of outcome
laws over all finite POVMs. -/
def quantumErrProb (ρ σ : Operator D) (hρ : IsDensityOperator ρ)
    (hσ : IsDensityOperator σ) : ℝ :=
  sInf { x : ℝ | ∃ (m : ℕ) (E : FinitePOVM (Fin m) D),
    x = classicalErrProb (povmRecordLaw E ρ hρ) (povmRecordLaw E σ hσ) }

/-- Defines quantum Kolmogorov distance as the supremum of classical Kolmogorov distances of
outcome laws over all finite POVMs. -/
def quantumKolmogorov (ρ σ : Operator D) (hρ : IsDensityOperator ρ)
    (hσ : IsDensityOperator σ) : ℝ :=
  sSup { x : ℝ | ∃ (m : ℕ) (E : FinitePOVM (Fin m) D),
    x = classicalKolmogorov (povmRecordLaw E ρ hρ) (povmRecordLaw E σ hσ) }

/-- Defines the quantum Bhattacharyya coefficient as the infimum of the classical coefficients
of outcome laws over all finite POVMs. -/
def quantumBhattacharyya (ρ σ : Operator D) (hρ : IsDensityOperator ρ)
    (hσ : IsDensityOperator σ) : ℝ :=
  sInf { x : ℝ | ∃ (m : ℕ) (E : FinitePOVM (Fin m) D),
    x = bhattacharyya (povmRecordLaw E ρ hρ) (povmRecordLaw E σ hσ) }

/-- Defines quantum Shannon distinguishability as the supremum of classical Shannon
distinguishabilities of outcome laws over all finite POVMs. -/
def quantumShannon (ρ σ : Operator D) (hρ : IsDensityOperator ρ)
    (hσ : IsDensityOperator σ) : ℝ :=
  sSup { x : ℝ | ∃ (m : ℕ) (E : FinitePOVM (Fin m) D),
    x = shannonDist (povmRecordLaw E ρ hρ) (povmRecordLaw E σ hσ) }

/-- Requires an eventual upper bound `d n ≤ ε ^ n` for some real `ε` strictly between zero and
one. -/
def ExpSmall (d : ℕ → ℝ) : Prop :=
  ∃ (n0 : ℕ) (ε : ℝ), 0 < ε ∧ ε < 1 ∧ ∀ n, n0 ≤ n → d n ≤ ε ^ n

/-- Requires the absolute deviation of `d n` from `L` to be eventually bounded by `ε ^ n` for
some real `ε` strictly between zero and one. -/
def ExpNear (d : ℕ → ℝ) (L : ℝ) : Prop :=
  ∃ (n0 : ℕ) (ε : ℝ), 0 < ε ∧ ε < 1 ∧ ∀ n, n0 ≤ n → |d n - L| ≤ ε ^ n

/-- Requires the sequence of classical Kolmogorov distances to satisfy `ExpSmall`. -/
def ClassExpK (P Q : ℕ → FinDist X) : Prop :=
  ExpSmall fun n => classicalKolmogorov (P n) (Q n)

/-- Requires the sequence of classical error probabilities to satisfy `ExpNear` with limit `1 /
2`. -/
def ClassExpPE (P Q : ℕ → FinDist X) : Prop :=
  ExpNear (fun n => classicalErrProb (P n) (Q n)) (1 / 2)

/-- Requires the sequence of Bhattacharyya coefficients to satisfy `ExpNear` with limit one. -/
def ClassExpB (P Q : ℕ → FinDist X) : Prop :=
  ExpNear (fun n => bhattacharyya (P n) (Q n)) 1

/-- Requires the sequence of Shannon distinguishabilities to satisfy `ExpSmall`. -/
def ClassExpSD (P Q : ℕ → FinDist X) : Prop :=
  ExpSmall fun n => shannonDist (P n) (Q n)

end Qatlib.Papers.CryptoDisting99.Equivalence
