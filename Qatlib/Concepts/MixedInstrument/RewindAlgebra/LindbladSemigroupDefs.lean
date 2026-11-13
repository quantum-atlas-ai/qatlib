/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LindbladFlow.GkslSemigroup.LindbladSemigroup
import Qatlib.Concepts.RiskEstimation.PopulationGap.GibbsMetropolisDefs
import Qatlib.Concepts.LindbladFlow.GkslSemigroup.LindbladSemigroupCore
import Qatlib.Concepts.LindbladFlow.GkslSemigroup.LindbladSemigroupDirichlet
import Qatlib.Concepts.LindbladFlow.GkslSemigroup.LindbladSemigroupEntropy
import Qatlib.Concepts.LindbladFlow.GkslSemigroup.LindbladSemigroupKmsMixing

/-!
# Lindblad entropy and Metropolis cost definitions

This module defines `kmsChiSq`, the inverse square root norm prefactor `kmsMinSpectralWeight`,
and three distinct entropy evolution hypotheses. `EntropyContractionRate` and
`EntropyContractionStep` impose upper bounds, whereas `MlsiEntropyProduction` imposes a lower
bound. It also defines filtered Metropolis rows and query counts used in later estimates. The
semigroup setting is that of [Lindblad1976].

## Main statements

* `kmsChiSq`: The squared KMS norm of the density ratio of `σ` relative to `ρ`, minus one.
* `EntropyContractionRate`: The property `0 < γ ≤ 1` together with relative entropy contraction
  by `1 - γ * h` for every `0 < h ≤ 1` and every density input.
* `MlsiEntropyProduction`: The property `0 < γ ≤ 1` together with a lower bound of `1 - γ * h`
  times the initial relative entropy at every `0 < h ≤ 1` for density inputs.
* `metropolisActualStepQueries`: The actual step query count `(2 + nStar) * qpeWindowQueries M
  n`.

## References

* [Lindblad, 1976][Lindblad1976]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Qatlib.Concepts.GibbsMetropolis.RationalBath
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.DirichletForm.KmsDirichlet

open Qatlib.Concepts.LindbladFlow.GkslSemigroup

namespace Qatlib.Concepts.MixedInstrument.RewindAlgebra

open Matrix
open Qatlib
open Qatlib
open Qatlib.Concepts.LindbladFlow.GkslSemigroup.LindbladSemigroupCore
open Qatlib.Concepts.MixedInstrument.RewindAlgebra
open Qatlib.Concepts.RiskEstimation.PopulationGap
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal BigOperators Classical

noncomputable section

variable {D : ℕ}

/-- The squared KMS norm of the density ratio of `σ` relative to `ρ`, minus one. -/
noncomputable def kmsChiSq (ρ σ : Operator D) : ℝ :=
  (kmsNorm ρ (kmsDensityRatio ρ σ)) ^ 2 - 1

/-- The norm of the inverse of the positive square root of `ρ`, used as a spectral prefactor. -/
noncomputable def kmsMinSpectralWeight (ρ : Operator D) : ℝ :=
  ‖(CFC.sqrt ρ)⁻¹‖

/-- The property `0 < γ ≤ 1` together with relative entropy contraction by `1 - γ * h` for every
`0 < h ≤ 1` and every density input. -/
def EntropyContractionRate (G : GKSL D) (ρ : Operator D) (γ : ℝ) : Prop :=
  0 < γ ∧ γ ≤ 1 ∧
    ∀ (h : ℝ) (σ : Operator D), 0 < h → h ≤ 1 → IsDensityOperator σ →
      relativeEntropy (lindbladSemigroup G h σ) ρ ≤ (1 - γ * h) * relativeEntropy σ ρ

/-- The property `0 < γ ≤ 1` together with relative entropy contraction by `1 - γ` at unit time
for every density input. -/
def EntropyContractionStep (G : GKSL D) (ρ : Operator D) (γ : ℝ) : Prop :=
  0 < γ ∧ γ ≤ 1 ∧
    ∀ σ : Operator D, IsDensityOperator σ →
      relativeEntropy (lindbladSemigroup G 1 σ) ρ ≤ (1 - γ) * relativeEntropy σ ρ

/-- The property `0 < γ ≤ 1` together with a lower bound of `1 - γ * h` times the initial
relative entropy at every `0 < h ≤ 1` for density inputs. -/
def MlsiEntropyProduction (G : GKSL D) (ρ : Operator D) (γ : ℝ) : Prop :=
  0 < γ ∧ γ ≤ 1 ∧
    ∀ (h : ℝ) (σ : Operator D), 0 < h → h ≤ 1 → IsDensityOperator σ →
      (1 - γ * h) * relativeEntropy σ ρ ≤ relativeEntropy (lindbladSemigroup G h σ) ρ

/-- The acceptance contribution from initial energy index `i`, summed over final energy indices
and proposal gates with energy representative filtering and thermal acceptance weights. -/
noncomputable def metropolisAcceptRow {D : ℕ} (E : Fin D → ℝ) (ψ : Fin D → QState (Fin D))
    (ens : ProposalEnsemble D) (β : ℝ) (ρ : Operator D) (i : Fin D) : Operator D :=
  ∑ j, ∑ c,
    ((if isEnergyRep E i ∧ isEnergyRep E j then (1 : ℝ) else 0) *
        ens.weight c * thermalAcceptance E β i j) •
      (energyPi E ψ j * ens.gate c * energyPi E ψ i * ρ * energyPi E ψ i *
        (ens.gate c)ᴴ * energyPi E ψ j)

/-- The rejection contribution from initial energy index `i` and a fixed Boolean history, summed
over paired energy histories with representative filtering. -/
noncomputable def metropolisRejectRow {D : ℕ} (E :Fin D → ℝ) (ψ : Fin D → QState (Fin D))
    (C : Operator D) (β : ℝ) (n : ℕ) (s : Fin n → Bool) (ρ : Operator D) (i : Fin D) :
    Operator D :=
  ∑ l, ∑ r,
    (if isEnergyRep E i ∧ (∀ j, isEnergyRep E (l j)) ∧ (∀ j, isEnergyRep E (r j))
      then temmeG E β i n s l r else 0) •
      (temmeD E ψ C i n l * ρ * (temmeD E ψ C i n r)ᴴ)

/-- The natural number specification cost `D * 2 * 2`. -/
def metropolisSpecStepCost (D : ℕ) : ℕ := D * 2 * 2

/-- The actual step query count `(2 + nStar) * qpeWindowQueries M n`. -/
def metropolisActualStepQueries (M n nStar : ℕ) : ℕ :=
  (2 + nStar) * qpeWindowQueries M n

/-- The exponential factor `exp γ` used to compare unit time entropy contraction with continuous
exponential decay. -/
noncomputable def entropyComparisonConstant (γ : ℝ) : ℝ :=
  Real.exp γ

end

end Qatlib.Concepts.MixedInstrument.RewindAlgebra
