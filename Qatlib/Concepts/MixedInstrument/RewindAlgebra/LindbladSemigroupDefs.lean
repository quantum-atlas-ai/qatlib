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
set_option warningAsError false
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

noncomputable def kmsChiSq (ρ σ : Operator D) : ℝ :=
  (kmsNorm ρ (kmsDensityRatio ρ σ)) ^ 2 - 1

noncomputable def kmsMinSpectralWeight (ρ : Operator D) : ℝ :=
  ‖(CFC.sqrt ρ)⁻¹‖

def EntropyContractionRate (G : GKSL D) (ρ : Operator D) (γ : ℝ) : Prop :=
  0 < γ ∧ γ ≤ 1 ∧
    ∀ (h : ℝ) (σ : Operator D), 0 < h → h ≤ 1 → IsDensityOperator σ →
      relativeEntropy (lindbladSemigroup G h σ) ρ ≤ (1 - γ * h) * relativeEntropy σ ρ

def EntropyContractionStep (G : GKSL D) (ρ : Operator D) (γ : ℝ) : Prop :=
  0 < γ ∧ γ ≤ 1 ∧
    ∀ σ : Operator D, IsDensityOperator σ →
      relativeEntropy (lindbladSemigroup G 1 σ) ρ ≤ (1 - γ) * relativeEntropy σ ρ

def MlsiEntropyProduction (G : GKSL D) (ρ : Operator D) (γ : ℝ) : Prop :=
  0 < γ ∧ γ ≤ 1 ∧
    ∀ (h : ℝ) (σ : Operator D), 0 < h → h ≤ 1 → IsDensityOperator σ →
      (1 - γ * h) * relativeEntropy σ ρ ≤ relativeEntropy (lindbladSemigroup G h σ) ρ

noncomputable def metropolisAcceptRow {D : ℕ} (E : Fin D → ℝ) (ψ : Fin D → QState (Fin D))
    (ens : ProposalEnsemble D) (β : ℝ) (ρ : Operator D) (i : Fin D) : Operator D :=
  ∑ j, ∑ c,
    ((if isEnergyRep E i ∧ isEnergyRep E j then (1 : ℝ) else 0) *
        ens.weight c * thermalAcceptance E β i j) •
      (energyPi E ψ j * ens.gate c * energyPi E ψ i * ρ * energyPi E ψ i *
        (ens.gate c)ᴴ * energyPi E ψ j)

noncomputable def metropolisRejectRow {D : ℕ} (E :Fin D → ℝ) (ψ : Fin D → QState (Fin D))
    (C : Operator D) (β : ℝ) (n : ℕ) (s : Fin n → Bool) (ρ : Operator D) (i : Fin D) :
    Operator D :=
  ∑ l, ∑ r,
    (if isEnergyRep E i ∧ (∀ j, isEnergyRep E (l j)) ∧ (∀ j, isEnergyRep E (r j))
      then temmeG E β i n s l r else 0) •
      (temmeD E ψ C i n l * ρ * (temmeD E ψ C i n r)ᴴ)

def metropolisSpecStepCost (D : ℕ) : ℕ := D * 2 * 2

def metropolisActualStepQueries (M n nStar : ℕ) : ℕ :=
  (2 + nStar) * qpeWindowQueries M n

noncomputable def entropyComparisonConstant (γ : ℝ) : ℝ :=
  Real.exp γ

end

end Qatlib.Concepts.MixedInstrument.RewindAlgebra
