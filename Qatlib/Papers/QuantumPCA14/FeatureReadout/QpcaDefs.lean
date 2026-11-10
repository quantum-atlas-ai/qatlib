/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CopyEvolution.SelfTomography.CopyEvolutionDefs
import Qatlib.Concepts.CopyEvolution.Discriminate.FiniteCopyHelstromDiscriminationQuan
import Qatlib.Concepts.CopyEvolution.Discriminate.TrainingSetFiniteDiscriminationQuan
import Qatlib.Concepts.CopyEvolution.CopyExponent.LowRankExponentiationRestrictedQuan
import Qatlib.Concepts.CopyEvolution.SelfTomography.GramFirstRegisterDensityQuan
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.CopyEvolution.GramReadout (gramColumn gramMatrix gramState)
open Qatlib.Concepts.FreshCopyExec.QpeConsumers
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.CopyEvolution.CopyExponent
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.CopyEvolution.SelfTomography
open Qatlib.Concepts.CopyEvolution.SelfTomography

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Qatlib.Papers.QuantumPCA14.FeatureReadout

open Matrix Qatlib
open scoped ComplexOrder BigOperators Classical Matrix.Norms.L2Operator

abbrev sharedLoadingSpec :=
  Qatlib.Concepts.CopyEvolution.SelfTomography.walkGoalEndpointSpec

abbrev sharedSpectrumSpec :=
  Qatlib.Concepts.CopyEvolution.SelfTomography.clause16EndpointSpec

noncomputable def maximalScoreIndices {m : ℕ} {S : Type*} [Fintype S] [DecidableEq S]
    [Nonempty (Fin m)] (score : S → Fin m → ℝ) (x : S) : Finset (Fin m) :=
  Finset.univ.filter (fun i =>
    score x i = Finset.max' (Finset.image (fun i => score x i) Finset.univ)
      (Finset.image_nonempty.mpr Finset.univ_nonempty))

noncomputable def maximalObservableScore {m : ℕ} {S : Type*} [Fintype S] [DecidableEq S]
    [Nonempty (Fin m)] (score : S → Fin m → ℝ) (x : S) : ℝ :=
  Finset.max' (Finset.image (fun i => score x i) Finset.univ)
    (Finset.image_nonempty.mpr Finset.univ_nonempty)

theorem maximalScoreIndices_nonempty {m : ℕ} {S : Type*} [Fintype S] [DecidableEq S]
    [Nonempty (Fin m)] (score : S → Fin m → ℝ) (x : S) :
    (maximalScoreIndices score x).Nonempty := by
  have hmem : maximalObservableScore score x ∈ Finset.image (fun i => score x i) Finset.univ :=
    Finset.max'_mem _ _
  obtain ⟨i, hi⟩ := Finset.mem_image.mp hmem
  refine ⟨i, ?_⟩
  simp only [maximalScoreIndices, Finset.mem_filter]
  exact ⟨Finset.mem_univ i, hi.2⟩

noncomputable def clusterAssignment {m : ℕ} {S : Type*} [Fintype S] [DecidableEq S]
    [Nonempty (Fin m)] (score : S → Fin m → ℝ) (x : S) : Fin m :=
  Finset.min' (maximalScoreIndices score x) (maximalScoreIndices_nonempty score x)

noncomputable def learnedHypothesis {m : ℕ} {S : Type*} [Fintype S] [DecidableEq S]
    [Nonempty (Fin m)] (score : S → Fin m → ℝ) (x : S) : Fin m :=
  clusterAssignment score x

def clause16EndpointSpec : Prop :=
  sharedLoadingSpec

def clause17EndpointSpec : Prop :=
  sharedSpectrumSpec ∧
  LowRankExponentiationRestricted ∧
  (∀ (r d : ℕ) (ψ : Fin r → QState (Fin d)) (hψ : ∀ i, Normalized (ψ i))
      (w : Fin r → ℝ) (hw : ∀ i, 0 ≤ w i) (hsumw : ∑ i, (w i) ^ 2 = 1),
    Normalized (gramState ψ w) ∧
    PartialTrace (outerProduct (gramState ψ w)) = gramMatrix ψ w ∧
    IsDensityOperator (gramMatrix ψ w))

def clause19EndpointSpec : Prop :=

  FiniteCopyHelstromDiscrimination ∧
  TrainingSetFiniteDiscrimination ∧

  (∀ (M n : ℕ), 0 < M →
    twoSpeciesQPEResources M n =
      (2 * (M - 1) * n, 2 * (M - 1) * n, 2 * (M - 1) * n, 0)) ∧
  (∀ (M n : ℕ) (γ : ℝ),
    twoSpeciesSignErrorBudget M n γ =
      128 / ((M : ℝ) * γ) + 8 * (M - 1 : ℕ) * Real.pi ^ 2 / (n : ℝ)) ∧

  (∀ (d M n : ℕ) (ρ : Operator d),
    0 < M → IsDensityOperator ρ →
    (twoSpeciesTimedPositiveMass d M n ρ ρ ρ +
      twoSpeciesTimedNegativeMass d M n ρ ρ ρ)/2 = 1/2 ∧
    ¬ (2/3 : ℝ) ≤ (twoSpeciesTimedPositiveMass d M n ρ ρ ρ +
      twoSpeciesTimedNegativeMass d M n ρ ρ ρ)/2) ∧

  (∀ (m : ℕ) (S : Type) [Fintype S] [DecidableEq S] [Nonempty (Fin m)]
      (score : S → Fin m → ℝ) (x : S),
    score x (learnedHypothesis score x) = maximalObservableScore score x) ∧

  (∀ (t ε R R' : ℝ), 0 < ε → 0 ≤ R → R ≤ R' →
    Qatlib.Concepts.CopyEvolution.SelfTomography.normDependentCopyBudget t ε R ≤
      Qatlib.Concepts.CopyEvolution.SelfTomography.normDependentCopyBudget t ε R') ∧
  (∀ (t ε R : ℝ), 0 < ε → 0 ≤ R → 1 ≤ Qatlib.Concepts.CopyEvolution.SelfTomography.normDependentCopyBudget t ε R)

end Qatlib.Papers.QuantumPCA14.FeatureReadout
