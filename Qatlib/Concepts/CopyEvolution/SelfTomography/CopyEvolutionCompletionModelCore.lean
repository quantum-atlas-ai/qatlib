/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FreshCopyExec.QpeConsumers.FreshCopyComposition
import Qatlib.Concepts.CopyEvolution.Discriminate.CopyEvolutionConsumer
import Qatlib.Concepts.CopyEvolution.Discriminate.CopyExponentialPrecision
import Qatlib.Concepts.CopyEvolution.CopyExponent.CopyStateDependentPrecision
import Qatlib.Concepts.FreshCopyExec.QpeConsumers.CopyDrivenPhaseReadout
import Qatlib.Concepts.CopyEvolution.Discriminate.TwoSpeciesCopyExponential
import Qatlib.Concepts.FreshCopyExec.QpeConsumers.TwoSpeciesCopyPhaseReadout
import Qatlib.Concepts.CopyEvolution.Discriminate.TimedTwoSpeciesCopyPhaseReadout
import Qatlib.Concepts.GateVocabulary.FiniteGateDescription
import Qatlib.Concepts.WalkFind.QRAMModel.OrdinaryGateQRAMFallbackQuan
import Qatlib.Concepts.WalkFind.QRAMModel.QRAMImplementation
import Qatlib.Concepts.WalkFind.WalkSpectrum.EffectiveQRAMImplementation
import Qatlib.Concepts.CopyEvolution.SelfTomography.EpsilonCubedSelfTomographyStat
import Qatlib.Concepts.CopyEvolution.SelfTomography.SelfTomographyOnGridOutputStat
import Qatlib.Concepts.CopyEvolution.CopyExponent.LowRankExponentiationRestrictedStat
import Qatlib.Concepts.CopyEvolution.CopyExponent.SupNormTightCopyBudgetStat
import Qatlib.Concepts.CopyEvolution.CopyExponent.StateDependentCopyPrecisionStat
import Qatlib.Concepts.CopyEvolution.CopyExponent.CommutingCopyExactTightnessStat
import Qatlib.Concepts.CopyEvolution.Discriminate.FiniteCopyHelstromDiscriminationStat
import Qatlib.Concepts.CopyEvolution.Discriminate.TrainingSetFiniteDiscriminationStat
import Qatlib.Concepts.CopyEvolution.SelfTomography.GramFirstRegisterDensityStat
import Qatlib.Concepts.FreshCopyExec.QpeConsumers.CopyPureReadout
import Qatlib.Concepts.FreshCopyExec.QpeConsumers.CopySpectralReadout

/-!
# Specifications for copy-evolution completion

This module defines the aggregate propositions used to assemble copy-evolution results.
`StageACopyEvolutionPaidWalk` records QRAM legality, description costs, simulation precision,
and exact channel identities; `StageACopyEvolutionClause16` records spectral self-tomography and
discrimination guarantees.

The mathematical background is described in [LloydMohseniRebentrost2014].

## Main statements

* `copyEvolutionBasicGates`: the basic gate budget `3 * n * b`.
* `StageACopyEvolutionPaidWalk`: loading, simulation, and resource requirements.
* `StageACopyEvolutionClause16`: tomography, Gram-state, and discrimination requirements.

## References

* [Lloyd, Mohseni, and Rebentrost, 2014][LloydMohseniRebentrost2014]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.CopyEvolution.GramReadout (gramColumn gramMatrix gramState)

open Qatlib.Concepts.QueryComplexity.DegreeMethod

open Qatlib.Concepts.FreshCopyExec.QpeConsumers
open Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.WalkFind.SearchAlgorithm
open Qatlib.Concepts.BlockEncoding.LinearCombination Qatlib.Concepts.WalkFind.QRAMModel
open Qatlib.Concepts.CopyEvolution.CopyExponent
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false

namespace Qatlib.Concepts.CopyEvolution.SelfTomography

open Matrix
open Qatlib
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib
open Qatlib.Concepts.NonNormalSpec.ResolventWord
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.CopyEvolution.SelfTomography
open Qatlib
open Qatlib.Concepts.WalkFind.GroverInterp
open Qatlib
open Qatlib.Concepts.WalkFind.UniqueCollision
open Qatlib.Concepts.WalkFind.WalkSpectrum
open scoped ComplexOrder BigOperators Classical Matrix.Norms.L2Operator

/-- The basic gate budget `3 * n * b` for `n` copy-evolution steps on `b` bits. -/
def copyEvolutionBasicGates (n b : ℕ) : ℕ := 3 * n * b

/-- The aggregate specification for legal QRAM loading, finite-gate unitarity, copy-evolution
precision and resource bounds, and exact partial-swap examples. -/
def StageACopyEvolutionPaidWalk : Prop :=

  (∀ {b a aw t m ml : ℕ} (hg : sourceCodeLegal b (.qram a aw t m ml) = true) (ψ : Reg b),
    addressValue (qramAction b a aw t m ψ) a aw = addressValue ψ a aw) ∧
  (∀ {b a aw t m ml : ℕ} (hg : sourceCodeLegal b (.qram a aw t m ml) = true) (ψ : Reg b),
    t < b ∧ m + addressValue ψ a aw < b ∧ t ≠ m + addressValue ψ a aw) ∧
  (∀ {b a aw t m ml : ℕ} (hg : sourceCodeLegal b (.qram a aw t m ml) = true),
    Function.Involutive (qramAction b a aw t m)) ∧
  (∀ (g : SourceCode), codeBits g ≤ (sourceDescription g).length) ∧
  (∀ (cs : List SourceCode),
    (cs.map codeBits).sum ≤ (cs.map (fun g => (sourceDescription g).length ^ 2)).sum ∧
    cs.length ≤ (cs.map (fun g => (sourceDescription g).length ^ 2)).sum) ∧
  (EffectiveQRAMImplementationContract → QRAMImplementationContract) ∧

  (∀ (n : ℕ) (g : FiniteGateCode),
    finiteCodeLegal n g = true → finiteCodeMatrix n g ∈ Matrix.unitaryGroup (Reg n) ℂ) ∧
  (∀ (n b : ℕ), copyEvolutionBasicGates n b = 3 * n * b) ∧

  (∀ (D r : ℕ) (ρ : Operator D) (t : ℝ) (n : ℕ)
    (X : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ),
    IsDensityOperator ρ → X.PosSemidef → 0 < n →
    Matrix.traceNorm (freshCopyReferenceRun ρ (List.replicate n (t / (n : ℝ))) r X -
      TensorGate (HamiltonianEvolution ρ t) (1 : Operator r) * X *
        (TensorGate (HamiltonianEvolution ρ t) (1 : Operator r))ᴴ) ≤
      8 * t ^ 2 / (n : ℝ) * Matrix.traceNorm (X - TensorGate ρ (Matrix.traceLeft X))) ∧
  SupNormTightCopyBudget ∧
  CommutingCopyExactTightness ∧

  (∀ (D r T k : ℕ) (ρ : Operator D) (t : ℝ)
    (X : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ),
    IsDensityOperator ρ → X.PosSemidef → |t| ≤ (T : ℝ) →
    let n := copyPrecisionBudget T k
    Matrix.traceNorm (freshCopyReferenceRun ρ (List.replicate n (t / (n : ℝ))) r X -
        TensorGate (HamiltonianEvolution ρ t) (1 : Operator r) * X *
          (TensorGate (HamiltonianEvolution ρ t) (1 : Operator r))ᴴ) ≤
        ((2 : ℝ)⁻¹) ^ k * Matrix.traceNorm X ∧
      freshCopyResourceCounts D (List.replicate n (t / (n : ℝ))) = (n, n, n, 0)) ∧

  (∀ (D M n : ℕ), 2 ≤ M → 0 < n →
    copyQPEResources D M n = ((M - 1) * n, (M - 1) * n, (M - 1) * n, 0)) ∧
  (∀ (D M : ℕ), 0 < M → copyQPEFixedMacros D M = 2 * (M - 1) + 2) ∧

  (∀ (θ : ℝ) (σ : Operator 2),
    partialSwapOutput (outerProduct (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 2))) θ σ =
    !![σ 0 0 + ((Real.sin θ)^2 : ℂ)*σ 1 1,
       (((Real.cos θ)^2 : ℂ)-Complex.I*(Real.sin θ : ℂ)*(Real.cos θ : ℂ))*σ 0 1;
       (((Real.cos θ)^2 : ℂ)+Complex.I*(Real.sin θ : ℂ)*(Real.cos θ : ℂ))*σ 1 0,
       ((Real.cos θ)^2 : ℂ)*σ 1 1]) ∧
  (∀ (θ : ℝ) (n : ℕ) (σ : Operator 2),
    freshCopyRun (outerProduct (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 2))) (List.replicate n θ) σ =
    !![Matrix.trace σ - (((Real.cos θ)^2)^n : ℂ)*σ 1 1,
       ((((Real.cos θ)^2 : ℂ)-Complex.I*(Real.sin θ : ℂ)*(Real.cos θ : ℂ))^n)*σ 0 1;
       ((((Real.cos θ)^2 : ℂ)+Complex.I*(Real.sin θ : ℂ)*(Real.cos θ : ℂ))^n)*σ 1 0,
       (((Real.cos θ)^2)^n : ℂ)*σ 1 1] ∧
    freshCopyResourceCounts 2 (List.replicate n θ) = (n,n,n,0)) ∧
  (copyEvolutionPlusInput = (1/2 : ℂ) • !![1,1;1,1] ∧
    IsDensityOperator copyEvolutionPlusInput ∧
    partialSwapOutput (outerProduct (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 2))) (Real.pi/4) copyEvolutionPlusInput =
    !![3/4,(1-Complex.I)/4;(1+Complex.I)/4,1/4] ∧
    IsDensityOperator (partialSwapOutput (outerProduct (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 2))) (Real.pi/4)
      copyEvolutionPlusInput) ∧
    ¬ IsPureDensityOperator (partialSwapOutput (outerProduct (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 2))) (Real.pi/4)
      copyEvolutionPlusInput)) ∧
  (Matrix.traceLeft (outerProduct copyEvolutionBellInput) = (1/2 : ℂ) • (1 : Operator 2) ∧
    partialSwapReferenceOutput (outerProduct (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 2))) (Real.pi/2) 2
      (outerProduct copyEvolutionBellInput)
      = TensorGate (outerProduct (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 2))) ((1/2 : ℂ) • (1 : Operator 2))) ∧
  (∀ {D : ℕ} (ρ : Operator D) (hρ : IsDensityOperator ρ) (σ : Operator D),
    partialSwapOutput ρ 0 σ = σ ∧ partialSwapOutput ρ (Real.pi/2) σ = Matrix.trace σ • ρ ∧
    freshCopyRun ρ [] σ = σ ∧ freshCopyResourceCounts D [] = (0,0,0,0))

/-- The aggregate specification for self-tomography, copy-QPE positivity and trace preservation,
restricted low-rank evolution, Gram states, and finite-copy discrimination. -/
def StageACopyEvolutionClause16 : Prop :=

  EpsilonCubedSelfTomography ∧
  SelfTomographyOnGridOutput ∧

  (∀ (D M n : ℕ) (ρ : Operator D) (hρ : IsDensityOperator ρ)
    (C : Circuit (Fin M × (Bool × Fin D))) (hC : IsUnitaryCircuit C)
    (X : Matrix (Fin M × (Bool × Fin D)) (Fin M × (Bool × Fin D)) ℂ) (hX : X.PosSemidef),
    (copyQPEProgram D M n ρ C X).PosSemidef ∧
      Matrix.trace (copyQPEProgram D M n ρ C X) = Matrix.trace X) ∧
  (∀ (D M n : ℕ) (ρ : Operator D) (hρ : IsDensityOperator ρ)
    (X : Matrix (Fin M × (Bool × Fin D)) (Fin M × (Bool × Fin D)) ℂ) (hX : X.PosSemidef),
    (copyQPEQuery D M n ρ X).PosSemidef ∧
      Matrix.trace (copyQPEQuery D M n ρ X) = Matrix.trace X) ∧
  (∀ (D M : ℕ) (X : Matrix (Fin M × (Bool × Fin D)) (Fin M × (Bool × Fin D)) ℂ),
    (∑ z, copyQPELabelMass D M X z) = (Matrix.trace X).re) ∧

  LowRankExponentiationRestricted ∧
  (∀ (r d : ℕ) (ψ : Fin r → QState (Fin d)) (hψ : ∀ i, Normalized (ψ i))
    (w : Fin r → ℝ) (hw : ∀ i, 0 ≤ w i) (hsumw : ∑ i, (w i) ^ 2 = 1),
    Normalized (gramState ψ w) ∧
    PartialTrace (outerProduct (gramState ψ w)) = gramMatrix ψ w ∧
    IsDensityOperator (gramMatrix ψ w)) ∧

  TrainingSetFiniteDiscrimination ∧
  (∀ (d m : ℕ) (φ : Fin m → QState (Fin d)) (hφ : ∀ i, Normalized (φ i)) (hm : 0 < m),
    IsDensityOperator (pureStateMixture d m φ)) ∧

  FiniteCopyHelstromDiscrimination ∧
  (∀ (M n : ℕ) (γ : ℝ),
    twoSpeciesSignErrorBudget M n γ = 128 / ((M : ℝ) * γ) + 8 * (M - 1 : ℕ) * Real.pi ^ 2 / (n : ℝ))

end Qatlib.Concepts.CopyEvolution.SelfTomography
