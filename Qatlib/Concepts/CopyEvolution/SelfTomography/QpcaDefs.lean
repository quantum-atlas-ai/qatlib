/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CopyEvolution.SelfTomography.CopyEvolutionCompletionModelCore

/-!
# Stage-B QPCA specifications

This module defines the three aggregate stage-B specifications for copy-based QPCA.
`StageBCopyQpcaClause16` records loading and evolution resources; `StageBCopyQpcaClause17`
records self-tomography and Gram-state properties; `StageBCopyQpcaClause19` records training-set
discrimination and two-species readout costs.

The mathematical background is described in [LloydMohseniRebentrost2014].

## Main statements

* `StageBCopyQpcaClause16`: loading and evolution requirements.
* `StageBCopyQpcaClause17`: tomography and Gram-state requirements.
* `StageBCopyQpcaClause19`: discrimination and two-species resource requirements.

## References

* [Lloyd, Mohseni, and Rebentrost, 2014][LloydMohseniRebentrost2014]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.CopyEvolution.GramReadout (gramColumn gramMatrix gramState)

open Qatlib.Concepts.QueryComplexity.DegreeMethod

open Qatlib.Concepts.FreshCopyExec.QpeConsumers
open Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
open Qatlib.Concepts.WalkFind.SearchAlgorithm
open Qatlib.Concepts.CopyEvolution.CopyExponent
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
set_option linter.unusedVariables false

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
open Qatlib.Concepts.CopyEvolution.SelfTomography
open scoped ComplexOrder BigOperators Classical Matrix.Norms.L2Operator

/-- The stage-B specification for legal QRAM loading, finite-gate unitarity, copy-evolution
precision and tightness, and exact QPE resource counts. -/
def StageBCopyQpcaClause16 : Prop :=

  (∀ {b a aw t m ml : ℕ} (hg : sourceCodeLegal b (.qram a aw t m ml) = true) (ψ : Reg b),
    addressValue (qramAction b a aw t m ψ) a aw = addressValue ψ a aw) ∧
  (∀ {b a aw t m ml : ℕ} (hg : sourceCodeLegal b (.qram a aw t m ml) = true) (ψ : Reg b),
    t < b ∧ m + addressValue ψ a aw < b ∧ t ≠ m + addressValue ψ a aw) ∧
  (∀ {b a aw t m ml : ℕ} (hg : sourceCodeLegal b (.qram a aw t m ml) = true),
    Function.Involutive (qramAction b a aw t m)) ∧
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
  (∀ (D M : ℕ), 0 < M → copyQPEFixedMacros D M = 2 * (M - 1) + 2)

/-- The stage-B specification for self-tomography, QPE positivity and trace preservation,
restricted low-rank exponentiation, and the Gram-state partial-trace identity. -/
def StageBCopyQpcaClause17 : Prop :=

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
    IsDensityOperator (gramMatrix ψ w))

/-- The stage-B specification for training-set and finite-copy Helstrom discrimination, the
two-species sign-error budget, and QPE resource accounting. -/
def StageBCopyQpcaClause19 : Prop :=

  TrainingSetFiniteDiscrimination ∧
  (∀ (d m : ℕ) (φ : Fin m → QState (Fin d)) (hφ : ∀ i, Normalized (φ i)) (hm : 0 < m),
    IsDensityOperator (pureStateMixture d m φ)) ∧

  FiniteCopyHelstromDiscrimination ∧
  (∀ (M n : ℕ) (γ : ℝ),
    twoSpeciesSignErrorBudget M n γ = 128 / ((M : ℝ) * γ) + 8 * (M - 1 : ℕ) * Real.pi ^ 2 / (n : ℝ)) ∧

  (∀ (D M n : ℕ), 0 < M →
    twoSpeciesQPEResources M n =
      copyQPEProgramResources (2 * n) (countedPhaseCircuit (I := Fin D) M))

end Qatlib.Concepts.CopyEvolution.SelfTomography
