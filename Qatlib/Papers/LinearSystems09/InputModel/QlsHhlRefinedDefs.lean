/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HhlAlgorithms.SinEnvProgram.Theorem1ActualProgramCorrectedHarr
import Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SectionIIAmplifiedRuntimeCorrectedHarr
import Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SignedQuantizationAuxiliary
import Qatlib.Concepts.HhlAlgorithms.SinEnvProgram.SinEnvelopeProgramDefinitions
import Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeAmplifiedDefinitions
import Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.HamiltonianInputModels
import Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.LinearSystemCostDefs
import Qatlib.Concepts.HhlAlgorithms.SinEnvProgram.QlsHhl
import Qatlib.Concepts.LocalMachine.LocalTransport.LeastSquaresOutputSpec
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.HhlAlgorithms.Postselection
open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter
open Qatlib.Concepts.HhlAlgorithms.SinEnvProgram

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.LinearSystems09.InputModel

open Matrix Qatlib
open scoped BigOperators

noncomputable def simonInstanceSize (n : ℕ) : ℝ := 36 * (n : ℝ) * (2 : ℝ) ^ (3 * (n : ℝ))

noncomputable def simonConditionNumber (n : ℕ) : ℝ := 4 * (n : ℝ)

noncomputable def simonReductionRuntime (α β : ℝ) (n : ℕ) : ℝ :=
  simonInstanceSize n ^ α * (2 : ℝ) ^ (β * simonConditionNumber n)

noncomputable def simonReductionExponent (α β : ℝ) : ℝ := 3 * α + 4 * β

noncomputable def simonPositiveDefiniteRuntime (α β : ℝ) (n : ℕ) : ℝ :=
  simonInstanceSize n ^ α * (2 : ℝ) ^ (β * Real.sqrt (simonConditionNumber n))

structure HhlAccessLedger where

  rounds : ℕ

  phaseSteps : ℕ

  oracleCalls : ℕ

  controlledSynthesis : ℕ

  integerBitTime : ℕ

  peakWorkspace : ℕ
  deriving DecidableEq, Repr

def hhlAccessLedger (m d : ℕ) (bitTime workspace : ℕ) : HhlAccessLedger where
  rounds := m
  phaseSteps := d
  oracleCalls := m * d
  controlledSynthesis := m * d
  integerBitTime := bitTime
  peakWorkspace := workspace

noncomputable def cumulativeQuantizationError (n : ℕ) (ε : ℝ) : ℝ := (n : ℝ) * ε

inductive PrepGate where

  | uniform

  | ramp (bits : ℕ)

  | mirror
  deriving DecidableEq, Repr

noncomputable def halfGridAngle (M : ℕ) (τ : Fin M) : ℝ :=
  Real.pi * ((2 * (τ.val : ℝ) + 1)) / (2 * (M : ℝ))

def halfGridParam (M k : ℕ) (τ : Fin M) : ℕ :=
  Nat.floor (((2 * (τ.val : ℝ) + 1) / (2 * (M : ℝ))) * 2 ^ k)

noncomputable def halfGridAngleDyadic (M k : ℕ) (τ : Fin M) : ℝ :=
  Real.pi * ((halfGridParam M k τ : ℝ) / 2 ^ k)

def halfGridMirrorIndex (M : ℕ) (τ : Fin M) : Fin M := ⟨M - 1 - τ.val, by omega⟩

noncomputable def halfGridAmplitude (M : ℕ) : ℂ := (Real.sqrt (M : ℝ) : ℂ)⁻¹

noncomputable def uniformSuperposition (M : ℕ) : Matrix (Fin M) (Fin M) ℂ :=
  Matrix.of fun _ _ => halfGridAmplitude M

def halfGridMirrorGate (M : ℕ) : Matrix (Fin M) (Fin M) ℂ :=
  Matrix.of fun p q => if q = halfGridMirrorIndex M p then 1 else 0

noncomputable def halfGridChirp (M : ℕ) : QState (Fin M) :=
  fun τ =>
    halfGridAmplitude M *
      ((Real.cos (halfGridAngle M τ) : ℝ) + (Real.sin (halfGridAngle M τ) : ℝ) * Complex.I)

noncomputable def halfGridChirpDyadic (M k : ℕ) : QState (Fin M) :=
  fun τ =>
    halfGridAmplitude M *
      ((Real.cos (halfGridAngleDyadic M k τ) : ℝ) +
        (Real.sin (halfGridAngleDyadic M k τ) : ℝ) * Complex.I)

noncomputable def halfGridSymmetrized (M : ℕ) : QState (Fin M) :=
  fun τ => (halfGridChirp M τ + halfGridChirp M (halfGridMirrorIndex M τ)) / 2

def prepGateCount (M k : ℕ) : ℕ := 3 * M

def prepWorkspace (M : ℕ) : ℕ := M

def prepParamBits (M k : ℕ) : ℕ := M * k

def dilationSize (m n : ℕ) : ℕ := m + n

def dilationSolutionBlock {O I : Type} (x : QState (O ⊕ I)) : QState I := fun i => x (Sum.inr i)

def dilationRhsBlock {O I : Type} (x : QState (O ⊕ I)) : QState O := fun o => x (Sum.inl o)

structure DilationRouteLedger where

  prepareGates : ℕ

  hamiltonianLevels : ℕ

  extractionLevels : ℕ

  totalGates : ℕ
  deriving DecidableEq, Repr

def dilationRouteLedger (m n prepareGates : ℕ) : DilationRouteLedger where
  prepareGates := prepareGates
  hamiltonianLevels := dilationSize m n
  extractionLevels := n
  totalGates := prepareGates + dilationSize m n + n

def SignedSpectrumCondition {D : ℕ} (eig : Fin D → ℝ) (d : ℝ) : Prop :=
  ∀ i, eig i = 0 ∨ (d ≤ |eig i| ∧ |eig i| ≤ 1 / 4)

noncomputable def signedFirstOrderBudget (C d M : ℝ) : ℝ := C / (d * M)

noncomputable def signedErrorBudget (C d M : ℝ) (k : ℕ) (δ : ℝ) : ℝ :=
  signedFirstOrderBudget C d M + 32 / 2 ^ k + 2 * (M - 1) * δ

end Qatlib.Papers.LinearSystems09.InputModel
