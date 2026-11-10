/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.Lemma2Stat
import Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.Lemma3Stat
import Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.AppendixA3PhaseConcentrationStat
import Qatlib.Concepts.NativeNumerics.LayeredMean.CountedHHLProgram
import Qatlib.Concepts.HhlAlgorithms.SinEnvProgram.NearGridHHLOutput
import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge
import Qatlib.Foundations.PureStateMath.MixedState
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false


open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.NativeNumerics.LayeredMean
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.HHL2009
open Qatlib.Concepts.HhlAlgorithms.SinEnvProgram

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter
open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeSpecDefs
open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeSpecDefs.SinEnvelopeSpec
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Qatlib.Concepts.HhlAlgorithms.SinEnvProgram.SinEnvelopeProgramDefinitions

open Matrix Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Real

variable {I : Type} [Fintype I] [DecidableEq I]

noncomputable def sinEnvelopeDecode (M : ℕ) (z : Fin M) : ℝ :=
  if 2 * (z.val : ℕ) ≤ M then (z.val : ℝ) / (M : ℝ) else (z.val : ℝ) / (M : ℝ) - 1

noncomputable def sinEnvelopePrepUnit (M : ℕ) (hM : 2 ≤ M) : QState (Fin M) :=
  ((Real.sqrt (2 * (1 + (sinEnvelopeState M ⟨0, by omega⟩).re)) : ℂ))⁻¹ •
    (Ket (⟨0, by omega⟩ : Fin M) + sinEnvelopeState M)

noncomputable def sinEnvelopePrep (M : ℕ) (hM : 2 ≤ M) :
    Matrix (Fin M) (Fin M) ℂ :=
  ReflectionAbout (outerProduct (sinEnvelopePrepUnit M hM))

noncomputable def sinEnvelopeFlagRotationDir (d θ : ℝ) : QState (Fin 3) :=
  ((Real.sqrt (2 * (1 + (sinEnvelopeHVector d θ 0).re)) : ℂ))⁻¹ •
    ((fun s => if s = 0 then (1 : ℂ) else 0) + sinEnvelopeHVector d θ)

noncomputable def sinEnvelopeFlagRotation (d θ : ℝ) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  ReflectionAbout (outerProduct (sinEnvelopeFlagRotationDir d θ))

noncomputable def sinEnvelopePhaseCircuit (M : ℕ) (hM : 2 ≤ M) :
    Circuit (Fin M × (Bool × I)) :=
  [Step.gate (TensorGate (sinEnvelopePrep M hM)
      (1 : Matrix (Bool × I) (Bool × I) ℂ))] ++
    phaseThresholdLoop M (M - 1) ++
    [Step.gate (TensorGate (QFTMatrix M)ᴴ (1 : Matrix (Bool × I) (Bool × I) ℂ))]

noncomputable def sinEnvelopeForwardWord (M : ℕ) (hM : 2 ≤ M) :
    List (AdjointStep (Fin M × (Bool × I))) :=
  ((sinEnvelopePhaseCircuit (I := I) M hM).map stepToAdjoint).reverse

def sinEnvelopeSectorEquiv (D M : ℕ) :
    Bool × (Fin M × (Fin 3 × Fin D)) ≃ Fin M × (Bool × (Fin 3 × Fin D)) :=
  (Equiv.prodComm Bool (Fin M × (Fin 3 × Fin D))).trans
    ((Equiv.prodAssoc (Fin M) (Fin 3 × Fin D) Bool).trans
      (Equiv.prodCongr (Equiv.refl (Fin M)) (Equiv.prodComm (Fin 3 × Fin D) Bool)))

noncomputable def sinEnvelopeLiftGate {D M : ℕ}
    (G : Matrix (Fin M × (Fin 3 × Fin D)) (Fin M × (Fin 3 × Fin D)) ℂ) :
    Matrix (Fin M × (Bool × (Fin 3 × Fin D))) (Fin M × (Bool × (Fin 3 × Fin D))) ℂ :=
  relabelGate (sinEnvelopeSectorEquiv D M) (TensorGate (1 : Matrix Bool Bool ℂ) G)

noncomputable def sinEnvelopeOracleLift {D M : ℕ} (U : Operator D) :
    Matrix (Fin M × (Bool × (Fin 3 × Fin D))) (Fin M × (Bool × (Fin 3 × Fin D))) ℂ :=
  TensorGate (1 : Matrix (Fin M) (Fin M) ℂ)
    (controlOracle (TensorGate (1 : Matrix (Fin 3) (Fin 3) ℂ) U))

noncomputable def sinEnvelopeFlagGate {D M : ℕ} (d : ℝ) :
    Matrix (Fin M × (Fin 3 × Fin D)) (Fin M × (Fin 3 × Fin D)) ℂ :=
  relabelGate (Equiv.prodAssoc (Fin M) (Fin 3) (Fin D))
    (TensorGate (BlockDiag (fun z : Fin M =>
      sinEnvelopeFlagRotation d (sinEnvelopeDecode M z))) (1 : Operator D))

noncomputable def sinEnvelopePrepMain {D M : ℕ} (B : Operator D) :
    Matrix (Fin M × (Fin 3 × Fin D)) (Fin M × (Fin 3 × Fin D)) ℂ :=
  relabelGate (Equiv.prodAssoc (Fin M) (Fin 3) (Fin D))
    (TensorGate (TensorGate (1 : Matrix (Fin M) (Fin M) ℂ)
      (1 : Matrix (Fin 3) (Fin 3) ℂ)) B)

noncomputable def sinEnvelopeHHLWord {D : ℕ} (M : ℕ) (hM : 2 ≤ M) (d : ℝ)
    (B : Operator D) :
    List (AdjointStep (Fin M × (Bool × (Fin 3 × Fin D)))) :=
  adjointCircuit (sinEnvelopeForwardWord M hM) ++
    [AdjointStep.gate (sinEnvelopeLiftGate (sinEnvelopeFlagGate d))] ++
    sinEnvelopeForwardWord M hM ++
    [AdjointStep.gate (sinEnvelopeLiftGate (sinEnvelopePrepMain B))]

noncomputable def sinEnvelopeHHLRun {D : ℕ} (M : ℕ) (hM : 2 ≤ M) (U : Operator D)
    (d : ℝ) (B : Operator D) (j : Fin D) :
    QState (Fin M × (Bool × (Fin 3 × Fin D))) :=
  evaluate (sinEnvelopeOracleLift U) (sinEnvelopeHHLWord M hM d B) *ᵥ
    TensorState (Ket (⟨0, by omega⟩ : Fin M))
      (TensorState (Ket false) (TensorState (Ket (0 : Fin 3)) (Ket j)))

noncomputable def sinEnvelopeHHLIdeal {D : ℕ} (M : ℕ) (hM : 2 ≤ M) (eig : Fin D → ℝ)
    (V : Operator D) (d : ℝ) (B : Operator D) (j : Fin D) :
    QState (Fin M × (Bool × (Fin 3 × Fin D))) :=
  TensorState (Ket (⟨0, by omega⟩ : Fin M)) (TensorState (Ket false)
    (fun p : Fin 3 × Fin D =>
      ((V * Matrix.diagonal (fun i => sinEnvelopeHVector d (eig i) p.1) * Vᴴ) *ᵥ
        (B *ᵥ Ket j)) p.2))

noncomputable def sinEnvelopeFlagMass (d θ : ℝ) : ℝ :=
  sinEnvelopeFilterF d θ ^ 2 + sinEnvelopeFilterG d θ ^ 2

noncomputable def sinEnvelopeIdealMass {D : ℕ} (M : ℕ) (hM : 2 ≤ M)
    (eig : Fin D → ℝ) (V B : Operator D) (j : Fin D) (d : ℝ) : ℝ :=
  ∑ i, ‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖ ^ 2 * sinEnvelopeFlagMass d (eig i)

noncomputable def sinEnvelopeActualMass {D : ℕ} (M : ℕ) (hM : 2 ≤ M)
    (eig : Fin D → ℝ) (V B : Operator D) (j : Fin D) (d : ℝ) : ℝ :=
  ∑ i, ‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖ ^ 2 *
    ∑ z, ‖sinEnvelopeKernel M (eig i) z‖ ^ 2 *
      sinEnvelopeFlagMass d (sinEnvelopeDecode M z)

noncomputable def sinEnvelopeActualWellState {D : ℕ} (M : ℕ) (hM : 2 ≤ M)
    (eig : Fin D → ℝ) (V B : Operator D) (j : Fin D) (d : ℝ) :
    QState (Fin M × (Fin 3 × Fin D)) :=
  ∑ i, (Vᴴ *ᵥ (B *ᵥ Ket j)) i • ∑ z, sinEnvelopeKernel M (eig i) z •
    TensorState (Ket z) (TensorState (Ket (1 : Fin 3)) (V *ᵥ Ket i))

noncomputable def sinEnvelopeActualWellStateCorrected {D : ℕ} (M : ℕ) (hM : 2 ≤ M)
    (eig : Fin D → ℝ) (V B : Operator D) (j : Fin D) (d : ℝ) :
    QState (Fin M × (Fin 3 × Fin D)) :=
  ∑ i, (Vᴴ *ᵥ (B *ᵥ Ket j)) i • ∑ z, sinEnvelopeKernel M (eig i) z •
    (sinEnvelopeFilterF d (sinEnvelopeDecode M z) : ℂ) •
      TensorState (Ket z) (TensorState (Ket (1 : Fin 3)) (V *ᵥ Ket i))

noncomputable def sinEnvelopeIdealWellState {D : ℕ} (M : ℕ) (hM : 2 ≤ M)
    (eig : Fin D → ℝ) (V B : Operator D) (j : Fin D) (d : ℝ) :
    QState (Fin M × (Fin 3 × Fin D)) :=
  ∑ i, (Vᴴ *ᵥ (B *ᵥ Ket j)) i • (sinEnvelopeFilterF d (eig i) : ℂ) •
    ∑ z, sinEnvelopeKernel M (eig i) z •
      TensorState (Ket z) (TensorState (Ket (1 : Fin 3)) (V *ᵥ Ket i))

noncomputable def sinEnvelopeConditionalOutput {I : Type} [Fintype I] [DecidableEq I]
    (v : QState I) : QState I :=
  (Real.sqrt (∑ p, ‖v p‖ ^ 2))⁻¹ • v

end Qatlib.Concepts.HhlAlgorithms.SinEnvProgram.SinEnvelopeProgramDefinitions

namespace Qatlib.Concepts.HhlAlgorithms.SinEnvProgram.SinEnvelopeProgramDefinitions.HHL2009

open Matrix Qatlib.Concepts.HhlAlgorithms.SinEnvFilter
open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeSpecDefs
open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeSpecDefs.SinEnvelopeSpec
open Qatlib.Concepts.HhlAlgorithms.SinEnvProgram.SinEnvelopeProgramDefinitions
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Real

def SinEnvelopeBasicLaws : Prop :=
  (∀ (d θ : ℝ), 0 < d → sinEnvelopeFlagMass d θ ≤ 1 / 4) ∧
  (∀ (d : ℝ), 0 < d →
    sinEnvelopeFilterF d (2 * d) = 1 / 2 ∧ sinEnvelopeFilterG d (2 * d) = 0 ∧
      sinEnvelopeFilterF d d = 0 ∧ sinEnvelopeFilterG d d = 1 / 2 ∧
      sinEnvelopeFilterF d 0 = 0 ∧ sinEnvelopeFilterG d 0 = 1 / 2 ∧
      sinEnvelopeFilterF d (-1 / 4) = 0 ∧ sinEnvelopeFilterG d (-1 / 4) = 1 / 2 ∧
      (∀ θ, 2 * d ≤ θ → sinEnvelopeFilterF d θ = d / θ ∧
        sinEnvelopeFilterG d θ = 0)) ∧
  (∀ (d θ : ℝ), 0 < d → ∑ s : Fin 3, ‖sinEnvelopeHVector d θ s‖ ^ 2 = 1) ∧
  (∀ (d θ : ℝ), 0 < d →
    sinEnvelopeFlagRotation d θ ∈ Matrix.unitaryGroup (Fin 3) ℂ ∧
      sinEnvelopeFlagRotation d θ *ᵥ Ket (0 : Fin 3) = sinEnvelopeHVector d θ) ∧
  (∀ (M : ℕ) (hM : 2 ≤ M),
    ∑ τ, ‖sinEnvelopeState M τ‖ ^ 2 = 1 ∧
      sinEnvelopePrep M hM ∈ Matrix.unitaryGroup (Fin M) ℂ ∧
      sinEnvelopePrep M hM *ᵥ (Ket (⟨0, by omega⟩ : Fin M)) = sinEnvelopeState M) ∧
  (∀ (D M : ℕ) (hM : 2 ≤ M) (d : ℝ) (B U : Operator D),
    B ∈ Matrix.unitaryGroup (Fin D) ℂ → U ∈ Matrix.unitaryGroup (Fin D) ℂ →
    WellFormedAdjointCircuit (sinEnvelopeHHLWord M hM d B) ∧
      evaluate (sinEnvelopeOracleLift (D := D) (M := M) U)
          (sinEnvelopeHHLWord M hM d B) ∈
        Matrix.unitaryGroup (Fin M × (Bool × (Fin 3 × Fin D))) ℂ ∧
      adjointQueryCount (sinEnvelopeHHLWord M hM d B) = 2 * (M - 1) ∧
      adjointGateCount (sinEnvelopeHHLWord M hM d B) = 4 * (M - 1) + 6)

def SinEnvelopeBasicLawsCorrected : Prop :=
  (∀ (d θ : ℝ), 0 < d → sinEnvelopeFlagMass d θ ≤ 1 / 4) ∧
  (∀ (d : ℝ), 0 < d →
    sinEnvelopeFilterF d (2 * d) = 1 / 2 ∧ sinEnvelopeFilterG d (2 * d) = 0 ∧
      sinEnvelopeFilterF d d = 0 ∧ sinEnvelopeFilterG d d = 1 / 2 ∧
      sinEnvelopeFilterF d 0 = 0 ∧ sinEnvelopeFilterG d 0 = 1 / 2 ∧
      sinEnvelopeFilterF d (-1 / 4) = 0 ∧ sinEnvelopeFilterG d (-1 / 4) = 1 / 2 ∧
      (∀ θ, 2 * d ≤ θ → sinEnvelopeFilterF d θ = d / θ ∧
        sinEnvelopeFilterG d θ = 0)) ∧
  (∀ (d θ : ℝ), 0 < d → ∑ s : Fin 3, ‖sinEnvelopeHVector d θ s‖ ^ 2 = 1) ∧
  (∀ (d θ : ℝ), 0 < d →
    sinEnvelopeFlagRotation d θ ∈ Matrix.unitaryGroup (Fin 3) ℂ ∧
      sinEnvelopeFlagRotation d θ *ᵥ Ket (0 : Fin 3) = sinEnvelopeHVector d θ) ∧
  (∀ (M : ℕ) (hM : 2 ≤ M),
    ∑ τ, ‖sinEnvelopeState M τ‖ ^ 2 = 1 ∧
      sinEnvelopePrep M hM ∈ Matrix.unitaryGroup (Fin M) ℂ ∧
      sinEnvelopePrep M hM *ᵥ (Ket (⟨0, by omega⟩ : Fin M)) = sinEnvelopeState M) ∧
  (∀ (D M : ℕ) (hM : 2 ≤ M) (d : ℝ), 0 < d → ∀ (B U : Operator D),
    B ∈ Matrix.unitaryGroup (Fin D) ℂ → U ∈ Matrix.unitaryGroup (Fin D) ℂ →
    WellFormedAdjointCircuit (sinEnvelopeHHLWord M hM d B) ∧
      evaluate (sinEnvelopeOracleLift (D := D) (M := M) U)
          (sinEnvelopeHHLWord M hM d B) ∈
        Matrix.unitaryGroup (Fin M × (Bool × (Fin 3 × Fin D))) ℂ ∧
      adjointQueryCount (sinEnvelopeHHLWord M hM d B) = 2 * (M - 1) ∧
      adjointGateCount (sinEnvelopeHHLWord M hM d B) = 4 * (M - 1) + 6)

def Theorem1ActualProgram : Prop :=
  SinEnvelopeBasicLaws ∧
  (∀ (D M : ℕ) (hM : 2 ≤ M) (eig : Fin D → ℝ) (V B : Operator D) (j : Fin D)
      (d η : ℝ),
    V ∈ Matrix.unitaryGroup (Fin D) ℂ → B ∈ Matrix.unitaryGroup (Fin D) ℂ →
    0 < d → 0 < η → η ≤ 1 → (∀ i, 0 ≤ eig i ∧ eig i ≤ 1 / 4) →
    21 / (d * η) ≤ (M : ℝ) →
    ‖toEuclidean_fromVec (sinEnvelopeHHLRun M hM (continuousHHLOracle eig V) d B j -
        sinEnvelopeHHLIdeal M hM eig V d B j)‖ ≤ η ∧
      |sinEnvelopeActualMass M hM eig V B j d -
          sinEnvelopeIdealMass M hM eig V B j d| ≤
        (47 / (d * (M : ℝ))) ^ 2 * sinEnvelopeIdealMass M hM eig V B j d) ∧
  (∀ (D M : ℕ) (hM : 2 ≤ M) (eig : Fin D → ℝ) (V B : Operator D) (j : Fin D)
      (d η : ℝ),
    V ∈ Matrix.unitaryGroup (Fin D) ℂ → B ∈ Matrix.unitaryGroup (Fin D) ℂ →
    0 < d → 2 * d ≤ 1 / 4 → 0 < η → η ≤ 1 →
    (∀ i, 2 * d ≤ eig i ∧ eig i ≤ 1 / 4) → 420 / (d * η) ≤ (M : ℝ) →
    (‖toEuclidean_fromVec (sinEnvelopeConditionalOutput
          (sinEnvelopeActualWellState M hM eig V B j d) -
        sinEnvelopeConditionalOutput
          (sinEnvelopeIdealWellState M hM eig V B j d))‖ ≤ η ∧
      |∑ p, ‖sinEnvelopeActualWellState M hM eig V B j d p‖ ^ 2 -
          ∑ p, ‖sinEnvelopeIdealWellState M hM eig V B j d p‖ ^ 2| ≤
        (47 / (d * (M : ℝ))) ^ 2 *
          ∑ p, ‖sinEnvelopeIdealWellState M hM eig V B j d p‖ ^ 2 ∧
      (V * Matrix.diagonal (fun i => (sinEnvelopeFilterF d (eig i) : ℂ)) * Vᴴ) *ᵥ
          (B *ᵥ Ket j) =
        (V * Matrix.diagonal (fun i => ((d / eig i : ℝ) : ℂ)) * Vᴴ) *ᵥ
          (B *ᵥ Ket j)))

end Qatlib.Concepts.HhlAlgorithms.SinEnvProgram.SinEnvelopeProgramDefinitions.HHL2009
