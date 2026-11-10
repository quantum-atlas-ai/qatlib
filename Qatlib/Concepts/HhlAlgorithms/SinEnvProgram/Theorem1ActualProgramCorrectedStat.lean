/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HhlAlgorithms.SinEnvProgram.SinEnvelopeProgramDefinitions
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.HhlAlgorithms.SinEnvProgram.SinEnvelopeProgramDefinitions.HHL2009

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter
open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeSpecDefs
open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeSpecDefs.SinEnvelopeSpec
open Qatlib.Concepts.HhlAlgorithms.SinEnvProgram.SinEnvelopeProgramDefinitions
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false

namespace Qatlib.Concepts.HhlAlgorithms.SinEnvProgram

open Matrix Qatlib.Concepts.HhlAlgorithms.SinEnvFilter
open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeSpecDefs
open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeSpecDefs.SinEnvelopeSpec
open Qatlib.Concepts.HhlAlgorithms.SinEnvProgram.SinEnvelopeProgramDefinitions
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Real

def Theorem1ActualProgramCorrected : Prop :=
  SinEnvelopeBasicLawsCorrected ∧
  (∀ (D M : ℕ) (hM : 2 ≤ M) (eig : Fin D → ℝ) (V B : Operator D) (j : Fin D)
      (d η : ℝ),
    V ∈ Matrix.unitaryGroup (Fin D) ℂ → B ∈ Matrix.unitaryGroup (Fin D) ℂ →
    0 < d → 0 < η → η ≤ 1 → (∀ i, 0 ≤ eig i ∧ eig i ≤ 1 / 4) →
    21 / (d * η) ≤ (M : ℝ) →
    ‖toEuclidean_fromVec (sinEnvelopeHHLRun M hM (continuousHHLOracle eig V) d B j -
        sinEnvelopeHHLIdeal M hM eig V d B j)‖ ≤ η ∧
      |sinEnvelopeActualMass M hM eig V B j d -
          sinEnvelopeIdealMass M hM eig V B j d| ≤
        (47 / (d * (M : ℝ))) * sinEnvelopeIdealMass M hM eig V B j d) ∧
  (∀ (D M : ℕ) (hM : 2 ≤ M) (eig : Fin D → ℝ) (V B : Operator D) (j : Fin D)
      (d η : ℝ),
    V ∈ Matrix.unitaryGroup (Fin D) ℂ → B ∈ Matrix.unitaryGroup (Fin D) ℂ →
    0 < d → 2 * d ≤ 1 / 4 → 0 < η → η ≤ 1 →
    (∀ i, 2 * d ≤ eig i ∧ eig i ≤ 1 / 4) → 420 / (d * η) ≤ (M : ℝ) →
    (‖toEuclidean_fromVec (sinEnvelopeConditionalOutput
          (sinEnvelopeActualWellStateCorrected M hM eig V B j d) -
        sinEnvelopeConditionalOutput
          (sinEnvelopeIdealWellState M hM eig V B j d))‖ ≤ η ∧
      |∑ p, ‖sinEnvelopeActualWellStateCorrected M hM eig V B j d p‖ ^ 2 -
          ∑ p, ‖sinEnvelopeIdealWellState M hM eig V B j d p‖ ^ 2| ≤
        (47 / (d * (M : ℝ))) *
          ∑ p, ‖sinEnvelopeIdealWellState M hM eig V B j d p‖ ^ 2 ∧
      (V * Matrix.diagonal (fun i => (sinEnvelopeFilterF d (eig i) : ℂ)) * Vᴴ) *ᵥ
          (B *ᵥ Ket j) =
        (V * Matrix.diagonal (fun i => ((d / eig i : ℝ) : ℂ)) * Vᴴ) *ᵥ
          (B *ᵥ Ket j)))

end Qatlib.Concepts.HhlAlgorithms.SinEnvProgram
