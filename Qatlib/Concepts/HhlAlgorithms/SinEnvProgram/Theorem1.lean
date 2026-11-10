/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HhlAlgorithms.SinEnvProgram.Theorem1ActualProgramCorrectedHarr
import Qatlib.Concepts.HhlAlgorithms.SinEnvProgram.QlsHhl
import Qatlib.Concepts.HhlAlgorithms.SinEnvProgram.SinEnvelopeHHLConsumers
import Qatlib.Foundations.InstrumentCore.Measurement.Basic
import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge
import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Foundations.PureStateMath.MixedState
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.HhlAlgorithms.SinEnvProgram.Theorem1

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.HhlAlgorithms.SinEnvProgram.SinEnvelopeHHLConsumers
open Qatlib.Concepts.HhlAlgorithms.SinEnvProgram
open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter
open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeSpecDefs.SinEnvelopeSpec
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate
open scoped Real

theorem source_theorem1_program : Theorem1ActualProgramCorrected :=
  theorem1ActualProgram

theorem source_A4_no_postselection_error
    (D M : ℕ) (hM : 2 ≤ M) (eig : Fin D → ℝ) (V B : Operator D) (j : Fin D)
    (d η : ℝ) (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (hB : B ∈ Matrix.unitaryGroup (Fin D) ℂ) (hd : 0 < d) (hη : 0 < η) (hη1 : η ≤ 1)
    (heig : ∀ i, 0 ≤ eig i ∧ eig i ≤ 1 / 4) (hbudget : 21 / (d * η) ≤ (M : ℝ)) :
    ‖toEuclidean_fromVec (sinEnvelopeHHLRun M hM (continuousHHLOracle eig V) d B j -
        sinEnvelopeHHLIdeal M hM eig V d B j)‖ ≤ η :=
  (theorem1ActualProgram.2.1 D M hM eig V B j d η hV hB hd hη hη1 heig hbudget).1

theorem source_A5_joint_postselection :
    ∃ C : ℕ, 0 < C ∧
      ∀ (D M : ℕ) (hM : 2 ≤ M) (eig : Fin D → ℝ) (V B : Operator D) (j : Fin D)
          (d ε : ℝ),
        V ∈ Matrix.unitaryGroup (Fin D) ℂ → B ∈ Matrix.unitaryGroup (Fin D) ℂ →
        0 < d → 0 < ε → ε ≤ 1 →
        (∀ i, 0 ≤ eig i ∧ eig i ≤ 1 / 4) →
        (C : ℝ) / (d * ε) ≤ (M : ℝ) →
        min (1 / 4) (16 * d ^ 2) ≤ sinEnvelopeJointIdealMass M hM eig V B j d ∧
          0 < MeasureProb (sinEnvelopeHHLRun M hM (continuousHHLOracle eig V) d B j)
            (sinEnvelopeJointSet D M) ∧
          ‖toEuclidean_fromVec
              (sinEnvelopeConditionalOutput
                  (PostMeasure (sinEnvelopeHHLRun M hM (continuousHHLOracle eig V) d B j)
                    (sinEnvelopeJointSet D M)) -
                sinEnvelopeConditionalOutput
                  (PostMeasure (sinEnvelopeHHLIdeal M hM eig V d B j)
                    (sinEnvelopeJointSet D M)))‖ ≤ ε := by
  obtain ⟨C, hC, h⟩ := clause58
  exact ⟨C, hC, fun D M hM eig V B j d ε hV hB hd hε hε1 heig hbudget =>
    (h D M hM eig V B j d ε hV hB hd hε hε1 heig hbudget).1⟩

theorem source_A6_well_branch_error
    (D M : ℕ) (hM : 2 ≤ M) (eig : Fin D → ℝ) (V B : Operator D) (j : Fin D)
    (d η : ℝ) (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (hB : B ∈ Matrix.unitaryGroup (Fin D) ℂ) (hd : 0 < d) (h2d : 2 * d ≤ 1 / 4)
    (hη : 0 < η) (hη1 : η ≤ 1)
    (heig : ∀ i, 2 * d ≤ eig i ∧ eig i ≤ 1 / 4) (hbudget : 420 / (d * η) ≤ (M : ℝ)) :
    ‖toEuclidean_fromVec
        (sinEnvelopeConditionalOutput (sinEnvelopeActualWellStateCorrected M hM eig V B j d) -
          sinEnvelopeConditionalOutput (sinEnvelopeIdealWellState M hM eig V B j d))‖ ≤ η :=
  (theorem1ActualProgram.2.2 D M hM eig V B j d η hV hB hd h2d hη hη1 heig hbudget).1

end Qatlib.Concepts.HhlAlgorithms.SinEnvProgram.Theorem1
