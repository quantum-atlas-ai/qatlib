/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.QsVtMain.LengthQSVT
import Qatlib.Concepts.CoherentSim.CoherentOAA.Pseudoinverse
import Qatlib.Concepts.WalshMoment.Forrelation.ThresholdApproximation
import Qatlib.Concepts.BlockEncoding.Basic
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false


open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.QsvtCore.QsVtMain
open Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.WalshMoment.Forrelation

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

namespace Qatlib.Concepts.QsvtCore.LinearSystems

open Matrix Polynomial Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Matrix.Norms.L2Operator

def Theorem41OriginalPseudoinverse : Prop :=
  ∀ (H I O : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    [Fintype O] [DecidableEq O] (A : Matrix O I ℂ) (U : Matrix H H ℂ)
    (L : Matrix H O ℂ) (R : Matrix H I ℂ) (ε δ : ℝ),
    ProjectedUnitaryEncoding A U L R → 0 < ε → ε ≤ δ → δ ≤ 1/2 →
    (∀ i : Fin (Fintype.card I), matrixSingularValues A i ≠ 0 →
      δ ≤ matrixSingularValues A i) →
    ∃ (Pw : Polynomial ℝ) (J k : ℕ) (Φ : List ℝ),
      Φ.length = 2*J+1+2*3^k ∧
      (2*J+1 : ℝ) ≤ 32*(2/δ)*Real.log (16/(δ*ε)) ∧
      ((3 : ℝ)^k) ≤ 3*(64/(δ*ε))^(12/(δ*δ)) ∧
      (∀ x ∈ Set.Icc (-1 : ℝ) 1, |Pw.eval x| ≤ 1) ∧
      Pw.eval 0 = 0 ∧
      (∀ x ∈ Set.Icc δ 1, |Pw.eval x - (δ/2)/x| ≤ ε) ∧
      ProjectedUnitaryEncoding
        (Qatlib.Concepts.CoherentSim.CoherentOAA.oddSingularTransform A
          (fun x : ℝ => ((Pw.eval x : ℝ) : ℂ)))
        (sourceRealWord U (rangeProjector R) (rangeProjector L) Φ)
        (sourceAverageClean L) (sourceAverageClean R) ∧
      cppCounts (cppCompile (sourceRealFamily Φ)) =
        (2*J+1+2*3^k, 2*J+2*3^k, 2*J+2+2*3^k, 2*J+1+2*3^k) ∧
      let C : Matrix I O ℂ :=
        (Qatlib.Concepts.CoherentSim.CoherentOAA.oddSingularTransform A
          (fun x : ℝ => ((Pw.eval x : ℝ) : ℂ)))ᴴ
      let sectorR : Matrix I I ℂ :=
        1 - (rightThresholdProjection A 0 - rightThresholdProjection A δ)
      let sectorL : Matrix O O ℂ :=
        1 - (leftThresholdProjection A 0 - leftThresholdProjection A δ)
      ‖sectorR * C * sectorL - (δ/2 : ℂ) • (matrixPseudoinverse A * sectorL)‖ ≤ ε

end Qatlib.Concepts.QsvtCore.LinearSystems
