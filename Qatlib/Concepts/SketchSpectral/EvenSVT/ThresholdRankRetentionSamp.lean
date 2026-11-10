/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SketchSpectral.EvenSVT.ThresholdRankRetentionStat
import Qatlib.Concepts.SketchSpectral.SketchPerturb.SketchSingularValueStabilitySamp
set_option warningAsError false

open Qatlib.Concepts.SketchSpectral.SketchPerturb
open Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.SketchSpectral.EvenSVT
open Matrix Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Classical BigOperators Matrix.Norms.L2Operator

theorem matrixSingularValues_antitone' (K C : Type) [Fintype K] [DecidableEq K]
    [Fintype C] [DecidableEq C] (A : Matrix K C ℂ) :
    Antitone (fun i : ℕ => matrixSingularValues A i) := A.toEuclideanLin.singularValues_antitone

theorem thresholdRankRetention : ThresholdRankRetention := by
  intro K C RS CT _ _ _ _ _ _ _ _ A R Cc k η₁ η₂ τ hη₁ hη₂ hkRS hkC _hσ h₁ h₂ hcut i hi
  have hpos := matrixSingularValues_nonneg Cc i
  have hstable := sketchSingularValueStability K C RS CT A R Cc η₁ η₂ hη₁ hη₂ h₁ h₂ i
    (lt_min (hi.trans_le hkRS) (hi.trans_le hkC))
  have horder := matrixSingularValues_antitone' K C A hi.le
  have hsquared := pow_le_pow_left₀ (matrixSingularValues_nonneg A k) horder 2
  have hlow := (abs_le.mp hstable).1
  have hsq : τ^2 ≤ (matrixSingularValues Cc i)^2 := by nlinarith
  by_cases hτ : 0 ≤ τ
  · exact (sq_le_sq₀ hτ hpos).mp hsq
  · exact (le_of_not_ge hτ).trans hpos

end Qatlib.Concepts.SketchSpectral.EvenSVT
