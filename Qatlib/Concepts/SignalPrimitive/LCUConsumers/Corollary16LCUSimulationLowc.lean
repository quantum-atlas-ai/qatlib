/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SignalPrimitive.LCUConsumers.Corollary16LCUSimulationStat
import Qatlib.Concepts.SignalPrimitive.MainResults.Theorem1TaylorTruncationLowc
import Qatlib.Concepts.SignalPrimitive.MainResults.Theorem1Simulation
import Qatlib.Concepts.BlockEncoding.StateBlockEncoding.FiberBridge
open Qatlib.Concepts.BlockEncoding.StateBlockEncoding
set_option warningAsError false

open Qatlib.Concepts.BlockEncoding.LinearCombination
open Qatlib.Concepts.SignalPrimitive.MainResults
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
namespace Qatlib.Concepts.SignalPrimitive.LCUConsumers
open Matrix Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open scoped Classical BigOperators Matrix.Norms.L2Operator

theorem corollary16LCUSimulation : Corollary16LCUSimulation := by
  intro J I _ _ _ _ U hU hHerm w hw P j₀ hP t ε hε hε1
  have hα : 0 < ∑ j, w j := hP.2.1
  have hH : (∑ j, w j • U j).IsHermitian := by
    change (∑ j, w j • U j)ᴴ = ∑ j, w j • U j
    rw [Matrix.conjTranspose_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp [Matrix.conjTranspose_smul, hHerm]
  have hnorm : ‖∑ j, w j • U j‖ ≤ ∑ j, w j := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _ => ?_))
    rw [norm_smul, Real.norm_of_nonneg (hw j)]
    exact mul_le_of_le_one_right (hw j) (unitary_norm_le_one (hU j))
  have henc :=
      IsBlockEncoding.toProjectedUnitaryEncoding (lcu_isBlockEncoding_of_isScaledPrepare U hU hw hP)
  obtain ⟨n, hcut, htail, hdegree⟩ := theorem1TaylorTruncation (t * ∑ j, w j) ε hε
  obtain ⟨wc, ws, hqc, hgc, hqs, hgs, herr⟩ := theorem1Simulation J I
    (∑ j, w j • U j) (LCUWorkspace U P) j₀ (∑ j, w j) t ε n
    hH hα hnorm hε hε1 henc hcut htail
  refine ⟨n, wc, ws, ?_, hqc, hgc, hqs, hgs, herr⟩
  simpa only [min_eq_left hε1.le] using hdegree

end Qatlib.Concepts.SignalPrimitive.LCUConsumers
