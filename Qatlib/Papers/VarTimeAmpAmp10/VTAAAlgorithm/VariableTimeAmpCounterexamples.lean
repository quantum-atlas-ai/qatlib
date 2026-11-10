/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.VarTimeAmpAmp10.CoherentAA.VariableTimeAmplificationDefs
import Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.VariableTimeAlgorithmVari
import Qatlib.Papers.VarTimeAmpAmp10.StopModel.VariableTimeModelWellFormedVari
import Qatlib.Papers.VarTimeAmpAmp10.Estimate.StructuralEstimateCompilationVari
import Qatlib.Papers.VarTimeAmpAmp10.StopModel.CascadePrefixTransportVari
import Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.RecordDrivenVariableTimeAlgorithmVari
import Qatlib.Papers.VarTimeAmpAmp10.Estimate.EstimateSandwichVari
import Qatlib.Papers.VarTimeAmpAmp10.StopModel.AverageStopTailBoundVari
import Qatlib.Concepts.QlsReadoutSpec.PrepLowerBound.InitialStatePrepLowerBoundLows
import Qatlib.Concepts.LchsSimulation.StaticLchs.PreparedAmplitudeAmplification
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false


set_option autoImplicit false

open Matrix Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.HhlAlgorithms.Postselection.SignalProcessing
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.QlsReadoutSpec.Amplification
open Qatlib.Concepts.QlsReadoutSpec.BlockPrecond
open Qatlib.Concepts.QlsReadoutSpec.PrepLowerBound
open Qatlib.Concepts.QlsReadoutSpec.WalkQSVT
open Qatlib.Concepts.BitWordCompiler.WordComposition
open Qatlib.Concepts.QlsReadoutSpec.Amplification
open Qatlib.Concepts.QlsReadoutSpec.WalkQSVT
open Qatlib.Papers.VarTimeAmpAmp10.CoherentAA
open Qatlib.Papers.VarTimeAmpAmp10.CoherentAA
open Qatlib.Papers.VarTimeAmpAmp10.Estimate
open Qatlib.Papers.VarTimeAmpAmp10.StopModel
open Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm
open scoped Classical BigOperators ENNReal Matrix.Norms.L2Operator

namespace Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm
open Qatlib
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib
open Qatlib.Concepts.HhlAlgorithms.Postselection.SignalProcessing
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib
open Qatlib
open Qatlib
noncomputable section

lemma clause64_tightAccessCost_negative :
    ∃ (m : ℕ) (p t : Fin m → ℝ) (Tmax Tav psucc : ℝ),
      stopTimeData m p t Tmax Tav ∧ 0 < psucc ∧ tightAccessCost Tmax Tav psucc < 0 := by
  refine ⟨1, fun _ => 1, fun _ => 1, 1, -1, 1 / 4, ?_, by norm_num, ?_⟩
  · refine ⟨by norm_num, by intro i; simp, by simp, by intro i; simp, by intro i; simp,
      by norm_num, by simp⟩
  · norm_num [tightAccessCost, tightLogFactor, Real.log_one, Real.one_rpow]
end
noncomputable section

lemma clause67_unbounded_legal_accessTime :
    ∀ (H : Type) [Fintype H] [DecidableEq H] (n : ℕ),
      ∃ prog : VtAmpProgram H, 0 < prog.r ∧ legal 2 prog.word ∧
        (n : ℝ) ≤ (prog.accessTime (fun _ => 1) : ℝ) := by
  intro H _ _ n
  refine ⟨(⟨1, List.replicate n (Step.call 0 ∅ false), {0}⟩ : VtAmpProgram H),
    zero_lt_one, ?_, ?_⟩
  · intro s hs
    rw [List.mem_replicate] at hs
    obtain ⟨_, rfl⟩ := hs
    norm_num
  · have hacc : VtAmpProgram.accessTime
        (⟨1, List.replicate n (Step.call 0 ∅ false), {0}⟩ : VtAmpProgram H)
        (fun _ => 1) = n := by
      simp [VtAmpProgram.accessTime, weightedCost]
    rw [hacc]
end

private noncomputable def g68rs : ℕ → ℝ := fun j => if j = 1 then 1 / 9 else 0

private noncomputable def g68rs' : ℕ → ℝ := fun j => if j = 1 then 1 / 900 else 0

private noncomputable def g68pstop : ℕ → ℝ := fun _ => 0
noncomputable section

lemma clause68_gainRatioProduct_counterexample :
    (1 / (9 * (1:ℝ)) ≤ g68rs 1 ∧ 0 ≤ g68rs' 1) ∧
      (g68rs 1 = g68rs' 1 ∨
        ∃ k : ℕ, (1 - 1 / (3 * (1:ℝ))) * ((2 * k + 1 : ℝ) ^ 2) * g68rs' 1 ≤ g68rs 1) ∧
      gainRatioProduct g68rs g68rs' 1 2 = 10 ∧
      lemma3Rhs (remainingStopMass 1 g68pstop 1) 1 = 3 ∧
      ¬(gainRatioProduct g68rs g68rs' 1 2 ≤
        lemma3Rhs (remainingStopMass 1 g68pstop 1) 1) := by
  have hprod : gainRatioProduct g68rs g68rs' 1 2 = 10 := by
    have hIco : Finset.Ico (1:ℕ) 2 = {1} := by decide
    rw [gainRatioProduct, hIco, Finset.prod_singleton, gainRatio]
    simp [g68rs, g68rs']
    norm_num
  have hrhs : lemma3Rhs (remainingStopMass 1 g68pstop 1) 1 = 3 := by
    simp [lemma3Rhs, remainingStopMass, g68pstop]
  refine ⟨?_, ?_, hprod, hrhs, ?_⟩
  · norm_num [g68rs, g68rs']
  · refine Or.inr ⟨0, ?_⟩
    norm_num [g68rs, g68rs']
  · rw [hprod, hrhs]
    norm_num
end
end Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm
