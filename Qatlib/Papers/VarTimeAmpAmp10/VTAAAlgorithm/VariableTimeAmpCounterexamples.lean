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

/-!
# Counterexamples to unrestricted amplification bounds

This module constructs explicit counterexamples for overly broad cost and gain-product
formulations in the variable-time framework. The examples exhibit negative `tightAccessCost`,
arbitrarily large legal access time, and a gain-ratio product exceeding the proposed right-hand
side.

The variable-time amplification setting is described in [Ambainis2012].

## Main statements

* `clause64_tightAccessCost_negative`: stopping data with negative cost expression.
* `clause67_unbounded_legal_accessTime`: unbounded costs of legal programs.
* `clause68_gainRatioProduct_counterexample`: explicit failure of a gain-product inequality.

## References

* [Ambainis, 2012][Ambainis2012]
-/

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

/-- There exist stopping-time data and a positive success parameter for which `tightAccessCost`
is negative. -/
lemma clause64_tightAccessCost_negative :
    ∃ (m : ℕ) (p t : Fin m → ℝ) (Tmax Tav psucc : ℝ),
      stopTimeData m p t Tmax Tav ∧ 0 < psucc ∧ tightAccessCost Tmax Tav psucc < 0 := by
  refine ⟨1, fun _ => 1, fun _ => 1, 1, -1, 1 / 4, ?_, by norm_num, ?_⟩
  · refine ⟨by norm_num, by intro i; simp, by simp, by intro i; simp, by intro i; simp,
      by norm_num, by simp⟩
  · norm_num [tightAccessCost, tightLogFactor, Real.log_one, Real.one_rpow]
end
noncomputable section

/-- For every finite state space and natural bound, there is a legal two-slot program with
positive register size whose unit-price access time meets that bound. -/
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

/-- The sequence equal to `1 / 9` at index one and zero elsewhere, used in the gain-product
counterexample. -/
private noncomputable def g68rs : ℕ → ℝ := fun j => if j = 1 then 1 / 9 else 0

/-- The sequence equal to `1 / 900` at index one and zero elsewhere, used in the gain-product
counterexample. -/
private noncomputable def g68rs' : ℕ → ℝ := fun j => if j = 1 then 1 / 900 else 0

/-- The identically zero stopping-mass sequence used in the gain-product counterexample. -/
private noncomputable def g68pstop : ℕ → ℝ := fun _ => 0
noncomputable section

/-- The explicit sequences satisfy the displayed local gain conditions, but their gain-ratio
product is `10` while the proposed bound is `3`. -/
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
