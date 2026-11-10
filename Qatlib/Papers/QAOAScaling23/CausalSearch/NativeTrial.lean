/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QAOAScaling23.CausalSearch.NativeCoin
import Qatlib.Foundations.ProbabilityCore.FiniteBranch.ClockedBind
import Qatlib.Concepts.LchsSimulation.StaticLchs.BitSampledPreparedSearch
set_option warningAsError false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QAOAScaling23.CausalSearch
open scoped Classical
open Qatlib.Foundations.ProbabilityCore.FiniteBranch.ClockedCode
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge
variable {I : Type} [Fintype I] [DecidableEq I]

def trialWordFee (U : Matrix I I ℂ) (seed : I) (j : ℕ) : ℕ :=
  QueryCount (preparedAACircuit U seed j) + (2*QueryCount (preparedAACircuit U seed j)+1) +
    GateCount (preparedAACircuit U seed j)

def trialCode (U : Matrix I I ℂ) (hU : U∈Matrix.unitaryGroup I ℂ) (seed : I) (S : Finset I)
    {m : ℕ} (j : Fin m) : Code I ((I×ℕ)×ℕ) :=
  .pay (trialWordFee U seed j.val)
    (drawF (bornDistribution (Run (preparedMark S) (preparedAACircuit U seed j.val) (Ket seed))
      ((prepared_aa_actual_circuit U seed S j.val hU).1.normalized_run
        ((prepared_aa_reflection_and_access U seed S hU).1) (normalized_ket seed)))
      (fun y => .ret ((y,GateCount (preparedAACircuit U seed j.val)),QueryCount (preparedAACircuit U seed j.val))))

theorem trialCode_actual_law (cost : I → ℝ) (current : I)
    (U : Matrix I I ℂ) (hU : U∈Matrix.unitaryGroup I ℂ) (seed : I) (S : Finset I)
    {m : ℕ} (j : Fin m) :
    valueLaw cost current (trialCode U hU seed S j)=preparedAATrial U hU seed S j := by
  rw [trialCode,valueLaw,valueLaw_drawF]
  rfl

theorem trialCode_noSave (U : Matrix I I ℂ) (hU : U∈Matrix.unitaryGroup I ℂ)
    (seed : I) (S : Finset I) {m : ℕ} (j : Fin m) : NoSave (trialCode U hU seed S j) := by
  simp [trialCode,NoSave,drawF]

theorem trialCode_returns (cost : I → ℝ) (current : I)
    (U : Matrix I I ℂ) (hU : U∈Matrix.unitaryGroup I ℂ) (seed : I) (S : Finset I)
    {m : ℕ} (j : Fin m) :
    Returns cost current (trialCode U hU seed S j)
      (fun out fee => fee=trialWordFee U seed j.val ∧
        out.1.2=GateCount (preparedAACircuit U seed j.val) ∧
        out.2=QueryCount (preparedAACircuit U seed j.val)) := by
  unfold trialCode
  rw [Returns,returns_drawF]
  intro y
  simp [Returns]
end Qatlib.Papers.QAOAScaling23.CausalSearch
