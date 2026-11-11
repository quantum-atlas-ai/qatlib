/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QAOAScaling23.CausalSearch.NativeCoin
import Qatlib.Foundations.ProbabilityCore.FiniteBranch.ClockedBind
import Qatlib.Concepts.LchsSimulation.StaticLchs.BitSampledPreparedSearch

/-!
# Clocked prepared amplification trials

`trialCode` charges for a prepared amplitude-amplification circuit and samples its actual Born
distribution. The returned gate and query counts are exact, and the value law agrees with
`preparedAATrial`.

This development accompanies the study of QAOA-assisted minimum finding in [ShaydulinEtAl2024].

## Main statements

* `trialCode_actual_law`: The value law of the clocked prepared trial equals `preparedAATrial`.
* `trialCode_returns`: Every prepared trial returns its exact circuit gate and query counts and
  pays exactly `trialWordFee`.

## References

* [Shaydulin et al., 2024][ShaydulinEtAl2024]
-/

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

/-- The query count plus preparation-call count `2 * QueryCount + 1` plus gate count of the
prepared amplification circuit. -/
def trialWordFee (U : Matrix I I ℂ) (seed : I) (j : ℕ) : ℕ :=
  QueryCount (preparedAACircuit U seed j) + (2*QueryCount (preparedAACircuit U seed j)+1) +
    GateCount (preparedAACircuit U seed j)

/-- Pays the prepared circuit word fee and samples its Born output, returning the measured
candidate together with gate and query counts. -/
def trialCode (U : Matrix I I ℂ) (hU : U∈Matrix.unitaryGroup I ℂ) (seed : I) (S : Finset I)
    {m : ℕ} (j : Fin m) : Code I ((I×ℕ)×ℕ) :=
  .pay (trialWordFee U seed j.val)
    (drawF (bornDistribution (Run (preparedMark S) (preparedAACircuit U seed j.val) (Ket seed))
      ((prepared_aa_actual_circuit U seed S j.val hU).1.normalized_run
        ((prepared_aa_reflection_and_access U seed S hU).1) (normalized_ket seed)))
      (fun y => .ret ((y,GateCount (preparedAACircuit U seed j.val)),QueryCount (preparedAACircuit U seed j.val))))

/-- The value law of the clocked prepared trial equals `preparedAATrial`. -/
theorem trialCode_actual_law (cost : I → ℝ) (current : I)
    (U : Matrix I I ℂ) (hU : U∈Matrix.unitaryGroup I ℂ) (seed : I) (S : Finset I)
    {m : ℕ} (j : Fin m) :
    valueLaw cost current (trialCode U hU seed S j)=preparedAATrial U hU seed S j := by
  rw [trialCode,valueLaw,valueLaw_drawF]
  rfl

/-- A clocked prepared amplification trial contains no save instructions. -/
theorem trialCode_noSave (U : Matrix I I ℂ) (hU : U∈Matrix.unitaryGroup I ℂ)
    (seed : I) (S : Finset I) {m : ℕ} (j : Fin m) : NoSave (trialCode U hU seed S j) := by
  simp [trialCode,NoSave,drawF]

/-- Every prepared trial returns its exact circuit gate and query counts and pays exactly
`trialWordFee`. -/
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
