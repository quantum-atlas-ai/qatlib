/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import Qatlib.Papers.DistinctLB26.MainResults.Execution.ConcreteEndpoints
public import Qatlib.Papers.DistinctLB26.MainResults.Execution.FlatSpace

@[expose] public section

/-! # Distinctness execution consumer -/

namespace QatlibTests.DistinctLB26ExecutionInterfaces

set_option autoImplicit false
set_option warningAsError true

open Qatlib.Papers.DistinctLB26.MainResults.Execution
open Qatlib.Papers.DistinctLB26.MainResults.FixedCorrect

/-- The same instruction list used by execution carries its exact query count. -/
def countedWord : List (Instr 1 2 PUnit) := [.oracle, .oracle]

example : queryCount countedWord = 2 := by
  decide

def binaryWork : Work 1 2 PUnit := (0, 0, ())

noncomputable def binaryBasis : Local 1 2 PUnit :=
  EuclideanSpace.basisFun (Work 1 2 PUnit) ℂ binaryWork

example : ‖binaryBasis‖ = 1 := by
  simp [binaryBasis]

/-- The consumer invokes the concrete zero-query success probability. -/
theorem binary_success_consumer (answer : Work 1 2 PUnit → Label 1 2) :
    averageSuccess (fun x a => x = answer a) binaryNoQuery binaryBasis = (1 / 2 : ℝ) := by
  classical
  exact binary_no_query_average binaryBasis (by simp [binaryBasis]) answer

/-- The consumer invokes the final uniform-label success-probability bound. -/
theorem success_bound_consumer
    {Y A : Type*} [Fintype Y] [Fintype A] [DecidableEq Y] [Nonempty Y]
    (ψ : Vec (Y × A))
    (hψ : Strong (flatSpace : Submodule ℂ (Vec Y)) ψ) (hnorm : ‖ψ‖ = 1)
    (answer : A → Y) (U : Vec A ≃ₗᵢ[ℂ] Vec A) :
    successProb (fun r y : Y => y = r) answer U ψ ≤ 1 / (Fintype.card Y : ℝ) :=
  uninformed_bound ψ hψ hnorm answer U

end QatlibTests.DistinctLB26ExecutionInterfaces
