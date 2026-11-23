/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import Qatlib.Papers.DistinctLB26.MainResults.Execution.FlatSpace
public import Qatlib.Papers.DistinctLB26.MainResults.Execution.FourierRun

@[expose] public section

/-! # Distinctness execution consumer -/

namespace QatlibTests.DistinctLB26Execution

set_option autoImplicit false
set_option warningAsError true

open Qatlib.Papers.DistinctLB26.MainResults.Execution
open Qatlib.Papers.DistinctLB26.MainResults.FixedCorrect

/-- The same instruction list used by execution carries its exact query count. -/
def countedWord : List (Instr 1 2 PUnit) := [.oracle, .oracle]

example : queryCount countedWord = 2 := by
  decide

/-- The consumer invokes the final uniform-label success-probability bound. -/
theorem success_bound_consumer
    {Y A : Type*} [Fintype Y] [Fintype A] [DecidableEq Y] [Nonempty Y]
    (ψ : Vec (Y × A))
    (hψ : Strong (flatSpace : Submodule ℂ (Vec Y)) ψ) (hnorm : ‖ψ‖ = 1)
    (answer : A → Y) (U : Vec A ≃ₗᵢ[ℂ] Vec A) :
    successProb (fun r y : Y => y = r) answer U ψ ≤ 1 / (Fintype.card Y : ℝ) :=
  uninformed_bound ψ hψ hnorm answer U

end QatlibTests.DistinctLB26Execution
