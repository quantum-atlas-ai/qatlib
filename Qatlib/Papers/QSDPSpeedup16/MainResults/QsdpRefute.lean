/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QSDPSpeedup16.MainResults.RuntimeAlgebra
public import Qatlib.Papers.QSDPSpeedup16.MainResults.FailureExpression
public import Mathlib.Tactic.NormNum

@[expose] public section


/-! Finite record counterexamples to the exact legacy run-bound contracts.

The source record is copied with all original fields and their types. Its
isSourceRun field is an arbitrary proposition, not an execution certificate.
-/
set_option autoImplicit false
noncomputable section

open Qatlib.Papers.QSDPSpeedup16.MainResults.Corollary5Runtime
open Qatlib.Papers.QSDPSpeedup16.MainResults.FailureExpr

namespace Qatlib.Papers.QSDPSpeedup16.MainResults.RunRefute

/-- The complete original Algorithm3Run interface, including its unconstrained source-run flag. -/
structure Algorithm3Run where
  /-- Total charged time of the run. -/
  time : ℝ
  /-- Probability that the run fails. -/
  failureProb : ℝ
  /-- Hamiltonian-simulation cost per Gibbs-sampler call. -/
  Gh : ℝ
  /-- Matrix-multiplicative-weights Gibbs cost. -/
  GM : ℝ
  /-- Cost of one expectation-estimation call. -/
  TMeas : ℝ
  /-- Size parameter. -/
  R : ℝ
  /-- Additive error. -/
  δ : ℝ
  /-- Primal dimension. -/
  n : ℕ
  /-- Number of constraints. -/
  m : ℕ
  /-- Exponent in the logarithmic failure term. -/
  ξ : ℝ
  /-- The original arbitrary proposition asserting that this is a source run. -/
  isSourceRun : Prop

/-- A positive time with positive dimensions and zero charged primitive costs. -/
def runtimeWitness : Algorithm3Run where
  time := 1
  failureProb := 0
  Gh := 0
  GM := 0
  TMeas := 0
  R := 1
  δ := 1
  n := 1
  m := 1
  ξ := 1
  isSourceRun := True

/-- the stated model is false with every original assumption included. -/
theorem runtime_contract_false :
    ¬ (∀ run : Algorithm3Run, run.isSourceRun → 0 < run.R → 0 < run.δ →
      ∃ (C : ℝ) (κ : ℕ), 0 < C ∧
        run.time ≤
          C * theorem4RuntimeRHS run.R run.δ run.Gh run.GM run.TMeas *
            (Real.log (2 + run.R / run.δ + (run.n : ℝ) * (run.m : ℝ))) ^ κ) := by
  intro h
  obtain ⟨C, κ, _hC, hbound⟩ := h runtimeWitness (by trivial)
    (by norm_num [runtimeWitness]) (by norm_num [runtimeWitness])
  norm_num [runtimeWitness, theorem4RuntimeRHS] at hbound

/-- A unit failure probability and a zero dimension permitted by the original assumptions. -/
def failureWitness : Algorithm3Run where
  time := 0
  failureProb := 1
  Gh := 0
  GM := 0
  TMeas := 0
  R := 1
  δ := 1
  n := 0
  m := 1
  ξ := 1
  isSourceRun := True

/-- the stated model is false even when the failure scalar lies in the probability interval. -/
theorem failure_contract_false :
    ¬ (∀ run : Algorithm3Run, run.isSourceRun → 0 < run.R → 0 < run.δ →
      ∃ C : ℝ, 0 < C ∧
        run.failureProb ≤
          C * theorem4FailureRHS run.R run.δ run.n run.m run.ξ) := by
  intro h
  obtain ⟨C, _hC, hbound⟩ := h failureWitness (by trivial)
    (by norm_num [failureWitness]) (by norm_num [failureWitness])
  norm_num [failureWitness, theorem4FailureRHS] at hbound

end Qatlib.Papers.QSDPSpeedup16.MainResults.RunRefute
