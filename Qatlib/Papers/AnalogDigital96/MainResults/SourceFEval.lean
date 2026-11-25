/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.AnalogDigital96.MainResults.DigitalAppendix
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Evaluation count in the digital search appendix

In the digital appendix of [Farhi and Gutmann][FarhiGutmann1998a], computation and erasure
account for two evaluations of the marking function per phase query. Applying that convention
to the single-target Grover word doubles its exact query count and its square-root upper bound.
-/

set_option autoImplicit false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.SearchStopping.KnownCount
open Qatlib.Concepts.AmplitudeSearch.InterruptMin
open Qatlib.Papers.AnalogDigital96.MainResults

namespace Qatlib.Papers.AnalogDigital96.MainResults

/-- The appendix charges two ordinary evaluations of the marking function to implement
each phase query: one computation and one erasure. -/
def sourceFEvalCount {I : Type*} (word : Circuit I) : ℕ :=
  2 * QueryCount word

/-- The appendix's single-target search uses exactly two function evaluations per Grover
iteration and at most `π√N/2` evaluations in the appendix's accounting convention. -/
theorem appendix_single_target_f_evals {I : Type} [Fintype I] [DecidableEq I]
    (w : I) (hN : 1 < Fintype.card I) :
    let k := groverIterations (knownCountAngle (1 / (Fintype.card I : ℝ)))
    sourceFEvalCount (GroverCircuit I k) = 2 * k ∧
      (sourceFEvalCount (GroverCircuit I k) : ℝ) ≤
        Real.pi / 2 * Real.sqrt (Fintype.card I) := by
  dsimp only
  obtain ⟨_, hcount, hbound⟩ := appendix_single_target w hN
  constructor
  · rw [sourceFEvalCount, hcount]
  · rw [sourceFEvalCount, Nat.cast_mul, Nat.cast_ofNat]
    calc
      _ ≤ 2 * (Real.pi / 4 * Real.sqrt (Fintype.card I)) :=
        mul_le_mul_of_nonneg_left hbound (by norm_num)
      _ = _ := by ring

end Qatlib.Papers.AnalogDigital96.MainResults
