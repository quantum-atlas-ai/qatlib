/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QSearchBoyer96.MainResults.ActualSearch

/-!
# The single-target digital search appendix

The theorem `appendix_single_target` packages the success and query count of the digital Grover
circuit started in the uniform state. The circuit uses the prescribed integer iteration count
and implements a single marked basis target. This development supports the treatment in
[FarhiGutmann1998a].

## Main statements

* `appendix_single_target`: failure at most `1/N`, exact query accounting, and at most `π *
  sqrt(N)/4` queries.

## References

* [Farhi and Gutmann, 1998][FarhiGutmann1998a]
-/

set_option autoImplicit false
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.QueryWordCore.QueryMachinery
open Qatlib.Concepts.SearchStopping.KnownCount
open Qatlib.Concepts.AmplitudeSearch.InterruptMin
namespace Qatlib.Papers.AnalogDigital96.MainResults

/-- For a single marked target in dimension `N > 1`, the prescribed Grover circuit has failure
probability at most `1/N`, query count equal to its iteration count, and at most `π * sqrt
N/4` queries [Farhi and Gutmann, Appendix][FarhiGutmann1998a]. -/
theorem appendix_single_target {I : Type} [Fintype I] [DecidableEq I]
    (w : I) (hN : 1 < Fintype.card I) :
    1 - MeasureProb (Run (SetOracle {w})
      (GroverCircuit I (groverIterations (knownCountAngle (1 / (Fintype.card I : ℝ)))) )
      (Uniform I)) {w} ≤ 1 / (Fintype.card I : ℝ) ∧
    QueryCount (GroverCircuit I (groverIterations
      (knownCountAngle (1 / (Fintype.card I : ℝ))))) =
      groverIterations (knownCountAngle (1 / (Fintype.card I : ℝ))) ∧
    (QueryCount (GroverCircuit I (groverIterations
      (knownCountAngle (1 / (Fintype.card I : ℝ))))) : ℝ) ≤
      Real.pi / 4 * Real.sqrt (Fintype.card I) := by
  have hNr : (1 : ℝ) < Fintype.card I := by exact_mod_cast hN
  have hp : (0 : ℝ) < 1 / (Fintype.card I : ℝ) := by positivity
  have hp1 : (1 : ℝ) / (Fintype.card I : ℝ) < 1 := (div_lt_one (by linarith)).mpr hNr
  obtain ⟨hpos, hhalf, hsin, hsq, hcos⟩ := knownCountAngle_spec hp hp1
  have hs : 0 < Real.sin (knownCountAngle (1 / (Fintype.card I : ℝ))) := by
    rw [hsin]; positivity
  simpa using Qatlib.Papers.QSearchBoyer96.MainResults.actual_floor_success_and_cost
    (Nat.zero_lt_of_lt hN) ({w} : Finset I) _ (by simp) (by simpa using hsq)
    hs hcos hpos hhalf.le

end Qatlib.Papers.AnalogDigital96.MainResults
