/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.UniversalWalk08.MainResults.WalkModel.Basic
import Qatlib.Papers.UniversalWalk08.MainResults.CircuitDefs
import Qatlib.Papers.UniversalWalk08.MainResults.Parameters.RunParameters
import Qatlib.Papers.UniversalWalk08.MainResults.Assembly
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Conditional time and output guarantees for walk simulation

This module bundles the time, phase, and output estimates for a supplied degree-three zero-one
Hermitian walk model. The theorem `conditional_time_and_output_bounds` assumes the selected
runtime and proportional circuit amplitudes with a nonzero scale satisfying the
inverse-fourth-power bound, then combines the corresponding estimates for [Childs2009].

## Main statements

* `conditional_time_and_output_bounds`: Combine runtime proximity, phase alignment, output
  probability, and conditioned-statistics guarantees.

## References

* [Childs, 2009][Childs2009]
-/

namespace Qatlib.Papers.UniversalWalk08.MainResults.UniversalComputer

open Matrix
open Qatlib.Papers.UniversalWalk08.MainResults.WalkDefsCore
open Qatlib.Papers.UniversalWalk08.MainResults.CircuitDefs
open Qatlib.Papers.UniversalWalk08.MainResults.Parameters

set_option autoImplicit false

/-- For a supplied degree-three zero-one Hermitian adjacency matrix, the selected runtime, and
walk amplitudes proportional to a circuit column with the stated nonzero scale bound,
combine runtime proximity, phase alignment, total output weight at least `1 / m ^ 4`, and
equality of conditioned output statistics. [Childs2009] -/
theorem conditional_time_and_output_bounds
    {n m : ℕ} (C : GateCircuit n)
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℂ) (hA : IsZeroOneHermitianAdjacency A) (hdeg : MaxDegreeLe A 3)
    (start : V) (out : Fin (2 ^ n) → V)
    (x l : ℝ) (t : ℝ) (ht : t = walkTime x l) (hxl : 0 ≤ x + l)
    (scale : ℂ) (hscale0 : scale ≠ 0)
    (hscale : 1 / (m : ℝ) ^ 4 ≤ Complex.normSq scale)
    (hprop : ∀ s, walkAmplitude A t (out s) start =
      scale * circuitEval C s (zeroBasis n)) :
    IsZeroOneHermitianAdjacency A ∧ MaxDegreeLe A 3 ∧
      t ≤ (x + l) / Real.sqrt 2 ∧
      (x + l) / Real.sqrt 2 < t + Real.pi ∧
      Complex.exp (((2 * t : ℝ) : ℂ) * Complex.I) =
        Complex.exp (((-(2 * t) : ℝ) : ℂ) * Complex.I) ∧
      1 / (m : ℝ) ^ 4 ≤ ∑ s, walkProbability A t (out s) start ∧
      (∀ s, walkProbability A t (out s) start /
            (∑ r, walkProbability A t (out r) start) =
          Complex.normSq (circuitEval C s (zeroBasis n)) /
            (∑ r, Complex.normSq (circuitEval C r (zeroBasis n)))) := by
  subst ht
  have htb := Assembly.walkTime_bounds hxl
  exact ⟨hA, hdeg, htb.1, htb.2,
    Assembly.bound_state_phases_equal x l,
    Assembly.output_probability_ge_inv_pow_four C A (walkTime x l) start out
      scale hprop hscale,
    Assembly.conditioned_output_statistics C A (walkTime x l) start out
      scale hscale0 hprop⟩

end Qatlib.Papers.UniversalWalk08.MainResults.UniversalComputer
