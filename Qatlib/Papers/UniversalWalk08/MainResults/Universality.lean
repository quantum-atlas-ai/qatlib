/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.UniversalWalk08.MainResults.WalkModel.Basic
import Qatlib.Papers.UniversalWalk08.MainResults.CircuitDefs
import Qatlib.Papers.UniversalWalk08.MainResults.AmplitudeStatistics
import Qatlib.Papers.UniversalWalk08.MainResults.Assembly

/-!
# Conditional output guarantees for walk simulation

This module packages output guarantees for a supplied finite walk model in the setting of
[Childs2009]. The theorem `conditional_indexed_output_bounds` retains the zero-one Hermitian
adjacency and degree-three predicates and deduces a probability-sum lower bound and conditioned
circuit statistics from the assumed amplitude proportionality and scale bound.

## Main statements

* `conditional_indexed_output_bounds`: Combine the supplied graph predicates with the output
  probability and statistics guarantees.

## References

* [Childs, 2009][Childs2009]
-/

namespace Qatlib.Papers.UniversalWalk08.MainResults.Universality

open Matrix
open Qatlib.Papers.UniversalWalk08.MainResults.WalkDefsCore
open Qatlib.Papers.UniversalWalk08.MainResults.CircuitDefs

set_option autoImplicit false

/-- Given a degree-three zero-one Hermitian adjacency matrix and walk amplitudes proportional to
a circuit column by a nonzero scale of squared modulus at least `1 / m ^ 4`, retain the
graph predicates and obtain that lower bound on the indexed output probability sum together
with equality of conditioned statistics. [Childs2009] -/
theorem conditional_indexed_output_bounds
    {n m : ℕ} (C : GateCircuit n)
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℂ) (hA : IsZeroOneHermitianAdjacency A) (hdeg : MaxDegreeLe A 3)
    (start : V) (out : Fin (2 ^ n) → V) (t : ℝ) (scale : ℂ)
    (hscale0 : scale ≠ 0)
    (hscale : 1 / (m : ℝ) ^ 4 ≤ Complex.normSq scale)
    (hprop : ∀ s, walkAmplitude A t (out s) start =
      scale * circuitEval C s (zeroBasis n)) :
    IsZeroOneHermitianAdjacency A ∧ MaxDegreeLe A 3 ∧
      1 / (m : ℝ) ^ 4 ≤ ∑ s, walkProbability A t (out s) start ∧
      (∀ s, walkProbability A t (out s) start /
            (∑ r, walkProbability A t (out r) start) =
          Complex.normSq (circuitEval C s (zeroBasis n)) /
            (∑ r, Complex.normSq (circuitEval C r (zeroBasis n)))) :=
  ⟨hA, hdeg,
   Assembly.output_probability_ge_inv_pow_four C A t start out scale hprop hscale,
   Assembly.conditioned_output_statistics C A t start out scale hscale0 hprop⟩

end Qatlib.Papers.UniversalWalk08.MainResults.Universality
