/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ManifoldInv07.MainResults.Defs

/-!
# Exact recognition from Jones matrix elements

This module relates a distinguished matrix element to the return probability used in the
automaton interpretation of [GarneroneMarzuoliRasetti2007]. The definitions
`acceptanceProbability` and `jonesDistribution` take the Born probability of a returned basis
state and the squared norm of a supplied polynomial value, respectively.

Assuming the matrix element equals the supplied Jones value, the recognition error is zero. A
pointwise version treats a family indexed by colors, retaining the matrix-element identity as a
hypothesis.

## Main statements

* `jones_automaton_recognizes_exactly`: The supplied matrix-element identity gives zero
  recognition error.
* `colored_automaton_recognizes_exactly`: Exact recognition holds for every color under
  pointwise identities.

## References

* [Garnerone et al., 2007][GarneroneMarzuoliRasetti2007]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators ComplexOrder

namespace Qatlib.Papers.ManifoldInv07.MainResults.AutomatonRecognition

open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.ManifoldInv07.MainResults.Defs

/-- The Born return probability at the basis label `p0` after applying `U` to `Ket p0`. -/
def acceptanceProbability {I : Type*} [Fintype I] [DecidableEq I] (U : Matrix I I ℂ) (p0 : I) : ℝ :=
  BornProb (ApplyGate U (Ket p0)) p0

/-- The squared complex norm of the supplied Jones polynomial value. -/
def jonesDistribution (Jpoly : ℂ) : ℝ := ‖Jpoly‖ ^ 2

/-- If the return matrix element equals `Jpoly`, its squared norm agrees exactly with the return
probability, so the absolute recognition error is zero [GarneroneMarzuoliRasetti2007]. -/
theorem jones_automaton_recognizes_exactly {I : Type*} [Fintype I] [DecidableEq I]
    (p0 : I) (U : Matrix I I ℂ) (Jpoly : ℂ)
    (hKaul : Inner (Ket p0) (ApplyGate U (Ket p0)) = Jpoly) :
    |jonesDistribution Jpoly - acceptanceProbability U p0| = 0 := by
  have hval : (ApplyGate U (Ket p0)) p0 = Jpoly := by
    rw [← hKaul, inner_ket_left]
  unfold jonesDistribution acceptanceProbability BornProb
  rw [hval, sub_self, abs_zero]

/-- The supplied return matrix-element identity bounds the absolute Jones recognition error by
zero [GarneroneMarzuoliRasetti2007]. -/
theorem jones_automaton_threshold_zero {I : Type*} [Fintype I] [DecidableEq I]
    (p0 : I) (U : Matrix I I ℂ) (Jpoly : ℂ)
    (hKaul : Inner (Ket p0) (ApplyGate U (Ket p0)) = Jpoly) :
    |jonesDistribution Jpoly - acceptanceProbability U p0| ≤ (0 : ℝ) := by
  rw [jones_automaton_recognizes_exactly p0 U Jpoly hKaul]

/-- For a color-indexed family satisfying the return matrix-element identity for each color,
every absolute recognition error is zero [GarneroneMarzuoliRasetti2007]. -/
theorem colored_automaton_recognizes_exactly {Color I : Type*}
    [Fintype Color] [Fintype I] [DecidableEq I]
    (p0 : I) (U : Color → Matrix I I ℂ) (Jpoly : Color → ℂ)
    (hKaul : ∀ c, Inner (Ket p0) (ApplyGate (U c) (Ket p0)) = Jpoly c) :
    ∀ c, |jonesDistribution (Jpoly c) - acceptanceProbability (U c) p0| = 0 :=
  fun c => jones_automaton_recognizes_exactly p0 (U c) (Jpoly c) (hKaul c)

end Qatlib.Papers.ManifoldInv07.MainResults.AutomatonRecognition
