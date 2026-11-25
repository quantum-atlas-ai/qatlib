/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QWalkConnect98.MainResults.MachineResults.Lemma6Amplitude

@[expose] public section

/-!
# Total acceptance of the two-coordinate amplification model

The formula in Lemma 6 and Figure 2 includes input acceptance
probability zero. In that case every local acceptance component
vanishes. For nonzero input probability the existing calculation applies.
-/

set_option autoImplicit false

open scoped BigOperators
open Qatlib.Papers.QWalkConnect98.MainResults.MachineResults

namespace Qatlib.Papers.QWalkConnect98.MainResults

/-- Summing the modeled acceptance at each iteration gives the Lemma 6
formula, including the initial probability zero case. -/
theorem ampTotalAccept_all (p s : ℝ) (hs : s ^ 2 = p * (1 - p)) (f : ℕ) :
    (∑ j ∈ Finset.range (f + 1), ampLocalAccept p s j) =
      1 - (1 - p) * (1 - 2 * p) ^ (2 * f) := by
  by_cases hp : p = 0
  · subst p
    simp [ampLocalAccept, ampAccept, ampDot]
  · exact ampTotalAccept p s hp hs f

end Qatlib.Papers.QWalkConnect98.MainResults
