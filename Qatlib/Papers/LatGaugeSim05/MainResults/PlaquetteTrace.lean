/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.LatGaugeSim05.MainResults.WilsonLoop

@[expose] public section

/-!
# Four-link Wilson loop trace

Equation (95) writes the trace around an oriented loop as a sum over the
intermediate matrix indices. The four-factor case describes a plaquette.
-/

set_option autoImplicit false

namespace Qatlib.Papers.LatGaugeSim05.MainResults

open scoped BigOperators

/-- The four-link trace is the cyclic contraction of the four link matrices. -/
theorem trace_four {β : Type*} [Fintype β]
    (V0 V1 V2 V3 : Matrix β β ℂ) :
    (V0 * V1 * V2 * V3).trace =
      ∑ m1, ∑ m2, ∑ m3, ∑ m4, V0 m1 m2 * V1 m2 m3 * V2 m3 m4 * V3 m4 m1 := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro m1 _
  rw [Finset.sum_comm]
  trans (∑ m3, ∑ m2, ∑ m4, V0 m1 m2 * V1 m2 m3 * V2 m3 m4 * V3 m4 m1)
  · exact Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
  · exact Finset.sum_comm

end Qatlib.Papers.LatGaugeSim05.MainResults
