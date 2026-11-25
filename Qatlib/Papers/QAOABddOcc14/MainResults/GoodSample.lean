/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QAOABddOcc14.MainResults.StateNorm

@[expose] public section

/-!
# From a QAOA expectation to a satisfying string

Section II from Eq. (44) to Eq. (45) uses the normalized measurement law
of the explicit QAOA state. Its expected satisfaction count gives a
lower bound attained by some basis string.
-/

set_option autoImplicit false

open Qatlib.Papers.QAOABddOcc14.MainResults

namespace Qatlib.Papers.QAOABddOcc14.MainResults

/-- A lower bound on the explicit QAOA expectation above the random
baseline is attained by a basis string, using the proved normalization. -/
theorem exists_string_of_expectation_normalized {n : ℕ}
    (I : E3Instance n) (γ β δ : ℝ) (hδ : δ ≤ qaoaExp I γ β) :
    ∃ z : Basis n, (I.numEquations : ℝ) / 2 + δ ≤ (I.satisfiedCount z : ℝ) :=
  exists_string_of_expectation I γ β (qaoaNormalized I γ β) δ hδ

end Qatlib.Papers.QAOABddOcc14.MainResults
