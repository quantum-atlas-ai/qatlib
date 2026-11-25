/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.Thermalize11.MainResults.SourceModel.SourceMicrocanonical

@[expose] public section

/-!
# Normalization of a rectangular dephased state

Theorem 1 uses the projection onto a nonempty energy window divided
by the number of eigenstates in that window. Given the projection's
trace, the normalization follows by linearity of trace.
-/

set_option autoImplicit false

open Qatlib.Papers.Thermalize11.MainResults.SourceModel

namespace Qatlib.Papers.Thermalize11.MainResults

/-- Dividing the trace of the window matrix by its nonzero rank
parameter gives unit trace for the dephased state. -/
theorem trace_dephasedState {ι : Type*} [Fintype ι]
    (P : Matrix ι ι ℂ) (Ω : ℕ) (hΩ : Ω ≠ 0) (htr : P.trace = (Ω : ℂ)) :
    (dephasedState P Ω).trace = 1 := by
  rw [dephasedState, Matrix.trace_smul, htr, smul_eq_mul]
  exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hΩ)

end Qatlib.Papers.Thermalize11.MainResults
