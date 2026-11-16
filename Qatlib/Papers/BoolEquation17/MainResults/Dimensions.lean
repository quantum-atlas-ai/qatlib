/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.BoolEquation17.MainResults.Support

@[expose] public section


/-! # Closed dimension calculations from the legacy Macaulay record. -/
set_option autoImplicit false
namespace Qatlib.Papers.BoolEquation17.MainResults

/-- The two Macaulay dimensions and the recorded right-hand-side count follow from the index data. -/
theorem macaulay_dims {n : ℕ} (M : MacaulaySystem n) :
    M.nRows = M.r * 2 ^ (M.delta * n) ∧
      M.nCols = 2 ^ (M.Delta * n) - 1 ∧ M.rho ≤ M.r - 1 := by
  refine ⟨?_, ?_, M.hrho⟩
  · unfold MacaulaySystem.nRows
    rw [M.hdelta, pow_mul]
  · unfold MacaulaySystem.nCols
    rw [M.hDelta, pow_mul]

end Qatlib.Papers.BoolEquation17.MainResults
