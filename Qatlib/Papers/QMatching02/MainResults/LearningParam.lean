/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QMatching02.MainResults.Comparison

@[expose] public section

/-!
# The adjacent-matrix-entry learning parameter

Equation (20) of arXiv:quant-ph/0202173v1 specifies the parameter
for an arbitrary copy number. Recover the explicit two-copy score
comparison as a specialization of that formula.
-/

set_option autoImplicit false

open scoped BigOperators
open Qatlib.Papers.QMatching02.MainResults.Comparison

namespace Qatlib.Papers.QMatching02.MainResults

/-- The adjacent-entry learning parameter of Eq. (20). -/
noncomputable def learningParameter (N : ℕ)
    (Λ : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) : ℝ :=
  (1 / (2 : ℝ) ^ (N + 1)) *
    ∑ m : Fin N, Real.sqrt ((Nat.choose N m : ℝ) * (Nat.choose N (m.val + 1) : ℝ)) *
      (Λ m.castSucc m.succ).re

/-- The two-copy instance of the general parameter is the pinned value `Rtwo`. -/
theorem learningParameter_two_eq : learningParameter 2 lamMat2 = Rtwo := by
  simp only [learningParameter, Rtwo, Fin.sum_univ_two]
  rfl

/-- At two copies the parameter in the general source expression is one eighth. -/
theorem learningParameter_two_value : learningParameter 2 lamMat2 = 1 / 8 :=
  learningParameter_two_eq.trans Rtwo_eq

end Qatlib.Papers.QMatching02.MainResults
