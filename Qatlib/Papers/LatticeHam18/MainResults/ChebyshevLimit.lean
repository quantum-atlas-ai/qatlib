/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.LatticeHam18.MainResults.Model.LatticeModel
public import Mathlib.Tactic.NormNum

@[expose] public section


/-! The legacy complex analytic approximation statement mistakenly requested real coefficients. -/

set_option autoImplicit false

namespace Qatlib.Papers.LatticeHam18.MainResults

/-- A real constant cannot approximate the constant imaginary unit within two thirds. -/
theorem imaginary_gap : ¬ ∃ a : ℝ, ‖Complex.I - (a : ℂ)‖ ≤ (2 : ℝ) / 3 := by
  rintro ⟨a, ha⟩
  have h := Complex.abs_im_le_norm (Complex.I - (a : ℂ))
  norm_num at h
  linarith

/-- The degree-zero instance of the old real-coefficient Chebyshev conclusion is false. -/
theorem real_coeff_fail :
    ¬ ∃ a : ℕ → ℝ, ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      ‖Complex.I - ∑ j ∈ Finset.range (0 + 1),
        (a j : ℂ) * (Polynomial.Chebyshev.T ℂ (j : ℤ)).eval (x : ℂ)‖ ≤
          2 * (1 : ℝ) / (4 - 1) * (4 : ℝ) ^ (-(0 : ℤ)) := by
  rintro ⟨a, ha⟩
  apply imaginary_gap
  refine ⟨a 0, ?_⟩
  have h := ha 0 (by constructor <;> norm_num)
  norm_num at h
  exact h

end Qatlib.Papers.LatticeHam18.MainResults
