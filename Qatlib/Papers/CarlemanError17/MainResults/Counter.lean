/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.CarlemanError17.MainResults.Core.SourceModel
public import Mathlib.Analysis.Calculus.Deriv.Prod

@[expose] public section


/-! # Degenerate boundary of the legacy logistic comparison formula.
At zero linear and quadratic coefficients the solution is constant, while the legacy
quotient evaluates to zero under Lean's totalized division. A correct bound needs the
continuous zero-coefficient branch and a positive-denominator time interval.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Qatlib.Papers.CarlemanError17.MainResults.Counter
open Qatlib.Papers.CarlemanError17.MainResults.Core

/-- The constant nonzero vector solves the zero quadratic vector field globally. -/
theorem zero_field_sol (t : ℝ) :
    HasDerivAt (fun _ : ℝ => fun _ : TP 1 1 => (1 : ℝ))
      (fun _ : TP 1 1 =>
        (∑ _q : TP 1 1, (0 : ℝ) * 1) + ∑ _q : TP 1 2, (0 : ℝ) * (1 * 1)) t := by
  apply hasDerivAt_pi.mpr
  intro i
  simpa using hasDerivAt_const t (1 : ℝ)

/-- The legacy Proposition 4.4 quotient fails at zero coefficients and time zero. -/
theorem zero_coeff_false :
    ¬ (vecSup (fun _ : TP 1 1 => (1 : ℝ)) ≤
      vecSup (fun _ : TP 1 1 => (1 : ℝ)) *
        Real.exp (matSup (0 : Matrix (TP 1 1) (TP 1 1) ℝ) * 0) *
        matSup (0 : Matrix (TP 1 1) (TP 1 1) ℝ) /
        (matSup (0 : Matrix (TP 1 1) (TP 1 1) ℝ) +
          matSup (0 : Matrix (TP 1 1) (TP 1 2) ℝ) *
            (1 - Real.exp (matSup (0 : Matrix (TP 1 1) (TP 1 1) ℝ) * 0)) *
              vecSup (fun _ : TP 1 1 => (1 : ℝ)))) := by
  have hn : Nonempty (TP 1 1) := ⟨fun _ => 0⟩
  norm_num [matSup, vecSup, hn]

end Qatlib.Papers.CarlemanError17.MainResults.Counter
