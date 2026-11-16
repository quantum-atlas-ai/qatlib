/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.CarlemanError17.MainResults.Counter

@[expose] public section


/-!
# Complete-contract counterexample to the legacy Proposition 4.4

The tensor-coordinate evaluation below is exactly the old embedding definition.
The input solution satisfies the differential equation at every real time. The
failure occurs at time zero, where the old quotient uses totalized zero division.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Qatlib.Papers.CarlemanError17.MainResults.Counter
open Qatlib.Papers.CarlemanError17.MainResults.Core

/-- Evaluate a first tensor-power vector at its constant one-coordinate index. -/
def vecVal {n : ℕ} (v : TP n 1 → ℝ) (a : Fin n) : ℝ := v (fun _ => a)

/-- The complete legacy Proposition 4.4 contract fails for the nonzero constant solution of the zero vector field. -/
theorem prop_four_four_false :
    ¬ (∀ {n : ℕ} (_hn : 0 < n)
      (F1 : Matrix (TP n 1) (TP n 1) ℝ) (F2 : Matrix (TP n 1) (TP n 2) ℝ)
      (x : ℝ → TP n 1 → ℝ) (x0 : TP n 1 → ℝ)
      (_hx0 : x 0 = x0)
      (_hx : ∀ t : ℝ,
        HasDerivAt x (fun w : TP n 1 =>
          (∑ q : TP n 1, F1 w q * x t q)
          + ∑ q : TP n 2,
              F2 w q * (vecVal (x t) (q 0) * vecVal (x t) (q 1))) t)
      (t : ℝ) (_ht : 0 ≤ t),
      vecSup (x t)
        ≤ vecSup x0 * Real.exp (matSup F1 * t) * matSup F1
            / (matSup F1 + matSup F2 * (1 - Real.exp (matSup F1 * t)) * vecSup x0)) := by
  intro h
  apply zero_coeff_false
  exact h (n := 1) (by norm_num)
    (0 : Matrix (TP 1 1) (TP 1 1) ℝ)
    (0 : Matrix (TP 1 1) (TP 1 2) ℝ)
    (fun _ : ℝ => fun _ : TP 1 1 => (1 : ℝ))
    (fun _ : TP 1 1 => (1 : ℝ)) rfl
    (fun t => by simpa [vecVal] using zero_field_sol t)
    0 (by norm_num)

end Qatlib.Papers.CarlemanError17.MainResults.Counter
