/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TrotterFormula.LieStrang.ProductFormulaConsumers
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Matrix
open scoped Matrix.Norms.L2Operator
open Qatlib.Concepts.TrotterFormula.LieStrang
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Papers.ChemDynamics08.MainResults.Simulation

theorem controlled_error_polynomial_cost
    (D : ℕ) (T V : Operator D) (t eps : ℝ)
    (hT : T.IsHermitian) (hV : V.IsHermitian) (heps : 0 < eps) :
    ∃ r : ℕ, 0 < r ∧
      ‖(pfStrang T V (t / r)) ^ r - HamiltonianEvolution (T + V) t‖ ≤ eps ∧
      (List.replicate r
        [HamiltonianEvolution T (t / (2 * r)), HamiltonianEvolution V (t / r),
          HamiltonianEvolution T (t / (2 * r))]).flatten.length = 3 * r := by
  let C : ℝ := |t| ^ 3 *
    (‖pfComm V (pfComm V T)‖ / 12 + ‖pfComm T (pfComm T V)‖ / 24)
  have hC0 : 0 ≤ C := by
    dsimp [C]
    positivity
  obtain ⟨r, hr⟩ := exists_nat_gt (C / eps)
  have hrposR : (0 : ℝ) < (r : ℝ) :=
    lt_of_le_of_lt (div_nonneg hC0 heps.le) hr
  have hrpos : 0 < r := Nat.cast_pos.mp hrposR
  have hr1 : (1 : ℝ) ≤ (r : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hrpos))
  have hCeps : C < (r : ℝ) * eps := (div_lt_iff₀ heps).mp hr
  have hcr : C / (r : ℝ) ^ 2 ≤ eps := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (r : ℝ) ^ 2)]
    have hmul : (r : ℝ) * eps ≤ (r : ℝ) ^ 2 * eps := by
      apply mul_le_mul_of_nonneg_right _ heps.le
      nlinarith
    linarith
  have hbud : |t| ^ 3 / (r : ℝ) ^ 2 *
        (‖pfComm V (pfComm V T)‖ / 12 + ‖pfComm T (pfComm T V)‖ / 24) ≤ eps := by
    have heq : |t| ^ 3 / (r : ℝ) ^ 2 *
          (‖pfComm V (pfComm V T)‖ / 12 + ‖pfComm T (pfComm T V)‖ / 24) =
        C / (r : ℝ) ^ 2 := by
      dsimp [C]
      ring
    rw [heq]
    exact hcr
  have hmain := product_formula_strang_paid_precision D r T V t eps hT hV hrpos heps.le hbud
  exact ⟨r, hrpos, hmain.1, hmain.2⟩

end Qatlib.Papers.ChemDynamics08.MainResults.Simulation
