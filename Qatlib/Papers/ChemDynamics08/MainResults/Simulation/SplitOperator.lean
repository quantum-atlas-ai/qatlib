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

theorem split_operator_simulation
    (D r : ℕ) (T V : Operator D) (t : ℝ)
    (hT : T.IsHermitian) (hV : V.IsHermitian) (hr : 0 < r) :
    ‖(pfStrang T V (t / r)) ^ r - HamiltonianEvolution (T + V) t‖ ≤
      |t| ^ 3 / (r : ℝ) ^ 2 *
        (‖pfComm V (pfComm V T)‖ / 12 + ‖pfComm T (pfComm T V)‖ / 24) ∧
    (List.replicate r
        [HamiltonianEvolution T (t / (2 * r)), HamiltonianEvolution V (t / r),
          HamiltonianEvolution T (t / (2 * r))]).flatten.length = 3 * r := by
  exact product_formula_strang_paid_precision D r T V t
    (|t| ^ 3 / (r : ℝ) ^ 2 *
      (‖pfComm V (pfComm V T)‖ / 12 + ‖pfComm T (pfComm T V)‖ / 24))
    hT hV hr (by positivity) le_rfl

end Qatlib.Papers.ChemDynamics08.MainResults.Simulation
