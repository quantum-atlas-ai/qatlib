/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TrotterFormula.LieStrang.ProductFormulaConsumers

/-!
# Split-operator simulation bound

`split_operator_simulation` specializes the Strang product formula to Hermitian kinetic and
potential operators. It bounds the operator-norm error by nested commutator norms with cubic
time dependence and inverse-square step-count dependence, and counts the evolution factors in
the repeated splitting.

These constructions support the treatment in [KassalEtAl2008].

## Main statements

* `split_operator_simulation`: combines the explicit commutator error bound with a list length
  of `3 * r`.

## References

* [Kassal et al., 2008][KassalEtAl2008]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Matrix
open scoped Matrix.Norms.L2Operator
open Qatlib.Concepts.TrotterFormula.LieStrang
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Papers.ChemDynamics08.MainResults.Simulation

/-- For Hermitian `T` and `V` and positive `r`, the repeated Strang product has error at most
`|t|³ / r²` times the stated nested-commutator expression, and its evolution list has length
`3 * r` [KassalEtAl2008]. -/
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
