/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixWeights.WeightsCore

/-!
# Trace form of weak SDP duality

`sdp_weak_duality_trace_bound` bounds the objective of a positive semidefinite primal feasible
matrix by the cost of a nonnegative dual feasible vector. Dual feasibility is expressed by
positive semidefiniteness of the matrix slack.

For the mathematical background, see [BrandaoSvore2017].

## Main statements

* `sdp_weak_duality_trace_bound`: A positive semidefinite primal feasible operator has objective
  at most the weighted cost of any nonnegative dual vector with positive semidefinite slack.

## References

* [Brandao and Svore, 2017][BrandaoSvore2017]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.MatrixWeights.WeightsCore

namespace Qatlib.Concepts.SdpMmwSolver.SdpContract
open Matrix
open scoped Classical BigOperators MatrixOrder ComplexOrder

/-- A positive semidefinite primal feasible operator has objective at most the weighted cost of
any nonnegative dual vector with positive semidefinite slack. -/
theorem sdp_weak_duality_trace_bound (D m : ℕ) (A : Fin m → Operator D) (Cv : Operator D)
    (b : Fin m → ℝ) (y : Fin m → ℝ) (X : Operator D)
    (hy : ∀ i, 0 ≤ y i) (hdual : ((∑ i, y i • A i)-Cv).PosSemidef)
    (hX : X.PosSemidef) (hprimal : ∀ i, (Matrix.trace (A i*X)).re ≤ b i) :
    (Matrix.trace (Cv*X)).re ≤ ∑ i, y i*b i := by
  have horder : Cv ≤ ∑ i, y i • A i := Matrix.le_iff.2 hdual
  have ht := mmw_trace_mul_mono D X Cv (∑ i, y i • A i) hX horder
  rw [Matrix.trace_mul_comm X Cv] at ht
  have he : (Matrix.trace (X*(∑ i, y i • A i))).re = ∑ i, y i*(Matrix.trace (A i*X)).re := by
    rw [Matrix.mul_sum,Matrix.trace_sum,Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Matrix.mul_smul,Matrix.trace_smul,Complex.smul_re,smul_eq_mul,Matrix.trace_mul_comm]
  rw [he] at ht
  exact ht.trans (Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hprimal i) (hy i))

end Qatlib.Concepts.SdpMmwSolver.SdpContract
