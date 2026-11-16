/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.ZeroSumGibbs23.MainResults.Model.SourceModel
public import Mathlib.Algebra.Polynomial.Eval.Defs

@[expose] public section


/-!
# WeightCore deterministic core

This module preserves closed algebraic and finite-dimensional source results
from arXiv:2301.03763v1. It does not assert a circuit implementation, concentration
bound, or end-to-end algorithmic complexity.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset Matrix
namespace Qatlib.Papers.ZeroSumGibbs23.MainResults.WeightCore
open Qatlib.Papers.ZeroSumGibbs23.MainResults.Model
variable {m n N : ℕ}

/-- `u_j = v_j/(2B)` of Corollary 5 (p.23). -/
def cor5u {n : ℕ} (B : ℝ) (v : Fin n → ℝ) (j : Fin n) : ℝ := v j / (2 * B)

/-- `w_j = P(u_j)² q_j` of Corollary 5 (p.23). -/
def cor5w {n : ℕ} (P : Polynomial ℝ) (q v : Fin n → ℝ) (B : ℝ) (j : Fin n) : ℝ :=
  (P.eval (cor5u B v j)) ^ 2 * q j

/-- `z_j = exp(2B u_j) q_j = exp(v_j) q_j` of Corollary 5 (p.23). -/
def cor5z {n : ℕ} (B : ℝ) (q v : Fin n → ℝ) (j : Fin n) : ℝ :=
  Real.exp (2 * B * cor5u B v j) * q j

/-- If the approximation is exact (`36 w_j = z_j`), the normalised weight
vectors are identical. This is the equality that the `3ξ` pointwise error of the
proof of Corollary 5 perturbs. -/
theorem exact_weights {n : ℕ} (z w : Fin n → ℝ)
    (h : ∀ j, 36 * w j = z j) (hw : 0 < l1Norm w) :
    (fun j => w j / l1Norm w) = fun j => z j / l1Norm z := by
  have hz36 : l1Norm z = 36 * l1Norm w := by
    unfold l1Norm
    rw [show (∑ j, |z j|) = ∑ j, |36 * w j| from
      Finset.sum_congr rfl fun j _ => by rw [h j]]
    rw [show (∑ j, |36 * w j|) = ∑ j, 36 * |w j| from
      Finset.sum_congr rfl fun j _ => by
        rw [abs_mul]
        norm_num]
    rw [← Finset.mul_sum]
  funext j
  rw [← h j, hz36]
  have h36 : (36 : ℝ) ≠ 0 := by norm_num
  field_simp [h36, ne_of_gt hw]

end Qatlib.Papers.ZeroSumGibbs23.MainResults.WeightCore
