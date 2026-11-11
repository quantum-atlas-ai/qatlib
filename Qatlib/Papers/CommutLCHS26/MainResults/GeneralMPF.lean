/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CommutLCHS26.MainResults.SubdivisionPolynomial
import Qatlib.Papers.HamLCUSim12.Multiproduct.MultiproductMomentHami

/-!
# Integer-node multi-product formulas

This module realizes interpolation nodes as the positive integers 1 through k together with N >
k, and transfers their cancellation moments to repeated Strang formulas. Coefficient matching
and uniform generator-mass bounds yield explicit local errors for the multi-product setting of
[AftabAnTrivisa2026].

## Main statements

* `integer_moments`: proves inverse-even-power cancellation.
* `integer_coefficients`: matches exponential coefficients through degree 2(k + 1).
* `uniform_local_error_from_moments`: bounds any positive-node Strang family with the required
  moments.

## References

* [Aftab et al., 2026][AftabAnTrivisa2026]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CommutLCHS26.MainResults.GeneralMPF

open scoped BigOperators Matrix.Norms.L2Operator
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Papers.CommutLCHS26.MainResults.MPFRemainder
open Qatlib.Papers.CommutLCHS26.MainResults.SubdivisionPolynomial
open Qatlib.Papers.HamLCUSim12.Multiproduct

variable {I : Type} [Fintype I] [DecidableEq I]

/-- The integer node j + 1 for j < k, with final node N. -/
def integerNode (k N : ℕ) (j : Fin (k + 1)) : ℕ :=
  if j.val < k then j.val + 1 else N

/-- Casting an integer interpolation node to the reals gives the corresponding real node. -/
theorem integerNode_cast (k N : ℕ) (j : Fin (k + 1)) :
    (integerNode k N j : ℝ) = mNode k (N : ℝ) j := by
  unfold integerNode mNode
  split_ifs <;> simp

/-- All integer interpolation nodes are positive when N > k. -/
theorem integerNode_pos (k N : ℕ) (hN : k < N) (j : Fin (k + 1)) :
    0 < integerNode k N j := by
  unfold integerNode
  split_ifs <;> omega

/-- The integer-node interpolation family has distinct nodes when N > k. -/
theorem integerNodes_distinct (k N : ℕ) (hN : k < N) : NodesDistinct k (N : ℝ) := by
  intro j hj he
  have h : N = j.val + 1 := by exact_mod_cast he
  omega

/-- For N > k, the interpolation weights satisfy inverse-even-power moments equal to 0^r for r <
k + 1. -/
theorem integer_moments (k N : ℕ) (hN : k < N) (r : ℕ) (hr : r < k + 1) :
    (∑ j : Fin (k + 1), mCoeff k (N : ℝ) j / (integerNode k N j : ℝ) ^ (2 * r)) = (0 : ℝ) ^ r := by
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  simp_rw [integerNode_cast]
  exact multiproduct_moment_of_squared_distinct k (N : ℝ)
    (fun j => ne_of_gt (multiproduct_node_pos k (N : ℝ) hNpos j))
    (multiproduct_squared_nodes_injective k (N : ℝ) hNpos (integerNodes_distinct k N hN))
    r (by omega)

/-- The integer-node multi-product coefficients agree with the target exponential through degree
2(k + 1). -/
theorem integer_coefficients (X Y : Matrix I I ℂ) (k N : ℕ) (hN : k < N)
    (n : ℕ) (hn : n < 2 * (k + 1) + 1) :
    coefficient (fun j => strangRepeats X Y (integerNode k N j)) (mCoeff k (N : ℝ)) n =
      ((n.factorial : ℝ)⁻¹) • (X + Y) ^ n :=
  coefficients_from_scalar_moments X Y (integerNode k N) (mCoeff k (N : ℝ)) (k + 1)
    (by omega) (integerNode_pos k N hN) (integer_moments k N hN) n hn

/-- The integer-node multi-product error is bounded by the sum of its weighted word Taylor tails
and the target exponential Taylor tail. -/
theorem integer_local_error (X Y : Matrix I I ℂ) (k N : ℕ) (hN : k < N) (t : ℝ) :
    ‖multiProduct (fun j => strangRepeats X Y (integerNode k N j)) (mCoeff k (N : ℝ)) t -
      NormedSpace.exp (t • (X + Y))‖ ≤
      (∑ j : Fin (k + 1), |mCoeff k (N : ℝ) j| *
        (Real.exp (|t| * suzukiMass (strangRepeats X Y (integerNode k N j))) *
          (|t| * suzukiMass (strangRepeats X Y (integerNode k N j))) ^ (2 * (k + 1) + 1) /
            ((2 * (k + 1) + 1).factorial : ℝ))) +
      Real.exp (|t| * ‖X + Y‖) * (|t| * ‖X + Y‖) ^ (2 * (k + 1) + 1) /
        ((2 * (k + 1) + 1).factorial : ℝ) :=
  matched_local_error _ (mCoeff k (N : ℝ)) (X + Y) t (2 * (k + 1) + 1)
    (integer_coefficients X Y k N hN)

omit [Fintype I] [DecidableEq I] in

/-- A word of q repeated Strang steps has length 3q. -/
theorem strangRepeats_length (X Y : Matrix I I ℂ) (q : ℕ) :
    (strangRepeats X Y q).length = 3 * q := by
  simp [strangRepeats, List.length_flatten, mul_comm]

/-- For positive q, the generator norm mass of q repeated Strang steps is ‖X‖ + ‖Y‖. -/
theorem strangRepeats_mass (X Y : Matrix I I ℂ) (q : ℕ) (hq : 0 < q) :
    suzukiMass (strangRepeats X Y q) = ‖X‖ + ‖Y‖ := by
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast hq
  simp only [strangRepeats, suzukiMass, List.map_flatten, List.map_replicate,
    List.sum_flatten, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    List.sum_replicate, norm_smul, Real.norm_eq_abs, add_zero, nsmul_eq_mul]
  rw [abs_of_nonneg (by positivity : 0 ≤ (1 / (2 * (q : ℝ)) : ℝ)),
    abs_of_nonneg (by positivity : 0 ≤ (1 / (q : ℝ) : ℝ))]
  field_simp
  ring

/-- Positive repetition counts with cancellation moments through order m - 1 give a local error
bounded by the absolute coefficient mass plus 1 times the exponential Taylor tail of order
2m + 1. -/
theorem uniform_local_error_from_moments {J : Type} [Fintype J]
    (X Y : Matrix I I ℂ) (q : J → ℕ) (a : J → ℝ) (m : ℕ) (hm : 0 < m)
    (hq : ∀ l, 0 < q l)
    (hmom : ∀ r : ℕ, r < m → (∑ l, a l / (q l : ℝ) ^ (2 * r)) = (0 : ℝ) ^ r) (t : ℝ) :
    ‖multiProduct (fun l => strangRepeats X Y (q l)) a t - NormedSpace.exp (t • (X + Y))‖ ≤
      ((∑ l, |a l|) + 1) *
        (Real.exp (|t| * (‖X‖ + ‖Y‖)) * (|t| * (‖X‖ + ‖Y‖)) ^ (2 * m + 1) /
          ((2 * m + 1).factorial : ℝ)) := by
  have h := matched_local_error (fun l => strangRepeats X Y (q l)) a (X + Y) t (2 * m + 1)
    (coefficients_from_scalar_moments X Y q a m hm hq hmom)
  simp_rw [strangRepeats_mass X Y _ (hq _)] at h
  have hnorm : |t| * ‖X + Y‖ ≤ |t| * (‖X‖ + ‖Y‖) :=
    mul_le_mul_of_nonneg_left (norm_add_le X Y) (abs_nonneg t)
  have ht : Real.exp (|t| * ‖X + Y‖) * (|t| * ‖X + Y‖) ^ (2 * m + 1) /
      ((2 * m + 1).factorial : ℝ) ≤
      Real.exp (|t| * (‖X‖ + ‖Y‖)) * (|t| * (‖X‖ + ‖Y‖)) ^ (2 * m + 1) /
        ((2 * m + 1).factorial : ℝ) := by
    exact div_le_div_of_nonneg_right
      (mul_le_mul (Real.exp_le_exp.mpr hnorm)
        (pow_le_pow_left₀ (mul_nonneg (abs_nonneg _) (norm_nonneg _)) hnorm _)
        (by positivity) (by positivity)) (by positivity)
  apply h.trans
  calc
    _ ≤ (∑ j : J, |a j| *
        (Real.exp (|t| * (‖X‖ + ‖Y‖)) * (|t| * (‖X‖ + ‖Y‖)) ^ (2 * m + 1) /
          ((2 * m + 1).factorial : ℝ))) +
        Real.exp (|t| * (‖X‖ + ‖Y‖)) * (|t| * (‖X‖ + ‖Y‖)) ^ (2 * m + 1) /
          ((2 * m + 1).factorial : ℝ) := _root_.add_le_add le_rfl ht
    _ = _ := by rw [← Finset.sum_mul]; ring

/-- For N > k, the integer-node multi-product error obeys the uniform exponential Taylor-tail
bound of order 2(k + 1) + 1. -/
theorem integer_uniform_local_error (X Y : Matrix I I ℂ) (k N : ℕ) (hN : k < N) (t : ℝ) :
    ‖multiProduct (fun j => strangRepeats X Y (integerNode k N j)) (mCoeff k (N : ℝ)) t -
      NormedSpace.exp (t • (X + Y))‖ ≤
      ((∑ j : Fin (k + 1), |mCoeff k (N : ℝ) j|) + 1) *
        (Real.exp (|t| * (‖X‖ + ‖Y‖)) * (|t| * (‖X‖ + ‖Y‖)) ^ (2 * (k + 1) + 1) /
          ((2 * (k + 1) + 1).factorial : ℝ)) :=
  uniform_local_error_from_moments X Y (integerNode k N) (mCoeff k (N : ℝ)) (k + 1)
    (by omega) (integerNode_pos k N hN) (integer_moments k N hN) t

end Qatlib.Papers.CommutLCHS26.MainResults.GeneralMPF
