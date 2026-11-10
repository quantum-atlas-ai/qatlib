/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CommutLCHS26.MainResults.SubdivisionPolynomial
import Qatlib.Papers.HamLCUSim12.Multiproduct.MultiproductMomentHami
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

def integerNode (k N : ℕ) (j : Fin (k + 1)) : ℕ :=
  if j.val < k then j.val + 1 else N

theorem integerNode_cast (k N : ℕ) (j : Fin (k + 1)) :
    (integerNode k N j : ℝ) = mNode k (N : ℝ) j := by
  unfold integerNode mNode
  split_ifs <;> simp

theorem integerNode_pos (k N : ℕ) (hN : k < N) (j : Fin (k + 1)) :
    0 < integerNode k N j := by
  unfold integerNode
  split_ifs <;> omega

theorem integerNodes_distinct (k N : ℕ) (hN : k < N) : NodesDistinct k (N : ℝ) := by
  intro j hj he
  have h : N = j.val + 1 := by exact_mod_cast he
  omega

theorem integer_moments (k N : ℕ) (hN : k < N) (r : ℕ) (hr : r < k + 1) :
    (∑ j : Fin (k + 1), mCoeff k (N : ℝ) j / (integerNode k N j : ℝ) ^ (2 * r)) = (0 : ℝ) ^ r := by
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  simp_rw [integerNode_cast]
  exact multiproduct_moment_of_squared_distinct k (N : ℝ)
    (fun j => ne_of_gt (multiproduct_node_pos k (N : ℝ) hNpos j))
    (multiproduct_squared_nodes_injective k (N : ℝ) hNpos (integerNodes_distinct k N hN))
    r (by omega)

theorem integer_coefficients (X Y : Matrix I I ℂ) (k N : ℕ) (hN : k < N)
    (n : ℕ) (hn : n < 2 * (k + 1) + 1) :
    coefficient (fun j => strangRepeats X Y (integerNode k N j)) (mCoeff k (N : ℝ)) n =
      ((n.factorial : ℝ)⁻¹) • (X + Y) ^ n :=
  coefficients_from_scalar_moments X Y (integerNode k N) (mCoeff k (N : ℝ)) (k + 1)
    (by omega) (integerNode_pos k N hN) (integer_moments k N hN) n hn

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

theorem strangRepeats_length (X Y : Matrix I I ℂ) (q : ℕ) :
    (strangRepeats X Y q).length = 3 * q := by
  simp [strangRepeats, List.length_flatten, mul_comm]

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

theorem integer_uniform_local_error (X Y : Matrix I I ℂ) (k N : ℕ) (hN : k < N) (t : ℝ) :
    ‖multiProduct (fun j => strangRepeats X Y (integerNode k N j)) (mCoeff k (N : ℝ)) t -
      NormedSpace.exp (t • (X + Y))‖ ≤
      ((∑ j : Fin (k + 1), |mCoeff k (N : ℝ) j|) + 1) *
        (Real.exp (|t| * (‖X‖ + ‖Y‖)) * (|t| * (‖X‖ + ‖Y‖)) ^ (2 * (k + 1) + 1) /
          ((2 * (k + 1) + 1).factorial : ℝ)) :=
  uniform_local_error_from_moments X Y (integerNode k N) (mCoeff k (N : ℝ)) (k + 1)
    (by omega) (integerNode_pos k N hN) (integer_moments k N hN) t

end Qatlib.Papers.CommutLCHS26.MainResults.GeneralMPF
