/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.EnergySpec09.MainResults.WaterPESNumerics

/-!
# Truncation to a few configuration state functions

This module gives finite-sum overlap identities and register-size arithmetic for the
few-configuration-state-function discussion of [WangEtAl2008]. The theorem
`inner_finset_smul_sum` expands the overlap of a truncated state, and
`truncated_csf_success_prob_eq` expresses its squared overlap through the retained coefficients.

The threshold theorem `few_csf_success_prob_gt_nine_tenths` takes the corresponding lower bound
on the overlap as a hypothesis. The qubit results count basis labels using the base-two ceiling
logarithm.

## Main statements

* `truncated_csf_success_prob_eq`: the squared overlap equals the squared norm of the retained
  overlap sum.
* `few_csf_success_prob_gt_nine_tenths`: a supplied overlap bound implies a squared overlap
  above `9 / 10`.
* `few_csf_qubit_bound`: retaining a finite subset cannot increase this register-size bound.
* `few_csf_qubit_counts` and `ci_register_qubits`: 152, 6, 8, and 13872 labels require 8, 3, 3,
  and 14 qubits, respectively.

## References

* [Wang et al., 2008][WangEtAl2008]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath

open scoped BigOperators Classical

namespace Qatlib.Papers.EnergySpec09.MainResults

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The overlap of a finite truncated expansion is the coefficient-weighted sum of the retained
overlaps. This finite-sum identity supports the few-configuration-state-function analysis in
[WangEtAl2008]. -/
theorem inner_finset_smul_sum {Idx : Type*} [Fintype Idx]
    (target : QState I) (c : Idx → ℂ) (Φ : Idx → QState I) (K : Finset Idx) :
    Inner target (∑ i ∈ K, c i • Φ i) = ∑ i ∈ K, c i * Inner target (Φ i) := by
  rw [inner_apply]
  have h1 : ∀ j, (∑ i ∈ K, c i • Φ i) j = ∑ i ∈ K, c i * Φ i j := by
    intro j
    rw [Finset.sum_apply]
    exact Finset.sum_congr rfl fun i _ => by rw [Pi.smul_apply, smul_eq_mul]
  simp_rw [h1]
  have hmul : ∀ j, (starRingEnd ℂ) (target j) * (∑ i ∈ K, c i * Φ i j)
      = ∑ i ∈ K, (starRingEnd ℂ) (target j) * (c i * Φ i j) := by
    intro j
    rw [Finset.mul_sum]
  simp_rw [hmul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- The squared overlap of the retained configuration-state-function expansion equals the
squared norm of its coefficient-weighted overlap sum. This is the algebraic truncation
identity used for the discussion in [WangEtAl2008]. -/
theorem truncated_csf_success_prob_eq {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (target : QState I) (c : Idx → ℂ) (Φ : Idx → QState I) (K : Finset Idx) :
    ‖Inner target (∑ i ∈ K, c i • Φ i)‖ ^ 2
      = ‖∑ i ∈ K, c i * Inner target (Φ i)‖ ^ 2 := by
  rw [inner_finset_smul_sum]

omit [DecidableEq I] in

/-- A supplied overlap norm above `sqrt (9 / 10)` for the truncated expansion implies squared
overlap above `9 / 10`. This conditional threshold captures the high-success criterion
discussed in [WangEtAl2008]. -/
theorem few_csf_success_prob_gt_nine_tenths {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (target : QState I) (c : Idx → ℂ) (Φ : Idx → QState I) (K : Finset Idx)
    (hdata : Real.sqrt (9 / 10 : ℝ) < ‖Inner target (∑ i ∈ K, c i • Φ i)‖) :
    (9 / 10 : ℝ) < ‖Inner target (∑ i ∈ K, c i • Φ i)‖ ^ 2 :=
  (success_prob_gt_nine_tenths_iff (Inner target (∑ i ∈ K, c i • Φ i))).2 hdata

omit [DecidableEq I] in

/-- Restricting the finite configuration label set to `K` cannot increase the base-two
ceiling-logarithm register bound. This is the dimension-counting bound associated with the
few-configuration-state-function discussion of [WangEtAl2008]. -/
theorem few_csf_qubit_bound {Idx : Type*} [Fintype Idx] (K : Finset Idx) :
    Nat.clog 2 K.card ≤ Nat.clog 2 (Fintype.card Idx) :=
  Nat.clog_mono_right 2 (Finset.card_le_univ K)

/-- The base-two ceiling logarithms of 152, 6, and 8 are 8, 3, and 3, respectively. These are
the register-size counts for the configuration spaces discussed in [WangEtAl2008]. -/
theorem few_csf_qubit_counts :
    Nat.clog 2 152 = 8 ∧ Nat.clog 2 6 = 3 ∧ Nat.clog 2 8 = 3 := by
  decide

/-- A register accommodating 13872 configuration labels requires 14 qubits by the base-two
ceiling-logarithm count used in [WangEtAl2008]. -/
theorem ci_register_qubits : Nat.clog 2 13872 = 14 := by
  decide

end Qatlib.Papers.EnergySpec09.MainResults
