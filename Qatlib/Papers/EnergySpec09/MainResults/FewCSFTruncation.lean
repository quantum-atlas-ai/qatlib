/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.EnergySpec09.MainResults.WaterPESNumerics
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath

open scoped BigOperators Classical

namespace Qatlib.Papers.EnergySpec09.MainResults

variable {I : Type*} [Fintype I] [DecidableEq I]

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

theorem truncated_csf_success_prob_eq {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (target : QState I) (c : Idx → ℂ) (Φ : Idx → QState I) (K : Finset Idx) :
    ‖Inner target (∑ i ∈ K, c i • Φ i)‖ ^ 2
      = ‖∑ i ∈ K, c i * Inner target (Φ i)‖ ^ 2 := by
  rw [inner_finset_smul_sum]

omit [DecidableEq I] in

theorem few_csf_success_prob_gt_nine_tenths {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (target : QState I) (c : Idx → ℂ) (Φ : Idx → QState I) (K : Finset Idx)
    (hdata : Real.sqrt (9 / 10 : ℝ) < ‖Inner target (∑ i ∈ K, c i • Φ i)‖) :
    (9 / 10 : ℝ) < ‖Inner target (∑ i ∈ K, c i • Φ i)‖ ^ 2 :=
  (success_prob_gt_nine_tenths_iff (Inner target (∑ i ∈ K, c i • Φ i))).2 hdata

omit [DecidableEq I] in

theorem few_csf_qubit_bound {Idx : Type*} [Fintype Idx] (K : Finset Idx) :
    Nat.clog 2 K.card ≤ Nat.clog 2 (Fintype.card Idx) :=
  Nat.clog_mono_right 2 (Finset.card_le_univ K)

theorem few_csf_qubit_counts :
    Nat.clog 2 152 = 8 ∧ Nat.clog 2 6 = 3 ∧ Nat.clog 2 8 = 3 := by
  decide

theorem ci_register_qubits : Nat.clog 2 13872 = 14 := by
  decide

end Qatlib.Papers.EnergySpec09.MainResults
