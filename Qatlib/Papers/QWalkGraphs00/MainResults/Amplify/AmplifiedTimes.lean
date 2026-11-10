/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QWalkGraphs00.MainResults.Amplify.Amplification
import Qatlib.Papers.QWalkGraphs00.MainResults.Times
import Mathlib.Analysis.SpecialFunctions.Log.Basic
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QWalkGraphs00.MainResults.Amplify

open scoped BigOperators Matrix Topology
open Filter
open Qatlib.Papers.QWalkGraphs00.MainResults.Core
open Qatlib.Papers.QWalkGraphs00.MainResults.Times

variable {Coin V : Type*} [Fintype Coin] [Fintype V] [DecidableEq Coin] [DecidableEq V]
variable {π : V → ℝ} {ε : ℝ}

def amplificationSteps (ε minπ : ℝ) : ℝ := Real.log (1 / minπ) / Real.log (1 / ε)

omit [DecidableEq V] in

theorem l1_bound_implies_sampling_at (σ π : V → ℝ) (ε' minπ : ℝ) (X : Finset V)
    (hL1 : l1Norm (σ - π) ≤ ε' * minπ)
    (hnn : ∀ v, 0 ≤ π v) (hmin : ∀ v, minπ ≤ π v)
    (hε' : 0 ≤ ε') :
    |(∑ x ∈ X, π x) - ∑ x ∈ X, σ x| ≤ ε' * (∑ x ∈ X, π x) := by
  by_cases hX : X.Nonempty
  · have hsub : (∑ x ∈ X, π x) - ∑ x ∈ X, σ x = ∑ x ∈ X, (π x - σ x) := by
      rw [Finset.sum_sub_distrib]
    have hmin_le : minπ ≤ ∑ x ∈ X, π x := by
      obtain ⟨x0, hx0⟩ := hX
      have hsingle : π x0 ≤ ∑ x ∈ X, π x :=
        Finset.single_le_sum (f := π) (fun i _ => hnn i) hx0
      exact le_trans (hmin x0) hsingle
    calc |(∑ x ∈ X, π x) - ∑ x ∈ X, σ x|
        = |∑ x ∈ X, (π x - σ x)| := by rw [hsub]
      _ ≤ ∑ x ∈ X, |π x - σ x| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ x, |π x - σ x| :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ X)
            (fun x _ _ => abs_nonneg _)
      _ = l1Norm (π - σ) := rfl
      _ = l1Norm (σ - π) := by
          apply Finset.sum_congr rfl
          intro x _
          rw [Pi.sub_apply, Pi.sub_apply, abs_sub_comm]
      _ ≤ ε' * minπ := hL1
      _ ≤ ε' * ∑ x ∈ X, π x := mul_le_mul_of_nonneg_left hmin_le hε'
  · rw [Finset.not_nonempty_iff_eq_empty.mp hX]
    simp

omit [DecidableEq V] in

theorem amplified_sampling_bound (A : AmplificationStep (V := V) π ε) (hε : 0 ≤ ε)
    (k : ℕ) (σ : V → ℝ) (δ ε' minπ : ℝ)
    (hσ : ∑ v, σ v = 1) (hπ : ∑ v, π v = 1)
    (hδ : l1Norm (σ - π) ≤ δ)
    (hnn : ∀ v, 0 ≤ π v) (hmin : ∀ v, minπ ≤ π v)
    (hε' : 0 ≤ ε') (hcrit : ε ^ k * δ ≤ ε' * minπ) :
    ∀ X : Finset V,
      |(∑ x ∈ X, π x) - ∑ x ∈ X, ((stochStep A.P)^[k] σ) x| ≤ ε' * (∑ x ∈ X, π x) := by
  intro X
  have hL1 : l1Norm ((stochStep A.P)^[k] σ - π) ≤ ε' * minπ :=
    le_trans (lemma_5_1 A hε k σ δ hσ hπ hδ) hcrit
  exact l1_bound_implies_sampling_at _ π ε' minπ X hL1 hnn hmin hε'

end Qatlib.Papers.QWalkGraphs00.MainResults.Amplify
