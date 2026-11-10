/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QMedianStats98.MainResults.Model.Basic
set_option warningAsError false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QMedianStats98.MainResults.Model

def below {n : ℕ} (x : Fin n → ℝ) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun j => x j < x i)

def above {n : ℕ} (x : Fin n → ℝ) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun j => x i < x j)

def rankSet {n : ℕ} (x : Fin n → ℝ) (i : Fin n) : Finset ℕ :=
  Finset.Icc ((below x i).card + 1) (n - (above x i).card)

def IsApproxKth {n : ℕ} (x : Fin n → ℝ) (k : ℕ) (delta : ℝ) (i : Fin n) : Prop :=
  ∃ r ∈ rankSet x i, |(r : ℝ) - (k : ℝ)| < delta

def IsApproxMedian {n : ℕ} (x : Fin n → ℝ) (epsilon : ℝ) (i : Fin n) : Prop :=
  ((below x i).card : ℝ) < (1 + epsilon) * n / 2 ∧
    ((above x i).card : ℝ) < (1 + epsilon) * n / 2

def IsApproxCount {n : ℕ} (X : Fin n → Bool) (delta estimate : ℝ) : Prop :=
  |estimate - (weight X : ℝ)| < delta

def IsStrictRelativeCount {n : ℕ} (X : Fin n → Bool) (epsilon estimate : ℝ) : Prop :=
  |estimate - (weight X : ℝ)| < epsilon * (weight X : ℝ)

theorem weight_all_false (n : ℕ) : weight (fun _ : Fin n => false) = 0 := by
  simp [weight]

theorem strict_relative_zero_impossible (n : ℕ) (epsilon estimate : ℝ) :
    ¬ IsStrictRelativeCount (fun _ : Fin n => false) epsilon estimate := by
  simp only [IsStrictRelativeCount, weight_all_false, Nat.cast_zero, sub_zero, mul_zero]
  exact not_lt_of_ge (abs_nonneg estimate)

def IsRelativeCount {n : ℕ} (X : Fin n → Bool) (epsilon estimate : ℝ) : Prop :=
  if weight X = 0 then estimate = 0 else IsStrictRelativeCount X epsilon estimate

theorem relative_zero_iff (n : ℕ) (epsilon estimate : ℝ) :
    IsRelativeCount (fun _ : Fin n => false) epsilon estimate ↔ estimate = 0 := by
  simp [IsRelativeCount, weight_all_false]

end Qatlib.Papers.QMedianStats98.MainResults.Model
