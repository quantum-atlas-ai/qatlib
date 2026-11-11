/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.LinearAlgebra.Matrix.Stochastic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Weighted time reversal of finite Markov kernels

`reverse` defines the weighted transpose with entries `π y * P y x / π x`, while `Stationary`
records the row-vector stationarity equation. Positive stationary weights ensure that reversal
of a row-stochastic matrix is again row-stochastic.

Reversal preserves the weights as stationary for a row-stochastic input, is involutive for
positive weights, and satisfies a weighted balance identity. These constructions underlie the
nonreversible-chain framework of [ClaudonPiquemalMonmarche2025].

## Main statements

* `reverse_stochastic`: Stochasticity of the reversed stationary kernel.
* `reverse_stationary`: Stationarity for the reversed kernel.
* `reverse_reverse`: Involutivity for positive weights.

## References

* [Claudon et al., 2025][ClaudonPiquemalMonmarche2025]
-/

set_option autoImplicit false
noncomputable section
open Matrix
open scoped Classical BigOperators
namespace Qatlib.Foundations.MarkovChains.ReverseKernel
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The weighted reverse matrix with entry `π y * P y x / π x` at `(x, y)`. -/
def reverse (P : Matrix I I ℝ) (π : I → ℝ) : Matrix I I ℝ := fun x y => π y*P y x/π x

/-- The condition that the row vector `π` satisfies `π ᵥ* P = π`. -/
def Stationary (P : Matrix I I ℝ) (π : I → ℝ) : Prop := π ᵥ* P=π

/-- Reversing a row-stochastic matrix with positive weights gives nonnegative entries. -/
theorem reverse_nonneg (P : Matrix I I ℝ) (π : I → ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ I) (hπ : ∀ x,0 < π x) (x y : I) : 0 ≤ reverse P π x y :=
  div_nonneg (mul_nonneg (le_of_lt (hπ y)) (hP.1 y x)) (le_of_lt (hπ x))
omit [DecidableEq I] in

/-- If positive weights are stationary for `P`, every row of the reversed matrix sums to one. -/
theorem reverse_row_sum (P : Matrix I I ℝ) (π : I → ℝ)
    (hπ : ∀ x,0 < π x) (hstat : Stationary P π) (x : I) : ∑ y,reverse P π x y=1 := by
  change (∑ y,π y*P y x/π x)=1
  rw [← Finset.sum_div]
  have hs : (∑ y,π y*P y x)=π x := congrFun hstat x
  rw [hs,div_self (ne_of_gt (hπ x))]

/-- The reverse of a row-stochastic matrix with positive stationary weights is row-stochastic. -/
theorem reverse_stochastic (P : Matrix I I ℝ) (π : I → ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ I) (hπ : ∀ x,0 < π x) (hstat : Stationary P π) :
    reverse P π ∈ Matrix.rowStochastic ℝ I :=
  Matrix.mem_rowStochastic_iff_sum.mpr ⟨reverse_nonneg P π hP hπ,reverse_row_sum P π hπ hstat⟩

/-- For a row-stochastic matrix and positive weights, those weights are stationary for its
weighted reverse. -/
theorem reverse_stationary (P : Matrix I I ℝ) (π : I → ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ I) (hπ : ∀ x,0 < π x) : Stationary (reverse P π) π := by
  funext y
  change (∑ x,π x*(π y*P y x/π x))=π y
  have he (x : I) : π x*(π y*P y x/π x)=π y*P y x := by field_simp [ne_of_gt (hπ x)]
  simp_rw [he]
  rw [← Finset.mul_sum,Matrix.sum_row_of_mem_rowStochastic hP,mul_one]
omit [Fintype I] [DecidableEq I] in

/-- Reversal with strictly positive weights is an involution. -/
theorem reverse_reverse (P : Matrix I I ℝ) (π : I → ℝ) (hπ : ∀ x,0 < π x) :
    reverse (reverse P π) π=P := by
  ext x y
  change π y*(π x*P x y/π y)/π x=P x y
  field_simp [ne_of_gt (hπ x),ne_of_gt (hπ y)]
omit [Fintype I] [DecidableEq I] in

/-- For positive weights, the reversed entries satisfy `π x * reverse P π x y = π y * P y x`. -/
theorem reverse_balance (P : Matrix I I ℝ) (π : I → ℝ) (hπ : ∀ x,0 < π x) (x y : I) :
    π x*reverse P π x y=π y*P y x := by
  change π x*(π y*P y x/π x)=_
  field_simp [ne_of_gt (hπ x)]
end Qatlib.Foundations.MarkovChains.ReverseKernel
