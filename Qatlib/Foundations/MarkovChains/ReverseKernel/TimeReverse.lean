/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.LinearAlgebra.Matrix.Stochastic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open Matrix
open scoped Classical BigOperators
namespace Qatlib.Foundations.MarkovChains.ReverseKernel
variable {I : Type*} [Fintype I] [DecidableEq I]

def reverse (P : Matrix I I ℝ) (π : I → ℝ) : Matrix I I ℝ := fun x y => π y*P y x/π x

def Stationary (P : Matrix I I ℝ) (π : I → ℝ) : Prop := π ᵥ* P=π

theorem reverse_nonneg (P : Matrix I I ℝ) (π : I → ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ I) (hπ : ∀ x,0 < π x) (x y : I) : 0 ≤ reverse P π x y :=
  div_nonneg (mul_nonneg (le_of_lt (hπ y)) (hP.1 y x)) (le_of_lt (hπ x))
omit [DecidableEq I] in

theorem reverse_row_sum (P : Matrix I I ℝ) (π : I → ℝ)
    (hπ : ∀ x,0 < π x) (hstat : Stationary P π) (x : I) : ∑ y,reverse P π x y=1 := by
  change (∑ y,π y*P y x/π x)=1
  rw [← Finset.sum_div]
  have hs : (∑ y,π y*P y x)=π x := congrFun hstat x
  rw [hs,div_self (ne_of_gt (hπ x))]

theorem reverse_stochastic (P : Matrix I I ℝ) (π : I → ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ I) (hπ : ∀ x,0 < π x) (hstat : Stationary P π) :
    reverse P π ∈ Matrix.rowStochastic ℝ I :=
  Matrix.mem_rowStochastic_iff_sum.mpr ⟨reverse_nonneg P π hP hπ,reverse_row_sum P π hπ hstat⟩

theorem reverse_stationary (P : Matrix I I ℝ) (π : I → ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ I) (hπ : ∀ x,0 < π x) : Stationary (reverse P π) π := by
  funext y
  change (∑ x,π x*(π y*P y x/π x))=π y
  have he (x : I) : π x*(π y*P y x/π x)=π y*P y x := by field_simp [ne_of_gt (hπ x)]
  simp_rw [he]
  rw [← Finset.mul_sum,Matrix.sum_row_of_mem_rowStochastic hP,mul_one]
omit [Fintype I] [DecidableEq I] in

theorem reverse_reverse (P : Matrix I I ℝ) (π : I → ℝ) (hπ : ∀ x,0 < π x) :
    reverse (reverse P π) π=P := by
  ext x y
  change π y*(π x*P x y/π y)/π x=P x y
  field_simp [ne_of_gt (hπ x),ne_of_gt (hπ y)]
omit [Fintype I] [DecidableEq I] in

theorem reverse_balance (P : Matrix I I ℝ) (π : I → ℝ) (hπ : ∀ x,0 < π x) (x y : I) :
    π x*reverse P π x y=π y*P y x := by
  change π x*(π y*P y x/π x)=_
  field_simp [ne_of_gt (hπ x)]
end Qatlib.Foundations.MarkovChains.ReverseKernel
