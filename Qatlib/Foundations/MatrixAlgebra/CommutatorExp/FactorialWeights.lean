/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
namespace Qatlib.Foundations.MatrixAlgebra.CommutatorExp
open scoped BigOperators

theorem factorial_convolution (a b : ℝ) (n : ℕ) :
    (∑ ij ∈ Finset.antidiagonal n, (a^ij.1/(ij.1.factorial : ℝ))*(b^ij.2/(ij.2.factorial : ℝ))) =
      (a+b)^n/(n.factorial : ℝ) := by
  rw [(Commute.all a b).add_pow', Finset.sum_div]
  apply Finset.sum_congr rfl
  intro ij hij
  obtain ⟨i, j⟩ := ij
  have hij' : i+j=n := Finset.mem_antidiagonal.mp hij
  subst n
  have hf : (((i+j).choose i : ℕ) : ℝ)*(i.factorial : ℝ)*(j.factorial : ℝ) = ((i+j).factorial : ℝ) := by
    exact_mod_cast (by simpa only [Nat.add_comm, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using Nat.add_choose_mul_factorial_mul_factorial j i)
  simp only [nsmul_eq_mul]
  rw [← hf]
  have hi : (i.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
  have hj : (j.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  have hc : (((i+j).choose i : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (Nat.le_add_right i j)).ne'
  field_simp
end Qatlib.Foundations.MatrixAlgebra.CommutatorExp
