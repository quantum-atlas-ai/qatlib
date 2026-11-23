/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# A variational ground energy of an actual finite matrix

The energy is the infimum of the actual matrix Rayleigh quotients over nonzero
vectors. A finite entry bound proves boundedness below. Every upper bound is
then obtained by evaluating a concrete nonzero test vector, rather than by
supplying an unconstrained scalar called a smallest eigenvalue.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Qatlib.Papers.KhovanovHom25.MainResults.RayleighMin

/-- The squared Euclidean mass of a finite vector. -/
def mass {α : Type*} [Fintype α] (x : α → ℝ) : ℝ := ∑ i, x i ^ 2

/-- The quadratic form computed by the actual finite matrix entries. -/
def quadratic {α : Type*} [Fintype α] (A : α → α → ℝ) (x : α → ℝ) : ℝ :=
  ∑ i, ∑ j, A i j * x i * x j

/-- The matrix Rayleigh quotient of a finite vector. -/
def quotient {α : Type*} [Fintype α] (A : α → α → ℝ) (x : α → ℝ) : ℝ :=
  quadratic A x / mass x

/-- The ground energy is fixed by the matrix, through all nonzero Rayleigh tests. -/
def bottom {α : Type*} [Fintype α] (A : α → α → ℝ) : ℝ :=
  sInf {r : ℝ | ∃ x : α → ℝ, x ≠ 0 ∧ r = quotient A x}

/-- Every finite vector has nonnegative squared mass. -/
theorem mass_nonneg {α : Type*} [Fintype α] (x : α → ℝ) : 0 ≤ mass x := by
  unfold mass
  positivity

/-- A nonzero finite vector has strictly positive squared mass. -/
theorem mass_pos {α : Type*} [Fintype α] (x : α → ℝ) (hx : x ≠ 0) : 0 < mass x := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (funext h)
  unfold mass
  exact Finset.sum_pos' (fun j _ => sq_nonneg (x j))
    ⟨i, Finset.mem_univ _, sq_pos_of_ne_zero hi⟩

/-- Each coordinate square is bounded by the actual total squared mass. -/
theorem coord_sq_le {α : Type*} [Fintype α] (x : α → ℝ) (i : α) :
    x i ^ 2 ≤ mass x := by
  exact Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)

/-- The absolute product of two coordinates never exceeds their total squared mass. -/
theorem coord_prod_le {α : Type*} [Fintype α] (x : α → ℝ) (i j : α) :
    |x i * x j| ≤ mass x := by
  have hi := coord_sq_le x i
  have hj := coord_sq_le x j
  have hs := sq_nonneg (|x i| - |x j|)
  rw [abs_mul]
  nlinarith [sq_abs (x i), sq_abs (x j)]

/-- Every matrix quadratic form has an explicit finite entrywise lower bound. -/
theorem quadratic_lower {α : Type*} [Fintype α] (A : α → α → ℝ) (x : α → ℝ) :
    -(∑ i, ∑ j, |A i j|) * mass x ≤ quadratic A x := by
  have hentry : ∀ i j, -(|A i j| * mass x) ≤ A i j * x i * x j := by
    intro i j
    have habs : |A i j * x i * x j| ≤ |A i j| * mass x := by
      rw [mul_assoc, abs_mul]
      exact mul_le_mul_of_nonneg_left (coord_prod_le x i j) (abs_nonneg _)
    linarith [neg_abs_le (A i j * x i * x j)]
  have hsum := Finset.sum_le_sum (fun i (_hi : i ∈ (Finset.univ : Finset α)) =>
    Finset.sum_le_sum (fun j (_hj : j ∈ (Finset.univ : Finset α)) => hentry i j))
  simp only [Finset.sum_neg_distrib, ← Finset.sum_mul] at hsum
  simpa only [quadratic, neg_mul] using hsum

/-- All nonzero Rayleigh quotients have a genuine matrix-derived lower bound. -/
theorem quotient_lower {α : Type*} [Fintype α] (A : α → α → ℝ)
    (x : α → ℝ) (hx : x ≠ 0) :
    -(∑ i, ∑ j, |A i j|) ≤ quotient A x := by
  rw [quotient, le_div_iff₀ (mass_pos x hx)]
  exact quadratic_lower A x

/-- Every concrete nonzero test vector bounds the matrix's variational ground energy above. -/
theorem bottom_le {α : Type*} [Fintype α] (A : α → α → ℝ)
    (x : α → ℝ) (hx : x ≠ 0) : bottom A ≤ quotient A x := by
  unfold bottom
  apply csInf_le
  · refine ⟨-(∑ i, ∑ j, |A i j|), ?_⟩
    rintro r ⟨y, hy, rfl⟩
    exact quotient_lower A y hy
  · exact ⟨x, hx, rfl⟩

/-- A positive semidefinite actual matrix has nonnegative variational ground energy. -/
theorem bottom_nonneg {α : Type*} [Fintype α] [Nonempty α] (A : α → α → ℝ)
    (hA : ∀ x : α → ℝ, 0 ≤ quadratic A x) : 0 ≤ bottom A := by
  unfold bottom
  apply le_csInf
  · refine ⟨quotient A (fun _ => 1), (fun _ => 1), ?_, rfl⟩
    intro h
    obtain ⟨i⟩ := ‹Nonempty α›
    have := congrFun h i
    norm_num at this
  · rintro r ⟨x, _, rfl⟩
    exact div_nonneg (hA x) (mass_nonneg x)

/-- An actual nonzero kernel vector forces zero ground energy for a positive matrix. -/
theorem bottom_zero_of_kernel {α : Type*} [Fintype α] [Nonempty α]
    (A : α → α → ℝ) (hA : ∀ x : α → ℝ, 0 ≤ quadratic A x)
    (x : α → ℝ) (hx : x ≠ 0) (hker : ∀ i, ∑ j, A i j * x j = 0) :
    bottom A = 0 := by
  apply le_antisymm
  · have hquad : quadratic A x = 0 := by
      unfold quadratic
      have heq : ∀ i j, A i j * x i * x j = x i * (A i j * x j) := by
        intro i j
        ring
      simp_rw [heq, ← Finset.mul_sum, hker, mul_zero]
      simp only [Finset.sum_const_zero]
    have htest := bottom_le A x hx
    simpa only [quotient, hquad, zero_div] using htest
  · exact bottom_nonneg A hA

end Qatlib.Papers.KhovanovHom25.MainResults.RayleighMin
