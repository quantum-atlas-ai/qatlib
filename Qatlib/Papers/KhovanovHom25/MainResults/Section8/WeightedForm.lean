/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KhovanovHom25.MainResults.Section8.RayleighMin
public import Qatlib.Papers.KhovanovHom25.MainResults.Section8.SectorKernel

/-!
# Actual weighted signless quadratic forms and coloring tests

The diagonal is computed from the loop weights and the incident edge weights.
A coloring determines an explicit alternating vector. Its Rayleigh test is
bounded by four times the actual coloring repair cost, with the source's
necessary factor four retained.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace Qatlib.Papers.KhovanovHom25.MainResults.WeightedForm

/-- The actual signless matrix of finite loop and off-diagonal edge weights. -/
def matrix {α : Type*} [Fintype α] (l : α → ℝ) (w : α → α → ℝ) (i j : α) : ℝ :=
  if i = j then 2 * l i + ∑ k, w i k else w i j

/-- The cost of deleting all loops and monochromatic undirected edges. -/
def repairCost {α : Type*} [Fintype α] (l : α → ℝ) (w : α → α → ℝ)
    (c : α → Bool) : ℝ :=
  (∑ i, l i) + (1 / 2) * ∑ i, ∑ j, if c i = c j then w i j else 0

/-- The quadratic form splits into its computed degree term and neighbor term. -/
theorem quadratic_expand {α : Type*} [Fintype α] (l : α → ℝ) (w : α → α → ℝ)
    (x : α → ℝ) (hdiag : ∀ i, w i i = 0) :
    RayleighMin.quadratic (matrix l w) x =
      2 * (∑ i, l i * x i ^ 2) +
        (∑ i, ∑ j, w i j * x i ^ 2) +
          ∑ i, ∑ j, w i j * x i * x j := by
  have heq : ∀ i j, matrix l w i j =
      (if i = j then 2 * l i + ∑ k, w i k else 0) + w i j := by
    intro i j
    by_cases h : i = j
    · subst j
      simp only [matrix, hdiag, add_zero]
    · simp only [matrix, ite_eq_right h, zero_add]
  unfold RayleighMin.quadratic
  simp_rw [heq, add_mul, ite_mul, zero_mul]
  simp_rw [Finset.sum_add_distrib]
  congr 1
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have hrow : ∀ i, (2 * l i + ∑ j, w i j) * x i * x i =
      2 * (l i * x i ^ 2) + ∑ j, w i j * x i ^ 2 := by
    intro i
    rw [← Finset.sum_mul]
    ring
  simp_rw [hrow, Finset.sum_add_distrib, ← Finset.mul_sum]

/-- Alternating coloring coordinates have unit square. -/
theorem sign_sq {α : Type*} (c : α → Bool) (i : α) : SectorKernel.sign c i ^ 2 = 1 := by
  unfold SectorKernel.sign
  split <;> norm_num

/-- The actual mass of a coloring test vector is the number of actual vertices. -/
theorem sign_mass {α : Type*} [Fintype α] (c : α → Bool) :
    RayleighMin.mass (SectorKernel.sign c) = Fintype.card α := by
  simp only [RayleighMin.mass, sign_sq, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

/-- A coloring test is a genuine nonzero vector on any nonempty finite graph. -/
theorem sign_ne_zero {α : Type*} [Nonempty α] (c : α → Bool) : SectorKernel.sign c ≠ 0 := by
  obtain ⟨i⟩ := ‹Nonempty α›
  intro h
  exact SectorKernel.sign_ne_zero c i (congrFun h i)

/-- The alternating vector computes exactly the loop and monochromatic-edge energy. -/
theorem sign_quadratic {α : Type*} [Fintype α] (l : α → ℝ) (w : α → α → ℝ)
    (c : α → Bool) (hdiag : ∀ i, w i i = 0) :
    RayleighMin.quadratic (matrix l w) (SectorKernel.sign c) =
      2 * (∑ i, l i) + 2 * ∑ i, ∑ j, if c i = c j then w i j else 0 := by
  rw [quadratic_expand l w _ hdiag]
  simp only [sign_sq, mul_one]
  have hsign : ∀ i j, w i j + w i j * SectorKernel.sign c i * SectorKernel.sign c j =
      2 * (if c i = c j then w i j else 0) := by
    intro i j
    unfold SectorKernel.sign
    cases hi : c i <;> cases hj : c j <;> norm_num [hi, hj]
    <;> ring
  have hs : (∑ i, ∑ j, w i j) +
      (∑ i, ∑ j, w i j * SectorKernel.sign c i * SectorKernel.sign c j) =
        2 * ∑ i, ∑ j, if c i = c j then w i j else 0 := by
    rw [← Finset.sum_add_distrib]
    simp_rw [← Finset.sum_add_distrib, hsign, ← Finset.mul_sum]
  linarith

/-- Every actual coloring supplies the source's four-times-repair Rayleigh upper bound. -/
theorem bottom_le_repair {α : Type*} [Fintype α] [Nonempty α]
    (l : α → ℝ) (w : α → α → ℝ) (c : α → Bool)
    (hl : ∀ i, 0 ≤ l i) (hdiag : ∀ i, w i i = 0) :
    RayleighMin.bottom (matrix l w) ≤ 4 * repairCost l w c / Fintype.card α := by
  have htest := RayleighMin.bottom_le (matrix l w) (SectorKernel.sign c) (sign_ne_zero c)
  rw [RayleighMin.quotient, sign_mass, sign_quadratic l w c hdiag] at htest
  apply htest.trans
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  unfold repairCost
  have hsum : 0 ≤ ∑ i, l i := Finset.sum_nonneg (fun i _ => hl i)
  linarith

/-- The actual symmetric signless form is a sum of loop and edge squares. -/
theorem quadratic_energy {α : Type*} [Fintype α] (l : α → ℝ) (w : α → α → ℝ)
    (x : α → ℝ) (hdiag : ∀ i, w i i = 0) (hsymm : ∀ i j, w i j = w j i) :
    RayleighMin.quadratic (matrix l w) x =
      2 * (∑ i, l i * x i ^ 2) +
        (1 / 2) * ∑ i, ∑ j, w i j * (x i + x j) ^ 2 := by
  have hswap : (∑ i, ∑ j, w i j * x j ^ 2) = ∑ i, ∑ j, w i j * x i ^ 2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hsymm j i]
  have hexpand : (∑ i, ∑ j, w i j * (x i + x j) ^ 2) =
      2 * (∑ i, ∑ j, w i j * x i ^ 2) +
        2 * ∑ i, ∑ j, w i j * x i * x j := by
    have heq : ∀ i j, w i j * (x i + x j) ^ 2 =
        w i j * x i ^ 2 + w i j * x j ^ 2 + 2 * (w i j * x i * x j) := by
      intro i j
      ring
    simp_rw [heq, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hswap]
    ring
  rw [quadratic_expand l w x hdiag]
  linarith

/-- Nonnegative loop and symmetric edge weights give a genuinely positive matrix form. -/
theorem quadratic_nonneg {α : Type*} [Fintype α] (l : α → ℝ) (w : α → α → ℝ)
    (hl : ∀ i, 0 ≤ l i) (hw : ∀ i j, 0 ≤ w i j)
    (hdiag : ∀ i, w i i = 0) (hsymm : ∀ i j, w i j = w j i) (x : α → ℝ) :
    0 ≤ RayleighMin.quadratic (matrix l w) x := by
  rw [quadratic_energy l w x hdiag hsymm]
  have hloop : 0 ≤ ∑ i, l i * x i ^ 2 :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hl i) (sq_nonneg _))
  have hedge : 0 ≤ ∑ i, ∑ j, w i j * (x i + x j) ^ 2 :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg
      (fun j _ => mul_nonneg (hw i j) (sq_nonneg _)))
  positivity

end Qatlib.Papers.KhovanovHom25.MainResults.WeightedForm
