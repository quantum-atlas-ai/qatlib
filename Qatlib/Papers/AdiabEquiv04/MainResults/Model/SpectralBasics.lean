/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdiabEquiv04.MainResults.Model.AdiabaticDefs

/-!
# Rayleigh expressions and coordinate projections

The real quadratic expression `rayleigh` is additive in its matrix argument and compatible with
real scalar multiplication and finite sums. The module defines `IsPositive` through this
expression and proves positivity of coordinate projections, providing elementary spectral tools
for the adiabatic construction of [AharonovEtAl2007Adiabatic].

## Main statements

* `rayleigh_add` and `rayleigh_real_smul`: linearity in the matrix argument over the reals.
* `rayleigh_basisProj`: a coordinate formula for the quadratic expression of a projection.
* `basisProj_isPositive`: positivity of every coordinate projection.

## References

* [Aharonov et al., 2007][AharonovEtAl2007Adiabatic]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators ComplexOrder

namespace Qatlib.Papers.AdiabEquiv04.MainResults.Model

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The Rayleigh expression of a matrix sum is the sum of the two Rayleigh expressions. -/
theorem rayleigh_add (A B : Matrix ι ι ℂ) (ψ : Vector ι) :
    rayleigh (A + B) ψ = rayleigh A ψ + rayleigh B ψ := by
  unfold rayleigh
  rw [Matrix.add_mulVec, dotProduct_add, Complex.add_re]

/-- Multiplying a matrix by a real scalar multiplies its Rayleigh expression by that scalar. -/
theorem rayleigh_real_smul (c : ℝ) (A : Matrix ι ι ℂ) (ψ : Vector ι) :
    rayleigh ((c : ℂ) • A) ψ = c * rayleigh A ψ := by
  unfold rayleigh
  rw [smul_mulVec, dotProduct_smul]
  simp [Complex.mul_re]

/-- The Rayleigh expression of a finite matrix sum equals the sum of the individual Rayleigh
expressions. -/
theorem rayleigh_finset_sum {κ : Type} (s : Finset κ) (f : κ → Matrix ι ι ℂ)
    (ψ : Vector ι) :
    rayleigh (∑ k ∈ s, f k) ψ = ∑ k ∈ s, rayleigh (f k) ψ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [rayleigh]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, rayleigh_add, ih]

/-- The condition that a matrix has nonnegative real quadratic expression on every vector. -/
def IsPositive (A : Matrix ι ι ℂ) : Prop := ∀ ψ : Vector ι, 0 ≤ rayleigh A ψ

/-- The zero matrix has nonnegative Rayleigh expression on every vector. -/
theorem isPositive_zero : IsPositive (0 : Matrix ι ι ℂ) := by
  intro ψ
  simp [IsPositive, rayleigh]

/-- Multiplication by a nonnegative real scalar preserves `IsPositive`. -/
theorem IsPositive.real_smul {A : Matrix ι ι ℂ} (hA : IsPositive A) {c : ℝ}
    (hc : 0 ≤ c) : IsPositive ((c : ℂ) • A) := by
  intro ψ
  rw [rayleigh_real_smul]
  exact mul_nonneg hc (hA ψ)

/-- The sum of two matrices satisfying `IsPositive` also satisfies `IsPositive`. -/
theorem IsPositive.add {A B : Matrix ι ι ℂ} (hA : IsPositive A) (hB : IsPositive B) :
    IsPositive (A + B) := by
  intro ψ
  rw [rayleigh_add]
  exact add_nonneg (hA ψ) (hB ψ)

/-- A finite sum of matrices satisfying `IsPositive` satisfies `IsPositive`. -/
theorem IsPositive.finset_sum {κ : Type} (s : Finset κ) {f : κ → Matrix ι ι ℂ}
    (h : ∀ k ∈ s, IsPositive (f k)) : IsPositive (∑ k ∈ s, f k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isPositive_zero (ι := ι)
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (h a (Finset.mem_insert_self a s)).add
        (ih (fun k hk => h k (Finset.mem_insert_of_mem hk)))

/-- A coordinate projection retains the coordinates satisfying `P` and replaces all other
coordinates by zero. -/
theorem basisProj_mulVec (P : ι → Prop) [DecidablePred P] (ψ : Vector ι) :
    basisProj P *ᵥ ψ = fun i => if P i then ψ i else 0 := by
  classical
  ext i
  rw [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single i]
  · simp [basisProj]
  · intro j _ hj
    have hji : ¬ (i = j) := fun h => hj h.symm
    simp [basisProj, hji]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- The Rayleigh expression of a coordinate projection is the sum of squared coordinate norms
over the coordinates satisfying `P`. -/
theorem rayleigh_basisProj (P : ι → Prop) [DecidablePred P] (ψ : Vector ι) :
    rayleigh (basisProj P) ψ = ∑ i, if P i then Complex.normSq (ψ i) else 0 := by
  classical
  unfold rayleigh
  rw [basisProj_mulVec, dotProduct, Complex.re_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases h : P i
  · simp only [h, if_true]
    have h1 : ((star ψ) i) * ψ i = ((Complex.normSq (ψ i) : ℝ) : ℂ) := by
      rw [Pi.star_apply, Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
    rw [h1]
    simp
  · simp [h]

/-- Every coordinate projection satisfies `IsPositive`. -/
theorem basisProj_isPositive (P : ι → Prop) [DecidablePred P] :
    IsPositive (basisProj P) := by
  intro ψ
  rw [rayleigh_basisProj]
  exact Finset.sum_nonneg (fun i _ => by
    by_cases h : P i
    · simp [h, Complex.normSq_nonneg]
    · simp [h])

/-- Every coordinate basis vector has squared norm one. -/
theorem normSq_basisKet (a : ι) : normSq (basisKet a) = 1 := by
  classical
  unfold normSq basisKet
  rw [Finset.sum_eq_single a]
  · simp [basisKet]
  · intro b _ hb
    simp [basisKet, if_neg hb]
  · intro ha
    exact absurd (Finset.mem_univ a) ha

/-- Every coordinate basis vector is normalized. -/
theorem isNormalized_basisKet (a : ι) : IsNormalized (basisKet a) :=
  normSq_basisKet a

end Qatlib.Papers.AdiabEquiv04.MainResults.Model
