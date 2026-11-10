/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixGeometry.FlagProjection.Born
set_option warningAsError false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Foundations.MatrixGeometry.FlagProjection
variable {X : Type*} [Fintype X] [DecidableEq X]

def coherent (pi : X → ℝ) : EuclideanSpace ℂ X :=
  WithLp.toLp 2 (fun x => (Real.sqrt (pi x) : ℂ))

omit [Fintype X] [DecidableEq X] in

theorem coherent_born (pi : X → ℝ) (hn : ∀ x, 0 ≤ pi x) (x : X) :
    ‖(coherent pi).ofLp x‖^2 = pi x := by
  simp [coherent, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (hn x)]

omit [DecidableEq X] in

theorem coherent_unit (pi : X → ℝ) (hn : ∀ x, 0 ≤ pi x) (hs : ∑ x, pi x = 1) :
    inner ℂ (coherent pi) (coherent pi) = 1 := by
  have hnorm : ‖coherent pi‖^2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp_rw [coherent_born pi hn]
    exact hs
  rw [inner_self_eq_norm_sq_to_K]
  simpa only [map_pow, map_one] using congrArg (algebraMap ℝ ℂ) hnorm

omit [Fintype X] [DecidableEq X] in

theorem coherent_mass (pi : X → ℝ) (hn : ∀ x, 0 ≤ pi x) (S : Finset X) :
    mass S (coherent pi) = ∑ x ∈ S, pi x := by
  simp [mass, coherent_born pi hn]

def pairCoherent (pi : X → ℝ) (P : X → X → ℝ) : EuclideanSpace ℂ (X × X) :=
  WithLp.toLp 2 (fun ij => (Real.sqrt (pi ij.1) : ℂ) * (Real.sqrt (P ij.2 ij.1) : ℂ))

omit [Fintype X] [DecidableEq X] in

theorem pair_born (pi : X → ℝ) (P : X → X → ℝ)
    (hn : ∀ x, 0 ≤ pi x) (hP : ∀ j i, 0 ≤ P j i) (i j : X) :
    ‖(pairCoherent pi P).ofLp (i,j)‖^2 = pi i * P j i := by
  simp [pairCoherent, mul_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (hn i), Real.sq_sqrt (hP j i)]

omit [DecidableEq X] in

theorem pair_marginal (pi : X → ℝ) (P : X → X → ℝ)
    (hn : ∀ x, 0 ≤ pi x) (hP : ∀ j i, 0 ≤ P j i) (hsP : ∀ i, ∑ j, P j i = 1) (i : X) :
    (∑ j, ‖(pairCoherent pi P).ofLp (i,j)‖^2) = pi i := by
  simp_rw [pair_born pi P hn hP]
  rw [← Finset.mul_sum, hsP i, mul_one]

omit [DecidableEq X] in

theorem pair_unit (pi : X → ℝ) (P : X → X → ℝ)
    (hn : ∀ x, 0 ≤ pi x) (hs : ∑ x, pi x = 1)
    (hP : ∀ j i, 0 ≤ P j i) (hsP : ∀ i, ∑ j, P j i = 1) :
    inner ℂ (pairCoherent pi P) (pairCoherent pi P) = 1 := by
  have hnorm : ‖pairCoherent pi P‖^2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
    simp_rw [pair_marginal pi P hn hP hsP]
    exact hs
  rw [inner_self_eq_norm_sq_to_K]
  simpa only [map_pow, map_one] using congrArg (algebraMap ℝ ℂ) hnorm

def pairFlags (S : Finset X) : Finset (X × X) := S ×ˢ Finset.univ

omit [DecidableEq X] in

theorem pair_mass (pi : X → ℝ) (P : X → X → ℝ)
    (hn : ∀ x, 0 ≤ pi x) (hP : ∀ j i, 0 ≤ P j i) (hsP : ∀ i, ∑ j, P j i = 1)
    (S : Finset X) : mass (pairFlags S) (pairCoherent pi P) = ∑ i ∈ S, pi i := by
  simp only [mass, pairFlags, Finset.sum_product]
  simp_rw [pair_marginal pi P hn hP hsP]

theorem pair_conditional (pi : X → ℝ) (P : X → X → ℝ)
    (hn : ∀ x, 0 ≤ pi x) (hP : ∀ j i, 0 ≤ P j i) (hsP : ∀ i, ∑ j, P j i = 1)
    (S : Finset X) (i : X) :
    (∑ j, conditionalBorn (pairFlags S) (pairCoherent pi P) (i,j)) =
      if i ∈ S then pi i / (∑ x ∈ S, pi x) else 0 := by
  simp only [conditionalBorn, pairFlags, Finset.mem_product, Finset.mem_univ, and_true]
  by_cases hi : i ∈ S
  · simp only [hi, if_true]
    rw [← Finset.sum_div, pair_marginal pi P hn hP hsP, ← pair_mass pi P hn hP hsP S]
    rfl
  · simp [hi]
end Qatlib.Foundations.MatrixGeometry.FlagProjection
