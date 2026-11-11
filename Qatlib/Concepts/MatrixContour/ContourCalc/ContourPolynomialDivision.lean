/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixContour.ContourCalc.ContourModel
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.RealDeriv

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.MatrixContour.ContourCalc
open Qatlib.Foundations.OpCalculus.ContourCalc

/-! Algebraic division of a monomial against the actual resolvent. This is a
preliminary ingredient for the Cauchy bridge; no contour integral or winding
number is asserted here. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace Qatlib.Concepts.MatrixContour.ContourCalc.ContourPolynomialDivision

open scoped BigOperators Matrix.Norms.L2Operator
open Complex

/-- Construction for polynomial Remainder in the contour polynomial division model. -/
def polynomialRemainder {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (terms : Finset ℕ) (c : ℕ → ℂ) (z : ℂ) : Matrix I I ℂ :=
  ∑ n ∈ terms, c n • (∑ k ∈ Finset.range n,
    (z • (1 : Matrix I I ℂ)) ^ k * A ^ (n-1-k))

/-- The identity or estimate `polynomial_remainder_differentiable` holds with the displayed separation, geometry and norm hypotheses. -/
theorem polynomial_remainder_differentiable {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (terms : Finset ℕ) (c : ℕ → ℂ) :
    Differentiable ℂ (polynomialRemainder A terms c) := by
  unfold polynomialRemainder
  fun_prop

/-- The identity or estimate `polynomial_remainder_circle_integral_zero` holds with the displayed separation, geometry and norm hypotheses. -/
theorem polynomial_remainder_circle_integral_zero {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (terms : Finset ℕ) (c : ℕ → ℂ) (center : ℂ) (r : ℝ)
    (hr : 0 ≤ r) : ∮ z in C(center, r), polynomialRemainder A terms c z = 0 := by
  apply DiffContOnCl.circleIntegral_eq_zero hr
  exact (polynomial_remainder_differentiable A terms c).differentiableOn.diffContOnCl

/-- A single entire primitive works for all edges of a polygon, so the
polynomial remainder has a path-independent primitive. -/
theorem polynomial_remainder_has_primitive {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (terms : Finset ℕ) (c : ℕ → ℂ) :
    ∃ G : ℂ → Matrix I I ℂ, ∀ z, HasDerivAt G (polynomialRemainder A terms c z) z := by
  obtain ⟨G, hG⟩ := (polynomial_remainder_differentiable A terms c).isExactOn_univ
  exact ⟨G, fun z => hG z (Set.mem_univ z)⟩

/-- The identity or estimate `monomial_resolvent_division` holds with the displayed separation, geometry and norm hypotheses. -/
theorem monomial_resolvent_division {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (z : ℂ) (r : ℝ) (hr : 0 < r)
    (hsep : ∀ w ∈ matrixNumericalRange A, r ≤ ‖z-w‖) (n : ℕ) :
    ((z • (1 : Matrix I I ℂ)) ^ n - A ^ n) * matrixResolvent A z =
      ∑ k ∈ Finset.range n, (z • (1 : Matrix I I ℂ)) ^ k * A ^ (n-1-k) := by
  let Z : Matrix I I ℂ := z • 1
  have hc : Commute Z A := by
    change (z • (1 : Matrix I I ℂ)) * A = A * (z • (1 : Matrix I I ℂ))
    rw [smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  obtain ⟨R, hZR, hRZ, hnorm, hpseudo⟩ :=
    exists_matrix_resolvent_of_numericalRange_separation A z r hr hsep
  have he : matrixResolvent A z = R := hpseudo
  rw [he]
  have hf := hc.geom_sum₂_mul n
  change (∑ k ∈ Finset.range n, Z ^ k * A ^ (n-1-k)) * (Z-A) = Z ^ n - A ^ n at hf
  rw [← hf, mul_assoc]
  change (∑ k ∈ Finset.range n, Z ^ k * A ^ (n-1-k)) * ((z • (1 : Matrix I I ℂ) - A) * R) = _
  rw [hZR, mul_one]

/-- Finite polynomial division holds for the same genuine pseudoinverse
resolvent, without assuming that the input matrix is normal. -/
theorem polynomial_resolvent_division {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (z : ℂ) (r : ℝ) (hr : 0 < r)
    (hsep : ∀ w ∈ matrixNumericalRange A, r ≤ ‖z-w‖)
    (terms : Finset ℕ) (c : ℕ → ℂ) :
    (∑ n ∈ terms, c n • (((z • (1 : Matrix I I ℂ)) ^ n) - A ^ n)) *
        matrixResolvent A z =
      ∑ n ∈ terms, c n • (∑ k ∈ Finset.range n,
        (z • (1 : Matrix I I ℂ)) ^ k * A ^ (n-1-k)) := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n hn
  rw [smul_mul_assoc, monomial_resolvent_division A z r hr hsep n]

end Qatlib.Concepts.MatrixContour.ContourCalc.ContourPolynomialDivision
