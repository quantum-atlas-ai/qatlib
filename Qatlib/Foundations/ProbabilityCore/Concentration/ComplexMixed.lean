/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.ProbabilityCore.Concentration.ComplexMoments
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section


/-! # Balanced actual complex Gaussian polynomial moments

Demand: LinearOptics10 Lemma15. The diagonal monomial moments are genuine
Gaussian integrals, not an assumed Fock pairing. Off-diagonal phase
orthogonality and finite multi-mode factorization remain separate.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ComplexConjugate
namespace Qatlib.Foundations.ProbabilityCore.Concentration.ComplexMixed
open Qatlib.Foundations.ProbabilityCore.Concentration.ComplexShift

/-- Balanced conjugate/nonconjugate monomials have the genuine factorial Gaussian moment. -/
theorem balanced (k : ℕ) :
    (∫ z : ℂ, conj (z^k) * z^k * (density z : ℂ) ∂volume) = (k.factorial : ℂ) := by
  have he : (fun z : ℂ => conj (z^k) * z^k * (density z : ℂ)) =
      fun z => ((Complex.normSq z ^ k * density z : ℝ) : ℂ) := by
    funext z
    rw [map_pow, ← mul_pow, ← Complex.normSq_eq_conj_mul_self]
    simp only [Complex.ofReal_mul, Complex.ofReal_pow]
  rw [he, integral_complex_ofReal, ComplexMoments.radialMoment]
  norm_cast

/-- Arbitrary scalar coefficients preserve the actual balanced Gaussian pairing formula. -/
theorem scalarPair (k : ℕ) (a b : ℂ) :
    (∫ z : ℂ, conj (a*z^k) * (b*z^k) * (density z : ℂ) ∂volume) =
      conj a * b * (k.factorial : ℂ) := by
  have he : (fun z : ℂ => conj (a*z^k) * (b*z^k) * (density z : ℂ)) =
      fun z => (conj a*b) * (conj (z^k)*z^k*(density z : ℂ)) := by
    funext z
    rw [map_mul]
    ring
  rw [he, integral_const_mul, balanced]

end Qatlib.Foundations.ProbabilityCore.Concentration.ComplexMixed
