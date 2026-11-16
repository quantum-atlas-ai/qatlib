/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.LinearOptics10.StockmeyerSrc.FockModel
public import Qatlib.Papers.LinearOptics10.StockmeyerSrc.FockAdjoint

@[expose] public section


/-! # Actual coefficient substitution and Fock-state normalization

These are components of the fixed-source unitary-action and amplitude
bridges. They use the actual polynomial substitution, not an assumed
invariance or a supplied amplitude formula. Identifying the separate
historical assignment-sum coefficient remains a separate obligation.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open ComplexConjugate MvPolynomial
namespace Qatlib.Papers.LinearOptics10.StockmeyerSrc.FockNormalize
open Qatlib.Papers.LinearOptics10.StockmeyerSrc
open Qatlib.Concepts.BosonFock.BosonOperators
open FockModel

/-- Scaling the actual coefficient vector scales its actual polynomial by a constant. -/
theorem polyScale {m n : ℕ} (c : ℂ) (a : FockCoeff m n) :
    polyOfCoeff (c • a) = C c * polyOfCoeff a := by
  simp [polyOfCoeff, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, C_mul_monomial]

/-- Actual mode substitution is complex-linear with respect to scalar multiplication. -/
theorem phiScale {m n : ℕ} (U : Matrix (Fin m) (Fin m) ℂ) (c : ℂ) (a : FockCoeff m n) :
    phi U (c • a) = c • phi U a := by
  ext S
  simp only [phi, coeffVec, substPoly, polyScale, map_mul, aeval_C, algebraMap_eq, coeff_C_mul,
    Pi.smul_apply, smul_eq_mul]

/-- The actual finite pairing has its genuine conjugate-linear/linear scalar law. -/
theorem pairScale {m n : ℕ} (c d : ℂ) (a b : FockCoeff m n) :
    fockInner (c • a) (d • b) = conj c * d * fockInner a b := by
  simp only [fockInner, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  ring

/-- The actual normalized state is the inverse factorial-root multiple of its monomial basis. -/
theorem stateScaled {m n : ℕ} (S : FockOccupation m n) :
    stateVec S = ((Real.sqrt (occFactorial S : ℝ) : ℂ)⁻¹) • basisCoeff S := by
  ext X
  by_cases h : X = S <;> simp [stateVec, basisCoeff, h, Pi.smul_apply, smul_eq_mul]

/-- Every actual occupation has a nonzero real factorial square root. -/
theorem rootNonzero {m n : ℕ} (S : FockOccupation m n) :
    Real.sqrt (occFactorial S : ℝ) ≠ 0 := by
  apply ne_of_gt
  apply Real.sqrt_pos.mpr
  exact lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm (FockAdjoint.weightNonzero S))

/-- The unnormalized monomial basis has exactly its genuine occupation factorial norm. -/
theorem basisNorm {m n : ℕ} (S : FockOccupation m n) :
    fockInner (basisCoeff S) (basisCoeff S) = (occFactorial S : ℂ) := by
  simp [fockInner, basisCoeff]

/-- Each actual normalized physical basis state has exactly unit Fock norm. -/
theorem stateNorm {m n : ℕ} (S : FockOccupation m n) :
    fockInner (stateVec S) (stateVec S) = 1 := by
  have hs : (Real.sqrt (occFactorial S : ℝ) : ℂ) ≠ 0 := by exact_mod_cast rootNonzero S
  have hs2 : (Real.sqrt (occFactorial S : ℝ) : ℂ)^2 = (occFactorial S : ℂ) := by
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg (occFactorial S) : (0 : ℝ) ≤ occFactorial S)
  simp only [stateScaled, pairScale, basisNorm, map_inv₀, Complex.conj_ofReal]
  rw [← hs2]
  field_simp

/-- Actual normalized-state amplitudes obey the full factorial-root normalization identity. -/
theorem amplitudeNorm {m n : ℕ} (U : Matrix (Fin m) (Fin m) ℂ)
    (S T : FockOccupation m n) :
    fockInner (basisCoeff S) (phi U (basisCoeff T)) =
      ((Real.sqrt (occFactorial S : ℝ) * Real.sqrt (occFactorial T : ℝ) : ℝ) : ℂ) *
        fockAmplitude U S T := by
  have hs : (Real.sqrt (occFactorial S : ℝ) : ℂ) ≠ 0 := by exact_mod_cast rootNonzero S
  have ht : (Real.sqrt (occFactorial T : ℝ) : ℂ) ≠ 0 := by exact_mod_cast rootNonzero T
  unfold fockAmplitude
  rw [stateScaled S, stateScaled T, phiScale, pairScale]
  simp only [map_inv₀, Complex.conj_ofReal, Complex.ofReal_mul]
  field_simp

end Qatlib.Papers.LinearOptics10.StockmeyerSrc.FockNormalize
