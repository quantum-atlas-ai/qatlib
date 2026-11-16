/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.LinearOptics10.StockmeyerSrc.FockModel

@[expose] public section


/-! # The genuine polynomial substitution action and its actual inverse

Coefficient readback reconstructs every homogeneous polynomial. Composition
of actual row-mode substitutions reverses matrix multiplication, so a
unitary matrix acts bijectively with its conjugate transpose as inverse.
This does not assume or prove weighted-inner-product invariance.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical Matrix ComplexConjugate
open MvPolynomial
namespace Qatlib.Papers.LinearOptics10.StockmeyerSrc.FockAction
open Qatlib.Papers.LinearOptics10.StockmeyerSrc
open FockModel

/-- The identity mode matrix gives the actual identity polynomial substitution. -/
theorem substIdentity {m : ℕ} (p : MvPolynomial (Fin m) ℂ) :
    substPoly (1 : Matrix (Fin m) (Fin m) ℂ) p = p := by
  have h (i : Fin m) :
      (∑ j, C ((1 : Matrix (Fin m) (Fin m) ℂ) i j) * X j) = X i := by
    simp [Matrix.one_apply]
  unfold substPoly
  simp_rw [h]
  exact aeval_X_left_apply p

/-- Actual row-mode substitutions compose with the reversed matrix product. -/
theorem substCompose {m : ℕ} (U V : Matrix (Fin m) (Fin m) ℂ)
    (p : MvPolynomial (Fin m) ℂ) :
    substPoly U (substPoly V p) = substPoly (V*U) p := by
  have h (i : Fin m) :
      aeval (fun j => ∑ k, C (U j k) * X k) (∑ j, C (V i j) * X j) =
        ∑ k, C ((V*U) i k) * X k := by
    simp only [map_sum, map_mul, aeval_C, algebraMap_eq, aeval_X, Matrix.mul_apply,
      Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp only [mul_assoc]
  unfold substPoly
  rw [comp_aeval_apply]
  simp_rw [h]

/-- Homogeneous coefficient readback makes the identity matrix act identically. -/
theorem phiIdentity {m n : ℕ} (a : FockCoeff m n) :
    phi (1 : Matrix (Fin m) (Fin m) ℂ) a = a := by
  apply polyInjective
  rw [substCommutes, substIdentity]

/-- The actual coefficient action inherits the true reversed composition law. -/
theorem phiCompose {m n : ℕ} (U V : Matrix (Fin m) (Fin m) ℂ) (a : FockCoeff m n) :
    phi U (phi V a) = phi (V*U) a := by
  apply polyInjective
  rw [substCommutes, substCommutes, substCompose, substCommutes]

/-- A genuine unitary mode matrix and its dagger give actual inverse coefficient actions. -/
theorem phiInverse {m n : ℕ} (U : Matrix (Fin m) (Fin m) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin m) ℂ) (a : FockCoeff m n) :
    phi Uᴴ (phi U a) = a ∧ phi U (phi Uᴴ a) = a := by
  have hleft : U*Uᴴ = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff.mp hU)
  have hright : Uᴴ*U = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff'.mp hU)
  constructor
  · rw [phiCompose, hleft, phiIdentity]
  · rw [phiCompose, hright, phiIdentity]

/-- Every genuine unitary mode matrix acts bijectively in every actual finite particle sector. -/
theorem phiBijective {m n : ℕ} (U : Matrix (Fin m) (Fin m) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin m) ℂ) :
    Function.Bijective (phi (m := m) (n := n) U) := by
  constructor
  · exact Function.LeftInverse.injective (fun a => (phiInverse U hU a).1)
  · intro b
    exact ⟨phi Uᴴ b, (phiInverse U hU b).2⟩

end Qatlib.Papers.LinearOptics10.StockmeyerSrc.FockAction
