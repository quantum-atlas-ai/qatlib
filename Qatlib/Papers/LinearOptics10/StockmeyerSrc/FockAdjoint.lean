/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.BosonFock.BosonOperators.WeightedPair
public import Qatlib.Papers.LinearOptics10.StockmeyerSrc.Defs

@[expose] public section


/-! # The actual finite Fock pairing has a unique adjoint

Fixed arXiv:1011.3245v1, Theorem 17. This result constructs the adjoint of
an arbitrary actual complex-linear map on coefficient vectors. Factorial
weights are nonzero, and no adjoint identity is assumed as a premise.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
namespace Qatlib.Papers.LinearOptics10.StockmeyerSrc.FockAdjoint
open Qatlib.Concepts.BosonFock.BosonOperators
open Qatlib.Papers.LinearOptics10.StockmeyerSrc

/-- Every actual occupation factorial weight is nonzero. -/
theorem weightNonzero {m n : ℕ} (S : FockOccupation m n) : (occFactorial S : ℝ) ≠ 0 := by
  have hw : occFactorial S ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => Nat.factorial_ne_zero _)
  exact_mod_cast hw

/-- The actual factorial-weighted Fock inner product gives each linear map a unique adjoint. -/
theorem adjointExists {m n : ℕ} (L : FockCoeff m n →ₗ[ℂ] FockCoeff m n) :
    ∃! D : FockCoeff m n →ₗ[ℂ] FockCoeff m n,
      ∀ p q, fockInner p (L q) = fockInner (D p) q := by
  exact Qatlib.Concepts.BosonFock.BosonOperators.WeightedPair.existsUnique
    (fun S => (occFactorial S : ℝ)) weightNonzero L

/-- An invertible actual linear map has the inverse-adjoint pairing of Theorem 17. -/
theorem invertiblePair {m n : ℕ} (e : FockCoeff m n ≃ₗ[ℂ] FockCoeff m n) :
    ∃ D : FockCoeff m n →ₗ[ℂ] FockCoeff m n,
      ∀ p q, fockInner p q = fockInner (D p) (e q) := by
  obtain ⟨D, hD, _⟩ := adjointExists e.symm.toLinearMap
  exact ⟨D, fun p q => by simpa using hD p (e q)⟩

end Qatlib.Papers.LinearOptics10.StockmeyerSrc.FockAdjoint
