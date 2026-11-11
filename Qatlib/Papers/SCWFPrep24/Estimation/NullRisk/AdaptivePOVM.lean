/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SCWFPrep24.Estimation.NullRisk.SeparablePOVM

set_option backward.isDefEq.respectTransparency false

/-!
# Adaptive POVM

Tensoring a fixed Hermitian effect commutes with the actual finite sum on the second register.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators ComplexOrder HermitianMat
namespace Qatlib.Papers.SCWFPrep24.Estimation.NullRisk

/-- Tensoring a fixed Hermitian effect commutes with the actual finite sum on the second register. -/
theorem effect_kronecker_sum {I K : Type*} [Fintype I] [Fintype K]
    (E : HermitianMat I ℂ) (F : K → HermitianMat I ℂ) :
    (∑ k, E ⊗ₖ F k) = E ⊗ₖ (∑ k, F k) := by
  apply HermitianMat.ext
  ext i j
  rcases i with ⟨i₁,i₂⟩
  rcases j with ⟨j₁,j₂⟩
  simp only [HermitianMat.mat_finset_sum, HermitianMat.kronecker_mat,
    Matrix.sum_apply, Matrix.kronecker_apply, Finset.mul_sum]

/-- Tensoring with a fixed Hermitian effect commutes with the actual finite sum on the first register. -/
theorem effect_sum_kronecker {I K : Type*} [Fintype I] [Fintype K]
    (E : K → HermitianMat I ℂ) (F : HermitianMat I ℂ) :
    (∑ k, E k ⊗ₖ F) = (∑ k, E k) ⊗ₖ F := by
  apply HermitianMat.ext
  ext i j
  rcases i with ⟨i₁,i₂⟩
  rcases j with ⟨j₁,j₂⟩
  simp only [HermitianMat.mat_finset_sum, HermitianMat.kronecker_mat,
    Matrix.sum_apply, Matrix.kronecker_apply, Finset.sum_mul]

/-- The existing canonical POVM for a full-register first measurement followed by an arbitrary outcome-dependent full-register second measurement on the other supplied copy. -/
def adaptiveTwoCopyPOVM {I X Y : Type*} [Fintype I] [DecidableEq I]
    [Fintype X] [Fintype Y] (P : POVM X I) (Q : X → POVM Y I) : POVM (X × Y) (I × I) where
  mats z := P.mats z.1 ⊗ₖ (Q z.1).mats z.2
  nonneg z := HermitianMat.kronecker_nonneg (P.nonneg z.1) ((Q z.1).nonneg z.2)
  normalized := by
    simp only [Fintype.sum_prod_type, effect_kronecker_sum, POVM.normalized,
      effect_sum_kronecker, HermitianMat.kronecker_one_one]

/-- The actual two-copy terminal Born probability is the product for the chosen first outcome and its conditional second POVM, without fixing or measuring an address beforehand. -/
theorem adaptiveTwoCopyPOVM_probability {I X Y : Type*} [Fintype I] [DecidableEq I]
    [Fintype X] [Fintype Y] (P : POVM X I) (Q : X → POVM Y I)
    (ψ : I → ℂ) (z : X × Y) :
    effectWeight ((adaptiveTwoCopyPOVM P Q).mats z) (pairedState ψ) =
      effectWeight (P.mats z.1) ψ*effectWeight ((Q z.1).mats z.2) ψ :=
  effectWeight_kronecker_same_input _ _ _

/-- Every outcome of this actual finite adaptive canonical measurement satisfies the shared-phase six-frame domination derived from the positive effects. -/
theorem adaptiveTwoCopyPOVM_prior_domination {A X Y : Type*} [Fintype A]
    [DecidableEq A] [Fintype X] [Fintype Y]
    (P : POVM X (A × Fin 2)) (Q : X → POVM Y (A × Fin 2))
    (v : A → Fin 2 → ℂ) (hv : ∀ x, ∑ i, Complex.normSq (v x i) = 1)
    (parity : A → Bool) (z : X × Y) :
    phaseMeanReal (fun ω => effectWeight ((adaptiveTwoCopyPOVM P Q).mats z)
      (pairedState (phasedFieldState v ω))) ≤
      24*nullSeparablePrior ((adaptiveTwoCopyPOVM P Q).mats z) parity := by
  simp_rw [adaptiveTwoCopyPOVM_probability]
  change fieldProductWeight (P.mats z.1) ((Q z.1).mats z.2) v ≤ _
  have hn : nullSeparablePrior ((adaptiveTwoCopyPOVM P Q).mats z) parity =
      nullProductWeight (P.mats z.1) ((Q z.1).mats z.2) parity := by
    unfold nullSeparablePrior nullProductWeight fieldProductWeight
    simp only [adaptiveTwoCopyPOVM_probability]
  rw [hn]
  exact actual_positive_effect_prior_domination _ _ (P.nonneg _) ((Q _).nonneg _) parity v hv

end Qatlib.Papers.SCWFPrep24.Estimation.NullRisk
