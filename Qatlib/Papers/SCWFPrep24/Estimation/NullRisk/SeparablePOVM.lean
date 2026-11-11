/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SCWFPrep24.Estimation.NullRisk.TensorEffects
import Qatlib.Papers.SCWFPrep24.Estimation.NullRisk.SuppliedEffects
import QuantumInfo.Measurements.POVM

set_option backward.isDefEq.respectTransparency false

/-!
# Separable POVM

The actual finite separable effect is evaluated on two copies of one fixed hidden-phase input before the phase is averaged.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators ComplexOrder HermitianMat
namespace Qatlib.Papers.SCWFPrep24.Estimation.NullRisk

/-- The actual finite separable effect is evaluated on two copies of one fixed hidden-phase input before the phase is averaged. -/
theorem separable_effect_field_prior {A K : Type*} [Fintype A] [Fintype K]
    (E F : K → HermitianMat (A × Fin 2) ℂ) (v : A → Fin 2 → ℂ) :
    phaseMeanReal (fun ω => effectWeight (∑ k, E k ⊗ₖ F k)
      (pairedState (phasedFieldState v ω))) = ∑ k, fieldProductWeight (E k) (F k) v := by
  simp_rw [effectWeight_finite_separable_same_input, phaseMeanReal_sum]
  rfl

/-- The null prior of a literal two-copy effect uses the same six frames and shared phase assignments as the physical state preparation. -/
def nullSeparablePrior {A : Type*} [Fintype A]
    (L : HermitianMat ((A × Fin 2) × (A × Fin 2)) ℂ) (parity : A → Bool) : ℝ :=
  (∑ θ : Fin 3 × Bool, phaseMeanReal (fun ω => effectWeight L
    (pairedState (phasedFieldState (nullField parity θ.1 θ.2) ω))))/6

/-- The exact null finite separable-effect average is the sum of its positive product-effect averages. -/
theorem separable_effect_null_prior {A K : Type*} [Fintype A] [Fintype K]
    (E F : K → HermitianMat (A × Fin 2) ℂ) (parity : A → Bool) :
    nullSeparablePrior (∑ k, E k ⊗ₖ F k) parity = ∑ k, nullProductWeight (E k) (F k) parity := by
  unfold nullSeparablePrior nullProductWeight
  simp_rw [separable_effect_field_prior]
  rw [Finset.sum_comm]
  rw [Finset.sum_div]

/-- Every actual positive separable terminal effect obeys the physical prior domination on the two identical complete-address supplied copies. -/
theorem actual_separable_effect_prior_domination {A K : Type*} [Fintype A]
    [DecidableEq A] [Fintype K]
    (E F : K → HermitianMat (A × Fin 2) ℂ)
    (hE : ∀ k, 0 ≤ E k) (hF : ∀ k, 0 ≤ F k)
    (v : A → Fin 2 → ℂ) (hv : ∀ x, ∑ i, Complex.normSq (v x i) = 1)
    (parity : A → Bool) :
    phaseMeanReal (fun ω => effectWeight (∑ k, E k ⊗ₖ F k)
      (pairedState (phasedFieldState v ω))) ≤
      24*nullSeparablePrior (∑ k, E k ⊗ₖ F k) parity := by
  rw [separable_effect_field_prior, separable_effect_null_prior]
  exact actual_finite_product_sum_prior_domination E F hE hF parity v hv

/-- Every positive effect has nonnegative actual quadratic Born weight. -/
theorem effectWeight_nonneg {I : Type*} [Fintype I] [DecidableEq I]
    (E : HermitianMat I ℂ) (hE : 0 ≤ E) (ψ : I → ℂ) : 0 ≤ effectWeight E ψ := by
  rw [effectWeight_eq_gram_rows E hE]
  exact Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

/-- The identity effect has exactly the squared norm of the actual input vector. -/
theorem effectWeight_one {I : Type*} [Fintype I] [DecidableEq I] (ψ : I → ℂ) :
    effectWeight 1 ψ = ∑ i, Complex.normSq (ψ i) := by
  simp only [effectWeight, HermitianMat.mat_one, Matrix.one_mulVec, dotProduct,
    Complex.re_sum, Pi.star_apply, Complex.star_def, Complex.mul_re,
    Complex.conj_re, Complex.conj_im, neg_mul, sub_neg_eq_add, Complex.normSq_apply]

/-- The literal Born weights of the existing canonical POVM sum to one on every normalized vector. -/
theorem canonical_povm_effectWeight_sum {I O : Type*} [Fintype I] [DecidableEq I]
    [Fintype O] (P : POVM O I) (ψ : I → ℂ)
    (hψ : ∑ i, Complex.normSq (ψ i) = 1) :
    ∑ o, effectWeight (P.mats o) ψ = 1 := by
  rw [← effectWeight_sum, P.normalized, effectWeight_one, hψ]

/-- The existing canonical pure state of the supplied vector uses exactly its actual vector effect. -/
theorem canonical_pure_vectorEffect {I : Type*} [Fintype I] [DecidableEq I]
    (ψ : I → ℂ) (hψ : ∑ i, Complex.normSq (ψ i) = 1) :
    (MState.pure (⟨ψ, by simpa only [Complex.sq_norm] using hψ⟩ : Ket I)).M =
      vectorEffect ψ := by
  apply HermitianMat.ext
  ext i j
  rfl

/-- The literal quadratic probabilities agree with the existing canonical POVM measurement on the actual supplied pure state. -/
theorem canonical_povm_measure_eq_effectWeight {I O : Type*} [Fintype I]
    [DecidableEq I] [Fintype O] [DecidableEq O]
    (P : POVM O I) (ψ : I → ℂ) (hψ : ∑ i, Complex.normSq (ψ i) = 1) (o : O) :
    P.measure (MState.pure (⟨ψ, by simpa only [Complex.sq_norm] using hψ⟩ : Ket I)) o =
      effectWeight (P.mats o) ψ := by
  change inner ℝ (P.mats o) (MState.pure
    (⟨ψ, by simpa only [Complex.sq_norm] using hψ⟩ : Ket I)).M = _
  rw [canonical_pure_vectorEffect ψ hψ, HermitianMat.inner_comm, ← effectWeight_eq_vector_inner]

/-- Pairing two identical normalized supplied vectors produces a normalized actual two-copy vector. -/
theorem pairedState_normalized {I : Type*} [Fintype I] (ψ : I → ℂ)
    (hψ : ∑ i, Complex.normSq (ψ i) = 1) :
    ∑ z, Complex.normSq (pairedState ψ z) = 1 := by
  simp only [pairedState, Complex.normSq_mul, Fintype.sum_prod_type,
    ← Finset.mul_sum, hψ, mul_one]

/-- For an existing canonical finite POVM whose terminal effects admit finite PSD product decompositions, actual two-copy Born laws satisfy the derived physical-prior bound at every terminal outcome. -/
theorem canonical_separable_povm_prior_domination {A O K : Type*}
    [Fintype A] [DecidableEq A] [Fintype O] [Fintype K]
    (P : POVM O ((A × Fin 2) × (A × Fin 2)))
    (E F : O → K → HermitianMat (A × Fin 2) ℂ)
    (hE : ∀ o k, 0 ≤ E o k) (hF : ∀ o k, 0 ≤ F o k)
    (hsep : ∀ o, P.mats o = ∑ k, E o k ⊗ₖ F o k)
    (v : A → Fin 2 → ℂ) (hv : ∀ x, ∑ i, Complex.normSq (v x i) = 1)
    (parity : A → Bool) (o : O) :
    phaseMeanReal (fun ω => effectWeight (P.mats o)
      (pairedState (phasedFieldState v ω))) ≤ 24*nullSeparablePrior (P.mats o) parity := by
  rw [hsep]
  exact actual_separable_effect_prior_domination (E o) (F o) (hE o) (hF o) v hv parity

end Qatlib.Papers.SCWFPrep24.Estimation.NullRisk
