/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.GibbsSource.SourceForms.NormalizedPauli

@[expose] public section


/-!
# Normalization of the original complete local Pauli family

The physical proposals are Hermitian and their adjoint squares sum to the
identity for n > 0. The proof uses the same reindexed CSS matrices as the source
module. The scalar identity also fixes the factor `1/(3*n)` in source energies.
-/

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuantumGibbs.FormAlgebra
open Qatlib.Concepts.GibbsSource.FormAlgebra
open Qatlib.Concepts.CodingDecoding.CssTesters
open Matrix
open scoped BigOperators

namespace Qatlib.Concepts.GibbsSource.SourceForms

/-- Local Pauli X self mul for the stated finite source data. -/
theorem localPauliX_self_mul (n : ℕ) (i : Fin n) :
    fullPauliX n i * fullPauliX n i = 1 := by
  convert! congrArg (Matrix.reindexAlgEquiv ℂ ℂ (regIndexEquiv (Fin n)))
    (cssPauliX_self_mul (Pi.single i 1)) using 1 <;>
    simp only [map_mul, map_one, fullPauliX, fullPauliDim]
  all_goals rfl

/-- Local Pauli Z self mul for the stated finite source data. -/
theorem localPauliZ_self_mul (n : ℕ) (i : Fin n) :
    fullPauliZ n i * fullPauliZ n i = 1 := by
  convert! congrArg (Matrix.reindexAlgEquiv ℂ ℂ (regIndexEquiv (Fin n)))
    (cssPauliZ_self_mul (Pi.single i 1)) using 1 <;>
    simp only [map_mul, map_one, fullPauliZ, fullPauliDim]
  all_goals rfl

/-- Local Pauli Y self mul for the stated finite source data. -/
theorem localPauliY_self_mul (n : ℕ) (i : Fin n) :
    fullPauliY n i * fullPauliY n i = 1 := by
  unfold fullPauliY
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Complex.I_mul_I]
  have h : (fullPauliX n i * fullPauliZ n i) *
      (fullPauliX n i * fullPauliZ n i) = -(1 : Operator (fullPauliDim n)) := by
    calc
      _ = fullPauliX n i * (fullPauliZ n i * fullPauliX n i) * fullPauliZ n i := by
        simp only [Matrix.mul_assoc]
      _ = fullPauliX n i * (-(fullPauliX n i * fullPauliZ n i)) * fullPauliZ n i := by
        rw [fullPauliZ_mul_X]
      _ = -(fullPauliX n i * fullPauliX n i * (fullPauliZ n i * fullPauliZ n i)) := by
        simp only [mul_neg, neg_mul, Matrix.mul_assoc]
      _ = -1 := by rw [localPauliX_self_mul, localPauliZ_self_mul, Matrix.mul_one]
  rw [h]
  simp

/-- Local Pauli Matrix self mul for the stated finite source data. -/
theorem localPauliMatrix_self_mul (n : ℕ) (p : Fin n × Fin 3) :
    fullPauliFamily n p * fullPauliFamily n p = 1 := by
  unfold fullPauliFamily
  split_ifs
  · exact localPauliX_self_mul n p.1
  · exact localPauliY_self_mul n p.1
  · exact localPauliZ_self_mul n p.1

/-- The real Pauli normalization is fixed by complex conjugation. -/
@[simp] theorem star_localPauliScale (n : ℕ) :
    star (localPauliScale n) = localPauliScale n := by
  simp [localPauliScale]

/-- Exact scalar normalization used by the physical source energy. -/
theorem localPauliScale_mul_self {n : ℕ} (hn : 0 < n) :
    localPauliScale n * localPauliScale n = (((3 * (n : ℝ))⁻¹ : ℝ) : ℂ) := by
  have hz : 0 ≤ 3 * (n : ℝ) := le_of_lt (mul_pos (by norm_num) (Nat.cast_pos.mpr hn))
  unfold localPauliScale
  rw [← Complex.ofReal_mul, ← pow_two, inv_pow, Real.sq_sqrt hz]

/-- Normalized Local Pauli is Hermitian for the stated finite source data. -/
theorem normalizedLocalPauli_isHermitian (n : ℕ) (p : Fin n × Fin 3) :
    (normalizedLocalPauli n p).IsHermitian := by
  change (localPauliScale n • fullPauliFamily n p)ᴴ =
    localPauliScale n • fullPauliFamily n p
  rw [Matrix.conjTranspose_smul, star_localPauliScale, fullPauliFamily_isHermitian]

/-- Normalized Local Pauli adjoint mul for the stated finite source data. -/
theorem normalizedLocalPauli_adjoint_mul {n : ℕ} (hn : 0 < n)
    (p : Fin n × Fin 3) :
    (normalizedLocalPauli n p)ᴴ * normalizedLocalPauli n p =
      (((3 * (n : ℝ))⁻¹ : ℝ) : ℂ) • (1 : Operator (fullPauliDim n)) := by
  have hP : (fullPauliFamily n p)ᴴ = fullPauliFamily n p :=
    fullPauliFamily_isHermitian n p
  simp only [normalizedLocalPauli, Matrix.conjTranspose_smul, star_localPauliScale,
    hP, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    localPauliScale_mul_self hn, localPauliMatrix_self_mul]

/-- The complete `3n` normalized proposal family satisfies the physical normalization. -/
theorem sum_normalizedLocalPauli_adjoint_mul {n : ℕ} (hn : 0 < n) :
    ∑ p : Fin n × Fin 3, (normalizedLocalPauli n p)ᴴ * normalizedLocalPauli n p =
      (1 : Operator (fullPauliDim n)) := by
  classical
  simp_rw [normalizedLocalPauli_adjoint_mul hn]
  rw [← Finset.sum_smul]
  have hsum : (∑ _p : Fin n × Fin 3, (((3 * (n : ℝ))⁻¹ : ℝ) : ℂ)) = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, card_localPauliLabels, nsmul_eq_mul]
    push_cast
    exact mul_inv_cancel₀ (mul_ne_zero (by norm_num : (3 : ℂ) ≠ 0)
      (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)))
  rw [hsum, one_smul]

end Qatlib.Concepts.GibbsSource.SourceForms
