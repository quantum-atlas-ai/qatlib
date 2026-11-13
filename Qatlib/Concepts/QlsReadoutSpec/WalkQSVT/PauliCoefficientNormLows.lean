/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QlsReadoutSpec.WalkQSVT.PauliCoefficientNormStat

/-!
# Norms of real Pauli coefficient matrices

This module computes the Gram matrix of `pauliCoefficients` and the operator norm of the
difference of two such matrices. The latter equals the Euclidean distance between their four
real coefficient vectors. Related mathematical background is given in [LowSu2026].

## Main statements

* `pauli_gram`: The Gram matrix is a scalar multiple of the identity.
* `Clause13PauliCoefficientNorm_answer`: The coefficient-distance identity of Lemma 21.

## References

* [Low and Su, 2026, Lemma 21][LowSu2026]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.QlsReadoutSpec.Amplification
open Qatlib.Concepts.QlsReadoutSpec.WalkQSVT

namespace Qatlib.Concepts.QlsReadoutSpec.WalkQSVT

open Matrix Qatlib.Concepts.QlsReadoutSpec.Amplification Qatlib.Concepts.QlsReadoutSpec.WalkQSVT
open scoped Classical BigOperators Matrix.Norms.L2Operator

/-- The square of the complex imaginary unit is minus one. -/
private theorem I_sq : Complex.I ^ 2 = -1 := by
  rw [pow_two, Complex.I_mul_I]

/-- The Gram matrix of the real Pauli coefficient matrix is the identity scaled by the sum of
the four squared coefficients. -/
private theorem pauli_gram (a b c d : ℝ) :
    (pauliCoefficients a b c d)ᴴ * pauliCoefficients a b c d
      = (((a^2+b^2+c^2+d^2 : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    norm_num [Matrix.mul_apply, Matrix.conjTranspose_apply, pauliCoefficients,
      Matrix.of_apply, one_apply, Matrix.smul_apply, Fin.sum_univ_two,
      Complex.ext_iff, Complex.mul_re, Complex.mul_im, Complex.add_re,
      Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.ofReal_pow, Complex.ofReal_add, Complex.ofReal_mul,
      map_add, map_sub, map_mul, star_trivial,
      Complex.conj_I, I_sq, Complex.I_re, Complex.I_im, ← Complex.ofReal_pow,
      and_true, true_and, and_self_iff]
  all_goals
    apply And.intro
  all_goals
    first | trivial | ring

/-- The difference of two Pauli coefficient matrices is the Pauli coefficient matrix of their
coefficient differences. -/
private theorem pauli_diff_form (a b c d a' b' c' d' : ℝ) :
    pauliCoefficients a b c d - pauliCoefficients a' b' c' d'
      = pauliCoefficients (a-a') (b-b') (c-c') (d-d') := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pauliCoefficients, Matrix.sub_apply, Matrix.of_apply,
      Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_sub] <;>
    ring

/-- The operator-norm distance between two real Pauli coefficient matrices equals the Euclidean
distance of their coefficient vectors, and each Gram matrix is the stated scalar identity.
See [Low and Su, Lemma 21][LowSu2026]. -/
theorem Clause13PauliCoefficientNorm_answer : Clause13PauliCoefficientNorm := by
  intro a b c d a' b' c' d'
  have hgramSelf := pauli_gram a b c d
  have hform := pauli_diff_form a b c d a' b' c' d'
  have hgram : (pauliCoefficients a b c d - pauliCoefficients a' b' c' d')ᴴ *
      (pauliCoefficients a b c d - pauliCoefficients a' b' c' d')
      = ((((a-a')^2+(b-b')^2+(c-c')^2+(d-d')^2 : ℝ) : ℂ) •
          (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
    rw [hform]
    exact pauli_gram (a-a') (b-b') (c-c') (d-d')
  refine ⟨?_, hgramSelf⟩
  have hnn : (0 : ℝ) ≤ (a-a')^2+(b-b')^2+(c-c')^2+(d-d')^2 :=
    add_nonneg (add_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _)) (sq_nonneg _)
  have hsq : ‖pauliCoefficients a b c d - pauliCoefficients a' b' c' d'‖ ^ 2
      = (a-a')^2+(b-b')^2+(c-c')^2+(d-d')^2 := by
    have h := Matrix.l2_opNorm_conjTranspose_mul_self
      (pauliCoefficients a b c d - pauliCoefficients a' b' c' d')
    rw [hgram] at h
    rw [norm_smul, l2_norm_one_eq, mul_one] at h
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn] at h
    rw [pow_two]
    exact h.symm
  have hnormnn : 0 ≤ ‖pauliCoefficients a b c d - pauliCoefficients a' b' c' d'‖ :=
    norm_nonneg _
  have hsqrt : (Real.sqrt ((a-a')^2+(b-b')^2+(c-c')^2+(d-d')^2)) ^ 2
      = (a-a')^2+(b-b')^2+(c-c')^2+(d-d')^2 :=
    Real.sq_sqrt hnn
  exact (sq_eq_sq₀ hnormnn (Real.sqrt_nonneg _)).mp (hsq.trans hsqrt.symm)

end Qatlib.Concepts.QlsReadoutSpec.WalkQSVT
