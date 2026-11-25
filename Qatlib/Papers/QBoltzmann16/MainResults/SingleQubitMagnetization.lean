/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QBoltzmann16.MainResults.VisibleSector
public import Qatlib.Concepts.GateVocabulary.GateVocab.GateVocabulary
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.Tactic

@[expose] public section

/-!
# `Z` magnetization of one hidden qubit

The semi-restricted model of [AminEtAl2018] decouples every hidden qubit into a two-level
transverse-field term `- (Γ σx + b σz)`. This module computes its Gibbs average of `σz` in closed
form, `⟨σz⟩ = (b / D) tanh D` with `D = sqrt (Γ² + b²)`, including the value `0` on the degenerate
branch `D = 0`, where the fraction printed as Eq (36) has a zero denominator.

The computation rests on the matrix-exponential identity
`exp A = cosh D • 1 + (sinh D / D) • A` for a complex matrix with `A * A = D² • 1` and `D ≠ 0`,
obtained from the parity split of the exponential series, together with the explicit two-by-two
Pauli matrices of `Qatlib.Concepts.GateVocabulary.GateVocab.pauliFin`. The scalar factor
`(b / D) tanh D` is the continuous extension of that Gibbs average to `D = 0`.

Uncovered boundaries: the identity concerns the decoupled two-level summand only. It does not
prove the hidden-qubit factorization of the whole clamped Hamiltonian, the classical `Γ → 0` limit
of the semi-restricted model, or any parameter update of the training law.

## Main statements

* `exp_of_sq_eq_smul_one`: closed form of `exp A` when `A * A = c • 1` at `c > 0`.
* `singleQubit_z_magnetization`: `⟨σz⟩ = (b / D) tanh D` for the two-level term `-(Γ σx + b σz)`.

## References

* [Amin et al., 2018][AminEtAl2018]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators ComplexOrder Matrix Matrix.Norms.L2Operator

namespace Qatlib.Papers.QBoltzmann16.MainResults

open Qatlib.Foundations.PureStateMath Qatlib.Concepts.GateVocabulary.GateVocab
open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Papers.QBoltzmann16.MainResults

/-! ## Exponentiation of matrices whose square is a scalar multiple of the identity -/

/-- For a matrix `A` with `A * A = D² • 1`, every even power of `A` is the corresponding power of
`D` times the identity, and every odd power is the corresponding power of `D` times `A`. -/
theorem sq_eq_smul_one_pow {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (D : ℝ)
    (hA : A * A = ((D : ℂ) ^ 2) • (1 : Matrix (Fin n) (Fin n) ℂ)) (k : ℕ) :
    A ^ (2 * k) = ((D : ℂ) ^ (2 * k)) • (1 : Matrix (Fin n) (Fin n) ℂ) ∧
      A ^ (2 * k + 1) = ((D : ℂ) ^ (2 * k)) • A := by
  induction k with
  | zero => simp
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    have heven : A ^ (2 * (k + 1)) = ((D : ℂ) ^ (2 * (k + 1))) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
      rw [show 2 * (k + 1) = 2 * k + 1 + 1 from by omega, pow_succ, h2, Matrix.smul_mul, hA,
        smul_smul, ← pow_add, show 2 * k + 2 = 2 * (k + 1) from by omega]
    have hodd : A ^ (2 * (k + 1) + 1) = ((D : ℂ) ^ (2 * (k + 1))) • A := by
      rw [pow_succ, heven, Matrix.smul_mul, Matrix.one_mul]
    exact ⟨heven, hodd⟩

/-- If `A * A = D² • 1`, the even terms of the exponential series of `A` are the even terms of the
hyperbolic cosine series at `D`, multiplied by the identity. -/
theorem expSeries_even_of_sq_eq_smul_one {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (D : ℝ)
    (hA : A * A = ((D : ℂ) ^ 2) • (1 : Matrix (Fin n) (Fin n) ℂ)) (k : ℕ) :
    NormedSpace.expSeries ℂ (Matrix (Fin n) (Fin n) ℂ) (2 * k) (fun _ => A) =
      ((D : ℂ) ^ (2 * k) / (Nat.factorial (2 * k) : ℂ)) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  rw [NormedSpace.expSeries_apply_eq, (sq_eq_smul_one_pow A D hA k).1, smul_smul,
    div_eq_mul_inv, mul_comm]

/-- If `A * A = D² • 1`, the odd terms of the exponential series of `A` are the even-index terms of
the hyperbolic sine series at `D`, multiplied by `A`. -/
theorem expSeries_odd_of_sq_eq_smul_one {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (D : ℝ)
    (hA : A * A = ((D : ℂ) ^ 2) • (1 : Matrix (Fin n) (Fin n) ℂ)) (k : ℕ) :
    NormedSpace.expSeries ℂ (Matrix (Fin n) (Fin n) ℂ) (2 * k + 1) (fun _ => A) =
      ((D : ℂ) ^ (2 * k) / (Nat.factorial (2 * k + 1) : ℂ)) • A := by
  rw [NormedSpace.expSeries_apply_eq, (sq_eq_smul_one_pow A D hA k).2, smul_smul,
    div_eq_mul_inv, mul_comm]

/-- The exponential series of a matrix with `A * A = D² • 1` and `D ≠ 0` sums to
`cosh D • 1 + (sinh D / D) • A`, obtained by splitting the series into its even and odd
subseries. -/
theorem hasSum_expSeries_of_sq_eq_smul_one {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) {D : ℝ}
    (hD : D ≠ 0) (hA : A * A = ((D : ℂ) ^ 2) • (1 : Matrix (Fin n) (Fin n) ℂ)) :
    HasSum (fun m => NormedSpace.expSeries ℂ (Matrix (Fin n) (Fin n) ℂ) m (fun _ => A))
      (Complex.cosh (D : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) +
        (Complex.sinh (D : ℂ) / (D : ℂ)) • A) := by
  have hDc : (D : ℂ) ≠ 0 := by
    simpa using hD
  have hsc (k : ℕ) : (D : ℂ) ^ (2 * k) / (Nat.factorial (2 * k + 1) : ℂ) =
      ((D : ℂ) ^ (2 * k + 1) / (Nat.factorial (2 * k + 1) : ℂ)) / (D : ℂ) := by
    rw [pow_succ, div_div, mul_div_mul_right]
    exact hDc
  refine HasSum.even_add_odd ?_ ?_
  · convert (Complex.hasSum_cosh (D : ℂ)).smul_const (1 : Matrix (Fin n) (Fin n) ℂ) using 1
    ext k
    rw [expSeries_even_of_sq_eq_smul_one A D hA k]
  · convert ((Complex.hasSum_sinh (D : ℂ)).div_const (D : ℂ)).smul_const A using 1
    ext k
    rw [expSeries_odd_of_sq_eq_smul_one A D hA k, hsc k]

/-- For a complex matrix `A` with `A * A = c • 1` and positive `c`, the matrix exponential is the
hyperbolic combination `cosh (sqrt c) • 1 + (sinh (sqrt c) / sqrt c) • A`. -/
theorem exp_of_sq_eq_smul_one {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) {c : ℝ} (hc : 0 < c)
    (hA : A * A = (c : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) :
    NormedSpace.exp A = (Real.cosh (Real.sqrt c) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) +
      ((Real.sinh (Real.sqrt c) / Real.sqrt c : ℝ) : ℂ) • A := by
  have hD : Real.sqrt c ≠ 0 := (Real.sqrt_pos.mpr hc).ne'
  have hsq : A * A = ((Real.sqrt c : ℂ) ^ 2) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    rw [hA, ← Complex.ofReal_pow, Real.sq_sqrt hc.le]
  have hsum := hasSum_expSeries_of_sq_eq_smul_one A hD hsq
  rw [NormedSpace.exp_eq_tsum ℂ]
  refine HasSum.tsum_eq ?_
  simp_rw [← NormedSpace.expSeries_apply_eq]
  simpa only [Complex.ofReal_cosh, Complex.ofReal_sinh, Complex.ofReal_div] using hsum

/-! ## The two-level transverse-field term -/

/-- The two-level transverse-field term `Γ σx + b σz` in the computational basis, written out
entrywise. -/
def singleQubitFieldMatrix (gamma bias : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(bias : ℂ), (gamma : ℂ); (gamma : ℂ), -(bias : ℂ)]

/-- The entrywise matrix display agrees with the Pauli combination `Γ σx + b σz` of the paper
conventions [AminEtAl2018], Eq (36). -/
theorem singleQubitFieldMatrix_eq (gamma bias : ℝ) :
    gamma • pauliFin 1 + bias • pauliFin 3 = singleQubitFieldMatrix gamma bias := by
  rw [pauliFin_legacy.1, pauliFin_legacy.2.2]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [singleQubitFieldMatrix, pauliX, pauliZ, Complex.real_smul]

/-- The two-level term squares to the scalar multiple `(Γ² + b²) • 1` of the identity. -/
theorem singleQubitFieldMatrix_mul_self (gamma bias : ℝ) :
    singleQubitFieldMatrix gamma bias * singleQubitFieldMatrix gamma bias =
      ((gamma ^ 2 + bias ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [singleQubitFieldMatrix, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- The two-level term is traceless. -/
theorem singleQubitFieldMatrix_trace (gamma bias : ℝ) :
    Matrix.trace (singleQubitFieldMatrix gamma bias) = 0 := by
  rw [Matrix.trace_fin_two]
  simp [singleQubitFieldMatrix]

/-- The product of the two-level term with `σz` has trace `2 b`, the numerator of the magnetization
[AminEtAl2018], Eq (36). -/
theorem singleQubitFieldMatrix_trace_mul_z (gamma bias : ℝ) :
    Matrix.trace (singleQubitFieldMatrix gamma bias * pauliFin 3) = 2 * (bias : ℂ) := by
  rw [pauliFin_legacy.2.2, Matrix.trace_fin_two]
  simp [singleQubitFieldMatrix, pauliZ, Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- The Pauli `Z` matrix is traceless. -/
theorem pauliFin_three_trace : Matrix.trace (pauliFin 3) = 0 := by
  rw [pauliFin_legacy.2.2, Matrix.trace_fin_two]
  simp [pauliZ]

/-- Multiplication by a complex scalar on the left of a two-by-two matrix product. -/
theorem smul_mul_fin_two (c : ℂ) (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    (c • A) * B = c • (A * B) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.smul_apply, Finset.mul_sum, smul_eq_mul, mul_assoc]

/-- The Gibbs average of `σz` in the decoupled hidden-qubit term `-(Γ σx + b σz)` equals
`(b / D) tanh D` with `D = sqrt (Γ² + b²)`, and equals `0` on the degenerate branch `D = 0`
[AminEtAl2018], Eq (36)-(37). -/
theorem singleQubit_z_magnetization (gamma bias : ℝ) :
    boltzmannAverage 2 (-(gamma • pauliFin 1 + bias • pauliFin 3)) (pauliFin 3) =
      if Real.sqrt (gamma ^ 2 + bias ^ 2) = 0 then 0
      else bias / Real.sqrt (gamma ^ 2 + bias ^ 2) *
        Real.tanh (Real.sqrt (gamma ^ 2 + bias ^ 2)) := by
  have hnorm_nonneg : (0 : ℝ) ≤ gamma ^ 2 + bias ^ 2 := by positivity
  rcases lt_or_eq_of_le hnorm_nonneg with hpos | hzero
  · have hsqrt_ne : Real.sqrt (gamma ^ 2 + bias ^ 2) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
    have hpow : singleQubitFieldMatrix gamma bias * singleQubitFieldMatrix gamma bias =
        ((gamma ^ 2 + bias ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) :=
      singleQubitFieldMatrix_mul_self gamma bias
    have hexp := exp_of_sq_eq_smul_one (singleQubitFieldMatrix gamma bias) hpos hpow
    have hnum : Matrix.trace (NormedSpace.exp (singleQubitFieldMatrix gamma bias) * pauliFin 3) =
        (((Real.sinh (Real.sqrt (gamma ^ 2 + bias ^ 2)) /
          Real.sqrt (gamma ^ 2 + bias ^ 2)) * (2 * bias) : ℝ) : ℂ) := by
      rw [hexp, Matrix.add_mul, smul_mul_fin_two, smul_mul_fin_two, Matrix.one_mul,
        Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, pauliFin_three_trace,
        singleQubitFieldMatrix_trace_mul_z]
      simp only [smul_eq_mul, mul_zero, zero_add, Complex.ofReal_mul, Complex.ofReal_div,
        Complex.ofReal_ofNat]
    have hden : Matrix.trace (NormedSpace.exp (singleQubitFieldMatrix gamma bias)) =
        ((Real.cosh (Real.sqrt (gamma ^ 2 + bias ^ 2)) * 2 : ℝ) : ℂ) := by
      have htr1 : Matrix.trace (1 : Matrix (Fin 2) (Fin 2) ℂ) = 2 := by
        rw [Matrix.trace_one]
        norm_num
      rw [hexp, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, htr1,
        singleQubitFieldMatrix_trace]
      simp only [smul_eq_mul, mul_zero, add_zero, Complex.ofReal_mul, Complex.ofReal_ofNat]
    rw [ite_eq_right hsqrt_ne, singleQubitFieldMatrix_eq]
    simp only [boltzmannAverage, gibbsPartition, neg_neg]
    rw [hnum, hden, Complex.ofReal_re, Complex.ofReal_re, Real.tanh_eq_sinh_div_cosh]
    have hcosh : Real.cosh (Real.sqrt (gamma ^ 2 + bias ^ 2)) ≠ 0 := (Real.cosh_pos _).ne'
    field_simp
  · have hgamma : gamma = 0 := by
      have hsq : gamma ^ 2 = 0 := by nlinarith [sq_nonneg gamma, sq_nonneg bias]
      exact (pow_eq_zero_iff (n := 2) (by norm_num)).mp hsq
    have hbias : bias = 0 := by
      have hsq : bias ^ 2 = 0 := by nlinarith [sq_nonneg gamma, sq_nonneg bias]
      exact (pow_eq_zero_iff (n := 2) (by norm_num)).mp hsq
    subst hgamma
    subst hbias
    rw [ite_eq_left (by simp)]
    simp only [boltzmannAverage, gibbsPartition, zero_smul, add_zero, neg_zero,
      NormedSpace.exp_zero, Matrix.one_mul, pauliFin_three_trace, Matrix.trace_one,
      Complex.zero_re, zero_div]

end Qatlib.Papers.QBoltzmann16.MainResults
