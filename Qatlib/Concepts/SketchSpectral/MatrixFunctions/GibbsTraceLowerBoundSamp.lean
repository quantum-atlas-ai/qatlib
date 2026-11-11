/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SketchSpectral.MatrixFunctions.GibbsTraceLowerBoundStat
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Spectral formulas and a Gibbs trace lower bound

The module expresses the real exponential trace and squared Frobenius norm of a Hermitian matrix
in terms of its ordered eigenvalues. `gibbsTraceLowerBound` uses these formulas to lower-bound
the exponential trace by half the dimension under a squared Frobenius-energy bound, supporting
the partition-function analysis in [ChiaEtAl2022].

## Main statements

* `hermitian_exp_trace`: The real trace of the exponential of a Hermitian matrix is the sum of
  the exponentials of its ordered eigenvalues.
* `hermitian_frobenius_sq`: The squared Frobenius norm of a Hermitian matrix equals the sum of
  squares of its ordered eigenvalues.
* `gibbsTraceLowerBound`: If a Hermitian matrix has squared Frobenius norm at most one quarter
  of its dimension, its real exponential trace is at least half its dimension. See
  [ChiaEtAl2022].

## References

* [Chia et al., 2022][ChiaEtAl2022]
-/

set_option warningAsError false

open Qatlib.Concepts.SpectralSketch.SpectrumPerturb
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

namespace Qatlib.Concepts.SketchSpectral.MatrixFunctions
open Matrix NormedSpace Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Matrix.Norms.L2Operator

/-- The real trace of the exponential of a Hermitian matrix is the sum of the exponentials of
its ordered eigenvalues. -/
theorem hermitian_exp_trace {I : Type} [Fintype I] [DecidableEq I]
    (H : Matrix I I ℂ) (hH : H.IsHermitian) :
    (Matrix.trace (exp H)).re = ∑ i, Real.exp (orderedHermitianValues hH i) := by
  let U := Unitary.toUnits hH.eigenvectorUnitary
  have hd : H = (U : Matrix I I ℂ) * Matrix.diagonal (fun i => (hH.eigenvalues i : ℂ)) *
      (↑U⁻¹ : Matrix I I ℂ) := hH.spectral_theorem
  conv_lhs => rw [hd, Matrix.exp_units_conj, Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  simp only [Units.inv_mul, Matrix.one_mul, Matrix.exp_diagonal, Matrix.trace_diagonal,
    Complex.re_sum, Pi.exp_def, ← Complex.exp_eq_exp_ℂ, Complex.exp_ofReal_re]
  exact (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card I))).symm.sum_comp
    (fun i => Real.exp (orderedHermitianValues hH i))

/-- The squared Frobenius norm of a Hermitian matrix equals the sum of squares of its ordered
eigenvalues. -/
theorem hermitian_frobenius_sq {I : Type} [Fintype I] [DecidableEq I]
    (H : Matrix I I ℂ) (hH : H.IsHermitian) :
    spectralFrobenius H ^ 2 = ∑ i, orderedHermitianValues hH i ^ 2 := by
  have hb := spectralFrobenius_bases H (orderedHermitianBasis hH) (orderedHermitianBasis hH)
  have hd := congrArg (fun M => (basisColumns (orderedHermitianBasis hH))ᴴ * M *
    basisColumns (orderedHermitianBasis hH)) (orderedHermitian_diagonal hH)
  simp only [basis_adjoint_mul_spectralDiagonal, Matrix.mul_assoc,
    basisColumns_adjoint_mul, Matrix.mul_one] at hd
  rw [Matrix.mul_assoc, hd] at hb
  rw [← hb, spectralFrobenius_sq]
  simp only [Matrix.diagonal_apply, apply_ite Complex.normSq, Complex.normSq_zero,
    Complex.normSq_ofReal, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp only [pow_two]

/-- If a Hermitian matrix has squared Frobenius norm at most one quarter of its dimension, its
real exponential trace is at least half its dimension. See [ChiaEtAl2022]. -/
theorem gibbsTraceLowerBound : GibbsTraceLowerBound := by
  intro I _ _ H hH henergy
  rw [hermitian_exp_trace H hH]
  rw [hermitian_frobenius_sq H hH] at henergy
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin (Fintype.card I)))
    (fun _ => (1 : ℝ)) (orderedHermitianValues hH)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] at hc
  have hn : 0 ≤ (Fintype.card I : ℝ) := Nat.cast_nonneg _
  have hs : -(Fintype.card I : ℝ) / 2 ≤ ∑ i, orderedHermitianValues hH i := by
    have := mul_le_mul_of_nonneg_left henergy hn
    nlinarith [sq_nonneg ((∑ i, orderedHermitianValues hH i) + (Fintype.card I : ℝ)/2)]
  have he := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => Real.add_one_le_exp (orderedHermitianValues hH i))
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one] at he
  linarith
end Qatlib.Concepts.SketchSpectral.MatrixFunctions
