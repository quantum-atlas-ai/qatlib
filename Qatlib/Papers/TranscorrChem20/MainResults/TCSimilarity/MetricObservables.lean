/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.TranscorrChem20.MainResults.TCSimilarity.Basic
import Qatlib.Concepts.ImaginaryFlow.Similarity.MatrixAction

/-!
# Transcorrelated metrics and observable readout

This module defines the metric `tcMetric g` induced by the exponential change of variables. It
relates physical observable expectations to metric-weighted transcorrelated expectations, proves
positivity on nonzero states, and connects right eigenvectors to eigenvectors of the adjoint for
a Hermitian original Hamiltonian. See [McArdleTew2020].

## Main statements

* `metric_normalized_observable`: Equality of normalized physical and metric-weighted readout.
* `metric_quasi_hermitian`: The adjoint intertwining identity for a Hermitian Hamiltonian.
* `metric_left_eigenvector`: Metric transport to an adjoint eigenvector equation.

## References

* [McArdle and Tew, 2020][McArdleTew2020]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section
open Matrix NormedSpace
open Qatlib.Concepts.ImaginaryFlow.Similarity
open Qatlib.Papers.TranscorrChem20.MainResults.ImaginaryTime

namespace Qatlib.Papers.TranscorrChem20.MainResults.TCSimilarity

/-- The metric matrix `(exp g).conjTranspose * exp g` induced by the correlator exponential. -/
def tcMetric {d : ℕ} (g : Op d) : Op d := (exp g).conjTranspose * exp g

/-- For Hermitian `g`, the metric equals the square of `exp g`. See [McArdleTew2020]. -/
theorem tcMetric_eq_square {d : ℕ} (g : Op d) (hg : g.IsHermitian) :
    tcMetric g = exp g ^ 2 := by rw [tcMetric, hg.exp.eq, pow_two]

/-- Multiplying a transcorrelated observable by the metric gives the physical congruence `(exp
g).conjTranspose * O * exp g`. -/
theorem metric_observable_matrix {d : ℕ} (g O : Op d) :
    tcMetric g * tc O g = (exp g).conjTranspose * O * exp g := by
  calc
    _ = (exp g).conjTranspose * (exp g * exp (-g)) * O * exp g := by
      simp only [tcMetric, tc, Matrix.mul_assoc]
    _ = _ := by rw [(actual_exp_inverse g).2]; simp

/-- The physical observable quadratic form on the transported state equals the metric-weighted
transcorrelated observable form. -/
theorem metric_observable_form {d : ℕ} (g O : Op d) (φ : State d) :
    inner ℂ (expEquiv g φ) (Matrix.toEuclideanLin O (expEquiv g φ)) =
      inner ℂ φ (Matrix.toEuclideanLin (tcMetric g * tc O g) φ) := by
  change inner ℂ (Matrix.toEuclideanLin (exp g) φ)
    (Matrix.toEuclideanLin O (Matrix.toEuclideanLin (exp g) φ)) = _
  rw [inner_matrix_adjoint, ← matrix_action_mul, ← matrix_action_mul,
    metric_observable_matrix]

/-- The metric quadratic form of a state equals the squared norm of its image under `expEquiv
g`. -/
theorem metric_norm_form {d : ℕ} (g : Op d) (φ : State d) :
    inner ℂ φ (Matrix.toEuclideanLin (tcMetric g) φ) = (‖expEquiv g φ‖^2 : ℂ) := by
  have h := metric_observable_form g (1 : Op d) φ
  have ht : tc (1 : Op d) g = 1 := by
    simpa only [tc, Matrix.mul_one] using (actual_exp_inverse g).1
  simpa only [ht, Matrix.mul_one, matrix_action_one, inner_self_eq_norm_sq_to_K] using! h.symm

/-- The real part of the metric quadratic form is strictly positive on every nonzero state. See
[McArdleTew2020]. -/
theorem metric_norm_pos {d : ℕ} (g : Op d) (φ : State d) (hφ : φ ≠ 0) :
    0 < (inner ℂ φ (Matrix.toEuclideanLin (tcMetric g) φ)).re := by
  rw [metric_norm_form]
  have hn : expEquiv g φ ≠ 0 := by
    intro hz
    apply hφ
    exact (expEquiv g).injective (by simpa using hz)
  simpa only [← Complex.ofReal_pow, Complex.ofReal_re] using sq_pos_of_pos (norm_pos_iff.mpr hn)

/-- The physical expectation divided by the transported squared norm equals the metric-weighted
transcorrelated expectation divided by the metric norm form. See [McArdleTew2020]. -/
theorem metric_normalized_observable {d : ℕ} (g O : Op d) (φ : State d) :
    inner ℂ (expEquiv g φ) (Matrix.toEuclideanLin O (expEquiv g φ)) / (‖expEquiv g φ‖^2 : ℂ) =
      inner ℂ φ (Matrix.toEuclideanLin (tcMetric g * tc O g) φ) /
        inner ℂ φ (Matrix.toEuclideanLin (tcMetric g) φ) := by
  rw [metric_observable_form, metric_norm_form]

/-- If `H` is Hermitian, the adjoint transcorrelated matrix intertwines with `tc H g` through
`tcMetric g`. See [McArdleTew2020]. -/
theorem metric_quasi_hermitian {d : ℕ} (H g : Op d) (hH : H.IsHermitian) :
    (tc H g).conjTranspose * tcMetric g = tcMetric g * tc H g := by
  have hstar : (exp (-g)).conjTranspose * (exp g).conjTranspose = 1 := by
    rw [← Matrix.conjTranspose_mul, (actual_exp_inverse g).2, Matrix.conjTranspose_one]
  calc
    _ = (exp g).conjTranspose * H *
        ((exp (-g)).conjTranspose * (exp g).conjTranspose) * exp g := by
      simp only [tc, tcMetric, Matrix.conjTranspose_mul, hH.eq, Matrix.mul_assoc]
    _ = (exp g).conjTranspose * H * exp g := by rw [hstar]; simp
    _ = tcMetric g * tc H g := (metric_observable_matrix g H).symm

/-- For Hermitian `H`, multiplying a state satisfying the transcorrelated eigenvalue equation at
a real energy by the metric gives a state satisfying the adjoint eigenvalue equation. See
[McArdleTew2020]. -/
theorem metric_left_eigenvector {d : ℕ} (H g : Op d) (hH : H.IsHermitian)
    (φ : State d) (energy : ℝ)
    (hφ : Matrix.toEuclideanLin (tc H g) φ = (energy : ℂ) • φ) :
    Matrix.toEuclideanLin (tc H g).conjTranspose (Matrix.toEuclideanLin (tcMetric g) φ) =
      (energy : ℂ) • Matrix.toEuclideanLin (tcMetric g) φ := by
  rw [← matrix_action_mul, metric_quasi_hermitian H g hH, matrix_action_mul, hφ, map_smul]

end Qatlib.Papers.TranscorrChem20.MainResults.TCSimilarity
