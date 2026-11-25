/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.ShadowChannel26.MainResults.SourceModel

@[expose] public section

/-!
# Traceless reduction of mixed-state predictions

Section 4.1.2 of the paper (p. 15, lines 975-990) splits an observable and a state into their
traceless parts plus identity summands,
`O = O₀ + tr(O)·I/d`, `ρ = ρ₀ + I/d`,
and uses `tr[O U ρ U†] = tr[O₀ U ρ₀ U†] + tr(O)/d` as the first step of every estimator
construction. The traceless parts are the `SourceModel` definition `tracelessPartMat`, and the
paper's normalization `tr ρ = 1` is the `IsDensity` trace condition.

This module proves that reduction:

* `tracelessPartMat_trace_eq_zero`: the traceless part of any operator has zero trace.
* `trace_conj_traceless_decomp`: for a unitary `U` and a density operator `ρ`,
  `tr[O U ρ U†] = tr[O₀ U ρ₀ U†] + tr(O)/d`.

The proof is finite matrix algebra: expand both summands, use `tr(A U U†) = tr A`,
`tr(U B U†) = tr B` (trace cyclicity and `U†U = UU† = 1`), and evaluate the pure scalar term
`(tr O/d)(tr ρ/d)·d = tr O/d` with `tr ρ = 1`. Only the real part is compared, so no positivity
or Hermiticity assumption is needed beyond `tr ρ = 1`.

Boundary: only the identity summand `I/d` of the paper's normalization is covered; the general
`b • 1` decomposition would need `tr ρ = b·d`. Nothing here asserts a trace-norm or spectral
estimate.

Paper: [arXiv:2606.13638v2](https://arxiv.org/abs/2606.13638v2), §4.1.2.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Matrix
open Qatlib.Papers.ShadowChannel26.MainResults.SourceModel

namespace Qatlib.Papers.ShadowChannel26.MainResults

/-- The traceless part of an operator has zero trace. -/
theorem tracelessPartMat_trace_eq_zero {d : ℕ} (hd : 0 < d) (O : Op d) :
    (tracelessPartMat O).trace = 0 := by
  have hdC : ((d : ℂ)) ≠ 0 := by exact_mod_cast hd.ne'
  unfold tracelessPartMat
  rw [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, smul_eq_mul, Fintype.card_fin]
  field_simp
  ring

/-- The traceless reduction of §4.1.2: `tr[O U ρ U†] = tr[O₀ U ρ₀ U†] + tr(O)/d` for a unitary
`U` and a state `ρ`. -/
theorem trace_conj_traceless_decomp {d : ℕ} (U ρ O : Op d) (hU : IsUnitary U)
    (hρ : IsDensity ρ) (hd : 0 < d) :
    ((O * U * ρ * Uᴴ).trace).re
      = ((tracelessPartMat O * U * tracelessPartMat ρ * Uᴴ).trace).re
        + O.trace.re / (d : ℝ) := by
  set A := tracelessPartMat O with hA
  set B := tracelessPartMat ρ with hB
  have hcard : (Fintype.card (Fin d) : ℂ) = (d : ℂ) := by simp
  have hdC : ((d : ℂ)) ≠ 0 := by exact_mod_cast hd.ne'
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hO : A + (O.trace / (d : ℂ)) • (1 : Op d) = O := by
    rw [hA]
    unfold tracelessPartMat
    rw [hcard]
    exact sub_add_cancel _ _
  have hρ' : B + (ρ.trace / (d : ℂ)) • (1 : Op d) = ρ := by
    rw [hB]
    unfold tracelessPartMat
    rw [hcard]
    exact sub_add_cancel _ _
  have hAtrace : A.trace = 0 := by
    rw [hA]
    exact tracelessPartMat_trace_eq_zero hd O
  have hBtrace : B.trace = 0 := by
    rw [hB]
    exact tracelessPartMat_trace_eq_zero hd ρ
  have hρtrace : ρ.trace = 1 := hρ.2
  have hUU : U * Uᴴ = 1 := hU.2
  have hU'U : Uᴴ * U = 1 := hU.1
  have hAUU : A * U * Uᴴ = A := by
    rw [Matrix.mul_assoc, hUU, Matrix.mul_one]
  have hUUtr : (U * Uᴴ).trace = (d : ℂ) := by
    rw [hUU, Matrix.trace_one, Fintype.card_fin]
  have hconj (M : Op d) : (U * M * Uᴴ).trace = M.trace := by
    rw [Matrix.trace_mul_cycle, hU'U, Matrix.one_mul]
  have hstep1 : (A * U * ρ * Uᴴ).trace = (A * U * B * Uᴴ).trace := by
    conv_lhs => rw [← hρ']
    rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, Matrix.add_mul, Matrix.smul_mul,
      Matrix.trace_add, Matrix.trace_smul, smul_eq_mul, hAUU, hAtrace, mul_zero, add_zero]
  have hmain : (O * U * ρ * Uᴴ).trace
      = (A * U * B * Uᴴ).trace + O.trace / (d : ℂ) := by
    conv_lhs => rw [← hO]
    rw [Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.add_mul, Matrix.smul_mul,
      Matrix.add_mul, Matrix.smul_mul, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul,
      hstep1, hconj ρ, hρtrace]
    ring
  have hcre : (O.trace / (d : ℂ)).re = O.trace.re / (d : ℝ) := by
    rw [show (d : ℂ) = ((d : ℝ) : ℂ) by simp, Complex.div_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.normSq_ofReal, mul_zero, zero_div,
      add_zero]
    field_simp
  rw [hmain, Complex.add_re, hcre]

end Qatlib.Papers.ShadowChannel26.MainResults
