/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import QuantumInfo.ForMathlib.MatrixNorm.TraceNorm
import Mathlib.Tactic

/-!
# Trace-distance bounds from semidefinite domination

`psd_native_traceNorm` identifies the trace norm of a positive semidefinite matrix with its real
trace. `density_domination_distance` uses this identity to bound half the trace norm between
trace-one matrices when the second dominates `(1 - delta)` times a positive semidefinite first
matrix for `delta ≥ 0`. See [Watrous2018].

## Main statements

* `psd_native_traceNorm`: trace norm equals real trace on positive semidefinite matrices.
* `density_domination_distance`: the semidefinite domination bound.

## References

* [Watrous, 2018][Watrous2018]
* [Bhatia, 1997][Bhatia1997]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MixedFidelity.FidelityMetric.Domination
open Matrix
open scoped ComplexOrder
variable {I : Type*} [Fintype I]

/-- The trace norm of a positive semidefinite matrix equals the real part of its trace. -/
theorem psd_native_traceNorm (A : Matrix I I ℂ) (hA : A.PosSemidef) :
    Matrix.traceNorm A=(Matrix.trace A).re := by
  simpa using congrArg Complex.re hA.traceNorm_eq_trace

/-- If `rho` is positive semidefinite, both matrices have trace one, `delta ≥ 0`, and `sigma -
(1 - delta) • rho` is positive semidefinite, then `Matrix.traceNorm (rho - sigma) / 2 ≤
delta`. -/
theorem density_domination_distance (rho sigma : Matrix I I ℂ)
    (hrho : rho.PosSemidef)
    (htrho : Matrix.trace rho=1) (htrsigma : Matrix.trace sigma=1)
    (delta : ℝ) (hd0 : 0≤delta)
    (hdom : (sigma-(((1-delta:ℝ):ℂ) • rho)).PosSemidef) :
    Matrix.traceNorm (rho-sigma)/2≤delta := by
  let T := sigma-(((1-delta:ℝ):ℂ) • rho)
  have hr : Matrix.traceNorm rho=1 := by
    rw [psd_native_traceNorm rho hrho,htrho,Complex.one_re]
  have ht : Matrix.traceNorm T=delta := by
    rw [psd_native_traceNorm T hdom]
    simp [T,Matrix.trace_sub,Matrix.trace_smul,htrho,htrsigma]
  have heq : rho-sigma=(delta:ℂ) • rho + -T := by
    dsimp [T]
    simp only [sub_smul,one_smul]
    module
  have hb := Matrix.traceNorm_add_le ((delta:ℂ) • rho) (-T)
  rw [← heq,Matrix.traceNorm_neg,Matrix.traceNorm_smul,hr,ht,mul_one,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hd0] at hb
  linarith

end Qatlib.Concepts.MixedFidelity.FidelityMetric.Domination
