/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ProjectorQAOA26.StageStability.ProjectorDistance

/-!
# Triangle and perturbation bounds for phase distance

This module proves the triangle inequality for `phaseDist` using the Euclidean triangle
inequality and optimal phase alignment. It also bounds the phase distance between matrix images
of a normalized vector by the operator distance, supporting the state comparison in
[ZhouAnLiu2026].

## Main statements

* `phaseDist_triangle`: Phase distance satisfies the triangle inequality.
* `phaseDist_mulVec_perturb`: For a normalized vector, the phase distance between its images
  under two matrices is at most the operator norm of the matrix difference.

## References

* [Zhou et al., 2026][ZhouAnLiu2026]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.ProjectorQAOA26.StageStability
open scoped Matrix Matrix.Norms.L2Operator
variable {I : Type*} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in

/-- The explicit Euclidean norm satisfies the triangle inequality. -/
theorem l2norm_add_le (x y : I → ℂ) : l2norm (x+y)≤l2norm x+l2norm y := by
  rw [← norm_toLp,← norm_toLp,← norm_toLp]
  exact norm_add_le (WithLp.toLp 2 x : EuclideanSpace ℂ I) (WithLp.toLp 2 y)

omit [DecidableEq I] in

/-- Phase distance is at most the Euclidean norm of the unaligned vector difference. -/
theorem phaseDist_le_difference (u v : I → ℂ) : phaseDist u v≤l2norm (u-v) := by
  simpa only [one_smul] using phaseDist_le_of_unit u v (z:=1) (by norm_num)

omit [DecidableEq I] in

/-- Phase distance satisfies the triangle inequality. -/
theorem phaseDist_triangle (u v w : I → ℂ) : phaseDist u w≤phaseDist u v+phaseDist v w := by
  let z:=phaseFactor u v
  let q:=phaseFactor v w
  have hz : Complex.normSq z=1 := normSq_phaseFactor u v
  have hq : Complex.normSq q=1 := normSq_phaseFactor v w
  have hprod : Complex.normSq (z*q)=1 := by rw [Complex.normSq_mul,hz,hq,one_mul]
  calc
    phaseDist u w≤l2norm (u-(z*q)•w) := phaseDist_le_of_unit u w hprod
    _=l2norm ((u-z•v)+z•(v-q•w)) := by congr 1; module
    _≤l2norm (u-z•v)+l2norm (z•(v-q•w)) := l2norm_add_le _ _
    _=phaseDist u v+phaseDist v w := by
      rw [l2norm_smul,hz,Real.sqrt_one,one_mul]
      rfl

/-- For a normalized vector, the phase distance between its images under two matrices is at most
the operator norm of the matrix difference. -/
theorem phaseDist_mulVec_perturb (A B : Matrix I I ℂ) (v : I → ℂ) (hv : l2norm v=1) :
    phaseDist (A*ᵥv) (B*ᵥv)≤‖A-B‖ := by
  calc
    phaseDist (A*ᵥv) (B*ᵥv)≤l2norm (A*ᵥv-B*ᵥv) := phaseDist_le_difference _ _
    _=l2norm ((A-B)*ᵥv) := by rw [Matrix.sub_mulVec]
    _≤‖A-B‖*l2norm v := l2norm_mulVec_le _ _
    _=‖A-B‖ := by rw [hv,mul_one]
end Qatlib.Papers.ProjectorQAOA26.StageStability
