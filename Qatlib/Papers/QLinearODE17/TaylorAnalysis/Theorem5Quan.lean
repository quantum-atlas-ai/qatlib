/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLinearODE17.TaylorAnalysis.Theorem5Stat
import Qatlib.Papers.QLinearODE17.TaylorAnalysis.Theorem5Norm
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QLinearODE17.TaylorAnalysis
open Matrix
open scoped Matrix.Norms.L2Operator
set_option warningAsError false

theorem theorem5V2 : Theorem5V2 := by
  intro N _ _ m k p A V D hm hk hp hfac hd hA hV1 hV2 hnorm hre
  have hz : ∀ n : N,‖D n n‖ ≤ 1 := by
    intro n
    simpa only [Complex.ofReal_one,one_mul,one_smul] using!
      hA_eigen_norm_le A V D hA hV1 hV2 hd 1 (by norm_num) (by simpa using! hnorm) n
  have hAV : A*V=V*D := by rw [hA,Matrix.mul_assoc,hV2,mul_one]
  have hD := taylorV2_diagonal_inverse_norm_le m k p D hm hk hp hfac hd hz hre
  have hInv : ‖(taylorStepMatrixV2 m k p A)⁻¹‖ ≤
      (‖V‖*‖V⁻¹‖)*(3*Real.sqrt (k : ℝ)*((m+p : ℕ) : ℝ)) :=
    (taylorV2_inverse_norm_transport m k p A V D hAV hV1 hV2).trans
      (mul_le_mul_of_nonneg_left hD (by positivity))
  have hF := taylorV2_forward_norm_le m k p A hk hnorm
  calc
    _ ≤ (2*Real.sqrt (k : ℝ))*((‖V‖*‖V⁻¹‖)*(3*Real.sqrt (k : ℝ)*((m+p : ℕ) : ℝ))) :=
      mul_le_mul hF hInv (norm_nonneg _) (by positivity)
    _ = 6*(‖V‖*‖V⁻¹‖)*(Real.sqrt (k : ℝ))^2*((m+p : ℕ) : ℝ) := by ring
    _ = _ := by rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ k)]

end Qatlib.Papers.QLinearODE17.TaylorAnalysis
