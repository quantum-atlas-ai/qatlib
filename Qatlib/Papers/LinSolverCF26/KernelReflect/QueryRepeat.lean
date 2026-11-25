/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.LinSolverCF26.KernelReflect.QueryComplexity
public import Qatlib.Papers.LinSolverCF26.KernelReflect.SuccessBounds

@[expose] public section

/-!
# Kernel-reflection cost per success

The known-norm case of Section III in arXiv:2604.22185v2 divides the
degree-based query cost by the postselection success probability.
-/

set_option autoImplicit false

open Qatlib.Papers.LinSolverCF26.KernelReflect.QueryComplexity
open Qatlib.Papers.LinSolverCF26.KernelReflect.SuccessBounds

namespace Qatlib.Papers.LinSolverCF26.KernelReflect

/-- Bound the degree-based query cost per success using the kernel-reflection
success lower bound in the known-norm regime. The error and angle conditions
ensure the lower bound is strictly positive. -/
theorem known_norm_degree_ratio_le {κ ε θ δ1 δ2 : ℝ}
    (hκ : 0 < κ) (hε : 0 < ε) (hsmall : ε < Real.sqrt 2)
    (hsin : Real.sin (2 * θ) ≠ 0) (hd1 : 0 ≤ δ1)
    (herror : let η := ε / Real.sqrt 2
              Real.sqrt (δ1 ^ 2 + δ2 ^ 2) ≤ 4 * η / (1 + η)) :
    let η := ε / Real.sqrt 2
    (2 * degreeBound κ η) / pSucc θ δ1 δ2 ≤
      (κ * Real.log (2 * Real.sqrt 2 / ε)) /
        (Real.sin (2 * θ) ^ 2 * ((1 - η) / (1 + η)) ^ 2) := by
  let η := ε / Real.sqrt 2
  change (2 * degreeBound κ (ε / Real.sqrt 2)) / pSucc θ δ1 δ2 ≤
    (κ * Real.log (2 * Real.sqrt 2 / ε)) /
      (Real.sin (2 * θ) ^ 2 * ((1 - η) / (1 + η)) ^ 2)
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hηpos : 0 < η := div_pos hε hsqrt
  have hηone : η < 1 := (div_lt_one hsqrt).2 hsmall
  have hcoeff : 0 < (1 - η) / (1 + η) :=
    div_pos (sub_pos.2 hηone) (by linarith)
  have hprob : 0 < Real.sin (2 * θ) ^ 2 * ((1 - η) / (1 + η)) ^ 2 :=
    mul_pos (sq_pos_of_ne_zero hsin) (sq_pos_of_ne_zero hcoeff.ne')
  have hnum : 0 ≤ κ * Real.log (2 * Real.sqrt 2 / ε) :=
    mul_nonneg hκ.le (Real.log_nonneg ((le_div_iff₀ hε).2 (by linarith)))
  rw [two_degreeBound_known_norm hκ hε]
  exact div_le_div_of_nonneg_left hnum hprob (pSucc_lower hηpos.le hηone.le hd1 herror)

end Qatlib.Papers.LinSolverCF26.KernelReflect
