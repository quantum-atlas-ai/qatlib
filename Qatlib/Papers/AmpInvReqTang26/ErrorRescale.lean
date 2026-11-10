/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AmpInvReqTang26.AccessModel.ActualAccess
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Qatlib.Papers.AmpInvReqTang26.ErrorRescale
open Qatlib.Papers.AmpInvReqTang26.AccessModel

theorem relative_error_iff (a eps v : ℝ) :
    |v-a|<a*eps ↔ (1-eps)*a<v ∧ v<(1+eps)*a := by
  rw [abs_lt]
  constructor <;> intro h <;> constructor <;> nlinarith [h.1,h.2]

theorem actual_relative_readout {I A : Type*} [Fintype I] [Fintype A] [DecidableEq I] [DecidableEq A]
    (Alg : PreparationAlgorithm I A) (X : Matrix I I ℂ) (n : ℕ) (eps : ℝ) :
    (∑x,if |Alg.value x-preparationAmplitude Alg.start Alg.goodData X|<
      preparationAmplitude Alg.start Alg.goodData X*eps then ‖preparationRun Alg X n x‖^2 else 0) =
    ∑x,if (1-eps)*preparationAmplitude Alg.start Alg.goodData X<Alg.value x ∧
      Alg.value x<(1+eps)*preparationAmplitude Alg.start Alg.goodData X
      then ‖preparationRun Alg X n x‖^2 else 0 := by
  simp_rw [relative_error_iff]

end Qatlib.Papers.AmpInvReqTang26.ErrorRescale
