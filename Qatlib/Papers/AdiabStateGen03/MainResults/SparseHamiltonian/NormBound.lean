/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdiabStateGen03.MainResults.Defs
import Mathlib.Analysis.Normed.Ring.Basic

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder InnerProductSpace

namespace Qatlib.Papers.AdiabStateGen03.MainResults.SparseHamiltonian

open Qatlib.Papers.AdiabStateGen03.MainResults

variable {n : ℕ}

theorem norm_entry_le (H : Ham n) (i j : Dim n) : ‖H i j‖ ≤ ‖H‖ := by
  set x : State n := EuclideanSpace.single j 1 with hxdef
  have hx : ‖x‖ = 1 := by simp [hxdef]
  have hle : ‖toOp H x‖ ≤ ‖H‖ := by
    have h := ContinuousLinearMap.le_opNorm (toOp H) x
    rw [norm_toOp, hx, mul_one] at h
    exact h
  have hcoord : ‖(toOp H x).ofLp i‖ ≤ ‖toOp H x‖ := PiLp.norm_apply_le (toOp H x) i
  have hval : (toOp H x).ofLp i = H i j := by
    unfold toOp
    rw [show x = WithLp.toLp 2 (Pi.single j (1 : ℂ)) from rfl,
      Matrix.toEuclideanCLM_toLp, PiLp.toLp_apply, Matrix.mulVec_single]
    simp [Matrix.col_apply]
  rw [hval] at hcoord
  exact hcoord.trans hle

end Qatlib.Papers.AdiabStateGen03.MainResults.SparseHamiltonian
