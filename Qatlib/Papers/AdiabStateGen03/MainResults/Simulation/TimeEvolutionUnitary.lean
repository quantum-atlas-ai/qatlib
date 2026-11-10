/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdiabStateGen03.MainResults.Defs
import Qatlib.Papers.AdiabStateGen03.MainResults.Simulation.CommutingAssembly
import Mathlib.Analysis.Normed.Algebra.Exponential
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder InnerProductSpace

namespace Qatlib.Papers.AdiabStateGen03.MainResults.Simulation

open Qatlib.Papers.AdiabStateGen03.MainResults

variable {n : ℕ}

theorem star_toOp_of_hermitian (H : Ham n) (hH : IsHermitian H) :
    star (toOp H) = toOp H := by
  have hmap : Matrix.toEuclideanCLM (n := Dim n) (𝕜 := ℂ) (star H)
      = star (Matrix.toEuclideanCLM (n := Dim n) (𝕜 := ℂ) H) := map_star _ _
  have hstar : star H = H := by
    rw [Matrix.star_eq_conjTranspose]; exact hH
  unfold toOp
  rw [← hmap, hstar]

theorem timeEvolution_mem_unitary (H : Ham n) (hH : IsHermitian H) (t : ℝ) :
    timeEvolution H t ∈ unitary (Op n) := by
  haveI : NormedAlgebra ℚ (Op n) := NormedAlgebra.restrictScalars ℚ ℂ (Op n)
  unfold timeEvolution
  apply NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
  rw [skewAdjoint.mem_iff]
  rw [real_smul_op (-t) (Complex.I • toOp H)]
  rw [star_smul, star_smul, Complex.star_def, Complex.conj_ofReal, Complex.conj_I,
    star_toOp_of_hermitian H hH]
  rw [smul_smul, smul_smul]
  rw [show (↑(-t : ℝ) * -Complex.I : ℂ) = -(↑(-t : ℝ) * Complex.I) by ring]
  exact neg_smul (↑(-t : ℝ) * Complex.I) (toOp H)

theorem timeEvolution_norm_map (H : Ham n) (hH : IsHermitian H) (t : ℝ) (ψ : State n) :
    ‖timeEvolution H t ψ‖ = ‖ψ‖ :=
  Unitary.norm_map ⟨timeEvolution H t, timeEvolution_mem_unitary H hH t⟩ ψ

theorem timeEvolution_contract (H : Ham n) (hH : IsHermitian H) (t : ℝ) (ψ : State n) :
    ‖timeEvolution H t ψ‖ ≤ ‖ψ‖ :=
  (timeEvolution_norm_map H hH t ψ).le

end Qatlib.Papers.AdiabStateGen03.MainResults.Simulation
