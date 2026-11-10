/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ContDiscWalk08.MainResults.WalkSpectrum.Theorem1Eigenpairs
set_option warningAsError false

set_option autoImplicit false

noncomputable section

open Matrix Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.AmplitudeCore.InvFreePhase
open Qatlib.Concepts.WalkSearch.TwoLevelLower
open scoped Matrix.Norms.L2Operator

namespace Qatlib.Papers.ContDiscWalk08.MainResults.SimulationComplexity

open Qatlib.Papers.ContDiscWalk08.MainResults.WalkSpectrum

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem theorem5_zero_time_fidelity (D : WalkSetup I) (δ : ℝ) (hδ : 0 < δ) :
    ∃ (run : Matrix I I ℂ) (steps : ℝ),
      run ∈ Matrix.unitaryGroup I ℂ ∧
      0 ≤ steps ∧
      (∀ ψ : QState I, Normalized ψ →
        1 - δ ≤ ‖Inner (HamiltonianEvolution D.H 0 *ᵥ ψ) (run *ᵥ ψ)‖ ^ 2) ∧
      (∃ C : ℝ, 0 < C ∧ steps ≤ C * D.absNorm * (0 : ℝ) / Real.sqrt δ) := by
  refine ⟨1, 0, ?_, le_refl 0, ?_, ⟨1, one_pos, ?_⟩⟩
  · rw [Matrix.mem_unitaryGroup_iff']
    simp
  · intro ψ hψ
    rw [hamiltonianEvolution_zero, Matrix.one_mulVec,
      (normalized_iff_inner_self ψ).mp hψ, norm_one, one_pow]
    linarith
  · simp

end Qatlib.Papers.ContDiscWalk08.MainResults.SimulationComplexity
