/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.ImagDBrak24.MainResults.SourceDynamics
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Tactic

@[expose] public section


set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ImagDBrak24.MainResults

open Qatlib.Papers.ImagDBrak24.MainResults

/-- The ground basis vector of a one-level system is a normalized state. -/
theorem ground_state_normalized : IsState (basisVec (0 : Fin 1)) := by
  norm_num [IsState, normSq, basisVec]

/-- The zero-order characteristic-function bound cannot discard the ground-state mass. -/
theorem derivative_zero_bound_false :
    ¬ ‖iteratedDeriv 0 (charFun (fun _ : Fin 1 => 0) (basisVec 0)) 0‖ ≤
      (1 - fidelity (basisVec (0 : Fin 1)) (basisVec 0)) * (1 : ℝ) ^ 0 := by
  norm_num [iteratedDeriv_zero, charFun, unitaryEvolve, diagHam, fidelity,
    vdot, basisVec, Matrix.mulVec, dotProduct]

/-- With zero per-step depth, the original positive-target stopping bound is impossible. -/
theorem zero_depth_obstruction :
    ¬ ∃ k : ℕ, (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ k ≤ 1 / 4 ∧
      ∃ C : ℝ, 0 < C ∧ (k : ℝ) ≤ C * 0 * (2 : ℝ) ^ (4 : ℝ) := by
  rintro ⟨k, herr, C, _, hbound⟩
  have hk : (k : ℝ) = 0 := le_antisymm (by simpa using hbound) (Nat.cast_nonneg k)
  have hk0 : k = 0 := by exact_mod_cast hk
  subst k
  norm_num at herr

end Qatlib.Papers.ImagDBrak24.MainResults
