/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Telescoping bound on ideal intermediate states (Lemma 5.6)

Shen--Wu--Yuan--Zhang, fixed arXiv:2610.05362v1, Lemma 5.6, page 37.
For an initialized input `x₀`, ideal intermediate vectors `x_j`, and actual
unitaries `Û_j` with `‖Û_j x_{j-1} - x_j‖ ≤ δ_j ‖x₀‖`, the accumulated error is
`‖Û_m ⋯ Û_1 x₀ - x_m‖ ≤ (∑_{j=1}^m δ_j) ‖x₀‖`.

The source proof is the triangle inequality applied to the telescoped chain
`Û_m ⋯ Û_1 x₀ - x_m = ∑_j Û_m ⋯ Û_{j+1} (Û_j x_{j-1} - x_j)`, with unitary
contraction at every later step.  We present it as a direct induction, which
keeps the exact per-step hypotheses and the exact constant one.
-/

namespace Qatlib.Papers.ShallowLind26.ShallowSim.IntermediateTelescoping

open scoped BigOperators

set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The actual accumulated state `Û_m ⋯ Û_1 x₀` of the telescoped chain. -/
noncomputable def actualRun (U : ℕ → E →L[ℂ] E) (x0 : E) : ℕ → E
  | 0 => x0
  | m + 1 => U m (actualRun U x0 m)

/-- **Lemma 5.6.**  If each actual unitary `Û_j` preserves norms and each step
satisfies `‖Û_j x_{j-1} - x_j‖ ≤ δ_j ‖x₀‖` with `δ_j ≥ 0`, then the actual
accumulated state is within `(∑_{j<m} δ_j) ‖x₀‖` of the ideal intermediate
vector `x_m`. -/
theorem intermediate_telescoping (U : ℕ → E →L[ℂ] E)
    (hU : ∀ (j : ℕ) (v : E), ‖U j v‖ = ‖v‖)
    (x : ℕ → E) (x0 : E) (δ : ℕ → ℝ)
    (hx0 : x 0 = x0)
    (hstep : ∀ j, ‖U j (x j) - x (j + 1)‖ ≤ δ j * ‖x0‖) :
    ∀ m, ‖actualRun U x0 m - x m‖ ≤ (∑ j ∈ Finset.range m, δ j) * ‖x0‖ := by
  intro m
  induction m with
  | zero => simp [actualRun, hx0]
  | succ m ih =>
    have hsplit :
        actualRun U x0 (m + 1) - x (m + 1)
          = (U m (actualRun U x0 m) - U m (x m)) + (U m (x m) - x (m + 1)) := by
      rw [actualRun]
      abel
    have hfirst : ‖U m (actualRun U x0 m) - U m (x m)‖ = ‖actualRun U x0 m - x m‖ := by
      rw [← map_sub, hU]
    have htri : ‖actualRun U x0 (m + 1) - x (m + 1)‖
        ≤ ‖actualRun U x0 m - x m‖ + δ m * ‖x0‖ := by
      rw [hsplit]
      calc ‖(U m (actualRun U x0 m) - U m (x m)) + (U m (x m) - x (m + 1))‖
          ≤ ‖U m (actualRun U x0 m) - U m (x m)‖ + ‖U m (x m) - x (m + 1)‖ :=
            norm_add_le _ _
        _ = ‖actualRun U x0 m - x m‖ + ‖U m (x m) - x (m + 1)‖ := by rw [hfirst]
        _ ≤ ‖actualRun U x0 m - x m‖ + δ m * ‖x0‖ :=
            add_le_add le_rfl (hstep m)
    calc ‖actualRun U x0 (m + 1) - x (m + 1)‖
        ≤ ‖actualRun U x0 m - x m‖ + δ m * ‖x0‖ := htri
      _ ≤ (∑ j ∈ Finset.range m, δ j) * ‖x0‖ + δ m * ‖x0‖ :=
            add_le_add ih le_rfl
      _ = (∑ j ∈ Finset.range (m + 1), δ j) * ‖x0‖ := by
            rw [Finset.sum_range_succ]
            ring

end Qatlib.Papers.ShallowLind26.ShallowSim.IntermediateTelescoping
