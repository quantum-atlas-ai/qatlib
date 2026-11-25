/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.LinearSystems09.Runtime
public import Qatlib.Concepts.HhlAlgorithms.SinEnvProgram.SinEnvelopeHHLConsumers
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

@[expose] public section

/-!
# Resolution and evolution-time units for HHL

Section II and Appendix A of arXiv:0811.3171v3 express the phase error
using `κ/t₀`. The pinned sine-envelope grid with `M` points uses
`t₀ = 2πM`; transport its precision budget using this same scale.
-/

set_option autoImplicit false

open Qatlib.Concepts.HhlAlgorithms.SinEnvProgram
open Qatlib.Concepts.HhlAlgorithms.SinEnvProgram.SinEnvelopeHHLConsumers
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

namespace Qatlib.Papers.LinearSystems09.SourceRuntime

/-- The inverse grid-separation rate in units of the paper's evolution time. -/
theorem sinEnvelope_budget_unit_bridge {κ M : ℝ} (hκ : 0 < κ) (hM : 0 < M) :
    1 / ((1 / (2 * κ)) * M) = 4 * Real.pi * κ / (2 * Real.pi * M) := by
  field_simp [hκ.ne', hM.ne', Real.pi_ne_zero]
  norm_num

/-- The sufficient sine-envelope full-workspace precision budget expressed in \`t₀\` units. -/
theorem sinEnvelope_clock_budget {κ η M : ℝ} (hκ : 0 < κ) (hη : 0 < η) :
    21 / ((1 / (2 * κ)) * η) ≤ M ↔
      84 * Real.pi * κ / η ≤ 2 * Real.pi * M := by
  have heq : 21 / ((1 / (2 * κ)) * η) = 42 * κ / η := by
    field_simp [hκ.ne', hη.ne']
    norm_num
  rw [heq]
  have hπ : 0 < 2 * Real.pi := by positivity
  rw [← mul_le_mul_iff_of_pos_left hπ]
  have hscale : (2 * Real.pi) * (42 * κ / η) = 84 * Real.pi * κ / η := by ring
  rw [hscale]

/-- At the translated time budget, the pinned actual HHL workspace meets the same error bound. -/
theorem sinEnvelope_workspace_at_clock {D : ℕ} (M : ℕ) (hM : 2 ≤ M)
    (eig : Fin D → ℝ) (V B : Operator D) (j : Fin D) {κ η : ℝ}
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) (hB : B ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (hκ : 0 < κ) (hη : 0 < η) (hη1 : η ≤ 1)
    (heig : ∀ i, 0 ≤ eig i ∧ eig i ≤ 1/4)
    (hclock : 84 * Real.pi * κ / η ≤ 2 * Real.pi * (M : ℝ)) :
    ‖toEuclidean_fromVec (sinEnvelopeHHLRun M hM (continuousHHLOracle eig V) (1 / (2 * κ)) B j -
        sinEnvelopeHHLIdeal M hM eig V (1 / (2 * κ)) B j)‖ ≤ η :=
  sin_envelope_hhl_full_workspace_error M hM eig V B j (1 / (2 * κ)) η
    hV hB (by positivity) hη hη1 heig ((sinEnvelope_clock_budget hκ hη).mpr hclock)

end Qatlib.Papers.LinearSystems09.SourceRuntime
