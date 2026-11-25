/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.StateConvLee10.PhaseDetect

@[expose] public section

/-!
# Phase detection at the state-conversion parameters

Theorem 4.3 of the paper states the reflection `R(U)` with `b = O(log(1/δ) log(1/Θ))` ancillary
qubits and `O(log(1/δ)/Θ)` controlled calls, and the conversion algorithm of §4 applies it to the
unitary `U_x` with the substitutions `Θ = ε²/W` and `δ = ε`. This module performs that
substitution on the uniform phase-detection statement
`Qatlib.Papers.StateConvLee10.PhaseDetect.source_phase_detection` and records the resulting
resource bounds and the two guarantees: exact action on invariant states and `ε`-accurate sign
reversal on states orthogonal to the small-phase subspace of threshold `ε²/W`.

The constant multiplying the resource bounds stays existential, exactly as in the source theorem,
because `source_phase_detection` states the existence of a positive constant rather than a
particular numeral. The ceiling expressions are kept in the library's shape: the call count uses
`max 1 ⌈W/ε²⌉` and the ancilla count is guarded by `W/ε² + 1`, so no hypothesis beyond
`0 < ε ≤ W` is needed.

Paper: [arXiv:1011.3020v2](https://arxiv.org/abs/1011.3020), printed p.6 Theorem 4.3 and p.7
Algorithm box.
-/

set_option autoImplicit false
noncomputable section

open Matrix

open scoped Classical

namespace Qatlib.Papers.StateConvLee10.PhaseDetect

open Qatlib.Concepts.GramQueryCore.LowerBoundTools
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge

/-- With `Θ = ε²/W` and `δ = ε`, the phase-detection word of
`Qatlib.Papers.StateConvLee10.PhaseDetect.source_phase_detection` keeps its uniform constant, its
`W/ε²`-shaped call and ancilla bounds, exact action on states fixed by `U`, and `ε`-accurate sign
reversal on states killed by the projector of threshold `ε²/W` [LeeEtAl2011]. -/
theorem source_phase_detection_at_conversion_params :
    ∃ c : ℕ, 0 < c ∧ ∀ (H : Type) [Fintype H] [DecidableEq H] (W ε : ℝ),
      0 < ε → ε ≤ W →
      ∃ (b : ℕ) (C : SourceWord ((Bool × H) × Fin (2 ^ b))),
        sourceWordLegal C ∧
        sourceWordCalls C ≤ c * max 1 (Nat.ceil (W / ε ^ 2)) *
          (Nat.ceil (Real.log (2 / min 1 ε)) + 1) ∧
        b ≤ c * (Nat.clog 2 (max 1 (Nat.ceil (W / ε ^ 2)) + 1) + 1) *
          (Nat.ceil (Real.log (2 / min 1 ε)) + 1) ∧
        ∀ (U V : Matrix H H ℂ) (angles : H → ℝ),
          U ∈ Matrix.unitaryGroup H ℂ → V ∈ Matrix.unitaryGroup H ℂ →
          (∀ h, -Real.pi < angles h ∧ angles h ≤ Real.pi) →
          U = V * Matrix.diagonal (fun h => Complex.exp (Complex.I * angles h)) * Vᴴ →
          ∀ ψ : QState H,
            let embed := fun φ : QState H =>
              TensorState (TensorState (Ket false) φ) (Ket (0 : Fin (2 ^ b)))
            let A := sourceWordMatrix (sourceControlledU (2 ^ b) U) C
            (U *ᵥ ψ = ψ → A *ᵥ embed ψ = embed ψ) ∧
            (sourcePhaseProjector V angles (ε ^ 2 / W) *ᵥ ψ = 0 →
              ‖toEuclidean_fromVec (A *ᵥ embed ψ + embed ψ)‖ ≤
                ε * ‖toEuclidean_fromVec ψ‖) := by
  obtain ⟨c, hc, hall⟩ := Qatlib.Papers.StateConvLee10.PhaseDetect.source_phase_detection
  refine ⟨c, hc, ?_⟩
  intro H _ _ W ε hε hεW
  have hW : 0 < W := lt_of_lt_of_le hε hεW
  have hΘ : 0 < ε ^ 2 / W := by positivity
  obtain ⟨b, C, hlegal, hcalls, hbits, hmain⟩ := hall H (ε ^ 2 / W) ε hΘ hε
  have hrewrite : 1 / (ε ^ 2 / W) = W / ε ^ 2 := by field_simp
  rw [hrewrite] at hcalls hbits
  exact ⟨b, C, hlegal, hcalls, hbits, hmain⟩

end Qatlib.Papers.StateConvLee10.PhaseDetect
