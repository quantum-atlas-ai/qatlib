/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.ResetDiscard.Equation14Simu

set_option backward.isDefEq.respectTransparency false

/-!
# Source Eq. (14) — compressed cubic action for general scale and nonunitary target

arXiv:1412.4687v1, p. 3, Eq. (14).  For a general positive-scale block encoding
`W` of `Ũ` with scale `s` (the LCU normalization `s = Σ β_j`, not necessarily
two, and `Ũ` not necessarily unitary), the zero fiber of the amplified word is

`P A |0⟩|ψ⟩ = |0⟩ ((3/s) Ũ - (4/s³) Ũ Ũ† Ũ) |ψ⟩`.

This is exactly the `P W P = (|0⟩⟨0| ⊗ Ũ)/s` consequence of Eq. (11) substituted
into the cubic identity Eq. (13).

Reusable FQN: `Qatlib.Papers.TruncTaylor14.ResetDiscard.equation14`
(`Statements/Equation14.lean:12`).
-/

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.StateBlockEncoding
open Qatlib.Concepts.CoherentSim.ResetDiscard

namespace Qatlib.Papers.TruncTaylor14.ResetDiscard.Equation14Bridge

/-- arXiv:1412.4687v1 Eq. (14), p. 3: compressed cubic formula for arbitrary
positive LCU scale `s` and an arbitrary (not necessarily unitary) encoded `Ũ`. -/
theorem source_equation14
    (J I : Type) [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (W : Matrix (J × I) (J × I) ℂ) (j₀ : J) (U : Matrix I I ℂ) (s : ℝ)
    (hW : IsBlockEncoding W j₀ U s) (ψ : QState I) :
    FiberProjector j₀ *ᵥ
      (ObliviousAmplitudeAmplification (FiberProjector j₀) W *ᵥ TensorState (Ket j₀) ψ) =
      TensorState (Ket j₀)
        (((((3 / s : ℝ) : ℂ) • U) - (((4 / s ^ 3 : ℝ) : ℂ) • (U * Uᴴ * U))) *ᵥ ψ) :=
  equation14 J I W j₀ U s hW ψ

end Qatlib.Papers.TruncTaylor14.ResetDiscard.Equation14Bridge
