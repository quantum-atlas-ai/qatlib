/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.ResetDiscard.Equation13Simu

set_option backward.isDefEq.respectTransparency false

/-!
# Source Eq. (13) — the projected cubic OAA identity

arXiv:1412.4687v1, p. 2, Eq. (13).  For an orthogonal projector `P`, a unitary
`W`, and a vector `ψ` in the range of `P`, the projected amplified word
`-W (1-2P) W† (1-2P) W` acts as `3(PW) - 4(PWPWᴴPW)`.

Frozen FQN reused: `QuantumAlgorithm.Papers.TruncTaylor14.ResetDiscard.equation13`
(`Statements/Equation13.lean:19`).  Hypotheses are exactly the source's
`P² = P`, unitarity of `W`, and `Pψ = ψ`; normalization is unnecessary.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Concepts.CoherentSim.ResetDiscard

namespace Qatlib.Papers.TruncTaylor14.ResetDiscard.Equation13Bridge

/-- arXiv:1412.4687v1 Eq. (13), p. 2: projected cubic action of the amplified
word on the range of an orthogonal projector. -/
theorem source_equation13
    (I : Type) [Fintype I] [DecidableEq I]
    (P W : Matrix I I ℂ) (hP : IsStarProjection P)
    (hW : W ∈ Matrix.unitaryGroup I ℂ)
    (ψ : I → ℂ) (hψ : P *ᵥ ψ = ψ) :
    P *ᵥ (ObliviousAmplitudeAmplification P W *ᵥ ψ) =
      (3 * (P * W) - 4 * (P * W * P * Wᴴ * P * W)) *ᵥ ψ :=
  equation13 I P W hP hW ψ hψ

end Qatlib.Papers.TruncTaylor14.ResetDiscard.Equation13Bridge
