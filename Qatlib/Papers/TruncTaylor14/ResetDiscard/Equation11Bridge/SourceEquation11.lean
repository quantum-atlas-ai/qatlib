/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.ResetDiscard.Equation11Simu
import Qatlib.Concepts.BlockEncoding.LinearCombination

set_option backward.isDefEq.respectTransparency false

/-!
# Source Eq. (11) — the scaled PREPARE/SELECT success block

arXiv:1412.4687v1, p. 2, Eq. (11).  With the LCU coefficients `β : J → ℝ`,
normalization `s = Σ β_j`, a `β`-implementation `B` whose label state is the
scaled PREPARE `P`, and `select(V)` folded into `W`, the projector
`P₀ = |0⟩⟨0| ⊗ 1` applied to `W |0⟩|ψ⟩` returns exactly
`(1/s) |0⟩ (Σ_j β_j V_j) |ψ⟩`.

Frozen FQN reused: `QuantumAlgorithm.Papers.TruncTaylor14.ResetDiscard.equation11`
(`Statements/Equation11.lean:11`).  The frozen form works with a supplied
unitary preparation `IsScaledPrepare` and does not claim its gate synthesis.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.StateBlockEncoding
open Qatlib.Concepts.BlockEncoding.LinearCombination
open Qatlib.Concepts.CoherentSim.ResetDiscard

namespace Qatlib.Papers.TruncTaylor14.ResetDiscard.Equation11Bridge

/-- arXiv:1412.4687v1 Eq. (11), p. 2: the zero-ancilla fiber of the scaled LCU
workspace carries exactly the normalized weighted sum. -/
theorem source_equation11
    (J I : Type) [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (U : J → Matrix I I ℂ) (hU : ∀ j, U j ∈ Matrix.unitaryGroup I ℂ)
    (w : J → ℝ) (hw : ∀ j, 0 ≤ w j)
    (P : Matrix J J ℂ) (s : ℝ) (j₀ : J) (hP : IsScaledPrepare P w s j₀)
    (ψ : QState I) :
    FiberProjector j₀ *ᵥ (LCUWorkspace U P *ᵥ TensorState (Ket j₀) ψ) =
      TensorState (Ket j₀) ((((s⁻¹ : ℝ) : ℂ) • (∑ j, w j • U j)) *ᵥ ψ) :=
  equation11 J I U hU w hw P s j₀ hP ψ

end Qatlib.Papers.TruncTaylor14.ResetDiscard.Equation11Bridge
