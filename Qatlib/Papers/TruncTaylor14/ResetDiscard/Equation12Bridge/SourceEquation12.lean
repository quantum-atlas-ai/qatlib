/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.ResetDiscard.Equation12Simu

set_option backward.isDefEq.respectTransparency false

/-!
# Source Eq. (12) — exact oblivious amplitude amplification at scale two

arXiv:1412.4687v1, p. 2, Eq. (12).  For a scale-two block encoding `W` of a
unitary `U` and every input `ψ`, the amplified word
`A = -W (1-2P) W† (1-2P) W` returns the full output state
`|0⟩ U |ψ⟩` with no leakage into the orthogonal fiber.  The companion counted
form supplies the gatewise-valid three-query word.

Library theorems:
* `Qatlib.Concepts.CoherentSim.ResetDiscard.equation12` (exact output identity);
* `Qatlib.Concepts.CoherentSim.ResetDiscard.equation12_counted`
  (three charged queries, four projector-phase macros).
-/

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.StateBlockEncoding
open Qatlib.Concepts.CoherentSim.ResetDiscard
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.BlockEncoding.EncodingCore

namespace Qatlib.Papers.TruncTaylor14.ResetDiscard.Equation12Bridge

/-- arXiv:1412.4687v1 Eq. (12), p. 2: exact scale-two OAA output identity for a
unitary target, including absence of leakage. -/
theorem source_equation12
    (J I : Type) [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (W : Matrix (J × I) (J × I) ℂ) (j₀ : J) (U : Matrix I I ℂ)
    (hW : IsBlockEncoding W j₀ U 2) (hU : U ∈ Matrix.unitaryGroup I ℂ)
    (ψ : QState I) :
    ObliviousAmplitudeAmplification (FiberProjector j₀) W *ᵥ TensorState (Ket j₀) ψ =
      TensorState (Ket j₀) (U *ᵥ ψ) :=
  equation12 J I W j₀ U hW hU ψ

/-- arXiv:1412.4687v1 Eq. (12), p. 2, counted form: the same encoding yields a
well-formed three-query actual word whose complete frame action is the target. -/
theorem source_equation12_counted
    {J I : Type} [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    {W : Matrix (J × I) (J × I) ℂ} {j₀ : J} {U : Matrix I I ℂ}
    (hW : IsBlockEncoding W j₀ U 2) (hU : U ∈ Matrix.unitaryGroup I ℂ) :
    ∃ cs : List (AdjointStep (J × I)),
      WellFormedAdjointCircuit cs ∧
      ProjectedUnitaryEncoding U (evaluate W cs) (encodingFiber j₀) (encodingFiber j₀) ∧
      (evaluate W cs * encodingFiber j₀ : Matrix (J × I) I ℂ) =
        (encodingFiber j₀ * U : Matrix (J × I) I ℂ) ∧
      adjointQueryCount cs = 3 ∧ adjointGateCount cs = 4 :=
  equation12_counted hW hU

end Qatlib.Papers.TruncTaylor14.ResetDiscard.Equation12Bridge
