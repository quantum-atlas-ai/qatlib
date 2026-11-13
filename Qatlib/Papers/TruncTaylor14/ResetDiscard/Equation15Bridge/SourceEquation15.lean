/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.ResetDiscard.Equation15Simu

set_option backward.isDefEq.respectTransparency false

/-!
# Source Eq. (15) — robust OAA for nonunitary target and scale defect

arXiv:1412.4687v1, p. 2, Eq. (15).  If the compressed block `X` of a
scale-`s` encoding `W` is `δ₁`-close to a unitary `U` and the LCU scale is
`δ₂`-close to two (`1 ≤ s`, `|s-2| ≤ δ₂ ≤ 1`), then for every normalized `ψ`

`‖ P A |0⟩|ψ⟩ - |0⟩ U |ψ⟩ ‖ ≤ (15 + 12 δ₁ + 4 δ₁²) δ₁ + 15 δ₂ = O(δ)`.

This is the quantitative form of the source's `O(δ)` estimate; the failure mass
in the orthogonal fiber is the subject of Eq. (16).

Reusable FQN: `Qatlib.Papers.TruncTaylor14.ResetDiscard.equation15`
(`Statements/Equation15.lean:12`).
-/

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.BlockEncoding.StateBlockEncoding
open Qatlib.Concepts.CoherentSim.ResetDiscard
open scoped Matrix.Norms.L2Operator

namespace Qatlib.Papers.TruncTaylor14.ResetDiscard.Equation15Bridge

/-- arXiv:1412.4687v1 Eq. (15), p. 2: projected successful fiber of the amplified
word is `O(δ₁+δ₂)`-close to the unitary target state. -/
theorem source_equation15
    (J I : Type) [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (W : Matrix (J × I) (J × I) ℂ) (j₀ : J) (X U : Matrix I I ℂ)
    (s δ₁ δ₂ : ℝ) (hW : IsBlockEncoding W j₀ X s)
    (hU : U ∈ Matrix.unitaryGroup I ℂ) (hXU : ‖X - U‖ ≤ δ₁)
    (hs : 1 ≤ s) (hδ₂ : |s - 2| ≤ δ₂) (hδ₂1 : δ₂ ≤ 1)
    (ψ : QState I) (hψ : Normalized ψ) :
    ‖toEuclidean_fromVec (FiberProjector j₀ *ᵥ
        (ObliviousAmplitudeAmplification (FiberProjector j₀) W *ᵥ TensorState (Ket j₀) ψ) -
        TensorState (Ket j₀) (U *ᵥ ψ))‖ ≤
      (15 + 12 * δ₁ + 4 * δ₁ ^ 2) * δ₁ + 15 * δ₂ :=
  equation15 J I W j₀ X U s δ₁ δ₂ hW hU hXU hs hδ₂ hδ₂1 ψ hψ

end Qatlib.Papers.TruncTaylor14.ResetDiscard.Equation15Bridge
