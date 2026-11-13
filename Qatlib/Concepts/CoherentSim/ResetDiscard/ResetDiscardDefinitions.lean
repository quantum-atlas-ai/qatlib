/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.ResetDiscard.Equation16Stat
import Qatlib.Foundations.PureStateMath.MixedState

/-!
# Raw and amplified reset-and-discard maps

`AncillaSystemOp` forms a product operator, `ResetDiscardStep` applies a workspace and selects
its ancillary fiber, and `ResetDiscardStepCorrected` traces out the ancilla after oblivious
amplification. These definitions support comparisons of raw and amplified segmentation in the
Taylor simulation setting [BerryEtAl2015Taylor].

## Main statements

* `ResetDiscardStep`: The raw projected workspace map.
* `ResetDiscardStepCorrected`: The amplified map with the ancilla traced out.
* `ResetDiscardSegmentation`: The proposed raw-step error property.

## References

* [Berry et al., 2015][BerryEtAl2015Taylor]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.StateBlockEncoding

namespace Qatlib.Concepts.CoherentSim.ResetDiscard

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder

/-- The tensor-product operator with entries `σ a b * ρ i i'` on the ancillary and system
registers. -/
def AncillaSystemOp {J I : Type*} [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (σ : Matrix J J ℂ) (ρ : Matrix I I ℂ) : Matrix (J × I) (J × I) ℂ :=
  Matrix.of fun (a, i) (b, i') => σ a b * ρ i i'

/-- The system map obtained by preparing the ancillary basis state, applying `W`, projecting
back onto the same ancillary fiber, and tracing out the ancilla. -/
noncomputable def ResetDiscardStep {J I : Type*} [Fintype J] [DecidableEq J] [Fintype I]
    [DecidableEq I] (W : Matrix (J × I) (J × I) ℂ) (j₀ : J) :
    Matrix I I ℂ → Matrix I I ℂ :=
  fun ρ => ReducedState (FiberProjector j₀ * (W * AncillaSystemOp (vecOuter (Ket j₀)) ρ *
    Wᴴ) * FiberProjector j₀)

/-- The proposed trace-norm error property for repeated raw steps, with comparison operator `U ^
r * ρ * Uᴴ` and the stated perturbation budget. -/
def ResetDiscardSegmentation : Prop :=
  ∀ (J I : Type*) [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (W : Matrix (J × I) (J × I) ℂ) (j₀ : J) (X U : Matrix I I ℂ) (s δ₁ δ₂ : ℝ) (r : ℕ),
    IsBlockEncoding W j₀ X s → U ∈ Matrix.unitaryGroup I ℂ →
    ‖X - U‖ ≤ δ₁ → 1 ≤ s → |s - 2| ≤ δ₂ → δ₂ ≤ 1 →
    ∀ ρ : Matrix I I ℂ, ρ.PosSemidef → Matrix.trace ρ = 1 →
    Matrix.traceNorm ((ResetDiscardStep W j₀)^[r] ρ -
        U ^ r * ρ * Uᴴ) ≤
      2 * r * ((15 + 12 * δ₁ + 4 * δ₁ ^ 2) * δ₁ + 15 * δ₂)

/-- The system map obtained by preparing the ancillary basis state, applying oblivious
amplification of `W`, and tracing out the entire ancillary register. -/
noncomputable def ResetDiscardStepCorrected {J I : Type*} [Fintype J] [DecidableEq J]
    [Fintype I] [DecidableEq I] (W : Matrix (J × I) (J × I) ℂ) (j₀ : J) :
    Matrix I I ℂ → Matrix I I ℂ :=
  fun ρ => ReducedState
    (ObliviousAmplitudeAmplification (FiberProjector j₀) W *
      AncillaSystemOp (vecOuter (Ket j₀)) ρ *
      (ObliviousAmplitudeAmplification (FiberProjector j₀) W)ᴴ)

end Qatlib.Concepts.CoherentSim.ResetDiscard
