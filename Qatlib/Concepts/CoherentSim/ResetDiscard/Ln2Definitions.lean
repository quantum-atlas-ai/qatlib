/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.ResetDiscard.ResetDiscardDefinitions
import Qatlib.Concepts.QspSimulation.Achievability.MatrixExponentialApproximation

/-!
# Log-two Taylor segment definitions

`truncatedSegment` is the finite matrix exponential series, and `ln2Scale` is its scalar mass at
`log 2`. `Ln2Segmentation` records a proposed bound for repeated raw reset-and-discard steps;
the associated analysis tests this formulation against the segmented Taylor method
[BerryEtAl2015Taylor].

## Main statements

* `truncatedSegment`: The Taylor polynomial through order `K`.
* `ln2Scale`: The truncated exponential mass at `log 2`.
* `Ln2Segmentation`: The proposed raw-step segmentation property.

## References

* [Berry et al., 2015][BerryEtAl2015Taylor]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.StateBlockEncoding

namespace Qatlib.Concepts.CoherentSim.ResetDiscard

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder

/-- The matrix Taylor polynomial for Hamiltonian evolution, summing terms of orders zero through
`K`. -/
noncomputable def truncatedSegment {I : Type*} [Fintype I] [DecidableEq I]
    (H : Matrix I I ℂ) (τ : ℝ) (K : ℕ) : Matrix I I ℂ :=
  ∑ k ∈ Finset.range (K + 1),
    ((-(τ : ℂ) * Complex.I) ^ k / ((k.factorial : ℕ) : ℂ)) • H ^ k

/-- The scalar exponential Taylor sum at `log 2`, through order `K`. -/
noncomputable def ln2Scale (K : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (K + 1), (Real.log 2) ^ k / ((k.factorial : ℕ) : ℝ)

/-- The proposition asserting trace-norm accuracy of repeated raw reset-and-discard Taylor
steps, with a segment count based on `Λ * t / log 2` and the specified tail budget. -/
def Ln2Segmentation : Prop :=
  ∀ (I : Type*) [Fintype I] [DecidableEq I]
    (H : Matrix I I ℂ) (t ε Λ : ℝ) (K : ℕ)
    (J : Type*) [Fintype J] [DecidableEq J]
    (W : Matrix (J × I) (J × I) ℂ) (j₀ : J),
    H.IsHermitian → 0 ≤ t → ‖H‖ ≤ Λ → 0 < Λ → 2 ≤ K → 0 < ε → ε ≤ 1 →
    IsBlockEncoding W j₀
      (truncatedSegment H (t / (max 1 (Nat.ceil (Λ * t / Real.log 2)))) K) (ln2Scale K) →
    (∑' j : ℕ, (Real.log 2) ^ (K + 1 + j) / (((K + 1 + j).factorial : ℕ) : ℝ)) ≤
      ε / (69 * (max 1 (Nat.ceil (Λ * t / Real.log 2)))) →
    ∀ ρ : Matrix I I ℂ, ρ.PosSemidef → Matrix.trace ρ = 1 →
    Matrix.traceNorm ((ResetDiscardStep W j₀)^[max 1 (Nat.ceil (Λ * t / Real.log 2))] ρ -
        HamiltonianEvolution H t * ρ * (HamiltonianEvolution H t)ᴴ) ≤ ε

end Qatlib.Concepts.CoherentSim.ResetDiscard
