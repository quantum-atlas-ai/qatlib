/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.ResetDiscard.ResetDiscardSegmentationCorrectedStat
import Qatlib.Concepts.CoherentSim.ResetDiscard.Ln2Definitions

/-!
# Statement of amplified log-two segmentation

`Ln2SegmentationCorrected` specifies a total trace-norm tolerance for repeated amplified
reset-and-discard Taylor steps. Its segment count and factorial-tail budget follow the log-two
segmentation strategy of [BerryEtAl2015Taylor].

## Main statements

* `Ln2SegmentationCorrected`: The proposition specifying the amplified segmented simulation
  guarantee.

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

/-- The proposition that repeated corrected reset-and-discard steps approximate Hamiltonian
conjugation within `ε` on density operators, using the stated log-two segment count,
encoding scale, and tail budget. -/
def Ln2SegmentationCorrected : Prop :=
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
    Matrix.traceNorm ((ResetDiscardStepCorrected W j₀)^[max 1 (Nat.ceil (Λ * t / Real.log 2))] ρ -
        HamiltonianEvolution H t * ρ * (HamiltonianEvolution H t)ᴴ) ≤ ε

end Qatlib.Concepts.CoherentSim.ResetDiscard
