/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Sqrt
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.AmplitudeCountingConsumers

/-!
# Adaptive grids and readouts for exact counting

This module defines the two preliminary estimates, adaptive final grid, rounded output, and
weighted success and cost expressions used for exact counting in [BrassardEtAl2002]. The final
grid depends on the smaller of the two preliminary rough scales.

## Main statements

* `BHMTTh17.exactCountGrid`: the adaptive final grid size.
* `BHMTTh17.exactCountSuccessMass`: the probability of the correct rounded cardinality.
* `BHMTTh17.exactCountCostMass`: the expected total grid-size cost.

## References

* [Brassard et al., 2002][BrassardEtAl2002]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AmplitudeCore.PreparedReadout

namespace Qatlib.Concepts.AEMeanReadout.LocalAEBackend.BHMTTh17

/-- The preliminary estimation grid size `ceil (14 * π * sqrt N)` for exact counting. -/
noncomputable def exactCountM₀ (N : ℕ) : ℕ :=
  Nat.ceil (14*Real.pi*Real.sqrt (N : ℝ))

/-- The rough scale `sqrt ((t' + 1) * (N - t' + 1))` derived from a preliminary count estimate. -/
noncomputable def exactCountRough (N : ℕ) (t' : ℝ) : ℝ :=
  Real.sqrt ((t'+1)*((N : ℝ)-t'+1))

/-- The final grid size, obtained by rounding up thirty times the smaller preliminary rough
scale. -/
noncomputable def exactCountGrid (N : ℕ) (t'₁ t'₂ : ℝ) : ℕ :=
  Nat.ceil (30*(min (exactCountRough N t'₁) (exactCountRough N t'₂)))

/-- The integer output obtained by rounding the scaled amplitude estimate via `floor (N *
aeEstimate M z + 1/2)`. -/
noncomputable def exactCountOutput (N : ℕ) {M : ℕ} (z : Fin M) : ℤ :=
  ⌊(N : ℝ)*Qatlib.Concepts.AmplitudeCore.PreparedReadout.aeEstimate M z + 1/2⌋

/-- The joint probability that two independent preliminary estimates followed by the adaptive
final estimate produce the exact marked cardinality. -/
noncomputable def exactCountSuccessMass {N : ℕ} (hN : 0 < N) (S : Finset (Fin N))
    (hM₀ : 2 ≤ exactCountM₀ N)
    (hM : ∀ z₁ z₂ : Fin (exactCountM₀ N),
      2 ≤ exactCountGrid N
        ((N : ℝ)*Qatlib.Concepts.AmplitudeCore.PreparedReadout.aeEstimate (exactCountM₀ N) z₁)
        ((N : ℝ)*Qatlib.Concepts.AmplitudeCore.PreparedReadout.aeEstimate (exactCountM₀ N) z₂)) : ℝ :=
  ∑ z₁ : Fin (exactCountM₀ N), ∑ z₂ : Fin (exactCountM₀ N),
    ((Qatlib.Concepts.AmplitudeCore.PreparedReadout.aeLaw (exactCountM₀ N) (Qatlib.Concepts.SpectralFilter.PhaseReadout.QFTMatrix N)
        (⟨0, hN⟩ : Fin N) S (Qatlib.Concepts.SpectralFilter.PhaseReadout.qftMatrix_unitary hN) hM₀).prob z₁) *
    ((Qatlib.Concepts.AmplitudeCore.PreparedReadout.aeLaw (exactCountM₀ N) (Qatlib.Concepts.SpectralFilter.PhaseReadout.QFTMatrix N)
        (⟨0, hN⟩ : Fin N) S (Qatlib.Concepts.SpectralFilter.PhaseReadout.qftMatrix_unitary hN) hM₀).prob z₂) *
    (∑ y ∈ Finset.univ.filter
        (fun y : Fin (exactCountGrid N
            ((N : ℝ)*Qatlib.Concepts.AmplitudeCore.PreparedReadout.aeEstimate (exactCountM₀ N) z₁)
            ((N : ℝ)*Qatlib.Concepts.AmplitudeCore.PreparedReadout.aeEstimate (exactCountM₀ N) z₂)) =>
          exactCountOutput N y = ((S.card : ℕ) : ℤ)),
      (Qatlib.Concepts.AmplitudeCore.PreparedReadout.aeLaw
        (exactCountGrid N
          ((N : ℝ)*Qatlib.Concepts.AmplitudeCore.PreparedReadout.aeEstimate (exactCountM₀ N) z₁)
          ((N : ℝ)*Qatlib.Concepts.AmplitudeCore.PreparedReadout.aeEstimate (exactCountM₀ N) z₂))
        (Qatlib.Concepts.SpectralFilter.PhaseReadout.QFTMatrix N) (⟨0, hN⟩ : Fin N) S
        (Qatlib.Concepts.SpectralFilter.PhaseReadout.qftMatrix_unitary hN) (hM z₁ z₂)).prob y)

/-- The expected sum of the two preliminary grid sizes and the adaptive final grid size. -/
noncomputable def exactCountCostMass {N : ℕ} (hN : 0 < N) (S : Finset (Fin N))
    (hM₀ : 2 ≤ exactCountM₀ N)
    (_hM : ∀ z₁ z₂ : Fin (exactCountM₀ N),
      2 ≤ exactCountGrid N
        ((N : ℝ)*Qatlib.Concepts.AmplitudeCore.PreparedReadout.aeEstimate (exactCountM₀ N) z₁)
        ((N : ℝ)*Qatlib.Concepts.AmplitudeCore.PreparedReadout.aeEstimate (exactCountM₀ N) z₂)) : ℝ :=
  ∑ z₁ : Fin (exactCountM₀ N), ∑ z₂ : Fin (exactCountM₀ N),
    ((Qatlib.Concepts.AmplitudeCore.PreparedReadout.aeLaw (exactCountM₀ N) (Qatlib.Concepts.SpectralFilter.PhaseReadout.QFTMatrix N)
        (⟨0, hN⟩ : Fin N) S (Qatlib.Concepts.SpectralFilter.PhaseReadout.qftMatrix_unitary hN) hM₀).prob z₁) *
    ((Qatlib.Concepts.AmplitudeCore.PreparedReadout.aeLaw (exactCountM₀ N) (Qatlib.Concepts.SpectralFilter.PhaseReadout.QFTMatrix N)
        (⟨0, hN⟩ : Fin N) S (Qatlib.Concepts.SpectralFilter.PhaseReadout.qftMatrix_unitary hN) hM₀).prob z₂) *
    ((2*(exactCountM₀ N : ℕ) + exactCountGrid N
        ((N : ℝ)*Qatlib.Concepts.AmplitudeCore.PreparedReadout.aeEstimate (exactCountM₀ N) z₁)
        ((N : ℝ)*Qatlib.Concepts.AmplitudeCore.PreparedReadout.aeEstimate (exactCountM₀ N) z₂) : ℕ) : ℝ)
end Qatlib.Concepts.AEMeanReadout.LocalAEBackend.BHMTTh17
