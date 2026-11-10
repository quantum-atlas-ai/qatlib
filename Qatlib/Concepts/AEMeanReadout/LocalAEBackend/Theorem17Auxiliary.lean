/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Sqrt
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.AmplitudeCountingConsumers
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AmplitudeCore.PreparedReadout

namespace Qatlib.Concepts.AEMeanReadout.LocalAEBackend.BHMTTh17

noncomputable def exactCountM₀ (N : ℕ) : ℕ :=
  Nat.ceil (14*Real.pi*Real.sqrt (N : ℝ))

noncomputable def exactCountRough (N : ℕ) (t' : ℝ) : ℝ :=
  Real.sqrt ((t'+1)*((N : ℝ)-t'+1))

noncomputable def exactCountGrid (N : ℕ) (t'₁ t'₂ : ℝ) : ℕ :=
  Nat.ceil (30*(min (exactCountRough N t'₁) (exactCountRough N t'₂)))

noncomputable def exactCountOutput (N : ℕ) {M : ℕ} (z : Fin M) : ℤ :=
  ⌊(N : ℝ)*Qatlib.Concepts.AmplitudeCore.PreparedReadout.aeEstimate M z + 1/2⌋

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
