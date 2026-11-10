/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ConversionCore.CoherentBound.StateConversionSDPLowerBoundStat
import Qatlib.Concepts.ConversionCore.CoherentBound.QueryDistanceLowerBoundQuan
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open scoped ComplexOrder MatrixOrder ENNReal
open Matrix

open Qatlib.Concepts.GramQueryCore.FilteredCert
open Qatlib.Concepts.GramQueryCore.GammaDuality

namespace Qatlib.Concepts.ConversionCore.CoherentBound

theorem stateConversionSDPLowerBound : StateConversionSDPLowerBound := by
  intro X _ _ n T R input ε hε hε1 ρ σ hρ hσ C hT hC hov
  obtain ⟨σ', hσ'psd, hcert1, hcert2⟩ :=
    stateConversionQueryDistanceLowerBound (X := X) (n := n) (T := T) (R := R)
      (input := input) (ε := ε) hε hε1 ρ σ hρ hσ C hT hC hov
  refine le_trans (iInf_le (fun σ'' : {σ'' : Matrix X X ℂ // σ''.PosSemidef ∧
      gramFilteredCert (σ'' - gramStateMatrix σ)
        (fun _ : Fin 1 => gramFilterAllOnes) (2 * Real.sqrt (2 * ε))}
      => filteredGamma2 (gramStateMatrix ρ - σ''.1) (gramFilterDelta input))
    ⟨σ', hσ'psd, hcert1⟩) ?_
  refine le_trans (filteredGamma2_le_of_gramFilteredCert hcert2) ?_
  have hcast : ENNReal.ofReal (2 * (T : ℝ)) = ((2 * T : ℕ) : ℝ≥0∞) := by
    rw [show (2 * (T : ℝ)) = ((2 * T : ℕ) : ℝ) from by
        rw [Nat.cast_mul, Nat.cast_ofNat], ENNReal.ofReal_natCast]
  rw [hcast]

end Qatlib.Concepts.ConversionCore.CoherentBound
