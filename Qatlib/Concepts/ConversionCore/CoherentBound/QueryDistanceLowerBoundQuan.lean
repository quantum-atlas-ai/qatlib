/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ConversionCore.CoherentBound.QueryDistanceLowerBoundStat
import Qatlib.Concepts.GramQueryCore.LowerBoundTools.QueryDistanceLowerBound
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open scoped ComplexOrder MatrixOrder
open Matrix

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.GramQueryCore.FilteredCert
open Qatlib.Concepts.GramQueryCore.LowerBoundTools
open Qatlib.Concepts.QueryComplexity.AdversarySearch

namespace Qatlib.Concepts.ConversionCore.CoherentBound

theorem stateConversionQueryDistanceLowerBound : StateConversionQueryDistanceLowerBound := by
  intro X _ _ n T R input ε hε hε1 ρ σ hρ hσ C hT hC hov
  let τ (x : X) := Run (workspaceBitOracle (W := Fin R) (input x)) C (ρ x)
  have hτ (x : X) : Normalized (τ x) :=
    hC.normalized_run (workspaceBitOracle_unitary (input x)) (hρ x)
  refine ⟨gramStateMatrix τ, ?_, ?_, ?_⟩
  · let V : Matrix ((Fin n × Bool) × Fin R) X ℂ := fun i x => τ x i
    have hg : gramStateMatrix τ = Vᴴ * V := by
      ext x y
      rfl
    rw [hg]
    exact Matrix.posSemidef_conjTranspose_mul_self V
  · exact gramFilteredCert_mono
      (gramFilteredCert_of_realPart_overlap hε.le hε1 τ σ hτ hσ hov)
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith : ε ≤ 2 * ε))
        (by norm_num))
  · exact gram_exact_state_conversion_filteredCert input ρ τ C hT hC hρ (fun _ _ => rfl)

end Qatlib.Concepts.ConversionCore.CoherentBound
