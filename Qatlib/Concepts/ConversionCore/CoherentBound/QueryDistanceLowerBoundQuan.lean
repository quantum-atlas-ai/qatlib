/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ConversionCore.CoherentBound.QueryDistanceLowerBoundStat
import Qatlib.Concepts.GramQueryCore.LowerBoundTools.QueryDistanceLowerBound

/-!
# Query distance certificates for coherent state conversion

`stateConversionQueryDistanceLowerBound` constructs a positive semidefinite intermediate Gram
matrix from the output of a unitary Boolean query circuit. A real overlap guarantee gives an
unfiltered certificate of budget `2 * Real.sqrt (2 * ε)`, while `T` queries give a
query-filtered certificate of budget `2 * T`.

The mathematical context is discussed in [LeeEtAl2011].

## Main statements

* `stateConversionQueryDistanceLowerBound`: The intermediate Gram matrix and its two certificate
  bounds.

## References

* [Lee et al., 2011][LeeEtAl2011]
-/

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

/-- For a unitary circuit with `T` queries and real overlaps at least √(1 − ε), where 0 < ε ≤ 1,
there exists a positive semidefinite intermediate Gram matrix with unfiltered error budget
2√(2ε) and query-filtered budget 2T [Lee et al., Theorem 4.9][LeeEtAl2011]. -/
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
