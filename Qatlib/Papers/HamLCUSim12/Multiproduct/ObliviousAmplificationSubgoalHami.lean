/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HamLCUSim12.Multiproduct.ObliviousAmplificationSubgoalStat
import Qatlib.Concepts.AmplitudeCore.InvFreePhase.Qubitization
import Qatlib.Concepts.BlockEncoding.LinearCombination
import Qatlib.Concepts.BlockEncoding.StateBlockEncoding.Basic

/-!
# An auxiliary qubitization projection identity

This module proves `obliviousAmplificationSubgoal` for an LCU of Hermitian unitaries with
nonnegative prepared weights. On a normalized eigenstate with real eigenvalue x, the projection
of the qubitization output onto the reference ancilla fiber is multiplied by 2x² − 1; the proof
uses `qubitization_amplifies_fiber`. See [ChildsWiebe2012] for the multiproduct and
linear-combination simulation framework.

## Main statements

* `obliviousAmplificationSubgoal`: For a prepared nonnegative LCU of Hermitian unitaries and a
  normalized eigenstate with real eigenvalue x, the reference-fiber projection of the
  qubitization output equals (2x² − 1) times the input tensor state.

## References

* [Childs and Wiebe, 2012][ChildsWiebe2012]
-/

set_option warningAsError false
open Qatlib.Concepts.BlockEncoding.LinearCombination
open Qatlib.Concepts.BlockEncoding.StateBlockEncoding
open Qatlib.Concepts.AmplitudeCore.InvFreePhase

namespace Qatlib.Papers.HamLCUSim12.Multiproduct

open Qatlib
open Matrix

/-- For a prepared nonnegative LCU of Hermitian unitaries and a normalized eigenstate with real
eigenvalue x, the reference-fiber projection of the qubitization output equals (2x² − 1)
times the input tensor state. -/
theorem obliviousAmplificationSubgoal : ObliviousAmplificationSubgoal := by
  intro J I _ _ _ _ U hU hUherm w hw P j₀ hP ψ hψ x hx
  have hA : (∑ j, w j • U j)ᴴ = ∑ j, w j • U j := by
    have hUje : ∀ (j : J) (a b : I), (starRingEnd ℂ) ((U j) b a) = (U j) a b := by
      intro j a b
      have h1 : (U j)ᴴ a b = (U j) a b := by rw [hUherm j]
      rw [Matrix.conjTranspose_apply] at h1
      simpa [RCLike.star_def] using h1
    ext i i'
    simp only [Matrix.conjTranspose_apply, Matrix.sum_apply, Matrix.smul_apply,
      Complex.real_smul, RCLike.star_def, map_sum, map_mul, starRingEnd_ofReal, hUje]
  exact qubitization_amplifies_fiber (LCUWorkspace U P) j₀ (∑ j, w j • U j)
    (lcu_isBlockEncoding U hU hw hP) hA ψ x hx

end Qatlib.Papers.HamLCUSim12.Multiproduct
