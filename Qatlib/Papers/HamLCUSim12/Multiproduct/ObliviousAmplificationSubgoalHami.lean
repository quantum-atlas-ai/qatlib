/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HamLCUSim12.Multiproduct.ObliviousAmplificationSubgoalStat
import Qatlib.Concepts.AmplitudeCore.InvFreePhase.Qubitization
import Qatlib.Concepts.BlockEncoding.LinearCombination
import Qatlib.Concepts.BlockEncoding.StateBlockEncoding.Basic
set_option warningAsError false
open Qatlib.Concepts.BlockEncoding.LinearCombination
open Qatlib.Concepts.BlockEncoding.StateBlockEncoding
open Qatlib.Concepts.AmplitudeCore.InvFreePhase

namespace Qatlib.Papers.HamLCUSim12.Multiproduct

open Qatlib
open Matrix

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
