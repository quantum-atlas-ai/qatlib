/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SignalPrimitive.LCUConsumers.InvariantSubspaceSubgoal
import Qatlib.Concepts.AmplitudeCore.InvFreePhase.Qubitization

/-!
# LCU Invariant Plane Construction

This module proves `invariantSubspaceSubgoal` by applying the general qubitization
invariant-subspace theorem to `LCUWorkspace U P`. A nonnegative prepared combination of
Hermitian unitaries supplies a Hermitian encoded operator in the setting of [LowChuang2019].

For each normalized eigenvector with `|x| < 1`, the result supplies an orthonormal pair on which
the walk acts with coefficients `2 * x ^ 2 - 1` and `2 * x * y`, where `y > 0` and `x ^ 2 + y ^
2 = 1`.

## Main statements

* `invariantSubspaceSubgoal` proves the LCU invariant-plane contract from the concrete block
  encoding.

## References

- [Low and Chuang, 2019][LowChuang2019].
-/

set_option warningAsError false
open Qatlib.Concepts.AmplitudeCore.InvFreePhase
open Qatlib.Concepts.BlockEncoding.StateBlockEncoding Qatlib.Concepts.SignalPrimitive.LCUConsumers
open Qatlib.Concepts.BlockEncoding.LinearCombination

namespace Qatlib.Concepts.SignalPrimitive.MainResults

open Qatlib
open Matrix

/-- Proves the LCU invariant-plane contract by applying the general qubitization
invariant-subspace theorem to the prepared linear combination of Hermitian unitaries. -/
theorem invariantSubspaceSubgoal : InvariantSubspaceSubgoal := by
  intro J I _ _ _ _ U hU hUherm w hw P j₀ hP ψ hψ x hx1 hx
  have hUje : ∀ (j : J) (a b : I), (starRingEnd ℂ) ((U j) b a) = (U j) a b := by
    intro j a b
    have h1 : (U j)ᴴ a b = (U j) a b := by rw [hUherm j]
    rw [Matrix.conjTranspose_apply] at h1
    simpa [RCLike.star_def] using h1
  have hA : (∑ j, w j • U j)ᴴ = ∑ j, w j • U j := by
    ext i i'
    simp only [Matrix.conjTranspose_apply, Matrix.sum_apply, Matrix.smul_apply,
      Complex.real_smul, RCLike.star_def, map_sum, map_mul, starRingEnd_ofReal, hUje]
  exact qubitization_invariant_subspace (LCUWorkspace U P) j₀ (∑ j, w j • U j)
    (lcu_isBlockEncoding U hU hw hP) hA ψ hψ x hx hx1

end Qatlib.Concepts.SignalPrimitive.MainResults
