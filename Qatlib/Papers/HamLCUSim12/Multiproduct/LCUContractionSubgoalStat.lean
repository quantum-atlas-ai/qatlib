/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.BlockEncoding.LinearCombination

/-!
# Prepared LCU workspace corner contract

`LCUContractionSubgoal` states the action of a prepared LCU workspace on its selected ancilla
corner. It requires nonnegative weights summing to one and `IsPrepare P w j0`, and identifies
the corner with the weighted system-matrix sum applied to the input, as used in the LCU
framework of [ChildsWiebe2012].

## Main statements

* `LCUContractionSubgoal`: specifies the weighted-sum action of the selected workspace corner.

## References

* [Childs and Wiebe, 2012][ChildsWiebe2012]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LinearCombination
open Qatlib
open Qatlib

open Matrix

namespace Qatlib.Papers.HamLCUSim12.Multiproduct

/-- The proposition that an LCU workspace prepared with nonnegative weights summing to one has
its `j0` output corner equal to the weighted sum of system matrices applied to the input. -/
def LCUContractionSubgoal : Prop :=
  ∀ (J I : Type) [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (U : J → Matrix I I ℂ) (w : J → ℝ), (∀ j, 0 ≤ w j) → (∑ j, w j = 1) →
    ∀ (P : Matrix J J ℂ) (j0 : J), IsPrepare P w j0 → ∀ (ψ : QState I),
      (fun i' => (LCUWorkspace U P *ᵥ TensorState (Ket j0) ψ) (j0, i'))
        = (∑ j, w j • U j) *ᵥ ψ

end Qatlib.Papers.HamLCUSim12.Multiproduct
