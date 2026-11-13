/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.BlockEncoding.LinearCombination

/-!
# LCU circuit and selected-fiber success

`Fig3Circuit` composes an ancillary preparation, a selected branch operator, and an ancillary
output gate. `Fig3SuccessProb` measures the resulting mass in a specified ancillary fiber,
providing the circuit quantities for linear-combination analysis [ChildsWiebe2012].

## Main statements

* `Fig3Circuit`: The ancillary-gate and SELECT matrix product.
* `Fig3SuccessProb`: The selected ancillary-fiber measurement mass.

## References

* [Childs and Wiebe, 2012][ChildsWiebe2012]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LinearCombination
open Qatlib
open Qatlib

open Matrix

namespace Qatlib.Concepts.CoherentSim.ResetDiscard

/-- The LCU circuit matrix `TensorGate B 1 * (Select U * TensorGate A 1)`. -/
noncomputable def Fig3Circuit {J I : Type} [Fintype J] [DecidableEq J] [Fintype I]
    [DecidableEq I] (U : J → Matrix I I ℂ) (A B : Matrix J J ℂ) :
    Matrix (J × I) (J × I) ℂ :=
  TensorGate B 1 * (Select U * TensorGate A 1)

/-- The measurement mass in ancillary fiber `j₀` after applying `Fig3Circuit` to the embedded
input vector. -/
noncomputable def Fig3SuccessProb {J I : Type} [Fintype J] [DecidableEq J] [Fintype I]
    [DecidableEq I] (U : J → Matrix I I ℂ) (A B : Matrix J J ℂ) (j₀ : J) (ψ : QState I) :
    ℝ :=
  MeasureProb (ApplyGate (Fig3Circuit U A B) (TensorState (Ket j₀) ψ))
    ({j₀} ×ˢ Finset.univ)
end Qatlib.Concepts.CoherentSim.ResetDiscard
