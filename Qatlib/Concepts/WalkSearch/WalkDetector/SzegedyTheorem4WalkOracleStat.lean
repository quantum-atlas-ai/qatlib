/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.TwoLevelLower
import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Foundations.PureStateMath.Tensor

/-!
# Szegedy walk-oracle contract

`SzegedyTheorem4WalkOracle` states the existence of a unitary extending `SzegedyIsometry` on
inputs whose second register is a chosen basis state. It formulates the state-preparation oracle
for a finite transition matrix in the quantum-walk framework of [Szegedy2004].

## References

* [Szegedy, 2004][Szegedy2004]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.WalkSearch.TwoLevelLower

open Matrix

namespace Qatlib.Concepts.WalkSearch.WalkDetector

/-- The proposition that every finite transition matrix has a unitary on two registers agreeing
with `SzegedyIsometry` when the second input register is a fixed basis state. -/
def SzegedyTheorem4WalkOracle : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (P : I → I → ℝ) (j : I),
    IsTransitionMatrix P →
    ∃ U : Matrix (I × I) (I × I) ℂ,
      U ∈ Matrix.unitaryGroup (I × I) ℂ ∧
      ∀ i, U *ᵥ TensorState (Ket i) (Ket j) = SzegedyIsometry P *ᵥ Ket i

end Qatlib.Concepts.WalkSearch.WalkDetector
