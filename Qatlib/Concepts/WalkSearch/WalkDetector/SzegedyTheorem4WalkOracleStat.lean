/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.TwoLevelLower
import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Foundations.PureStateMath.Tensor
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.WalkSearch.TwoLevelLower

open Matrix

namespace Qatlib.Concepts.WalkSearch.WalkDetector

def SzegedyTheorem4WalkOracle : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (P : I → I → ℝ) (j : I),
    IsTransitionMatrix P →
    ∃ U : Matrix (I × I) (I × I) ℂ,
      U ∈ Matrix.unitaryGroup (I × I) ℂ ∧
      ∀ i, U *ᵥ TensorState (Ket i) (Ket j) = SzegedyIsometry P *ᵥ Ket i

end Qatlib.Concepts.WalkSearch.WalkDetector
