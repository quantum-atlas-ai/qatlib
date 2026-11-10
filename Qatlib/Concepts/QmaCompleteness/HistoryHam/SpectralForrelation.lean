/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Foundations.PureStateMath

open Qatlib.Foundations.PureStateMath.BornBridge

namespace Qatlib.Concepts.QmaCompleteness.HistoryHam

open Qatlib
open scoped Matrix.Norms.L2Operator

variable (n : ℕ)

def charProjector (f : Reg n → Bool) : Matrix (Reg n) (Reg n) ℂ :=
  Matrix.diagonal fun x => if f x then 1 else 0

noncomputable def spectralForrelation (S U : Reg n → Bool) : ℝ :=
  (‖charProjector n U * HadamardN n * charProjector n S‖ : ℝ) ^ 2

noncomputable def forrWitnessMass (S U : Reg n → Bool) (ψ : QState (Reg n)) : ℝ :=
  ‖toEuclidean_fromVec ((charProjector n U * HadamardN n * charProjector n S).mulVec ψ)‖ ^ 2

end Qatlib.Concepts.QmaCompleteness.HistoryHam
