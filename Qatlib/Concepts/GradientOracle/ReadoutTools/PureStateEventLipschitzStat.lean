/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GradientOracle.ReadoutTools.AlmostAffineGradient
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false


open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate

set_option autoImplicit false
namespace Qatlib.Concepts.GradientOracle.ReadoutTools
open Qatlib
open scoped Classical

def PureStateEventLipschitz : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (u v : QState I),
    Normalized u → Normalized v → ∀ E : Finset I,
      |MeasureProb u E - MeasureProb v E| ≤ ‖toEuclidean_fromVec (u-v)‖

end Qatlib.Concepts.GradientOracle.ReadoutTools
