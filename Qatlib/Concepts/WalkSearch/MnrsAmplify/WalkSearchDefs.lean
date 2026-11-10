/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.FrameSpectral.DetectionDefs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option linter.unusedVariables false

open Qatlib.Concepts.WalkSearch.FrameSpectral

namespace Qatlib.Concepts.WalkSearch.MnrsAmplify

def Clause23Spec : Prop :=
  Clause20Spec

def Clause24Spec : Prop :=
  Clause21Spec

def Clause25Spec : Prop :=
  Clause22Spec

end Qatlib.Concepts.WalkSearch.MnrsAmplify
