/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.MnrsAmplify.WalkSearchDefs
import Qatlib.Concepts.WalkSearch.FrameSpectral.Detection
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
set_option linter.unusedVariables false

open Qatlib.Concepts.WalkSearch.FrameSpectral

namespace Qatlib.Concepts.WalkSearch.MnrsAmplify

theorem stageB_walk_search_clause5 : Clause23Spec :=
  stageB_szegedy_source_detection_clause5

theorem stageB_walk_search_clause6 : Clause24Spec :=
  stageB_szegedy_source_detection_clause6

theorem stageB_walk_search_clause7 : Clause25Spec :=
  stageB_szegedy_source_detection_clause7

end Qatlib.Concepts.WalkSearch.MnrsAmplify
