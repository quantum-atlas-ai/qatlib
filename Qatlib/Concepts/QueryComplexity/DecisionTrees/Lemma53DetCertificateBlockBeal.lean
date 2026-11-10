/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DecisionTrees.Lemma53DetCertificateBlockStat
import Qatlib.Concepts.QueryComplexity.DecisionTrees.SensitivityCertificateTree
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.QueryComplexity.DecisionTrees
open Qatlib
open scoped Classical

theorem lemma53DeterministicCertificateBlock : Lemma53DeterministicCertificateBlock := by
  intro N f
  exact certificateTree_exists f

end Qatlib.Concepts.QueryComplexity.DecisionTrees
