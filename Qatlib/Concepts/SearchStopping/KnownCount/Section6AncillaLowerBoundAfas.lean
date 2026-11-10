/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.KnownCount.Section6AncillaLowerBoundStat
import Qatlib.Concepts.SearchStopping.KnownCount.Section6LabelSpaceLowerBoundAfas
set_option warningAsError false

set_option autoImplicit false
namespace Qatlib.Concepts.SearchStopping.KnownCount

theorem section6AncillaLowerBound : Section6AncillaLowerBound := by
  intro I W _ _ _ _ _
  apply section6LabelSpaceLowerBound I (I × W) Prod.fst
  intro i
  exact ⟨(i, Classical.choice (inferInstance : Nonempty W)), rfl⟩

end Qatlib.Concepts.SearchStopping.KnownCount
