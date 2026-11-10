/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CopyEvolution.SelfTomography.GramFirstRegisterDensityStat
set_option warningAsError false

set_option autoImplicit false
namespace Qatlib.Concepts.CopyEvolution.SelfTomography

theorem gramFirstRegisterDensity : GramFirstRegisterDensity := by
  exact Qatlib.Concepts.CopyEvolution.GramReadout.gramFirstRegisterDensity

end Qatlib.Concepts.CopyEvolution.SelfTomography
