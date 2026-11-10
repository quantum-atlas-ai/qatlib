/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HamLCUSim12.Multiproduct.MultiproductAnalyticInputs
set_option warningAsError false
set_option autoImplicit false

namespace Qatlib.Papers.HamLCUSim12.Multiproduct

def MultiproductEtaRecord : Prop :=
  ∃ η : ℝ, 305 / 1000 < η ∧ η < 312 / 1000 ∧ EtaMaxProperty η

end Qatlib.Papers.HamLCUSim12.Multiproduct
