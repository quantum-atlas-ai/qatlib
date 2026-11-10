/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HamLCUSim12.Multiproduct.MultiproductCoefficientAux
import Qatlib.Papers.HamLCUSim12.Multiproduct.MultiproductCoefficientDiagnostics
set_option warningAsError false
set_option autoImplicit false
namespace Qatlib.Papers.HamLCUSim12.Multiproduct

theorem multiproductMassStructure : MultiproductMassStructure := by
  intro k hk N hN
  exact ⟨multiproduct_last_coefficient_ge_one k hk N hN,
    ⟨⟨k-1, by omega⟩, multiproduct_penultimate_negative k hk N hN⟩⟩

end Qatlib.Papers.HamLCUSim12.Multiproduct
