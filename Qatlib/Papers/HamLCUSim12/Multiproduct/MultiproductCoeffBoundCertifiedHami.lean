/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HamLCUSim12.Multiproduct.MultiproductCoeffBoundCertifiedStat
import Qatlib.Papers.HamLCUSim12.Multiproduct.MultiproductEtaRecordHami
import Qatlib.Papers.HamLCUSim12.Multiproduct.MultiproductFactorialLowerBoundHami
import Qatlib.Papers.HamLCUSim12.Multiproduct.MultiproductCoeffBoundHami
set_option warningAsError false
set_option autoImplicit false
namespace Qatlib.Papers.HamLCUSim12.Multiproduct

theorem multiproductCoeffBoundCertified : MultiproductCoeffBoundCertified := by
  obtain ⟨η, hlo, hhi, hE⟩ := multiproductEtaRecord
  refine ⟨η, hlo, hhi, ?_⟩
  intro k hk γ hγ hc q hq
  exact multiproductCoeffBound k hk γ η hγ (by linarith) hE
    multiproductFactorialLowerBound hc q hq

end Qatlib.Papers.HamLCUSim12.Multiproduct
