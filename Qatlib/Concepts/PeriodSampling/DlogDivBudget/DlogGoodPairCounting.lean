/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PeriodSampling.DlogGoodProb.DlogGoodPairCountingAnsw
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.PeriodSampling.DlogGoodProb

set_option autoImplicit false
namespace Qatlib.Concepts.PeriodSampling.DlogDivBudget

theorem DlogGoodPairCounting_proof : DlogGoodPairCounting := dlogGoodPairCounting
end Qatlib.Concepts.PeriodSampling.DlogDivBudget
