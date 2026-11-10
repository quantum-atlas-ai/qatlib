/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PeriodSampling.DlogSamplingLaw.DlogTwoDimSamplingLawAnsw
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.PeriodSampling.DlogSamplingLaw

set_option autoImplicit false
namespace Qatlib.Concepts.PeriodSampling.FactorAlgorithm

theorem DlogTwoDimSamplingLaw_proof : DlogTwoDimSamplingLaw := dlogTwoDimSamplingLaw
end Qatlib.Concepts.PeriodSampling.FactorAlgorithm
