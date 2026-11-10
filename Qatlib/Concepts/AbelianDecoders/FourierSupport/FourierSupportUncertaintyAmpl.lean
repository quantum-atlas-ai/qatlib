/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AbelianDecoders.FourierSupport.FourierSupportUncertaintyStat
import Qatlib.Concepts.AbelianDecoders.FourierSupport.SparseFourierSupport
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Concepts.AbelianDecoders.FourierSupport

theorem fourierSupportUncertainty : FourierSupportUncertainty := by
  intro N _ ψ hψ
  exact sparse_fourier_support_product ψ hψ

end Qatlib.Concepts.AbelianDecoders.FourierSupport
