/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AbelianDecoders.FourierSupport.FourierSupportUncertaintyStat
import Qatlib.Concepts.AbelianDecoders.FourierSupport.SparseFourierSupport

/-!
# Fourier support uncertainty

`fourierSupportUncertainty` proves the support-product uncertainty statement for nonzero states
on `ZMod N`. The product of the original and Fourier support cardinalities is at least `N`. For
background, see [Cornwell2014].

## Main statements

* `fourierSupportUncertainty`: Every nonzero state on `ZMod N` has original and Fourier support
  cardinalities whose product is at least `N`. See [Cornwell, Theorem 23][Cornwell2014].

## References

* [Cornwell, 2014][Cornwell2014]
-/

set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Concepts.AbelianDecoders.FourierSupport

/-- Every nonzero state on `ZMod N` has original and Fourier support cardinalities whose product
is at least `N`. See [Cornwell, Theorem 23][Cornwell2014]. -/
theorem fourierSupportUncertainty : FourierSupportUncertainty := by
  intro N _ ψ hψ
  exact sparse_fourier_support_product ψ hψ

end Qatlib.Concepts.AbelianDecoders.FourierSupport
