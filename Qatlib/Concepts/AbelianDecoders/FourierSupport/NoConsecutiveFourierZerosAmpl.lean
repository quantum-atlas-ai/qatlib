/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AbelianDecoders.FourierSupport.NoConsecutiveFourierZerosStat
import Qatlib.Concepts.AbelianDecoders.FourierSupport.SparseFourierSupport

/-!
# Nonvanishing in cyclic Fourier windows

`noConsecutiveFourierZeros` proves that every cyclic Fourier window of length equal to the
original support size contains a nonzero coefficient. The statement applies to every nonzero
state on `ZMod N`. For background, see [Cornwell2014].

## Main statements

* `noConsecutiveFourierZeros`: For a nonzero state with support size `T`, every cyclic interval
  of `T` consecutive Fourier coordinates contains a nonzero coefficient. See [Cornwell, Lemma
  22][Cornwell2014].

## References

* [Cornwell, 2014][Cornwell2014]
-/

set_option autoImplicit false

namespace Qatlib.Concepts.AbelianDecoders.FourierSupport

/-- For a nonzero state with support size `T`, every cyclic interval of `T` consecutive Fourier
coordinates contains a nonzero coefficient. See [Cornwell, Lemma 22][Cornwell2014]. -/
theorem noConsecutiveFourierZeros : NoConsecutiveFourierZeros := by
  intro N _ ψ hψ a
  exact sparse_fourier_circular_window ψ hψ a

end Qatlib.Concepts.AbelianDecoders.FourierSupport
