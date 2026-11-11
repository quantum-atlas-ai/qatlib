/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CopyEvolution.SelfTomography.GramFirstRegisterDensityStat

/-!
# The Gram first register is a density operator

This module proves `gramFirstRegisterDensity`: a weighted family of normalized states with
nonnegative weights of squared sum one defines a normalized Gram state. Tracing out its second
register gives `gramMatrix`, which is a density operator.

The mathematical background is described in [LloydMohseniRebentrost2014].

## Main statements

* `gramFirstRegisterDensity`: normalization, the partial-trace identity, and density-operator
  validity.

## References

* [Lloyd, Mohseni, and Rebentrost, 2014][LloydMohseniRebentrost2014]
-/

set_option warningAsError false

set_option autoImplicit false
namespace Qatlib.Concepts.CopyEvolution.SelfTomography

/-- Nonnegative weights of squared sum one and normalized input states yield a normalized Gram
state whose first-register reduction is `gramMatrix` and is a density operator. -/
theorem gramFirstRegisterDensity : GramFirstRegisterDensity := by
  exact Qatlib.Concepts.CopyEvolution.GramReadout.gramFirstRegisterDensity

end Qatlib.Concepts.CopyEvolution.SelfTomography
