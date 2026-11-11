/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.VarTimeAmpAmp10.CoherentAA.CoherentAmplificationContracts

/-!
# The coherent amplification proposition

This module names the coherent amplitude-amplification statement `CoherentAmplification`. It is
defined to be `coherentAmplificationWindow`, which packages the success formula and probability
bounds used for the variable-time construction of [Ambainis2012].

## Main statements

* `CoherentAmplification`: The named coherent amplification proposition.

## References

* [Ambainis, 2012][Ambainis2012]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Papers.VarTimeAmpAmp10.CoherentAA

/-- The coherent amplitude-amplification proposition, defined as `coherentAmplificationWindow`. -/
def CoherentAmplification : Prop := coherentAmplificationWindow

end Qatlib.Papers.VarTimeAmpAmp10.CoherentAA
