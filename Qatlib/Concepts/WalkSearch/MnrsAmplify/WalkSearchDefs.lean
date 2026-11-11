/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.FrameSpectral.DetectionDefs

/-!
# Quantum walk search contract aliases

Defines the MNRS-facing aliases `Clause23Spec`, `Clause24Spec`, and `Clause25Spec` for
established frame-spectral search contracts. These collect detection, compilation, and spectral
conclusions used in quantum walk search [MagniezNayakRolandSantha2011].

## Main statements

* `Clause23Spec`: The MNRS interface alias for `Clause20Spec`, which bundles walk setup,
  reachable dynamics, detection guarantees, and the associated spectral and amplification
  statements.
* `Clause24Spec`: The MNRS interface alias for `Clause21Spec`, which bundles empty-marked-set
  impossibility, zero success, the phase-search ledger, and associated search results.
* `Clause25Spec`: The MNRS interface alias for `Clause22Spec`, which bundles unmarked spectral
  compression, endpoint behavior, uniqueness of the unit discriminant singular value, and
  associated search results.

## References

* [Magniez et al., 2011][MagniezNayakRolandSantha2011]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option linter.unusedVariables false

open Qatlib.Concepts.WalkSearch.FrameSpectral

namespace Qatlib.Concepts.WalkSearch.MnrsAmplify

/-- The MNRS interface alias for `Clause20Spec`, which bundles walk setup, reachable dynamics,
detection guarantees, and the associated spectral and amplification statements. -/
def Clause23Spec : Prop :=
  Clause20Spec

/-- The MNRS interface alias for `Clause21Spec`, which bundles empty-marked-set impossibility,
zero success, the phase-search ledger, and associated search results. -/
def Clause24Spec : Prop :=
  Clause21Spec

/-- The MNRS interface alias for `Clause22Spec`, which bundles unmarked spectral compression,
endpoint behavior, uniqueness of the unit discriminant singular value, and associated search
results. -/
def Clause25Spec : Prop :=
  Clause22Spec

end Qatlib.Concepts.WalkSearch.MnrsAmplify
