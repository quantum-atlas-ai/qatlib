/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.MnrsAmplify.WalkSearchDefs
import Qatlib.Concepts.WalkSearch.FrameSpectral.Detection

/-!
# Quantum walk search interface theorems

Exports three established walk-detection and search contracts through the MNRS interface
[MagniezNayakRolandSantha2011]. The contracts bundle setup and reachable-subspace properties,
empty-marked-set and cost statements, and spectral endpoint estimates.

## Main statements

* `stageB_walk_search_clause5`: Establishes `Clause23Spec`, bundling walk setup,
  reachable-subspace dynamics, detection probability and operation bounds, and the associated
  amplification and spectral results.
* `stageB_walk_search_clause7`: Establishes `Clause25Spec`, bundling the unmarked compression
  bound, spectral endpoint properties, uniqueness of the unit discriminant singular value, and
  the associated detection and amplification results.

## References

* [Magniez et al., 2011][MagniezNayakRolandSantha2011]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Qatlib.Concepts.WalkSearch.FrameSpectral

namespace Qatlib.Concepts.WalkSearch.MnrsAmplify

/-- Establishes `Clause23Spec`, bundling walk setup, reachable-subspace dynamics, detection
probability and operation bounds, and the associated amplification and spectral results. -/
theorem stageB_walk_search_clause5 : Clause23Spec :=
  stageB_szegedy_source_detection_clause5

/-- Establishes `Clause24Spec`, including impossibility of positive-success find contracts for
an empty marked set, zero empty-set success, and the phase-search ledger. -/
theorem stageB_walk_search_clause6 : Clause24Spec :=
  stageB_szegedy_source_detection_clause6

/-- Establishes `Clause25Spec`, bundling the unmarked compression bound, spectral endpoint
properties, uniqueness of the unit discriminant singular value, and the associated detection
and amplification results. -/
theorem stageB_walk_search_clause7 : Clause25Spec :=
  stageB_szegedy_source_detection_clause7

end Qatlib.Concepts.WalkSearch.MnrsAmplify
