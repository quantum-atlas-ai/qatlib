/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkFind.SearchAlgorithm.NativeSourceDefs

/-!
# Johnson eigenphase asymptotic specification

`JohnsonPhaseAsymptotic` names `JohnsonPhaseAsymptoticContract`, the asymptotic specification
for the Johnson-walk phases. It supplies the phase-scaling interface for the reduced-walk
analysis in [Ambainis2007ElementDistinctness].

## Main statements

* `JohnsonPhaseAsymptotic`: the named phase-asymptotic proposition.

## References

* [Ambainis, 2007][Ambainis2007ElementDistinctness]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.WalkFind.SearchAlgorithm
set_option autoImplicit false
namespace Qatlib.Concepts.WalkFind.WalkSpectrum

/-- The proposition `JohnsonPhaseAsymptoticContract`, specifying the asymptotic scale of
Johnson-walk eigenphases. -/
def JohnsonPhaseAsymptotic : Prop := JohnsonPhaseAsymptoticContract
end Qatlib.Concepts.WalkFind.WalkSpectrum
