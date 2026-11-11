/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkFind.SearchAlgorithm.NativeSourceDefs

/-!
# Normal spectral perturbation statement

`NormalSpectralPerturbation` names `NormalSpectralPerturbationContract`, the proposition used to
collect the finite-matrix perturbation estimates for Johnson-walk spectral analysis. See
[Bhatia1997] for the mathematical background.

## Main statements

* `NormalSpectralPerturbation`: the normal spectral perturbation proposition.

## References

* [Bhatia, 1997][Bhatia1997]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.WalkFind.SearchAlgorithm
set_option autoImplicit false
namespace Qatlib.Concepts.WalkFind.WalkSpectrum

/-- The proposition `NormalSpectralPerturbationContract`, naming the spectral perturbation
requirements used in the walk analysis. -/
def NormalSpectralPerturbation : Prop := NormalSpectralPerturbationContract
end Qatlib.Concepts.WalkFind.WalkSpectrum
