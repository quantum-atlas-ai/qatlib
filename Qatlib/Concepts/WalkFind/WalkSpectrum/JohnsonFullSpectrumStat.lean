/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkFind.SearchAlgorithm.NativeSourceDefs

/-!
# Full Johnson-walk spectrum specification

`JohnsonFullSpectrum` names `JohnsonFullSpectrumContract`, the spectral specification for the
reduced Johnson walk. It provides the interface for the spectral decomposition used in the
collision-search analysis of [Ambainis2007ElementDistinctness].

## Main statements

* `JohnsonFullSpectrum`: the full-spectrum proposition.

## References

* [Ambainis, 2007][Ambainis2007ElementDistinctness]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.WalkFind.SearchAlgorithm
set_option autoImplicit false
namespace Qatlib.Concepts.WalkFind.WalkSpectrum

/-- The proposition `JohnsonFullSpectrumContract`, specifying the full reduced Johnson-walk
spectrum. -/
def JohnsonFullSpectrum : Prop := JohnsonFullSpectrumContract
end Qatlib.Concepts.WalkFind.WalkSpectrum
