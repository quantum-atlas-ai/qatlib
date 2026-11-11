/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.CBMDCompat

import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Derivatives of iterated derivatives within sets

This module identifies the ordinary derivative of `iteratedDerivWithin k` at points where the
underlying set is a neighborhood. The local and setwise smoothness forms provide calculus tools
for the contour regularity arguments supporting [WangEtAl2026].

## Main statements

* `ContDiffWithinAt.hasDerivAt_iteratedDerivWithin`: the local smoothness form.
* `ContDiffOn.hasDerivAt_iteratedDerivWithin`: the setwise smoothness form.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

namespace Qatlib.Foundations.CbmdAnalysis.Residue

section

open Set
open scoped ContDiff Topology

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {g : 𝕜 → E} {s : Set 𝕜} {x : 𝕜} {n : ℕ∞ω} {k : ℕ}

/-- At an interior neighborhood point of a set with unique derivatives, the derivative of the
`k`th derivative within the set is the next iterated derivative, provided `k < n`. -/
theorem ContDiffWithinAt.hasDerivAt_iteratedDerivWithin (hg : ContDiffWithinAt 𝕜 n g s x)
    (hk : k < n) (hs : UniqueDiffOn 𝕜 s) (hx : s ∈ 𝓝 x) :
    HasDerivAt (iteratedDerivWithin k g s) (iteratedDerivWithin (k + 1) g s x) x := by
  rw [iteratedDerivWithin_succ]
  exact (hg.differentiableWithinAt_iteratedDerivWithin hk
    (by rwa [insert_eq_of_mem (mem_of_mem_nhds hx)])).hasDerivWithinAt.hasDerivAt hx

/-- For a Cⁿ function on a set with unique derivatives, successive iterated derivatives within
the set satisfy the ordinary derivative relation at neighborhood points. -/
theorem ContDiffOn.hasDerivAt_iteratedDerivWithin (hg : ContDiffOn 𝕜 n g s) (hk : k < n)
    (hs : UniqueDiffOn 𝕜 s) (hx : s ∈ 𝓝 x) :
    HasDerivAt (iteratedDerivWithin k g s) (iteratedDerivWithin (k + 1) g s x) x :=
  ContDiffWithinAt.hasDerivAt_iteratedDerivWithin (hg x (mem_of_mem_nhds hx)) hk hs hx

end
end Qatlib.Foundations.CbmdAnalysis.Residue
