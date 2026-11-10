/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.CBMDCompat

import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

namespace Qatlib.Foundations.CbmdAnalysis.Residue

section

open Set
open scoped ContDiff Topology

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {g : 𝕜 → E} {s : Set 𝕜} {x : 𝕜} {n : ℕ∞ω} {k : ℕ}

theorem ContDiffWithinAt.hasDerivAt_iteratedDerivWithin (hg : ContDiffWithinAt 𝕜 n g s x)
    (hk : k < n) (hs : UniqueDiffOn 𝕜 s) (hx : s ∈ 𝓝 x) :
    HasDerivAt (iteratedDerivWithin k g s) (iteratedDerivWithin (k + 1) g s x) x := by
  rw [iteratedDerivWithin_succ]
  exact (hg.differentiableWithinAt_iteratedDerivWithin hk
    (by rwa [insert_eq_of_mem (mem_of_mem_nhds hx)])).hasDerivWithinAt.hasDerivAt hx

theorem ContDiffOn.hasDerivAt_iteratedDerivWithin (hg : ContDiffOn 𝕜 n g s) (hk : k < n)
    (hs : UniqueDiffOn 𝕜 s) (hx : s ∈ 𝓝 x) :
    HasDerivAt (iteratedDerivWithin k g s) (iteratedDerivWithin (k + 1) g s x) x :=
  ContDiffWithinAt.hasDerivAt_iteratedDerivWithin (hg x (mem_of_mem_nhds hx)) hk hs hx

end
end Qatlib.Foundations.CbmdAnalysis.Residue
