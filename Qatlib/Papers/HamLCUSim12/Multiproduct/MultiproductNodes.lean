/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Data.Real.Basic
set_option autoImplicit false

namespace Qatlib.Papers.HamLCUSim12.Multiproduct
open scoped BigOperators

noncomputable def mNode (k : ℕ) (N : ℝ) (q : Fin (k+1)) : ℝ :=
  if (q : ℕ) < k then ((q : ℕ) + 1 : ℝ) else N

noncomputable def mCoeff (k : ℕ) (N : ℝ) (q : Fin (k+1)) : ℝ :=
  ∏ j : Fin (k+1), if j = q then 1 else mNode k N q ^ 2 / (mNode k N q ^ 2 - mNode k N j ^ 2)

def NodesDistinct (k : ℕ) (N : ℝ) : Prop :=
  ∀ j : Fin (k+1), (j : ℕ) < k → N ≠ ((j : ℕ) + 1 : ℝ)

end Qatlib.Papers.HamLCUSim12.Multiproduct
