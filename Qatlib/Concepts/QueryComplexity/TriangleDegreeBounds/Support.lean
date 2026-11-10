/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.QueryDegree
import Qatlib.Concepts.QueryWordCore.QueryMachinery.NegativeAdversary
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QueryComplexity.DegreeMethod

namespace Qatlib.Concepts.QueryComplexity.TriangleDegreeBounds

open scoped Matrix.Norms.L2Operator

variable {I : Type} [Fintype I] [DecidableEq I]

noncomputable def sensAdjacency (f : (I → Bool) → Bool) : Matrix (I → Bool) (I → Bool) ℂ :=
  fun x y => if (Finset.univ.filter (fun i => x i ≠ y i)).card = 1 ∧ f x ≠ f y then 1 else 0

noncomputable def spectralSensitivity (f : (I → Bool) → Bool) : ℝ := ‖sensAdjacency f‖

noncomputable def gf2Degree (f : (I → Bool) → Bool) : ℕ :=
  sInf ((fun p : MvPolynomial I (ZMod 2) => p.totalDegree) ''
    {p : MvPolynomial I (ZMod 2) |
      ∀ x : I → Bool, MvPolynomial.eval (fun i => if x i then (1 : ZMod 2) else 0) p
        = if f x then 1 else 0})

end Qatlib.Concepts.QueryComplexity.TriangleDegreeBounds
