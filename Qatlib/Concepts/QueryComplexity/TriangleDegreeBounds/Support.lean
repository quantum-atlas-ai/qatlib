/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.QueryDegree
import Qatlib.Concepts.QueryWordCore.QueryMachinery.NegativeAdversary

/-!
# Sensitivity graphs and Boolean degree

This module defines the sensitivity graph of a Boolean function and its operator-norm spectral
sensitivity. It also defines `gf2Degree` using polynomial representations over `ZMod 2`,
providing quantities for comparing spectral and polynomial complexity measures.

The mathematical background is described in [BealsEtAl2001].

## Main statements

* `sensAdjacency`: adjacency of sensitive edges of the Boolean cube.
* `spectralSensitivity`: the adjacency operator norm.
* `gf2Degree`: minimum polynomial degree over the field with two elements.

## References

* [Beals et al., 2001][BealsEtAl2001]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QueryComplexity.DegreeMethod

namespace Qatlib.Concepts.QueryComplexity.TriangleDegreeBounds

open scoped Matrix.Norms.L2Operator

variable {I : Type} [Fintype I] [DecidableEq I]

/-- The complex adjacency matrix connecting inputs that differ in exactly one coordinate and
have different function values. -/
noncomputable def sensAdjacency (f : (I → Bool) → Bool) : Matrix (I → Bool) (I → Bool) ℂ :=
  fun x y => if (Finset.univ.filter (fun i => x i ≠ y i)).card = 1 ∧ f x ≠ f y then 1 else 0

/-- The operator norm of the sensitivity-graph adjacency matrix of `f`. -/
noncomputable def spectralSensitivity (f : (I → Bool) → Bool) : ℝ := ‖sensAdjacency f‖

/-- The infimum of total degrees of polynomials over `ZMod 2` representing `f` on Boolean
assignments. -/
noncomputable def gf2Degree (f : (I → Bool) → Bool) : ℕ :=
  sInf ((fun p : MvPolynomial I (ZMod 2) => p.totalDegree) ''
    {p : MvPolynomial I (ZMod 2) |
      ∀ x : I → Bool, MvPolynomial.eval (fun i => if x i then (1 : ZMod 2) else 0) p
        = if f x then 1 else 0})

end Qatlib.Concepts.QueryComplexity.TriangleDegreeBounds
