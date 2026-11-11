/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PeriodSampling.DlogGoodProb.DlogGoodPairCountingAnsw

/-!
# Good-pair counting for discrete-logarithm recovery

This module exports the established `DlogGoodPairCounting` theorem into the divisibility-budget
namespace. For prime `p ≥ 3` and `p < q`, the theorem supplies lower bounds of `q / 12` for both
small-residue first coordinates and good coordinate pairs, with natural-number division.

These counting bounds belong to the good-output analysis of discrete-logarithm Fourier sampling
in [Shor1997].

## Main statements

* `DlogGoodPairCounting_proof`: the small-residue and good-pair cardinality bounds.

## References

* [Shor, 1997, Section 6][Shor1997]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.PeriodSampling.DlogGoodProb

set_option autoImplicit false
namespace Qatlib.Concepts.PeriodSampling.DlogDivBudget

/-- For prime `p ≥ 3` and `p < q`, there are at least `q / 12` small-residue first coordinates
and at least `q / 12` good coordinate pairs for each exponent parameter [Shor1997]. -/
theorem DlogGoodPairCounting_proof : DlogGoodPairCounting := dlogGoodPairCounting
end Qatlib.Concepts.PeriodSampling.DlogDivBudget
