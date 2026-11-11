/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PolynomialCalc.ChebyshevScale

/-!
# Unit-interval bound for the scaled Chebyshev filter

The theorem `source_interval_max` identifies the supremum of the absolute scaled filter values
on `[-1, 1]` as one. It supplies the normalization bound for the Chebyshev filters appearing in
[ClaudonPiquemalMonmarche2025].

## Main statements

* `source_interval_max`: For `0 < ε ≤ 1` and positive degree, the supremum of the absolute
  scaled Chebyshev filter values on `[-1, 1]` is one.

## References

* [Claudon et al., 2025][ClaudonPiquemalMonmarche2025]
-/

set_option autoImplicit false
open Qatlib.Concepts.PolynomialCalc.ChebyshevScale
namespace Qatlib.Papers.NonrevMarkov25.ChebyshevScale

/-- For `0 < ε ≤ 1` and positive degree, the supremum of the absolute scaled Chebyshev filter
values on `[-1, 1]` is one [ClaudonPiquemalMonmarche2025]. -/
theorem source_interval_max (ε : ℝ) (d : ℕ) (hε0 : 0<ε) (hε1 : ε≤1) (hd : 1≤d) :
    sSup (Set.range (fun x : {x : ℝ // |x|≤1} => |filterValue ε d x.1|))=1 :=
  filter_interval_max ε d hε0 hε1 hd
end Qatlib.Papers.NonrevMarkov25.ChebyshevScale
