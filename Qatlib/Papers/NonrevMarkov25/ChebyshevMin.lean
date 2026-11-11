/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PolynomialCalc.ExtremalFilter

/-!
# Chebyshev filter candidate and band edge

This module exposes admissibility and exact degree for `filterPolynomial`, together with the
supremum of the level set where `filterValue` equals the tolerance. The results specialize the
Chebyshev filter construction used for nonreversible Markov chains in
[ClaudonPiquemalMonmarche2025].

## Main statements

* `source_candidate`: For `0 < ε < 1` and positive `k`, the scaled Chebyshev filter is
  admissible and has natural degree exactly `k`.
* `source_band_edge`: For positive `ε` and `k`, the supremum of points in `[-1, 1]` where the
  filter equals `ε` is `1 - bandWidth ε k`.

## References

* [Claudon et al., 2025][ClaudonPiquemalMonmarche2025]
-/

set_option autoImplicit false
open Qatlib.Concepts.PolynomialCalc.ChebyshevScale
open Qatlib.Concepts.PolynomialCalc.ExtremalFilter
namespace Qatlib.Papers.NonrevMarkov25.ChebyshevMin

/-- For `0 < ε < 1` and positive `k`, the scaled Chebyshev filter is admissible and has natural
degree exactly `k` [ClaudonPiquemalMonmarche2025]. -/
theorem source_candidate (ε : ℝ) (k : ℕ) (hε0 : 0<ε) (hε1 : ε<1) (hk : 1≤k) :
    AdmissibleFilter ε k (filterPolynomial ε k) ∧ (filterPolynomial ε k).natDegree=k :=
  candidate_membership ε k hε0 hε1 hk

/-- For positive `ε` and `k`, the supremum of points in `[-1, 1]` where the filter equals `ε` is
`1 - bandWidth ε k` [ClaudonPiquemalMonmarche2025]. -/
theorem source_band_edge (ε : ℝ) (k : ℕ) (hε0 : 0<ε) (hk : 1≤k) :
    sSup {x : ℝ | |x|≤1 ∧ filterValue ε k x=ε}=1-bandWidth ε k :=
  candidate_band_edge ε k hε0 hk
end Qatlib.Papers.NonrevMarkov25.ChebyshevMin
