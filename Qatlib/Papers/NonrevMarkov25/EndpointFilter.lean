/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PolynomialCalc.EndpointFilter

/-!
# Endpoint polynomial filters for each parameter pair

For each gap and tolerance in `(0, 1)`, `source_per_instance` constructs a polynomial bounded on
`[-1, 1]`, small below the upper gap, and close to one on a terminal interval. The positive
degree constant and terminal-interval constant are existentially chosen for that parameter pair,
as formalized for the filter setting of [ClaudonPiquemalMonmarche2025].

## Main statements

* `source_per_instance`: For each `δ, ε` in `(0, 1)`, there are `0 < c < 1`, `C > 0`, and a
  polynomial of degree at most `C * δ^(-1/2) * log (1/ε)`. Its modulus is at most one on `[-1,
  1]` and at most `ε` on `[-1, 1 - δ]`, while its value is at least `1 - ε` on `[1 - c * δ, 1]`.

## References

* [Claudon et al., 2025][ClaudonPiquemalMonmarche2025]
-/

set_option autoImplicit false
namespace Qatlib.Papers.NonrevMarkov25.EndpointFilter

/-- For each `δ, ε` in `(0, 1)`, there are `0 < c < 1`, `C > 0`, and a polynomial of degree at
most `C * δ^(-1/2) * log (1/ε)`. Its modulus is at most one on `[-1, 1]` and at most `ε` on
`[-1, 1 - δ]`, while its value is at least `1 - ε` on `[1 - c * δ, 1]`
[ClaudonPiquemalMonmarche2025]. -/
theorem source_per_instance (δ ε : ℝ) (hδ0 : 0<δ) (hδ1 : δ<1) (hε0 : 0<ε) (hε1 : ε<1) :
    ∃ c : ℝ,0<c ∧ c<1 ∧ ∃ C : ℝ,0<C ∧ ∃ p : Polynomial ℝ,
      (p.natDegree : ℝ)≤C*Real.rpow δ (-(1/2 : ℝ))*Real.log (1/ε) ∧
      (∀ x : ℝ,-1≤x → x≤1 → |p.eval x|≤1) ∧
      (∀ x : ℝ,-1≤x → x≤1-δ → |p.eval x|≤ε) ∧
      (∀ x : ℝ,1-c*δ≤x → x≤1 → 1-ε≤p.eval x) :=
  Qatlib.Concepts.PolynomialCalc.EndpointFilter.per_instance_filter δ ε hδ0 hδ1 hε0 hε1
end Qatlib.Papers.NonrevMarkov25.EndpointFilter
