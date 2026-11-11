/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Field.GeomSum
import Mathlib.Tactic

/-!
# Deterministic success probability for fixed-point search

`deterministicProbability` is the finite geometric-sum expression for deterministic success. The
module derives its closed form for `0 ≤ ε < 1` and `q ≥ 1`, and evaluates the initial case `q =
1`.

These constructions belong to the formalization of [TulsiGroverPatel2006].

## Main statements

* `deterministic_probability_eq`: the closed success-probability formula.
* `deterministic_probability_q1`: the initial success value.

## References

* [Tulsi et al., 2006][TulsiGroverPatel2006]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.FixedPntSrch05.MainResults.DeterministicProbability

open Finset

/-- The deterministic success expression consisting of the initial contribution `(1 - ε) / 2`
and a geometric sum with ratio `ε ^ 2` over `q - 1` further stages. -/
def deterministicProbability (ε : ℝ) (q : ℕ) : ℝ :=
  (1 - ε) / 2 + (1 + ε) / 2 * (1 - ε ^ 2) * (∑ j ∈ range (q - 1), (ε ^ 2) ^ j)

/-- For `0 ≤ ε < 1` and `q ≥ 1`, the deterministic success expression is `1 - ε ^ (2 * q - 2) *
(1 + ε) / 2`. [TulsiGroverPatel2006] -/
theorem deterministic_probability_eq (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε < 1) (q : ℕ)
    (hq : 1 ≤ q) :
    deterministicProbability ε q = 1 - ε ^ (2 * q - 2) * (1 + ε) / 2 := by
  have hxlt : ε ^ 2 < 1 := by nlinarith
  have hx : ε ^ 2 ≠ 1 := ne_of_lt hxlt
  have hden : 1 - ε ^ 2 ≠ 0 := by linarith
  unfold deterministicProbability
  have hgeo : (∑ j ∈ range (q - 1), (ε ^ 2) ^ j) =
      (1 - (ε ^ 2) ^ (q - 1)) / (1 - ε ^ 2) := by
    have := geom_sum_eq (x := ε ^ 2) hx (q - 1)
    rw [this]
    rw [show (ε ^ 2) ^ (q - 1) - 1 = - (1 - (ε ^ 2) ^ (q - 1)) by ring,
      show ε ^ 2 - 1 = - (1 - ε ^ 2) by ring, neg_div_neg_eq]
  rw [hgeo]
  have hpow : (ε ^ 2) ^ (q - 1) = ε ^ (2 * q - 2) := by
    rw [← pow_mul]
    congr 1
    omega
  rw [hpow]
  field_simp [hden]
  ring

/-- At `q = 1`, the deterministic success expression equals `(1 - ε) / 2`. See
[TulsiGroverPatel2006]. -/
theorem deterministic_probability_q1 (ε : ℝ) :
    deterministicProbability ε 1 = (1 - ε) / 2 := by
  unfold deterministicProbability
  simp

end Qatlib.Papers.FixedPntSrch05.MainResults.DeterministicProbability
