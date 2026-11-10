/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Field.GeomSum
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.FixedPntSrch05.MainResults.DeterministicProbability

open Finset

def deterministicProbability (ε : ℝ) (q : ℕ) : ℝ :=
  (1 - ε) / 2 + (1 + ε) / 2 * (1 - ε ^ 2) * (∑ j ∈ range (q - 1), (ε ^ 2) ^ j)

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

theorem deterministic_probability_q1 (ε : ℝ) :
    deterministicProbability ε 1 = (1 - ε) / 2 := by
  unfold deterministicProbability
  simp

end Qatlib.Papers.FixedPntSrch05.MainResults.DeterministicProbability
