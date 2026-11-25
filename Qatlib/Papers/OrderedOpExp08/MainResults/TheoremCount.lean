/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.OrderedOpExp08.MainResults.SegmentSelection

@[expose] public section

/-!
# The paper's segment count as a commutator budget

[WiebeEtAl2010], Theorem 1 and Eq. (11) on p. 5, propose the segment count
`N = 5 k Λ Δ (5 / 3)^k (Λ Δ / ε)^(1 / (2k))`, encoded as
`Qatlib.Papers.OrderedOpExp08.MainResults.theorem1Count`. That expression is the segment
selector `orderedSegments` applied to one particular value of the commutator coefficient,
`(5 k Λ Δ (5 / 3)^k)^(2k) * (Λ Δ)`. This module records that identification and transfers it:
whenever the coefficient of a word stays within the paper's budget, its selected segment count
is at most `theorem1Count`, so the count expression finally acquires a consumer.

## Main statements

* `segments_le_ceil_of_coefficient_le`: monotonicity of the segment selector in its coefficient.
* `theorem1Count_eq_segments`: Eq. (11) is the selector at the paper's coefficient budget.
* `orderedSegments_le_theorem1Count_of_coefficient_bound`: the count bound from a coefficient
  budget.

## Boundary

The coefficient budget is a hypothesis, not a theorem: it asks that the prefix commutator budget
`Qatlib.Concepts.TrotterFormula.GeneralOrder.orderedErrorCoefficient` of the word is at most
`(5 k Λ Δ (5 / 3)^k)^(2k) * (Λ Δ)`. That statement is the paper's own estimate of the nested
commutator mass; the library only has the conservative `3 ^ (k - 1) * Λ` mass bound, whose
`(2k + 1)`st power carries a `3 ^ (4 k^2)`-type factor against the paper's `(5 / 3) ^ (2 k^2)`,
so it does not imply the budget for large `k`. Nothing here re-derives Eq. (11) from the word.

## References

* [Wiebe et al., 2010][WiebeEtAl2010], Theorem 1, Eq. (11), p. 5,
  [arXiv:0812.0562](https://arxiv.org/abs/0812.0562)
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open Matrix
open Qatlib.Concepts.TrotterFormula.GeneralOrder
open scoped Classical BigOperators Matrix.Norms.L2Operator

namespace Qatlib.Papers.OrderedOpExp08.MainResults

open Qatlib.Papers.OrderedOpExp08.MainResults

/-- The segment selector is monotone in its coefficient: a smaller coefficient needs no more
segments than a larger one. -/
theorem segments_le_ceil_of_coefficient_le {C D ε : ℝ} {p : ℕ}
    (hC : 0 ≤ C) (hε : 0 < ε) (hCD : C ≤ D) :
    segments C ε p ≤ max 1 (Nat.ceil ((D / ε) ^ ((p : ℝ)⁻¹))) := by
  unfold segments
  have hdiv : C / ε ≤ D / ε := by gcongr
  have h0 : 0 ≤ C / ε := div_nonneg hC hε.le
  have hr : (C / ε) ^ ((p : ℝ) ⁻¹) ≤ (D / ε) ^ ((p : ℝ) ⁻¹) :=
    Real.rpow_le_rpow h0 hdiv (inv_nonneg.mpr (Nat.cast_nonneg p))
  exact max_le_max le_rfl (Nat.ceil_mono hr)

/-- The paper's count expression of Eq. (11) is the segment selector applied to the paper's
commutator budget `(5 k Λ Δ (5 / 3)^k)^(2k) * (Λ Δ)`. -/
theorem theorem1Count_eq_segments {Λ ε dlam : ℝ} {k : ℕ}
    (hΛ : 0 < Λ) (hdlam : 0 < dlam) (hε : 0 < ε) (hk : 0 < k) :
    theorem1Count Λ ε dlam k =
      segments ((5 * (k : ℝ) * Λ * dlam * ((5 : ℝ) / 3) ^ k) ^ (2 * k) * (Λ * dlam)) ε
        (2 * k) := by
  set A : ℝ := 5 * (k : ℝ) * Λ * dlam * ((5 : ℝ) / 3) ^ k with hA
  have hA0 : 0 < A := by
    rw [hA]
    positivity
  have h2k : (2 * k : ℕ) ≠ 0 := by omega
  have hroot : ((A ^ (2 * k) * (Λ * dlam)) / ε) ^ (((2 * k : ℕ) : ℝ)⁻¹) =
      A * ((Λ * dlam) / ε) ^ (((2 * k : ℕ) : ℝ)⁻¹) := by
    have hsplit : (A ^ (2 * k) * (Λ * dlam)) / ε = A ^ (2 * k) * ((Λ * dlam) / ε) := by
      ring
    rw [hsplit, Real.mul_rpow (by positivity) (by positivity),
      Real.pow_rpow_inv_natCast hA0.le h2k]
  have hpos : 0 < A * ((Λ * dlam) / ε) ^ (((2 * k : ℕ) : ℝ)⁻¹) :=
    mul_pos hA0 (Real.rpow_pos_of_pos (by positivity) _)
  unfold theorem1Count segments
  rw [hroot, max_eq_right (Nat.one_le_ceil_iff.mpr hpos)]
  congr 1
  rw [hA]
  push_cast
  ring

/-- If the prefix commutator coefficient of a word stays within the paper's budget of Eq. (11),
the selected segment count is at most `theorem1Count` [WiebeEtAl2010]. -/
theorem orderedSegments_le_theorem1Count_of_coefficient_bound {I : Type} [Fintype I]
    [DecidableEq I] {m : ℕ} (H : Fin m → ℝ → Matrix I I ℂ) (μ Λ ε dlam : ℝ) (k : ℕ)
    (hΛ : 0 < Λ) (hdlam : 0 < dlam) (hε : 0 < ε) (hk : 0 < k)
    (hcoef : orderedErrorCoefficient (ltsGenerators H μ dlam (k - 1)) (2 * k) dlam ≤
      (5 * (k : ℝ) * Λ * dlam * ((5 : ℝ) / 3) ^ k) ^ (2 * k) * (Λ * dlam)) :
    orderedSegments (ltsGenerators H μ dlam (k - 1)) (2 * k) dlam ε ≤
      theorem1Count Λ ε dlam k := by
  have hC := orderedErrorCoefficient_nonneg (ltsGenerators H μ dlam (k - 1)) (2 * k) dlam
  have hstep := segments_le_ceil_of_coefficient_le (p := 2 * k) hC hε hcoef
  rw [theorem1Count_eq_segments hΛ hdlam hε hk]
  unfold orderedSegments
  exact hstep

end Qatlib.Papers.OrderedOpExp08.MainResults
