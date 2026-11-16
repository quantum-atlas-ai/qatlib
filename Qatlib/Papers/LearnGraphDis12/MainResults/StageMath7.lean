/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.LearnGraphDis12.MainResults.QueryCost
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section


/-!
Arithmetic components of Belovs, arXiv:1205.1534v2, Sections 4.2 and 5.2.
These identities do not construct a learning graph or a quantum query algorithm.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.LearnGraphDis12.MainResults

/-! ## The complexity optimisation of §4.2

The paper (p. 10) collects the stages into

`O(r·√(α/n) + n/√r)`  (stage I, with `k ≤ 2α`, and the dominant stage II.2),

and remarks that at `r = n·α^{-1/3}` this is `O(√n·α^{1/6})`.  The two terms are
in fact *equal* at that parameter choice, so the bound holds with the explicit
constant `2`. -/

/-- Fixed arXiv:1205.1534v2, §4.2 (p. 10).  With the optimal parameter
`r = n·α^{-1/3}` the two learning-graph stage costs of Theorem 7 are both
`√n·α^{1/6}`:

`r·√(α/n) + n/√r = 2·√n·α^{1/6}`  for `n > 0`, `α > 0`.

This is the arithmetic content of "the total complexity of the learning graph
is `O(√n α^{1/6})` if `r = n α^{-1/3}`"; it is the `k ≤ α`-free part, the
`k ≤ 2α` counting input having already been absorbed into the stage-I term by
the paper. -/
theorem learningGraph_complexity_optimized (n α : ℝ) (hn : 0 < n) (hα : 0 < α) :
    (n * α ^ (-(1 / 3 : ℝ))) * Real.sqrt (α / n) +
        n / Real.sqrt (n * α ^ (-(1 / 3 : ℝ)))
      = 2 * Real.sqrt n * α ^ (1 / 6 : ℝ) := by
  set t : ℝ := α ^ (1 / 3 : ℝ) with ht_def
  have ht : 0 < t := Real.rpow_pos_of_pos hα _
  have ht3 : t ^ 3 = α := by
    rw [ht_def, ← Real.rpow_natCast (α ^ (1 / 3 : ℝ)) 3, ← Real.rpow_mul hα.le]
    norm_num
  have hneg : α ^ (-(1 / 3 : ℝ)) = t⁻¹ := by
    rw [Real.rpow_neg hα.le, ht_def]
  have hsq : t ^ 2 * t = α := by rw [← ht3]; ring
  have hsqrtα : Real.sqrt α = t * Real.sqrt t := by
    conv_lhs => rw [← hsq]
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq ht.le]
  have hsqrtt : Real.sqrt t = α ^ (1 / 6 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ht_def, ← Real.rpow_mul hα.le]
    norm_num
  have htne : t ≠ 0 := ht.ne'
  have hnne : Real.sqrt n ≠ 0 := (Real.sqrt_pos.mpr hn).ne'
  rw [hneg]
  have h1 : (n * t⁻¹) * Real.sqrt (α / n) = Real.sqrt n * α ^ (1 / 6 : ℝ) := by
    rw [Real.sqrt_div hα.le n, hsqrtα]
    have hstep : (n * t⁻¹) * ((t * Real.sqrt t) / Real.sqrt n)
        = (n / Real.sqrt n) * Real.sqrt t := by
      field_simp
    rw [hstep, Real.div_sqrt, hsqrtt]
  have h2 : n / Real.sqrt (n * t⁻¹) = Real.sqrt n * α ^ (1 / 6 : ℝ) := by
    have hnt : n * t⁻¹ = n / t := by ring
    rw [hnt, Real.sqrt_div hn.le]
    have hstep : n / (Real.sqrt n / Real.sqrt t) = (n / Real.sqrt n) * Real.sqrt t := by
      field_simp
    rw [hstep, Real.div_sqrt, hsqrtt]
  rw [h1, h2]
  ring


end Qatlib.Papers.LearnGraphDis12.MainResults
