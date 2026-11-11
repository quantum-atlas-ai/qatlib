/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.AbelianSampling.WideGenerationSubgoalStat
import Qatlib.Concepts.StabilizerAlg.NearUniformGen.NearUniformGenerationSubgoalQuan
import Qatlib.Concepts.HspRecovery.AbelianSampling.AbelianStabilizerGenerationSubgoalQuan

/-!
# Stabilizer generation with the wider error bound

This module proves subgroup generation from samples whose subset probabilities differ from
uniform by at most `1 / (6 * (n + 4))`. The numerical estimate
`asp_generation_numeric_bound_wide` controls the union bound for `n + 4` independent samples and
yields `abelianStabilizerWideGenerationSubgoal`. [Kitaev1995]

## Main statements

* `asp_generation_numeric_bound_wide`: bounds the explicit numerical failure expression by `1 /
  3`.
* `abelianStabilizerWideGenerationSubgoal`: proves the near uniform subgroup generation
  guarantee.

## References

* [Kitaev, 1995][Kitaev1995]
-/

set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 800000
open Qatlib.Concepts.StabilizerAlg.NearUniformGen

namespace Qatlib.Concepts.HspRecovery.AbelianSampling
open scoped Classical BigOperators
open Qatlib

/-- If `m ≤ 2 ^ n`, then `(n + 4) / (6 * (n + 4)) + m * (1 / 2 + 1 / (6 * (n + 4))) ^ (n + 4) ≤
1 / 3` over the reals. -/
theorem asp_generation_numeric_bound_wide (n m : ℕ) (hm : m ≤ 2 ^ n) :
    ((n + 4 : ℕ) : ℝ) * (1 / ((6 : ℝ) * ((n + 4 : ℕ) : ℝ))) +
      (m : ℝ) * (1 / 2 + 1 / ((6 : ℝ) * ((n + 4 : ℕ) : ℝ))) ^ (n + 4) ≤ 1 / 3 := by
  let l := n + 4
  have hl : (0 : ℝ) < l := by dsimp [l]; positivity
  have hfirst : (l : ℝ) * (1 / ((6 : ℝ) * (l : ℝ))) = 1 / 6 := by field_simp
  have hfactor : (1 / 2 + 1 / ((6 : ℝ) * (l : ℝ)) : ℝ)
      = (1 / 2) * (1 + 1 / (3 * (l : ℝ))) := by ring
  have hexp : (1 + 1 / (3 * (l : ℝ))) ^ l ≤ Real.exp (1 / 3) := by
    have hh := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + 1 / (3 * (l : ℝ)))
      (by simpa only [add_comm] using Real.add_one_le_exp (1 / (3 * (l : ℝ)))) l
    rw [← Real.exp_nat_mul] at hh
    have he : (l : ℝ) * (1 / (3 * (l : ℝ))) = (1 / 3 : ℝ) := by field_simp
    simpa only [he, add_comm] using hh
  have hwindow : (1 / 2 + 1 / ((6 : ℝ) * (l : ℝ))) ^ l ≤ (1 / 2 : ℝ) ^ l * 2 := by
    calc
      (1 / 2 + 1 / ((6 : ℝ) * (l : ℝ))) ^ l
          = (1 / 2 : ℝ) ^ l * (1 + 1 / (3 * (l : ℝ))) ^ l := by
        rw [hfactor, mul_pow]
      _ ≤ (1 / 2 : ℝ) ^ l * Real.exp (1 / 3) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left asp_exp_third_le_two (by positivity)
  have hmR : (m : ℝ) ≤ (2 : ℝ) ^ n := by exact_mod_cast hm
  have hsecond : (m : ℝ) * (1 / 2 + 1 / ((6 : ℝ) * (l : ℝ))) ^ l ≤ 1 / 8 := by
    have hh := mul_le_mul hmR hwindow (by positivity) (by positivity)
    have he : (2 : ℝ) ^ n * ((1 / 2 : ℝ) ^ l * 2) = 1 / 8 := by
      dsimp [l]
      rw [pow_add, div_pow]
      norm_num
      field_simp
      norm_num
    rwa [he] at hh
  change (l : ℝ) * (1 / ((6 : ℝ) * (l : ℝ))) +
    (m : ℝ) * (1 / 2 + 1 / ((6 : ℝ) * (l : ℝ))) ^ l ≤ 1 / 3
  rw [hfirst]
  linarith

/-- For `n > 0` and a subgroup of size at most `2 ^ n`, a distribution whose subgroup subset
probabilities differ from uniform by at most `1 / (6 * (n + 4))` fails to generate that
subgroup from `n + 4` independent samples with probability at most `1 / 3` [Kitaev1995]. -/
theorem abelianStabilizerWideGenerationSubgoal :
    AbelianStabilizerWideGenerationSubgoal := by
  intro n _hn G _ _ _ H hcard μ hnear
  obtain ⟨maxs, _hproper, _hcover, hcount, hfail⟩ :=
    nearUniformGenerationSubgoal (n + 4) G H μ (1 / ((6 : ℝ) * ↑(n + 4)))
      (by positivity) hnear
  have hfail' :
      Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent (L := n + 4) μ
          (fun hs => AddSubgroup.closure (Set.range hs) ≠ (H : AddSubgroup G))
        ≤ ((n + 4 : ℕ) : ℝ) * (1 / ((6 : ℝ) * ↑(n + 4))) +
          (maxs.card : ℝ) * (1 / 2 + 1 / ((6 : ℝ) * ↑(n + 4))) ^ (n + 4) := hfail
  exact hfail'.trans (asp_generation_numeric_bound_wide n maxs.card
    (hcount.le.trans (by exact_mod_cast hcard)))

end Qatlib.Concepts.HspRecovery.AbelianSampling
