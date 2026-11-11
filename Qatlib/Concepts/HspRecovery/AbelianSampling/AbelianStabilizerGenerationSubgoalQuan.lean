/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Lean.Elab.Tactic.NormCast
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Qatlib.Concepts.HspRecovery.AbelianSampling.AbelianStabilizerGenerationSubgoalStat
import Qatlib.Concepts.StabilizerAlg.NearUniformGen.NearUniformGenerationSubgoalQuan

/-!
# Generation bounds for abelian stabilizer sampling

This module proves the numerical estimate needed to turn near-uniform subgroup samples into a
generation guarantee for the abelian stabilizer problem [Kitaev1995]. The generic near-uniform
generation bound is instantiated with `n+4` samples and discrepancy `1/(6*k*(n+4))`.

The resulting failure probability is at most `1/3` for a subgroup of cardinality at most `2^n`,
as specified by `AbelianStabilizerGenerationSubgoal`.

## Main statements

* `asp_generation_numeric_bound`: the numerical failure estimate.
* `abelianStabilizerGenerationSubgoal`: the subgroup-generation guarantee.

## References

* [Kitaev, 1995][Kitaev1995]
-/

set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 800000
open Qatlib.Concepts.StabilizerAlg.NearUniformGen

namespace Qatlib.Concepts.HspRecovery.AbelianSampling
open scoped Classical BigOperators

/-- The real exponential satisfies `exp (1/3) ≤ 2`. -/
theorem asp_exp_third_le_two : Real.exp (1/3) ≤ 2 := by
  have h3 : Real.exp (1/3)^3=Real.exp 1 := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
  by_contra hn
  have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2)
    (le_of_lt (lt_of_not_ge hn)) 3
  rw [h3] at hh
  norm_num at hh
  linarith [Real.exp_one_lt_three]

/-- For positive `k` and `m ≤ 2^n`, the stated sum of the discrepancy term and the
maximal-subgroup failure term is at most `1/3`. -/
theorem asp_generation_numeric_bound (n k m : ℕ) (hk : 0 < k) (hm : m ≤ 2^n) :
    ((n+4 : ℕ) : ℝ)*(1/(6*(k : ℝ)*((n+4 : ℕ) : ℝ)))+
      (m : ℝ)*(1/2+1/(6*(k : ℝ)*((n+4 : ℕ) : ℝ)))^(n+4) ≤ 1/3 := by
  let l := n+4
  have hl : (0 : ℝ) < l := by dsimp [l]; positivity
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hd : 1/(6*(k : ℝ)*(l : ℝ)) ≤ 1/(6*(l : ℝ)) := by
    apply one_div_le_one_div_of_le (by positivity)
    have hh := mul_le_mul_of_nonneg_left hk1 (by positivity : 0 ≤ 6*(l : ℝ))
    nlinarith
  have hfirst : (l : ℝ)*(1/(6*(k : ℝ)*(l : ℝ))) ≤ 1/6 := by
    have hh := mul_le_mul_of_nonneg_left hd hl.le
    have he : (l : ℝ)*(1/(6*(l : ℝ)))=1/6 := by field_simp
    rwa [he] at hh
  have hfactor : (1/2+1/(6*(l : ℝ)) : ℝ)=(1/2)*(1+1/(3*(l : ℝ))) := by ring
  have hexp : (1+1/(3*(l : ℝ)))^l ≤ Real.exp (1/3) := by
    have hh := pow_le_pow_left₀ (by positivity : 0 ≤ 1+1/(3*(l : ℝ)))
      (by simpa only [add_comm] using Real.add_one_le_exp (1/(3*(l : ℝ)))) l
    rw [← Real.exp_nat_mul] at hh
    have he : (l : ℝ)*(1/(3*(l : ℝ)))=(1/3 : ℝ) := by field_simp
    simpa only [he, add_comm] using hh
  have hwindow : (1/2+1/(6*(k : ℝ)*(l : ℝ)))^l ≤ (1/2 : ℝ)^l*2 := by
    calc
      _ ≤ (1/2+1/(6*(l : ℝ)))^l :=
        pow_le_pow_left₀ (by positivity : 0 ≤ (1/2 : ℝ)+1/(6*(k : ℝ)*(l : ℝ)))
          (by simpa only [add_comm] using add_le_add_left hd (1/2 : ℝ)) l
      _ = (1/2 : ℝ)^l*(1+1/(3*(l : ℝ)))^l := by rw [hfactor, mul_pow]
      _ ≤ (1/2 : ℝ)^l*Real.exp (1/3) := mul_le_mul_of_nonneg_left hexp (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left asp_exp_third_le_two (by positivity)
  have hmR : (m : ℝ) ≤ (2 : ℝ)^n := by exact_mod_cast hm
  have hsecond : (m : ℝ)*(1/2+1/(6*(k : ℝ)*(l : ℝ)))^l ≤ 1/8 := by
    have hh := mul_le_mul hmR hwindow (by positivity) (by positivity)
    have he : (2 : ℝ)^n*((1/2 : ℝ)^l*2)=1/8 := by
      dsimp [l]
      rw [pow_add, div_pow]
      norm_num
      field_simp
      norm_num
    rwa [he] at hh
  change (l : ℝ)*(1/(6*(k : ℝ)*(l : ℝ)))+
    (m : ℝ)*(1/2+1/(6*(k : ℝ)*(l : ℝ)))^l ≤ 1/3
  linarith

/-- The abelian stabilizer generation specification holds: under its cardinality and
near-uniformity hypotheses, `n+4` independent samples fail to generate the subgroup with
probability at most `1/3`. -/
theorem abelianStabilizerGenerationSubgoal : AbelianStabilizerGenerationSubgoal := by
  intro n k _hn hk G _ _ _ H hcard μ hnear
  obtain ⟨maxs,_hproper,_hcover,hcount,hfail⟩ := nearUniformGenerationSubgoal
    (n+4) G H μ (1/(6*(k : ℝ)*((n+4 : ℕ) : ℝ))) (by positivity) hnear
  exact hfail.trans (asp_generation_numeric_bound n k maxs.card hk (hcount.le.trans hcard))

end Qatlib.Concepts.HspRecovery.AbelianSampling
