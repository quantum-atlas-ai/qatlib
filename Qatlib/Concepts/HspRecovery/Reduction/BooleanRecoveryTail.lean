/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.Reduction.BooleanRecoveryRank
set_option warningAsError false

open Qatlib.Concepts.WalkFind.UniformThree
open Qatlib.Concepts.HspRecovery.Distinguisher
open Qatlib.Concepts.PauliClifford.ExactRank

namespace Qatlib.Concepts.HspRecovery.ReductionCore

open scoped Classical

theorem two_pow_sub_one_div_two_pow_add_le_half_pow (r k : ℕ) :
    (((2 : ℝ) ^ r - 1) / (2 : ℝ) ^ (r + k)) ≤ (1 / 2 : ℝ) ^ k := by
  have hden : 0 < (2 : ℝ) ^ (r + k) := by positivity
  have hk : (2 : ℝ) ^ k ≠ 0 := by positivity
  rw [div_le_iff₀ hden]
  have hcancel : (1 / 2 : ℝ) ^ k * (2 : ℝ) ^ (r + k) = (2 : ℝ) ^ r := by
    rw [pow_add, div_pow, one_pow]
    field_simp [hk]
  rw [hcancel]
  linarith

variable {n : ℕ}
variable {R : Type*} [AddCommGroup R] [Fintype R] [DecidableEq R]

theorem hiddenSubgroupFreshSamples_boolean_failure_le_rank_add_budget
    (f : BooleanVec n → R) (H : AddSubgroup (BooleanVec n))
    (hf : HidesSubgroup f H) (e : BooleanVec n ≃ AddChar (BooleanVec n) ℂ) (k : ℕ) :
    (∑ xs ∈ Finset.univ.filter
        (fun xs : Fin (booleanOrthogonalRank H + k) → AddChar (BooleanVec n) ℂ =>
          booleanSampleCandidate (booleanDecodedSamples xs) ≠ H),
      hiddenSubgroupFreshSamples f e (booleanOrthogonalRank H + k) xs) ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ k) := by
  refine le_trans
    (hiddenSubgroupFreshSamples_boolean_failure_le_rank
      f H hf e (booleanOrthogonalRank H + k)) ?_
  exact ENNReal.ofReal_le_ofReal
    (two_pow_sub_one_div_two_pow_add_le_half_pow (booleanOrthogonalRank H) k)

theorem hiddenSubgroupFreshSamples_boolean_success_ge_rank_add_budget
    (f : BooleanVec n → R) (H : AddSubgroup (BooleanVec n))
    (hf : HidesSubgroup f H) (e : BooleanVec n ≃ AddChar (BooleanVec n) ℂ) (k : ℕ) :
    ENNReal.ofReal (1 - (1 / 2 : ℝ) ^ k) ≤
      ∑ xs ∈ Finset.univ.filter
        (fun xs : Fin (booleanOrthogonalRank H + k) → AddChar (BooleanVec n) ℂ =>
          booleanSampleCandidate (booleanDecodedSamples xs) = H),
        hiddenSubgroupFreshSamples f e (booleanOrthogonalRank H + k) xs := by
  refine le_trans ?_
    (hiddenSubgroupFreshSamples_boolean_success_ge_rank
      f H hf e (booleanOrthogonalRank H + k))
  apply ENNReal.ofReal_le_ofReal
  have htail :=
    two_pow_sub_one_div_two_pow_add_le_half_pow (booleanOrthogonalRank H) k
  linarith

end Qatlib.Concepts.HspRecovery.ReductionCore
