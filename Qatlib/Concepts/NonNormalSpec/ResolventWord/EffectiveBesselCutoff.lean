/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Data.Nat.Find
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
namespace Qatlib.Concepts.NonNormalSpec.ResolventWord
open Filter
open scoped Topology

def firstOmitted (R : ℕ) : ℕ := 2*R+2

def tailBound (t : ℚ) (R : ℕ) : ℚ :=
  (8/3 : ℚ) * ((|t|/2)^firstOmitted R / (firstOmitted R).factorial)

def Guard (t ε : ℚ) (R : ℕ) : Prop :=
  |t| ≤ (firstOmitted R : ℚ) ∧ tailBound t R ≤ ε

instance guardDecidable (t ε : ℚ) : DecidablePred (Guard t ε) := fun R =>
  inferInstanceAs (Decidable (|t| ≤ (firstOmitted R : ℚ) ∧ tailBound t R ≤ ε))

theorem tailBound_tendsto (t : ℚ) : Tendsto (tailBound t) atTop (𝓝 0) := by
  have hq : Tendsto firstOmitted atTop atTop :=
    tendsto_atTop_mono (fun R => by dsimp [firstOmitted]; omega) tendsto_id
  have h := ((FloorSemiring.tendsto_pow_div_factorial_atTop (|t|/2)).comp hq).const_mul (8/3 : ℚ)
  simpa only [tailBound, mul_zero] using! h

theorem guard_exists (t ε : ℚ) (hε : 0 < ε) : ∃ R, Guard t ε R := by
  obtain ⟨N,hN⟩ := exists_nat_gt |t|
  obtain ⟨M,hM⟩ := eventually_atTop.mp ((tailBound_tendsto t).eventually_lt_const hε)
  refine ⟨max N M, ?_, (hM _ (le_max_right _ _)).le⟩
  have hn : (N : ℚ) ≤ firstOmitted (max N M) := by
    exact_mod_cast (show N ≤ firstOmitted (max N M) from by
      dsimp [firstOmitted]; omega)
  exact hN.le.trans hn

def cutoff (t ε : ℚ) (hε : 0 < ε) : ℕ := Nat.find (guard_exists t ε hε)

theorem cutoff_guard (t ε : ℚ) (hε : 0 < ε) : Guard t ε (cutoff t ε hε) :=
  Nat.find_spec (guard_exists t ε hε)

theorem cutoff_le (t ε : ℚ) (hε : 0 < ε) (R : ℕ) (hR : Guard t ε R) :
    cutoff t ε hε ≤ R := Nat.find_min' (guard_exists t ε hε) hR

theorem cutoff_neg (t ε : ℚ) (hε : 0 < ε) : cutoff (-t) ε hε = cutoff t ε hε := by
  apply Nat.le_antisymm
  · apply cutoff_le
    simpa only [Guard, tailBound, abs_neg] using cutoff_guard t ε hε
  · apply cutoff_le
    simpa only [Guard, tailBound, abs_neg] using cutoff_guard (-t) ε hε

theorem cutoff_zero (ε : ℚ) (hε : 0 < ε) : cutoff 0 ε hε = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply cutoff_le
  constructor
  · norm_num [firstOmitted]
  · simpa [tailBound, firstOmitted] using hε.le

end Qatlib.Concepts.NonNormalSpec.ResolventWord
