/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Data.Nat.Find

/-!
# Effective rational Bessel cutoffs

An explicit rational factorial bound defines a decidable guard for truncation indices. The least
index `cutoff` satisfies this guard, is bounded by every other guarded index, and depends only
on the absolute value of the time parameter; the signal processing setting is described in
[LowChuang2017]

## Main statements

* `guard_exists`: every positive rational tolerance has a guarded index.
* `cutoff_guard` and `cutoff_le`: certify the least guarded cutoff.
* `cutoff_neg` and `cutoff_zero`: give sign symmetry and the zero time cutoff.

## References

* [Low and Chuang, 2017][LowChuang2017]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
namespace Qatlib.Concepts.NonNormalSpec.ResolventWord
open Filter
open scoped Topology

/-- The first omitted order `2 * R + 2` associated with a truncation index `R`. -/
def firstOmitted (R : ℕ) : ℕ := 2*R+2

/-- The rational bound `(8 / 3) * (|t| / 2)^(2 * R + 2) / (2 * R + 2)!`. -/
def tailBound (t : ℚ) (R : ℕ) : ℚ :=
  (8/3 : ℚ) * ((|t|/2)^firstOmitted R / (firstOmitted R).factorial)

/-- The cutoff condition requiring `|t| ≤ firstOmitted R` and `tailBound t R ≤ ε`. -/
def Guard (t ε : ℚ) (R : ℕ) : Prop :=
  |t| ≤ (firstOmitted R : ℚ) ∧ tailBound t R ≤ ε

instance guardDecidable (t ε : ℚ) : DecidablePred (Guard t ε) := fun R =>
  inferInstanceAs (Decidable (|t| ≤ (firstOmitted R : ℚ) ∧ tailBound t R ≤ ε))

/-- For fixed rational `t`, the rational tail bound tends to zero as the truncation index tends
to infinity. -/
theorem tailBound_tendsto (t : ℚ) : Tendsto (tailBound t) atTop (𝓝 0) := by
  have hq : Tendsto firstOmitted atTop atTop :=
    tendsto_atTop_mono (fun R => by dsimp [firstOmitted]; omega) tendsto_id
  have h := ((FloorSemiring.tendsto_pow_div_factorial_atTop (|t|/2)).comp hq).const_mul (8/3 : ℚ)
  simpa only [tailBound, mul_zero] using! h

/-- For every rational `t` and positive rational tolerance `ε`, some truncation index satisfies
`Guard t ε`. -/
theorem guard_exists (t ε : ℚ) (hε : 0 < ε) : ∃ R, Guard t ε R := by
  obtain ⟨N,hN⟩ := exists_nat_gt |t|
  obtain ⟨M,hM⟩ := eventually_atTop.mp ((tailBound_tendsto t).eventually_lt_const hε)
  refine ⟨max N M, ?_, (hM _ (le_max_right _ _)).le⟩
  have hn : (N : ℚ) ≤ firstOmitted (max N M) := by
    exact_mod_cast (show N ≤ firstOmitted (max N M) from by
      dsimp [firstOmitted]; omega)
  exact hN.le.trans hn

/-- The least natural index satisfying the rational tail guard for a positive tolerance. -/
def cutoff (t ε : ℚ) (hε : 0 < ε) : ℕ := Nat.find (guard_exists t ε hε)

/-- The chosen cutoff satisfies its defining guard. -/
theorem cutoff_guard (t ε : ℚ) (hε : 0 < ε) : Guard t ε (cutoff t ε hε) :=
  Nat.find_spec (guard_exists t ε hε)

/-- The chosen cutoff is at most any index satisfying the same guard. -/
theorem cutoff_le (t ε : ℚ) (hε : 0 < ε) (R : ℕ) (hR : Guard t ε R) :
    cutoff t ε hε ≤ R := Nat.find_min' (guard_exists t ε hε) hR

/-- Negating the time parameter leaves the chosen cutoff unchanged. -/
theorem cutoff_neg (t ε : ℚ) (hε : 0 < ε) : cutoff (-t) ε hε = cutoff t ε hε := by
  apply Nat.le_antisymm
  · apply cutoff_le
    simpa only [Guard, tailBound, abs_neg] using cutoff_guard t ε hε
  · apply cutoff_le
    simpa only [Guard, tailBound, abs_neg] using cutoff_guard (-t) ε hε

/-- For zero time and positive tolerance, the chosen cutoff is zero. -/
theorem cutoff_zero (ε : ℚ) (hε : 0 < ε) : cutoff 0 ε hε = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply cutoff_le
  constructor
  · norm_num [firstOmitted]
  · simpa [tailBound, firstOmitted] using hε.le

end Qatlib.Concepts.NonNormalSpec.ResolventWord
