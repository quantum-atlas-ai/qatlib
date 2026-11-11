/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AEMeanReadout.RankOneSubspace.Theorem3QuadraticSpeedupUnknownAStat

/-!
# Search schedules without a known success probability

`theorem3QuadraticSpeedupUnknownA` establishes the geometric-schedule search specification for
positive success angles at most `π/4`. The auxiliary estimates control the window sizes,
geometric tails, and expected preparation count. For background, see
[BrassardHoyerTapp1998Counting].

## Main statements

* `theorem3QuadraticSpeedupUnknownA`: For a unitary preparation with marked mass `sin² θ` and `0
  < θ ≤ π/4`, every positive tolerance has a geometric search schedule with failure mass at most
  that tolerance, expected preparation count at most `150 * sqrt 2 / sin θ`, and only marked
  successful outputs. See [BrassardHoyerTapp1998Counting].

## References

* [Brassard et al., 1998][BrassardHoyerTapp1998Counting]
-/

set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Concepts.WalkSearch.QuantumAccess

namespace Qatlib.Concepts.AEMeanReadout.RankOneSubspace

open Qatlib
open scoped ENNReal

/-- For `0 < θ ≤ π/4`, `sin (2 * θ)` is at least `sqrt 2 * sin θ`. -/
theorem sin_two_ge_sqrt_two_sin {θ : ℝ} (h0 : 0 < θ) (h4 : θ ≤ Real.pi / 4) :
    Real.sqrt 2 * Real.sin θ ≤ Real.sin (2 * θ) := by
  have h4pi : Real.pi / 4 ≤ Real.pi := by linarith [Real.pi_pos]
  have hs : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_nonneg_of_le_pi h0.le (h4.trans h4pi)
  have hc : Real.sqrt 2 / 2 ≤ Real.cos θ := by
    rw [← Real.cos_pi_div_four]
    exact Real.cos_le_cos_of_nonneg_of_le_pi h0.le h4pi h4
  have h2 : 2 * (Real.sqrt 2 / 2) = Real.sqrt 2 := by field_simp
  calc Real.sqrt 2 * Real.sin θ = (2 * (Real.sqrt 2 / 2)) * Real.sin θ := by rw [h2]
    _ = 2 * Real.sin θ * (Real.sqrt 2 / 2) := by ring
    _ ≤ 2 * Real.sin θ * Real.cos θ :=
        mul_le_mul_of_nonneg_left hc (mul_nonneg (by norm_num) hs)
    _ = Real.sin (2 * θ) := (Real.sin_two_mul θ).symm

/-- For nonnegative `c` and `0 < θ ≤ π/4`, the ratio `2 * c / sin (2 * θ)` is at most `c * sqrt
2 / sin θ`. -/
theorem two_div_sin_two_le {c θ : ℝ} (hc : 0 ≤ c) (h0 : 0 < θ) (h4 : θ ≤ Real.pi / 4) :
    (2 * c) / Real.sin (2 * θ) ≤ c * Real.sqrt 2 / Real.sin θ := by
  have hs : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_pos])
  have hs2 : 0 < Real.sin (2 * θ) := by
    refine Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  refine (div_le_div_iff₀ hs2 hs).2 ?_
  calc (2 * c) * Real.sin θ = c * ((Real.sqrt 2 * Real.sqrt 2) * Real.sin θ) := by
        rw [hsq]; ring
    _ = c * Real.sqrt 2 * (Real.sqrt 2 * Real.sin θ) := by ring
    _ ≤ c * Real.sqrt 2 * Real.sin (2 * θ) :=
        mul_le_mul_of_nonneg_left (sin_two_ge_sqrt_two_sin h0 h4)
          (mul_nonneg hc (by positivity))
    _ = (c * Real.sqrt 2) * Real.sin (2 * θ) := by ring

/-- The natural-number ceiling expression `(6 ^ j + 5 ^ j - 1) / 5 ^ j` bounds `(6 / 5) ^ j`
from above after casting to the reals. -/
theorem window_nat_div_ge {j : ℕ} :
    (6 / 5 : ℝ) ^ j ≤ (((6 ^ j + 5 ^ j - 1) / 5 ^ j : ℕ) : ℝ) := by
  have h5 : 0 < (5 ^ j : ℕ) := by positivity
  have hmod : (6 ^ j + 5 ^ j - 1) % 5 ^ j < 5 ^ j := Nat.mod_lt _ h5
  have hx : (6 ^ j : ℕ) ≤ ((6 ^ j + 5 ^ j - 1) / 5 ^ j) * 5 ^ j := by
    have hdm := Nat.div_add_mod (6 ^ j + 5 ^ j - 1) (5 ^ j)
    rw [Nat.mul_comm] at hdm
    omega
  have hx' : ((6 ^ j : ℕ) : ℝ) ≤
      (((6 ^ j + 5 ^ j - 1) / 5 ^ j : ℕ) : ℝ) * ((5 ^ j : ℕ) : ℝ) := by
    exact_mod_cast hx
  rw [Nat.cast_pow, Nat.cast_pow] at hx'
  rw [div_pow]
  exact (div_le_iff₀ (by positivity : (0:ℝ) < (5:ℝ) ^ j)).2 hx'

/-- For a positive angle at most `π/4` and positive tolerance, there exist initial and later
geometric windows meeting the reciprocal-sine threshold and a geometric tail below the
tolerance. -/
theorem exists_window_tail {θ ε : ℝ} (h0 : 0 < θ) (h4 : θ ≤ Real.pi / 4) (hε : 0 < ε) :
    ∃ M J k : ℕ,
      (1:ℝ) ≤ (M:ℝ) * Real.sin (2 * θ) ∧
      (1:ℝ) ≤ ((geometricWindow M J : ℕ) : ℝ) * Real.sin (2 * θ) ∧
      (25/32:ℝ) ^ k ≤ ε := by
  have hs2 : 0 < Real.sin (2 * θ) := by
    refine Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hs2le : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  set M := Nat.ceil (1 / Real.sin (2 * θ)) with hMdef
  have hMge : 1 / Real.sin (2 * θ) ≤ (M : ℝ) := by exact_mod_cast Nat.le_ceil _
  have hM1 : (1:ℝ) ≤ (M:ℝ) * Real.sin (2 * θ) := (div_le_iff₀ hs2).mp hMge
  have hone : (1:ℝ) ≤ 1 / Real.sin (2 * θ) := by
    rw [le_div_iff₀ hs2]
    linarith
  have hM1' : 1 ≤ M := by
    exact_mod_cast hone.trans hMge
  obtain ⟨J, hJ⟩ := pow_unbounded_of_one_lt ((M : ℝ)) (by norm_num : (1:ℝ) < 6 / 5)
  have hX : (M:ℝ) ≤ (((6 ^ J + 5 ^ J - 1) / 5 ^ J : ℕ) : ℝ) :=
    hJ.le.trans window_nat_div_ge
  have hX' : M ≤ ((6 ^ J + 5 ^ J - 1) / 5 ^ J : ℕ) := by exact_mod_cast hX
  have hwin : geometricWindow M J = M := by
    unfold geometricWindow
    rw [Nat.min_eq_left hX', Nat.max_eq_right hM1']
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 / ε) (by norm_num : (1:ℝ) < 32 / 25)
  have hk' : (1:ℝ) < ε * (32/25:ℝ) ^ k := by
    rw [mul_comm]
    exact (div_lt_iff₀ hε).mp hk
  have htail : (25/32:ℝ) ^ k ≤ ε := by
    rw [show (25/32:ℝ) ^ k = 1 / ((32/25:ℝ) ^ k) from by
        rw [show (25/32:ℝ) = ((32/25:ℝ))⁻¹ from by norm_num, inv_pow, inv_eq_one_div],
      div_le_iff₀ (pow_pos (by norm_num) k)]
    exact hk'.le
  exact ⟨M, J, k, hM1, by rw [hwin]; exact hM1, htail⟩

/-- The mass of any event under a probability mass function is at most one. -/
theorem event_le_one {α : Type} (p : PMF α) (E : α → Prop) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p E ≤ 1 :=
  Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_le_one p E

/-- For a unitary preparation with marked mass `sin² θ` and `0 < θ ≤ π/4`, every positive
tolerance has a geometric search schedule with failure mass at most that tolerance, expected
preparation count at most `150 * sqrt 2 / sin θ`, and only marked successful outputs. See
[BrassardHoyerTapp1998Counting]. -/
theorem theorem3QuadraticSpeedupUnknownA : Theorem3QuadraticSpeedupUnknownA := by
  intro I _ _ A j₀ S hA θ hθ0 hθ4 hmass ε hε
  have hθ1 : θ < Real.pi / 2 := by linarith [Real.pi_pos]
  obtain ⟨M, J, k, hM1, hwin1, htail⟩ := exists_window_tail hθ0 hθ4 hε
  have hvalid : ∀ y, (decide (y ∈ S) : Bool) = true ↔ y ∈ S := fun y => decide_eq_true_iff
  refine ⟨M, J + k, ?_, ?_, ?_⟩
  · have hc := geometric_search_actual_cutoff_failure_probability A hA j₀ S
      (fun y => decide (y ∈ S)) M (J + k) J θ hvalid hθ0 hθ1 hmass hwin1
    rw [Nat.add_sub_cancel_left] at hc
    have hle1 : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (searchForSchedule A hA j₀ S (fun y => decide (y ∈ S))
        (geometricSearchSchedule M (J + k))) (fun tr => tr.result = none) ≤ 1 :=
      event_le_one _ _
    have hne : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (searchForSchedule A hA j₀ S (fun y => decide (y ∈ S))
        (geometricSearchSchedule M (J + k))) (fun tr => tr.result = none) ≠ ⊤ :=
      (lt_of_le_of_lt hle1 ENNReal.one_lt_top).ne
    rw [← ENNReal.ofReal_toReal hne]
    exact ENNReal.ofReal_le_ofReal (hc.trans htail)
  · have hb := geometric_search_intrinsic_expected_resource_budget A hA j₀ S
      (fun y => decide (y ∈ S)) M (J + k) θ hvalid hθ0 hθ1 hmass hM1
    refine le_trans (hb.2.2.2.1) (ENNReal.ofReal_le_ofReal ?_)
    rw [show (300:ℝ) = 2 * 150 from by norm_num]
    exact two_div_sin_two_le (c := 150) (by norm_num) hθ0 hθ4
  · intro tr htr y hy
    exact (geometric_search_actual_support_soundness_and_metadata A hA j₀ S
      (fun y => decide (y ∈ S)) M (J + k) hvalid tr htr).1 y hy

end Qatlib.Concepts.AEMeanReadout.RankOneSubspace
