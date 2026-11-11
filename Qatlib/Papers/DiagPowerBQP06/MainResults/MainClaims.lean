/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.DiagPowerBQP06.MainResults.Defs
import Qatlib.Papers.DiagPowerBQP06.MainResults.Hardness
import Qatlib.Papers.DiagPowerBQP06.MainResults.EntryRestriction
import Qatlib.Papers.DiagPowerBQP06.MainResults.OffDiagonal
import Qatlib.Papers.DiagPowerBQP06.MainResults.SpectralMoment
import Qatlib.Papers.DiagPowerBQP06.MainResults.ReadoutBound
import Qatlib.Papers.DiagPowerBQP06.MainResults.Sampling
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Sampling counts and estimation composition

This module gives an explicit sample-count bound for the exponential concentration estimate and
combines two error contributions into a threshold decision guarantee. It also states the
quadratic-form identity recovering an off-diagonal entry of a symmetric matrix power.

These constructions accompany the results of [JanzingWocjan2006a].

## Main statements

* `hoeffding_sample_count`: chooses a positive sample count with failure bound at most one
  third.
* `estimation_pipeline`: combines estimation errors and separates the two threshold cases.
* `offdiag_entry_estimable`: expresses an off-diagonal entry through two quadratic forms.

## References

* [Janzing and Wocjan, 2006][JanzingWocjan2006a]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.DiagPowerBQP06.MainResults.MainClaims

open Qatlib.Papers.DiagPowerBQP06.MainResults.OffDiagonal

/-- For positive `ε`, there is a positive sample count with exponential failure bound at most
one third and count at most `18 * log 6 / ε ^ 2 + 1`. See [JanzingWocjan2006a]. -/
theorem hoeffding_sample_count (ε : ℝ) (hε : 0 < ε) :
    ∃ k : ℕ, 0 < k ∧ 2 * Real.exp (-(ε ^ 2 * (k : ℝ)) / 18) ≤ 1 / 3 ∧
      (k : ℝ) ≤ 18 * Real.log 6 / ε ^ 2 + 1 := by
  set x : ℝ := 18 * Real.log 6 / ε ^ 2 with hx
  have hlog : 0 < Real.log 6 := Real.log_pos (by norm_num)
  have hxpos : 0 < x := by rw [hx]; positivity
  refine ⟨Nat.ceil x, ?_, ?_, ?_⟩
  · have : (0:ℝ) < (Nat.ceil x : ℝ) := lt_of_lt_of_le hxpos (Nat.le_ceil x)
    exact_mod_cast this
  · have hle : x ≤ (Nat.ceil x : ℝ) := Nat.le_ceil x
    have hkey : Real.log 6 ≤ ε ^ 2 * (Nat.ceil x : ℝ) / 18 := by
      have h := mul_le_mul_of_nonneg_left hle (by positivity : (0:ℝ) ≤ ε ^ 2 / 18)
      have hx' : ε ^ 2 / 18 * x = Real.log 6 := by rw [hx]; field_simp
      have hk' : ε ^ 2 / 18 * (Nat.ceil x : ℝ) =
          ε ^ 2 * (Nat.ceil x : ℝ) / 18 := by ring
      rwa [hx', hk'] at h
    have hexp : Real.exp (-(ε ^ 2 * (Nat.ceil x : ℝ)) / 18) ≤ 1 / 6 := by
      have hneg : -(ε ^ 2 * (Nat.ceil x : ℝ)) / 18 ≤ -Real.log 6 := by linarith
      calc Real.exp (-(ε ^ 2 * (Nat.ceil x : ℝ)) / 18)
          ≤ Real.exp (-Real.log 6) := Real.exp_le_exp.mpr hneg
        _ = 1 / 6 := by
            rw [Real.exp_neg]
            have h6 : Real.exp (Real.log 6) = 6 := Real.exp_log (by norm_num)
            rw [h6]; norm_num
    calc 2 * Real.exp (-(ε ^ 2 * (Nat.ceil x : ℝ)) / 18) ≤ 2 * (1 / 6) := by linarith
      _ = 1 / 3 := by norm_num
  · have hlt : (Nat.ceil x : ℝ) < x + 1 := Nat.ceil_lt_add_one hxpos.le
    rw [hx] at hlt
    linarith

/-- Two errors bounded by `ε / 3` give total error at most `2 * ε / 3`, and the estimate lies
above `g` or at most `g` in the respective separated threshold cases. See
[JanzingWocjan2006a]. -/
theorem estimation_pipeline (entry moment est g ε : ℝ) (hε : 0 < ε)
    (hme : |moment - entry| ≤ ε / 3) (hsm : |est - moment| ≤ ε / 3) :
    |est - entry| ≤ 2 * ε / 3 ∧
      (g + ε ≤ entry → g < est) ∧ (entry ≤ g - ε → est ≤ g) := by
  have htri : |est - entry| ≤ 2 * ε / 3 := by
    calc |est - entry| = |(est - moment) + (moment - entry)| := by ring_nf
      _ ≤ |est - moment| + |moment - entry| := abs_add_le _ _
      _ ≤ ε / 3 + ε / 3 := add_le_add hsm hme
      _ = 2 * ε / 3 := by ring
  refine ⟨htri, ?_, ?_⟩
  · intro h
    have h1 : entry - 2 * ε / 3 ≤ est := by
      have := (abs_le.mp htri).1; linarith
    linarith
  · intro h
    have h1 : est ≤ entry + 2 * ε / 3 := by
      have := (abs_le.mp htri).2; linarith
    linarith

/-- For distinct indices, the difference of the plus-state and minus-state quadratic forms of a
real symmetric matrix power equals twice its corresponding off-diagonal entry. See
[JanzingWocjan2006a]. -/
theorem offdiag_entry_estimable (N : ℕ) (A : Matrix (Fin N) (Fin N) ℝ)
    (hA : A.IsHermitian) (m : ℕ) (i j : Fin N) (hij : i ≠ j) :
    quad (A ^ m) (plusState i j) - quad (A ^ m) (minusState i j)
      = 2 * (A ^ m) i j :=
  offdiag_quadratic_identity (A ^ m) (isHermitian_pow A hA m) i j hij

end Qatlib.Papers.DiagPowerBQP06.MainResults.MainClaims
