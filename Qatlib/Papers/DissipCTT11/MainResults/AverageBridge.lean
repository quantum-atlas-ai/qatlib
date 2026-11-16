/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.DissipCTT11.MainResults.AverageLiouvillian

@[expose] public section


/-! # Connecting the actual interval average to its comparison formula

The legacy comparison accepts an arbitrary constant matrix. Here it is
specialized to the actual integral average, whose integral deviation is
zero. This is structural support for Theorem 7, without claiming its
quantitative induced trace-norm error or GKSL closure under averaging.
-/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.DissipCTT11.MainResults.AverageBridge
open Matrix
open scoped Matrix.Norms.L2Operator
open Qatlib.Papers.DissipCTT11.MainResults.AverageLiouvillian
open Qatlib.Papers.DissipCTT11.MainResults.LiouvillianPropagator
variable {I : Type} [Fintype I] [DecidableEq I]

/-- Multiplying a nondegenerate interval average by its length recovers its integral. -/
theorem averageMass (K : ℝ → Matrix I I ℂ) {s t : ℝ} (hst : s ≠ t) :
    (t - s) • averageLiouvillian K s t = ∫ r in s..t, K r := by
  have h : t - s ≠ 0 := sub_ne_zero.mpr hst.symm
  simp [averageLiouvillian,smul_smul,h]

/-- The time integral of the actual generator deviation from its average is zero. -/
theorem deviationZero (K : ℝ → Matrix I I ℂ) (hK : Continuous K)
    {s t : ℝ} (hst : s ≠ t) :
    (∫ r in s..t, K r - averageLiouvillian K s t) = 0 := by
  rw [intervalIntegral.integral_sub (hK.intervalIntegrable s t) intervalIntegrable_const,
    intervalIntegral.integral_const,averageMass K hst,sub_self]

/-- The actual time average of a constant generator is that generator. -/
theorem constantAvg (A : Matrix I I ℂ) {s t : ℝ} (hst : s ≠ t) :
    averageLiouvillian (fun _ => A) s t = A := by
  have h : t - s ≠ 0 := sub_ne_zero.mpr hst.symm
  simp [averageLiouvillian,intervalIntegral.integral_const,smul_smul,h]

/-- A degenerate interval has zero integral average under the total Lean definition. -/
theorem equalAvg (K : ℝ → Matrix I I ℂ) (s : ℝ) :
    averageLiouvillian K s s = 0 := by simp [averageLiouvillian]

/-- The actual averaged-generator comparison specializes Duhamel to Eq. (33). -/
theorem actualDuhamel (K : ℝ → Matrix I I ℂ) (hK : Continuous K)
    {s t : ℝ} (hst : s ≤ t) :
    propagator K s t - NormedSpace.exp ((t - s) • averageLiouvillian K s t) =
      ∫ r in s..t, propagator K r t * (K r - averageLiouvillian K s t) *
        NormedSpace.exp ((r - s) • averageLiouvillian K s t) :=
  averageLiouvillian_duhamel K hK _ hst

/-- For a constant generator the actual average approximation is exact. -/
theorem constantExact (A : Matrix I I ℂ) {s t : ℝ} (hst : s ≠ t) :
    propagator (fun _ => A) s t -
      NormedSpace.exp ((t - s) • averageLiouvillian (fun _ => A) s t) = 0 := by
  rw [constantAvg A hst,propagator_const,sub_self]

end Qatlib.Papers.DissipCTT11.MainResults.AverageBridge
