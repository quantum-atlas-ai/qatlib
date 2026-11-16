/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.TimeDepHamSim19.MainResults.Model.TimeDepHamSimModel
public import Mathlib.Tactic

@[expose] public section


/-!
# Zero-time boundaries of continuous qDRIFT

The legacy contracts allowed `t = 0` while requiring a strictly increasing
division with a positive number of segments. The raw integral model also
returns the zero map at zero time, whereas evolution returns the identity.
-/

set_option autoImplicit false

namespace Qatlib.Papers.TimeDepHamSim19.MainResults

open Qatlib.Papers.TimeDepHamSim19.MainResults
open Matrix
open scoped ComplexOrder BigOperators

/-- A positive-length strictly increasing division cannot have coincident endpoints. -/
theorem no_zero_division (r : ℕ) (hr : 0 < r) :
    ¬ ∃ tdiv : ℕ → ℝ, IsDivision tdiv r 0 := by
  rintro ⟨tdiv, hzero, hlast, hstrict⟩
  have h := hstrict 0 r hr (le_refl r)
  rw [hzero, hlast] at h
  exact lt_irrefl 0 h

/-- The old qDRIFT integral produces zero on a zero-duration interval. -/
theorem qdrift_zero_time {D : ℕ} (h : Ham D) (ρ : Op D) :
    qdriftChannel h 0 ρ = 0 := by
  simp [qdriftChannel, qdriftSegment]

/-- The exact propagator is the identity at zero time. -/
theorem exact_zero_time {D : ℕ} (h : Ham D) : evo h 0 0 = 1 := by
  exact Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution.orderedEvolution_self _ _

/-- The one-segment zero-time conclusion of both long-time legacy contracts is impossible. -/
theorem long_time_counterexample :
    ¬ ∃ tdiv : ℕ → ℝ, IsDivision tdiv 1 0 :=
  no_zero_division 1 (by decide)

/-- The raw diamond distance from the identity channel to zero is at least one in dimension one. -/
theorem identity_zero_distance :
    1 ≤ channelDiamondDist (unitaryChannel (1 : Op 1)) (fun _ => 0) := by
  let x : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ := 1
  have hx : Matrix.traceNorm x = 1 := by
    have h := Matrix.PosSemidef.traceNorm_eq_trace
      (A := x) (by exact Matrix.PosSemidef.one)
    have hr := congrArg Complex.re h
    simpa [x, Matrix.trace_one] using hr
  have hid : amplify (unitaryChannel (1 : Op 1)) 1 x = x := by
    ext i j
    change ((1 : Op 1) * (show Op 1 from fun a b => x (i.1, a) (j.1, b)) *
      (1 : Op 1)ᴴ) i.2 j.2 = x i j
    rw [Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  have hz : amplify (fun _ : Op 1 => (0 : Op 1)) 1 x = 0 := rfl
  unfold channelDiamondDist
  apply le_iSup_of_le 1
  apply le_iSup_of_le x
  simp [hx, hid, hz]

/-- The short-time qDRIFT bound fails at zero because its integral channel is zero. -/
theorem short_time_counterexample (h : Ham 1) :
    ¬ channelDiamondDist (unitaryChannel (evo h 0 0)) (qdriftChannel h 0) ≤
      ENNReal.ofReal (4 * hamL1 h 0 ^ 2) := by
  have hq : qdriftChannel h 0 = fun _ => 0 := funext (qdrift_zero_time h)
  rw [exact_zero_time, hq]
  intro hb
  have hfalse := identity_zero_distance.trans hb
  norm_num [hamL1, intervalL1] at hfalse

/-- The LC version has the same zero-duration integral-channel defect. -/
theorem lc_short_time_counterexample {l : ℕ} (h : Fin l → Ham 1) :
    ¬ channelDiamondDist (unitaryChannel (evo (fun t => ∑ i, h i t) 0 0))
        (lcQdriftChannel h 0) ≤ ENNReal.ofReal (4 * hamL1One h 0 ^ 2) := by
  have hq : lcQdriftChannel h 0 = fun _ => 0 := by
    funext ρ
    simp [lcQdriftChannel, lcQdriftSegment]
  rw [exact_zero_time, hq]
  intro hb
  have hfalse := identity_zero_distance.trans hb
  norm_num [hamL1One] at hfalse

end Qatlib.Papers.TimeDepHamSim19.MainResults
