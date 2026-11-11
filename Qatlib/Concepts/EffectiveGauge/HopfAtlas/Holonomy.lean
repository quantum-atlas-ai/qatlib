/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.IntegerWinding
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! # Exact coordinate-loop periods of the constant-spin integer family -/

set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas

/-- Original `windingLift_connection_period` guarantee for the `Holonomy` construction; the complete source hypotheses are retained. -/
theorem windingLift_connection_period (n : Fin 3 → ℤ) (q0 : ℍ) (hq : ‖q0‖=1)
    (x : SpatialPoint) (j : Fin 3) :
    (∫ t in (0 : ℝ)..physicalPeriod,
      connection (windingLift n q0) (x+t • EuclideanSpace.single j 1) j) =
        physicalPeriod*(n j : ℝ) := by
  have h : ∀ t : ℝ, connection (windingLift n q0) (x+t • EuclideanSpace.single j 1) j=(n j : ℝ) := by
    intro t
    simpa [velocity] using windingLift_velocity n q0 hq 1 (x+t • EuclideanSpace.single j 1) j
  simp_rw [h]
  simp

/-- Original `windingLift_velocity_period` guarantee for the `Holonomy` construction; the complete source hypotheses are retained. -/
theorem windingLift_velocity_period (n : Fin 3 → ℤ) (q0 : ℍ) (hq : ‖q0‖=1)
    (hbar : ℝ) (x : SpatialPoint) (j : Fin 3) :
    (∫ t in (0 : ℝ)..physicalPeriod,
      velocity hbar (windingLift n q0) (x+t • EuclideanSpace.single j 1) j) =
        physicalPeriod*(hbar*(n j : ℝ)) := by
  simp_rw [windingLift_velocity n q0 hq]
  simp
  ring

/-- Original `windingLift_holonomy` guarantee for the `Holonomy` construction; the complete source hypotheses are retained. -/
theorem windingLift_holonomy (n : Fin 3 → ℤ) (q0 : ℍ) (hq : ‖q0‖=1)
    (x : SpatialPoint) (j : Fin 3) :
    phase (∫ t in (0 : ℝ)..physicalPeriod,
      connection (windingLift n q0) (x+t • EuclideanSpace.single j 1) j) = 1 := by
  rw [windingLift_connection_period n q0 hq x j]
  have h := phase_int_period 0 (n j)
  simpa [phase, mul_comm] using h

end Qatlib.Concepts.EffectiveGauge.HopfAtlas
