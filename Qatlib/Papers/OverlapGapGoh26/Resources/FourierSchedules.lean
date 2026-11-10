/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixGeometry.AxisRotations.Rotation

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Qatlib.Papers.OverlapGapGoh26.Resources.Fourier

abbrev Coefficients (r : ℕ) := Fin 2 → Fin r → ℝ

def phase {r p : ℕ} (k : Fin r) (j : Fin p) : ℝ :=
  ((k:ℝ)+1/2)*((j:ℝ)+1/2)*Real.pi/(p:ℝ)

def problemAngle {r p : ℕ} (c : Coefficients r) (j : Fin p) : ℝ :=
  ∑ k : Fin r,c 0 k*Real.sin (phase k j)

def mixerAngle {r p : ℕ} (c : Coefficients r) (j : Fin p) : ℝ :=
  ∑ k : Fin r,c 1 k*Real.cos (phase k j)

def schedule {r p : ℕ} (c : Coefficients r) : Fin 2 → Fin p → ℝ :=
  fun a => if a=0 then problemAngle c else mixerAngle c

def scheduleLinear (r p : ℕ) : Coefficients r →ₗ[ℝ] (Fin 2 → Fin p → ℝ) where
  toFun := schedule
  map_add' := by
    intro c d
    funext a j
    by_cases ha : a=0 <;> simp [schedule,problemAngle,mixerAngle,ha,add_mul,Finset.sum_add_distrib]
  map_smul' := by
    intro c d
    funext a j
    by_cases ha : a=0 <;> simp [schedule,problemAngle,mixerAngle,ha,mul_assoc,Finset.mul_sum]

theorem coefficient_positions (r : ℕ) : Fintype.card (Fin 2×Fin r)=2*r := by simp

theorem angle_positions (p : ℕ) : Fintype.card (Fin 2×Fin p)=2*p := by simp

theorem zero_schedule (r p : ℕ) : schedule (p:=p) (0 : Coefficients r)=0 :=
  (scheduleLinear r p).map_zero

def spinControl {r p : ℕ} (c : Coefficients r) (j : Fin p) : Matrix (Fin 3) (Fin 3) ℝ :=
  Qatlib.Foundations.MatrixGeometry.AxisRotations.Rotation.driverAngle (mixerAngle c j)*
    Qatlib.Foundations.MatrixGeometry.AxisRotations.Rotation.problemAngle (problemAngle c j)

theorem spinControl_unitary {r p : ℕ} (c : Coefficients r) (j : Fin p) :
    spinControl c j∈Matrix.unitaryGroup (Fin 3) ℝ :=
  mul_mem (Qatlib.Foundations.MatrixGeometry.AxisRotations.Rotation.driver_unitary _)
    (Qatlib.Foundations.MatrixGeometry.AxisRotations.Rotation.problem_unitary _)

end Qatlib.Papers.OverlapGapGoh26.Resources.Fourier
