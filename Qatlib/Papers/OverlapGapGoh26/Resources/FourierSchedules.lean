/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixGeometry.AxisRotations.Rotation

/-!
# Fourier parameterizations of control schedules

`Coefficients` stores two sets of Fourier coefficients, producing problem angles from sine modes
and mixer angles from cosine modes. `scheduleLinear` packages the parameterization as a real
linear map, and `spinControl` converts the angles into orthogonal three dimensional rotations.
The parameter counts formalize the schedule representation used in [GohMuller2026].

## Main statements

* `scheduleLinear`: The real linear map from Fourier coefficients to the two layer angle arrays.
* `coefficient_positions`: The two Fourier coefficient arrays have `2r` coordinate positions.
* `spinControl_unitary`: The Fourier spin control matrix belongs to the real unitary group,
  equivalently the orthogonal group.

## References

* [Goh and Müller, 2026][GohMuller2026]
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Qatlib.Papers.OverlapGapGoh26.Resources.Fourier

/-- Two real coefficient arrays of length `r`, one for problem angles and one for mixer angles. -/
abbrev Coefficients (r : ℕ) := Fin 2 → Fin r → ℝ

/-- The Fourier phase `(k+1/2)(j+1/2)π/p` for mode `k` and layer `j`. -/
def phase {r p : ℕ} (k : Fin r) (j : Fin p) : ℝ :=
  ((k:ℝ)+1/2)*((j:ℝ)+1/2)*Real.pi/(p:ℝ)

/-- The problem angle at layer `j`, given by the sine expansion with coefficient row zero. -/
def problemAngle {r p : ℕ} (c : Coefficients r) (j : Fin p) : ℝ :=
  ∑ k : Fin r,c 0 k*Real.sin (phase k j)

/-- The mixer angle at layer `j`, given by the cosine expansion with coefficient row one. -/
def mixerAngle {r p : ℕ} (c : Coefficients r) (j : Fin p) : ℝ :=
  ∑ k : Fin r,c 1 k*Real.cos (phase k j)

/-- The two angle arrays obtained from the problem sine expansion and the mixer cosine
expansion. -/
def schedule {r p : ℕ} (c : Coefficients r) : Fin 2 → Fin p → ℝ :=
  fun a => if a=0 then problemAngle c else mixerAngle c

/-- The real linear map from Fourier coefficients to the two layer angle arrays. -/
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

/-- The two Fourier coefficient arrays have `2r` coordinate positions. See [GohMuller2026]. -/
theorem coefficient_positions (r : ℕ) : Fintype.card (Fin 2×Fin r)=2*r := by simp

/-- The two depth `p` angle arrays have `2p` coordinate positions. See [GohMuller2026]. -/
theorem angle_positions (p : ℕ) : Fintype.card (Fin 2×Fin p)=2*p := by simp

/-- Zero Fourier coefficients produce the zero angle schedule. -/
theorem zero_schedule (r p : ℕ) : schedule (p:=p) (0 : Coefficients r)=0 :=
  (scheduleLinear r p).map_zero

/-- The product of the driver and problem rotation matrices determined by the Fourier mixer and
problem angles at a layer. -/
def spinControl {r p : ℕ} (c : Coefficients r) (j : Fin p) : Matrix (Fin 3) (Fin 3) ℝ :=
  Qatlib.Foundations.MatrixGeometry.AxisRotations.Rotation.driverAngle (mixerAngle c j)*
    Qatlib.Foundations.MatrixGeometry.AxisRotations.Rotation.problemAngle (problemAngle c j)

/-- The Fourier spin control matrix belongs to the real unitary group, equivalently the
orthogonal group. See [GohMuller2026]. -/
theorem spinControl_unitary {r p : ℕ} (c : Coefficients r) (j : Fin p) :
    spinControl c j∈Matrix.unitaryGroup (Fin 3) ℝ :=
  mul_mem (Qatlib.Foundations.MatrixGeometry.AxisRotations.Rotation.driver_unitary _)
    (Qatlib.Foundations.MatrixGeometry.AxisRotations.Rotation.problem_unitary _)

end Qatlib.Papers.OverlapGapGoh26.Resources.Fourier
