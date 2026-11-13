/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.Execution.WorkspaceCP.ProjectedUnitaryEncoding
import Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement

/-!
# Phases and projector rotations

`IsPhase` expresses the unit-modulus condition for a complex scalar, and `anglePhase` constructs
such a scalar from an angle. `phaseRotation P z` applies `z` on the range of `P` and its complex
conjugate on the complementary subspace, providing projector phase operations used in amplitude
amplification [Hoyer2000].

## Main statements

* `phaseRotation_mul`: rotations about an orthogonal projector multiply their phase parameters.
* `phaseRotation_unitary`: a unit-modulus phase gives a unitary rotation.
* `phaseRotation_mul_of_fixed`: the rotation acts by `z` on matrices fixed by `P`.

## References

* [Hoyer, 2000][Hoyer2000]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.Execution.WorkspaceCP

open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement

namespace Qatlib.Concepts.PhaseGeometry.Phase

open Matrix

variable {H : Type*} [Fintype H] [DecidableEq H]

/-- The complex scalar `z` satisfies `star z * z = 1`. -/
def IsPhase (z : ℂ) : Prop := star z * z = 1

/-- The complex phase with real part `cos θ` and imaginary part `sin θ`. -/
noncomputable def anglePhase (θ : ℝ) : ℂ := ⟨Real.cos θ, Real.sin θ⟩

/-- The scalar constructed from any real angle satisfies `IsPhase`. -/
theorem anglePhase_isPhase (θ : ℝ) : IsPhase (anglePhase θ) := by
  unfold IsPhase
  apply Complex.ext
  · simp [anglePhase, Complex.mul_re] at *
    nlinarith [Real.sin_sq_add_cos_sq θ]
  · simp [anglePhase, Complex.mul_im]
    ring

/-- The matrix `z • P + star z • (1 - P)`, applying conjugate phase parameters to the two
projector components. -/
noncomputable def phaseRotation (P : Matrix H H ℂ) (z : ℂ) : Matrix H H ℂ :=
  z • P + star z • (1 - P)

/-- For an orthogonal projector, taking the adjoint of a phase rotation conjugates its phase
parameter. -/
theorem phaseRotation_adjoint {P : Matrix H H ℂ} (hP : IsOrthogonalProjector P) (z : ℂ) :
    (phaseRotation P z)ᴴ = phaseRotation P (star z) := by
  have hs : Pᴴ = P := hP.2
  simp [phaseRotation, hs]

/-- For an orthogonal projector, multiplying two phase rotations multiplies their phase
parameters. -/
theorem phaseRotation_mul {P : Matrix H H ℂ} (hP : IsOrthogonalProjector P) (z w : ℂ) :
    phaseRotation P z * phaseRotation P w = phaseRotation P (z * w) := by
  have hid : P * P = P := hP.1
  have h01 : P * (1 - P) = 0 := by rw [mul_sub, mul_one, hid, sub_self]
  have h10 : (1 - P) * P = 0 := by rw [sub_mul, one_mul, hid, sub_self]
  have h11 : (1 - P) * (1 - P) = 1 - P := by
    rw [sub_mul, one_mul, h01, sub_zero]
  simp only [phaseRotation, Matrix.mul_add, Matrix.add_mul, Matrix.smul_mul,
    Matrix.mul_smul, hid, h01, h10, h11, smul_zero, add_zero, zero_add, smul_smul,
    star_mul]
  module

omit [Fintype H] in

/-- A phase rotation with parameter one is the identity matrix. -/
@[simp] theorem phaseRotation_one (P : Matrix H H ℂ) : phaseRotation P 1 = 1 := by
  simp [phaseRotation]

/-- An orthogonal projector and a scalar satisfying `IsPhase` determine a unitary phase
rotation. -/
theorem phaseRotation_unitary {P : Matrix H H ℂ} (hP : IsOrthogonalProjector P)
    {z : ℂ} (hz : IsPhase z) : phaseRotation P z ∈ Matrix.unitaryGroup H ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
    phaseRotation_adjoint hP, phaseRotation_mul hP]
  have hz' : star z * z = 1 := hz
  rw [hz', phaseRotation_one]

/-- If `P * V = V`, multiplication by the phase rotation scales `V` by `z`. -/
theorem phaseRotation_mul_of_fixed {K : Type*}
    {P : Matrix H H ℂ} {V : Matrix H K ℂ} (h : P * V = V) (z : ℂ) :
    phaseRotation P z * V = z • V := by
  simp [phaseRotation, Matrix.add_mul, Matrix.sub_mul, h]

/-- If `P * V = 0`, multiplication by the phase rotation scales `V` by `star z`. -/
theorem phaseRotation_mul_of_zero {K : Type*}
    {P : Matrix H H ℂ} {V : Matrix H K ℂ} (h : P * V = 0) (z : ℂ) :
    phaseRotation P z * V = star z • V := by
  simp [phaseRotation, Matrix.add_mul, Matrix.sub_mul, h]

end Qatlib.Concepts.PhaseGeometry.Phase
