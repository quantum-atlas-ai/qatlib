/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase
import Qatlib.Concepts.MatrixAccess.KnownFrameSynth.MultiKnownQubitControl
import Mathlib.Tactic.FinCases

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase

/-!
# Rational Circle

The constructed finite matrix is unitary under the stated hypotheses.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords
open Qatlib Matrix
open Qatlib.Concepts.PhaseGeometry
open scoped BigOperators Matrix.Norms.L2Operator
/-- Data and invariants for Circle in the rational circle model. -/
structure Circle where
  c : ℚ
  s : ℚ
  norm : c*c+s*s=1

/-- Construction for Circle.half in the rational circle model. -/
def Circle.half (t : ℚ) : Circle where
  c := (cayleyRat t).1
  s := (cayleyRat t).2
  norm := by
    dsimp [cayleyRat]
    have h : 1+t^2 ≠ 0 := by positivity
    field_simp
    ring

/-- Construction for Circle.inv in the rational circle model. -/
def Circle.inv (p : Circle) : Circle := ⟨p.c,-p.s,by nlinarith [p.norm]⟩

/-- Construction for rotation in the rational circle model. -/
def rotation (p : Circle) : Matrix Bool Bool ℂ
  | false,false => p.c
  | false,true => -p.s
  | true,false => p.s
  | true,true => p.c

/-- The constructed finite matrix is unitary under the stated hypotheses. -/
@[simp] theorem rotation_unitary (p : Circle) : rotation p ∈ unitaryGroup Bool ℂ := by
  have hn : (p.c : ℂ)*(p.c : ℂ)+(p.s : ℂ)*(p.s : ℂ)=1 := by exact_mod_cast p.norm
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  ext a b
  cases a <;> cases b <;> simp [rotation, Matrix.mul_apply, Matrix.conjTranspose_apply,
    hn, add_comm, mul_comm]

/-- The actual native inverse or adjoint satisfies the displayed operator identity. -/
@[simp] theorem rotation_inv (p : Circle) : rotation p.inv = (rotation p)ᴴ := by
  ext a b
  cases a <;> cases b <;> simp [rotation, Circle.inv, Matrix.conjTranspose_apply]


/-- Construction for phase Scalar in the rational circle model. -/
def phaseScalar (p : Circle) : ℂ := ⟨p.c,p.s⟩

/-- Construction for phase Matrix in the rational circle model. -/
def phaseMatrix (p : Circle) : Matrix Bool Bool ℂ :=
  rationalPhaseGate (p.c,p.s)

/-- The concrete rational or complex data satisfy the displayed normalization identity. -/
theorem phaseScalar_norm (p : Circle) : Complex.normSq (phaseScalar p)=1 := by
  change (p.c:ℝ)*(p.c:ℝ)+(p.s:ℝ)*(p.s:ℝ)=1
  exact_mod_cast p.norm

/-- The finite native construction `phaseScalar_as_gaussian` satisfies the displayed exact coordinate or algebraic relation. -/
theorem phaseScalar_as_gaussian (p : Circle) : phaseScalar p=gaussianRatComplex (p.c,p.s) := by
  apply Complex.ext <;> simp [phaseScalar,gaussianRatComplex]

/-- The constructed finite matrix is unitary under the stated hypotheses. -/
@[simp] theorem phaseMatrix_unitary (p : Circle) : phaseMatrix p ∈ unitaryGroup Bool ℂ := by
  apply rationalPhaseGate_mem_unitaryGroup
  have hn : ‖phaseScalar p‖^2=1 := by
    rw [Complex.sq_norm,phaseScalar_norm]
  have h : ‖phaseScalar p‖=1 := by nlinarith [norm_nonneg (phaseScalar p)]
  simpa only [← phaseScalar_as_gaussian] using h

/-- The actual native inverse or adjoint satisfies the displayed operator identity. -/
@[simp] theorem phaseScalar_inv (p : Circle) : phaseScalar p.inv=star (phaseScalar p) := by
  apply Complex.ext <;> simp [phaseScalar,Circle.inv]

/-- The actual native inverse or adjoint satisfies the displayed operator identity. -/
@[simp] theorem phaseMatrix_inv (p : Circle) : phaseMatrix p.inv=(phaseMatrix p)ᴴ := by
  ext a b
  cases a <;> cases b <;> simp [phaseMatrix,rationalPhaseGate,Matrix.conjTranspose_apply,← phaseScalar_as_gaussian]


end Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords
