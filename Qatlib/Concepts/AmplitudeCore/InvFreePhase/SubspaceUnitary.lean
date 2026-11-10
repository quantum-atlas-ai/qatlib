/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.Execution.WorkspaceCP.ProjectedUnitaryEncoding
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.Execution.WorkspaceCP

set_option autoImplicit false
namespace Qatlib.Concepts.AmplitudeCore.InvFreePhase
open Matrix
variable {H I : Type*} [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]

noncomputable def frameUnitary (E : Matrix H I ℂ) (T : Matrix I I ℂ) : Matrix H H ℂ :=
  1 - rangeProjector E + E*T*E.conjTranspose

theorem frameUnitary_frame (E : Matrix H I ℂ) (hE : IsIsometry E) (T : Matrix I I ℂ) :
    frameUnitary E T * E = E*T := by
  have h : E.conjTranspose*E=1 := hE
  simp [frameUnitary, Matrix.add_mul, Matrix.sub_mul, rangeProjector, Matrix.mul_assoc, h]

theorem frameUnitary_adjoint (E : Matrix H I ℂ) (T : Matrix I I ℂ) :
    (frameUnitary E T).conjTranspose = frameUnitary E T.conjTranspose := by
  simp [frameUnitary, rangeProjector, Matrix.mul_assoc]

theorem frameUnitary_mul (E : Matrix H I ℂ) (hE : IsIsometry E)
    (S T : Matrix I I ℂ) : frameUnitary E S * frameUnitary E T = frameUnitary E (S*T) := by
  have h : E.conjTranspose*E=1 := hE
  have hp := rangeProjector_isOrthogonalProjector hE
  have hQE : (1-rangeProjector E)*E=0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, rangeProjector_mul hE, sub_self]
  have hEQ : E.conjTranspose*(1-rangeProjector E)=0 := by
    have hh := congrArg Matrix.conjTranspose hQE
    simpa [rangeProjector] using hh
  have hQQ : (1-rangeProjector E)*(1-rangeProjector E)=1-rangeProjector E := hp.one_sub.1
  simp only [frameUnitary, Matrix.add_mul, Matrix.mul_add]
  rw [hQQ]
  have hcross1 : (1-rangeProjector E)*(E*T*E.conjTranspose)=0 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hQE, Matrix.zero_mul, Matrix.zero_mul]
  have hcross2 : E*S*E.conjTranspose*(1-rangeProjector E)=0 := by
    rw [Matrix.mul_assoc, hEQ, Matrix.mul_zero]
  have hlast : E*S*E.conjTranspose*(E*T*E.conjTranspose)=E*(S*T)*E.conjTranspose := by
    simp only [Matrix.mul_assoc, ← Matrix.mul_assoc E.conjTranspose E, h, Matrix.one_mul]
  rw [hcross1, hcross2, hlast, add_zero, zero_add]

@[simp] theorem frameUnitary_one (E : Matrix H I ℂ) : frameUnitary E 1 = 1 := by
  simp [frameUnitary, rangeProjector]

theorem frameUnitary_unitary (E : Matrix H I ℂ) (hE : IsIsometry E)
    (T : Matrix I I ℂ) (hT : T ∈ Matrix.unitaryGroup I ℂ) :
    frameUnitary E T ∈ Matrix.unitaryGroup H ℂ := by
  apply Matrix.mem_unitaryGroup_iff'.mpr
  change (frameUnitary E T).conjTranspose * frameUnitary E T = 1
  have hTT : T.conjTranspose*T=1 := Matrix.mem_unitaryGroup_iff'.mp hT
  rw [frameUnitary_adjoint, frameUnitary_mul E hE, hTT, frameUnitary_one]

end Qatlib.Concepts.AmplitudeCore.InvFreePhase
