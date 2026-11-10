/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ChannelTheory.Naimark.ProjectionBorn
import Qatlib.Papers.QGradient20.FilterBranch.ActualVector
set_option warningAsError false

set_option autoImplicit false
noncomputable section
open Matrix
open scoped Classical ComplexOrder Matrix.Norms.L2Operator
open Qatlib.Concepts.ChannelTheory.Naimark.ProjectionControl
open Qatlib.Concepts.ChannelTheory.Naimark.ProjectionBorn
open Qatlib.Concepts.ChannelTheory.Naimark.ContractionInstrument
open Qatlib.Concepts.ChannelTheory.Naimark.ContractionBorn
open Qatlib.Papers.QGradient20.FilterBranch

namespace Qatlib.Papers.QGradient20.FilterBranch.Projection
variable {I : Type} [Fintype I] [DecidableEq I]

omit [Fintype I] in

theorem source_projection_eq (zero : I) : projectionMatrix zero=removeZero zero := rfl

theorem source_projection_program_unitary (zero : I) :
    program (projectionMatrix zero)∈Matrix.unitaryGroup (I⊕I) ℂ := removeZero_program_unitary zero

theorem source_projection_success_corner (zero : I) (i j : I) :
    program (projectionMatrix zero) (Sum.inl i) (Sum.inl j)=projectionMatrix zero i j :=
  program_success_corner _ i j

theorem source_program_success_mass (zero : I) (x : EuclideanSpace ℂ I) (hx : ‖x‖=1) :
    (∑ i : I,‖(program (projectionMatrix zero)*ᵥSum.elim (WithLp.ofLp x) 0) (Sum.inl i)‖^2)=
      1-‖x zero‖^2 := by
  simpa only [hx,one_pow] using! program_success_mass zero x

theorem source_native_projection_Born (zero : I) (x : EuclideanSpace ℂ I) (hx : ‖x‖=1) :
    (((readout (projectionMatrix zero) (removeZero_norm zero)).measure (MState.pure (ketOfUnit x hx))) true : ℝ)=
      1-‖x zero‖^2 := native_projected_Born zero x hx

theorem empty_program_unitary : program (0 : Matrix (Fin 0) (Fin 0) ℂ)∈Matrix.unitaryGroup ((Fin 0)⊕(Fin 0)) ℂ :=
  program_unitary 0 (by simp) (by simp)

end Qatlib.Papers.QGradient20.FilterBranch.Projection
