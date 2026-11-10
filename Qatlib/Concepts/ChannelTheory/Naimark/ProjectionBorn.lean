/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ChannelTheory.Naimark.ProjectionControl
import Qatlib.Concepts.ChannelTheory.Naimark.ContractionBorn
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped Classical ComplexOrder Matrix.Norms.L2Operator
open Qatlib.Concepts.ChannelTheory.Naimark.ProjectionControl
open Qatlib.Concepts.ChannelTheory.Naimark.ContractionInstrument
open Qatlib.Concepts.ChannelTheory.Naimark.ContractionBorn

namespace Qatlib.Concepts.ChannelTheory.Naimark.ProjectionBorn
variable {I : Type} [Fintype I] [DecidableEq I]

theorem removeZero_norm (zero : I) : ‖removeZero zero‖≤1 := by
  rw [removeZero,Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤1)).mpr
  intro i
  split_ifs <;> norm_num

theorem projected_mass (zero : I) (x : EuclideanSpace ℂ I) :
    ‖(WithLp.toLp 2 (removeZero zero*ᵥWithLp.ofLp x) : EuclideanSpace ℂ I)‖^2=
      ‖x‖^2-‖x zero‖^2 := by
  have hs : (∑ i : I,((if i=zero then 0 else ‖x i‖^2)+(if i=zero then ‖x i‖^2 else 0)))=
      ∑ i : I,‖x i‖^2 := by
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp
  rw [Finset.sum_add_distrib] at hs
  simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true] at hs
  rw [EuclideanSpace.norm_sq_eq,EuclideanSpace.norm_sq_eq]
  have hproj : (∑ i : I,‖(removeZero zero*ᵥWithLp.ofLp x) i‖^2)=
      ∑ i : I,if i=zero then 0 else ‖x i‖^2 := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [removeZero,Matrix.mulVec_diagonal]
    by_cases hi : i=zero <;> simp [hi]
  rw [hproj]
  linarith

theorem program_success_mass (zero : I) (x : EuclideanSpace ℂ I) :
    (∑ i : I,‖(program (removeZero zero)*ᵥSum.elim (WithLp.ofLp x) 0) (Sum.inl i)‖^2)=
      ‖x‖^2-‖x zero‖^2 := by
  have he : (fun i => (program (removeZero zero)*ᵥSum.elim (WithLp.ofLp x) 0) (Sum.inl i))=
      removeZero zero*ᵥWithLp.ofLp x := by
    funext i
    rw [program_removeZero_action]
    simp only [removeZero,Matrix.mulVec_diagonal]
    by_cases hi : i=zero <;> simp [hi]
  change (∑ i : I,‖(fun i => (program (removeZero zero)*ᵥSum.elim (WithLp.ofLp x) 0) (Sum.inl i)) i‖^2)=_
  rw [he]
  exact (EuclideanSpace.norm_sq_eq (WithLp.toLp 2 (removeZero zero*ᵥWithLp.ofLp x) : EuclideanSpace ℂ I)).symm.trans
    (projected_mass zero x)

theorem native_projected_Born (zero : I) (x : EuclideanSpace ℂ I) (hx : ‖x‖=1) :
    (((readout (removeZero zero) (removeZero_norm zero)).measure (MState.pure (ketOfUnit x hx))) true : ℝ)=
      1-‖x zero‖^2 := by
  rw [native_success_Born_unit,projected_mass,hx,one_pow]

end Qatlib.Concepts.ChannelTheory.Naimark.ProjectionBorn
