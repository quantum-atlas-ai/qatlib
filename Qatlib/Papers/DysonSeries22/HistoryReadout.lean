/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ChannelTheory.Naimark.ContractionBorn
import Qatlib.Concepts.ChannelTheory.Naimark.ProjectionControl
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace Qatlib.Papers.DysonSeries22.HistoryReadout
open Matrix
open scoped Classical Matrix.Norms.L2Operator
open Qatlib.Concepts.ChannelTheory.Naimark
variable {C I : Type} [Fintype C] [Fintype I] [DecidableEq C] [DecidableEq I]

def clockProjector (S : Finset C) : Matrix (C×I) (C×I) ℂ :=
  diagonal (fun ci => if ci.1 ∈ S then 1 else 0)

omit [Fintype C] [Fintype I] in

theorem clockProjector_star (S : Finset C) : (clockProjector (I:=I) S)ᴴ=clockProjector S := by
  simp [clockProjector,Matrix.diagonal_conjTranspose]

theorem clockProjector_square (S : Finset C) : clockProjector (I:=I) S*clockProjector S=clockProjector S := by
  rw [clockProjector,Matrix.diagonal_mul_diagonal]
  congr 1
  funext ci
  split_ifs <;> simp

theorem clockProjector_norm (S : Finset C) : ‖clockProjector (I:=I) S‖ ≤ 1 := by
  rw [clockProjector,Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤1)).2
  intro ci
  split_ifs <;> norm_num

theorem endpoint_program_unitary (S : Finset C) :
    ProjectionControl.program (clockProjector (I:=I) S) ∈ Matrix.unitaryGroup ((C×I)⊕(C×I)) ℂ :=
  ProjectionControl.program_unitary _ (clockProjector_star S) (clockProjector_square S)

theorem endpoint_program_corner (S : Finset C) (i j : C×I) :
    ProjectionControl.program (clockProjector S) (Sum.inl i) (Sum.inl j)=clockProjector S i j :=
  ProjectionControl.program_success_corner _ _ _

def selectedMass (S : Finset C) (x : EuclideanSpace ℂ (C×I)) : ℝ :=
  ∑ c ∈ S, ∑ i, ‖x (c,i)‖^2

theorem clock_projected_mass (S : Finset C) (x : EuclideanSpace ℂ (C×I)) :
    ‖(WithLp.toLp 2 (clockProjector S*ᵥ x.ofLp) : EuclideanSpace ℂ (C×I))‖^2 =
      selectedMass S x := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [clockProjector,Matrix.mulVec_diagonal,Fintype.sum_prod_type]
  simp only [ite_mul,one_mul,zero_mul]
  simp_rw [apply_ite (fun z : ℂ => ‖z‖^2),norm_zero,zero_pow (by decide : 2≠0)]
  simp only [Finset.sum_ite_irrel,Finset.sum_const_zero]
  simp [selectedMass,Finset.sum_ite_mem]

theorem native_endpoint_Born (S : Finset C) (x : EuclideanSpace ℂ (C×I)) (hx : ‖x‖=1) :
    (((ContractionInstrument.readout (clockProjector S) (clockProjector_norm S)).measure
      (MState.pure (ContractionBorn.ketOfUnit x hx))) true : ℝ)=selectedMass S x := by
  rw [ContractionBorn.native_success_Born_unit,clock_projected_mass]

omit [Fintype C] [DecidableEq C] [DecidableEq I] in

theorem padded_endpoint_mass (S : Finset C) (x : EuclideanSpace ℂ (C×I))
    (v : EuclideanSpace ℂ I) (hpad : ∀ c ∈ S, ∀ i, x (c,i)=v i) :
    selectedMass S x = (S.card:ℝ)*‖v‖^2 := by
  unfold selectedMass
  have h : ∀ c ∈ S, (∑ i, ‖x (c,i)‖^2)=‖v‖^2 := by
    intro c hc
    simp_rw [hpad c hc]
    exact (EuclideanSpace.norm_sq_eq v).symm
  rw [Finset.sum_congr rfl h,Finset.sum_const, nsmul_eq_mul]

theorem padded_native_Born (S : Finset C) (x : EuclideanSpace ℂ (C×I)) (hx : ‖x‖=1)
    (v : EuclideanSpace ℂ I) (hpad : ∀ c ∈ S, ∀ i, x (c,i)=v i) :
    (((ContractionInstrument.readout (clockProjector S) (clockProjector_norm S)).measure
      (MState.pure (ContractionBorn.ketOfUnit x hx))) true : ℝ)=(S.card:ℝ)*‖v‖^2 := by
  rw [native_endpoint_Born,padded_endpoint_mass S x v hpad]
end Qatlib.Papers.DysonSeries22.HistoryReadout
