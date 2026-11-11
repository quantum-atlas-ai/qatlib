/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ChannelTheory.Naimark.ContractionBorn
import Qatlib.Concepts.ChannelTheory.Naimark.ProjectionControl

/-!
# Clock projection and endpoint readout

`clockProjector` selects a finite set of clock labels in a clock and system register. This
module proves that it is a self-adjoint projection of norm at most one and relates its native
instrument readout to `selectedMass`. If the selected clock slices all contain the same vector,
the selected mass is their number times its squared norm.

The mathematical setting follows [BerryCosta2024].

## Main statements

* `endpoint_program_unitary`: the projection control program is unitary.
* `native_endpoint_Born`: readout success equals the selected mass.
* `padded_native_Born`: identical selected slices give the multiplicity formula.

## References

* [Berry and Costa, 2024][BerryCosta2024]
-/

set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace Qatlib.Papers.DysonSeries22.HistoryReadout
open Matrix
open scoped Classical Matrix.Norms.L2Operator
open Qatlib.Concepts.ChannelTheory.Naimark
variable {C I : Type} [Fintype C] [Fintype I] [DecidableEq C] [DecidableEq I]

/-- The diagonal projection retaining exactly those clock labels that belong to `S`. -/
def clockProjector (S : Finset C) : Matrix (C×I) (C×I) ℂ :=
  diagonal (fun ci => if ci.1 ∈ S then 1 else 0)

omit [Fintype C] [Fintype I] in

/-- The clock projection is self-adjoint. -/
theorem clockProjector_star (S : Finset C) : (clockProjector (I:=I) S)ᴴ=clockProjector S := by
  simp [clockProjector,Matrix.diagonal_conjTranspose]

/-- The clock projection is idempotent. -/
theorem clockProjector_square (S : Finset C) : clockProjector (I:=I) S*clockProjector S=clockProjector S := by
  rw [clockProjector,Matrix.diagonal_mul_diagonal]
  congr 1
  funext ci
  split_ifs <;> simp

/-- The operator norm of the clock projection is at most one. -/
theorem clockProjector_norm (S : Finset C) : ‖clockProjector (I:=I) S‖ ≤ 1 := by
  rw [clockProjector,Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤1)).2
  intro ci
  split_ifs <;> norm_num

/-- The projection control program built from the clock projection is unitary. See [Berry and
Costa, 2024, Eqs. (96)–(101)][BerryCosta2024]. -/
theorem endpoint_program_unitary (S : Finset C) :
    ProjectionControl.program (clockProjector (I:=I) S) ∈ Matrix.unitaryGroup ((C×I)⊕(C×I)) ℂ :=
  ProjectionControl.program_unitary _ (clockProjector_star S) (clockProjector_square S)

/-- The success corner of the projection control program equals the clock projection. -/
theorem endpoint_program_corner (S : Finset C) (i j : C×I) :
    ProjectionControl.program (clockProjector S) (Sum.inl i) (Sum.inl j)=clockProjector S i j :=
  ProjectionControl.program_success_corner _ _ _

/-- The sum of squared coordinate norms over the system indices and the clock labels in `S`. -/
def selectedMass (S : Finset C) (x : EuclideanSpace ℂ (C×I)) : ℝ :=
  ∑ c ∈ S, ∑ i, ‖x (c,i)‖^2

/-- The squared Euclidean norm after clock projection equals `selectedMass S x`. -/
theorem clock_projected_mass (S : Finset C) (x : EuclideanSpace ℂ (C×I)) :
    ‖(WithLp.toLp 2 (clockProjector S*ᵥ x.ofLp) : EuclideanSpace ℂ (C×I))‖^2 =
      selectedMass S x := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [clockProjector,Matrix.mulVec_diagonal,Fintype.sum_prod_type]
  simp only [ite_mul,one_mul,zero_mul]
  simp_rw [apply_ite (fun z : ℂ => ‖z‖^2),norm_zero,zero_pow (by decide : 2≠0)]
  simp only [Finset.sum_ite_irrel,Finset.sum_const_zero]
  simp [selectedMass,Finset.sum_ite_mem]

/-- For a unit vector `x`, the success probability of the native clock projection readout equals
the selected mass. -/
theorem native_endpoint_Born (S : Finset C) (x : EuclideanSpace ℂ (C×I)) (hx : ‖x‖=1) :
    (((ContractionInstrument.readout (clockProjector S) (clockProjector_norm S)).measure
      (MState.pure (ContractionBorn.ketOfUnit x hx))) true : ℝ)=selectedMass S x := by
  rw [ContractionBorn.native_success_Born_unit,clock_projected_mass]

omit [Fintype C] [DecidableEq C] [DecidableEq I] in

/-- If each selected clock slice equals `v`, the selected mass equals the cardinality of `S`
times `‖v‖²`. -/
theorem padded_endpoint_mass (S : Finset C) (x : EuclideanSpace ℂ (C×I))
    (v : EuclideanSpace ℂ I) (hpad : ∀ c ∈ S, ∀ i, x (c,i)=v i) :
    selectedMass S x = (S.card:ℝ)*‖v‖^2 := by
  unfold selectedMass
  have h : ∀ c ∈ S, (∑ i, ‖x (c,i)‖^2)=‖v‖^2 := by
    intro c hc
    simp_rw [hpad c hc]
    exact (EuclideanSpace.norm_sq_eq v).symm
  rw [Finset.sum_congr rfl h,Finset.sum_const, nsmul_eq_mul]

/-- For a unit vector whose selected clock slices all equal `v`, native readout succeeds with
probability equal to the cardinality of `S` times `‖v‖²`. -/
theorem padded_native_Born (S : Finset C) (x : EuclideanSpace ℂ (C×I)) (hx : ‖x‖=1)
    (v : EuclideanSpace ℂ I) (hpad : ∀ c ∈ S, ∀ i, x (c,i)=v i) :
    (((ContractionInstrument.readout (clockProjector S) (clockProjector_norm S)).measure
      (MState.pure (ContractionBorn.ketOfUnit x hx))) true : ℝ)=(S.card:ℝ)*‖v‖^2 := by
  rw [native_endpoint_Born,padded_endpoint_mass S x v hpad]
end Qatlib.Papers.DysonSeries22.HistoryReadout
