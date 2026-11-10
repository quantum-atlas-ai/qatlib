/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QAOASupremacy16.GapModels
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace Qatlib.Papers.QAOASupremacy16.PathWeights

open Qatlib.Foundations.PureStateMath
open scoped BigOperators

variable {Ω : Type*} [Fintype Ω]

structure RejectionSampler (Ω : Type*) [Fintype Ω] where

  w : Ω → ℝ

  wmax : ℝ

  w_nonneg : ∀ ω, 0 ≤ w ω

  w_le_max : ∀ ω, w ω ≤ wmax

  wmax_pos : 0 < wmax

  card_pos : 0 < Fintype.card Ω

noncomputable def acceptJoint (R : RejectionSampler Ω) (ω : Ω) : ℝ :=
  ((Fintype.card Ω : ℝ))⁻¹ * (R.w ω / R.wmax)

noncomputable def acceptTotal (R : RejectionSampler Ω) : ℝ :=
  ∑ ω, acceptJoint R ω

theorem acceptTotal_eq (R : RejectionSampler Ω) :
    acceptTotal R
      = (∑ ω, R.w ω) / (((Fintype.card Ω : ℝ)) * R.wmax) := by
  have hNne : ((Fintype.card Ω : ℝ)) ≠ 0 := by
    exact_mod_cast (ne_of_gt R.card_pos)
  have hwne : R.wmax ≠ 0 := ne_of_gt R.wmax_pos
  unfold acceptTotal acceptJoint
  have h : ∀ ω, ((Fintype.card Ω : ℝ))⁻¹ * (R.w ω / R.wmax)
      = R.w ω / (((Fintype.card Ω : ℝ)) * R.wmax) := by
    intro ω
    field_simp [hNne, hwne]
  simp only [h]
  simpa using (Finset.sum_div (Finset.univ : Finset Ω) (fun ω => R.w ω)
    (((Fintype.card Ω : ℝ)) * R.wmax)).symm

theorem acceptTotal_pos (R : RejectionSampler Ω) (hS : 0 < ∑ ω, R.w ω) :
    0 < acceptTotal R := by
  rw [acceptTotal_eq]
  have hN : (0 : ℝ) < (Fintype.card Ω : ℝ) := by exact_mod_cast R.card_pos
  exact div_pos hS (mul_pos hN R.wmax_pos)

theorem condAccept_eq (R : RejectionSampler Ω) (hS : 0 < ∑ ω, R.w ω) (ω : Ω) :
    acceptJoint R ω / acceptTotal R = R.w ω / ∑ ω, R.w ω := by
  have hNne : ((Fintype.card Ω : ℝ)) ≠ 0 := by
    exact_mod_cast (ne_of_gt R.card_pos)
  have hwne : R.wmax ≠ 0 := ne_of_gt R.wmax_pos
  have hSne : (∑ ω, R.w ω) ≠ 0 := ne_of_gt hS
  rw [acceptTotal_eq]
  unfold acceptJoint
  field_simp [hNne, hwne, hSne]

theorem rejection_marginal {Ωz Ωx : Type*} [Fintype Ωz] [Fintype Ωx]
    (R : RejectionSampler (Ωz × Ωx)) (hS : 0 < ∑ ω, R.w ω) (z : Ωz) :
    ∑ x : Ωx, acceptJoint R (z, x) / acceptTotal R
      = (∑ x : Ωx, R.w (z, x)) / ∑ ω, R.w ω := by
  calc ∑ x : Ωx, acceptJoint R (z, x) / acceptTotal R
      = ∑ x : Ωx, R.w (z, x) / ∑ ω, R.w ω := by
        apply Finset.sum_congr rfl
        intro x _
        exact condAccept_eq R hS (z, x)
    _ = (∑ x : Ωx, R.w (z, x)) / ∑ ω, R.w ω := by
        simpa using (Finset.sum_div (Finset.univ : Finset Ωx) (fun x => R.w (z, x))
          (∑ ω, R.w ω)).symm

structure WeightedRejectionModel where

  n : ℕ

  L : ℕ

  sampler : RejectionSampler (Reg n × (Fin L → Reg n))

  total_pos : 0 < ∑ ω, sampler.w ω

  supplied_property : Prop

  supplied_property_holds : supplied_property

theorem modeled_path_marginal (Q : WeightedRejectionModel) (z : Reg Q.n) :
    ∑ x : Fin Q.L → Reg Q.n,
        acceptJoint Q.sampler (z, x) / acceptTotal Q.sampler
      = (∑ x : Fin Q.L → Reg Q.n, Q.sampler.w (z, x))
        / ∑ ω : Reg Q.n × (Fin Q.L → Reg Q.n), Q.sampler.w ω :=
  rejection_marginal Q.sampler Q.total_pos z

theorem acceptance_and_supplied_property (Q : WeightedRejectionModel) :
    0 < acceptTotal Q.sampler ∧ Q.supplied_property :=
  ⟨acceptTotal_pos Q.sampler Q.total_pos, Q.supplied_property_holds⟩

end Qatlib.Papers.QAOASupremacy16.PathWeights
