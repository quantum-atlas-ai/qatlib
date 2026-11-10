/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge
import Qatlib.Foundations.InstrumentCore.Measurement.Basic
open Qatlib.Foundations.InstrumentCore.Measurement
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

namespace Qatlib.Concepts.SpectralReadout.PhaseReadout

open Matrix

set_option linter.unusedSectionVars false

variable {I : Type*} [Fintype I] [DecidableEq I]

private theorem sub_toEuclidean_fromVec (ψ φ : QState I) :
    toEuclidean_fromVec ψ - toEuclidean_fromVec φ = toEuclidean_fromVec (ψ - φ) := by
  simp only [toEuclidean_fromVec, WithLp.toLp_sub]

private theorem collapse_sub_collapse (ψ φ : QState I) (S : Finset I) :
    Collapse ψ S - Collapse φ S = Collapse (ψ - φ) S := by
  funext i
  simp only [collapse_apply, Pi.sub_apply]
  split_ifs <;> simp

private theorem applyGate_sub_applyGate (U : Matrix I I ℂ) (ψ φ : QState I) :
    ApplyGate U ψ - ApplyGate U φ = ApplyGate U (ψ - φ) := by
  funext i
  simp only [ApplyGate, Matrix.mulVec, dotProduct, Pi.sub_apply]
  have hsplit : (∑ j, U i j * (ψ j - φ j)) = ∑ j, U i j * ψ j - ∑ j, U i j * φ j := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => mul_sub _ _ _
  rw [hsplit]

theorem norm_toEuclidean_collapse_le (ψ : QState I) (S : Finset I) :
    ‖toEuclidean_fromVec (Collapse ψ S)‖ ≤ ‖toEuclidean_fromVec ψ‖ := by
  have hsum : (∑ i, ‖Collapse ψ S i‖ ^ 2) ≤ ∑ i, ‖ψ i‖ ^ 2 := by
    refine Finset.sum_le_sum fun i _ => ?_
    by_cases h : i ∈ S
    · rw [collapse_apply, if_pos h]
    · rw [collapse_apply, if_neg h]
      norm_num
  have hsq : ‖toEuclidean_fromVec (Collapse ψ S)‖ ^ 2 ≤ ‖toEuclidean_fromVec ψ‖ ^ 2 := by
    rw [norm_toEuclidean_fromVec_sq, norm_toEuclidean_fromVec_sq]
    exact hsum
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

theorem measureProb_sub_le_l2 (ψ φ : QState I) (S : Finset I) :
    |MeasureProb ψ S - MeasureProb φ S| ≤
      (‖toEuclidean_fromVec ψ‖ + ‖toEuclidean_fromVec φ‖) * ‖toEuclidean_fromVec (ψ - φ)‖ := by
  set cψ : EuclideanSpace ℂ I := toEuclidean_fromVec (Collapse ψ S) with hcψ
  set cφ : EuclideanSpace ℂ I := toEuclidean_fromVec (Collapse φ S) with hcφ
  have hψsq : MeasureProb ψ S = ‖cψ‖ ^ 2 :=
    (sum_normSq_collapse ψ S).symm.trans
      (norm_toEuclidean_fromVec_sq (Collapse ψ S)).symm
  have hφsq : MeasureProb φ S = ‖cφ‖ ^ 2 :=
    (sum_normSq_collapse φ S).symm.trans
      (norm_toEuclidean_fromVec_sq (Collapse φ S)).symm
  have hcollapse : cψ - cφ = toEuclidean_fromVec (Collapse (ψ - φ) S) := by
    rw [hcψ, hcφ, sub_toEuclidean_fromVec, collapse_sub_collapse]
  have hcollapseNorm : ‖cψ - cφ‖ ≤ ‖toEuclidean_fromVec (ψ - φ)‖ := by
    rw [hcollapse]
    exact norm_toEuclidean_collapse_le (ψ - φ) S
  calc |MeasureProb ψ S - MeasureProb φ S|
      = (‖cψ‖ + ‖cφ‖) * |‖cψ‖ - ‖cφ‖| := by
        rw [hψsq, hφsq]
        have hab : (0 : ℝ) ≤ ‖cψ‖ + ‖cφ‖ := add_nonneg (norm_nonneg _) (norm_nonneg _)
        calc |‖cψ‖ ^ 2 - ‖cφ‖ ^ 2| = |(‖cψ‖ - ‖cφ‖) * (‖cψ‖ + ‖cφ‖)| := by
              congr 1
              ring
          _ = |‖cψ‖ - ‖cφ‖| * |‖cψ‖ + ‖cφ‖| := abs_mul _ _
          _ = (‖cψ‖ + ‖cφ‖) * |‖cψ‖ - ‖cφ‖| := by rw [abs_of_nonneg hab, mul_comm]
    _ ≤ (‖cψ‖ + ‖cφ‖) * ‖cψ - cφ‖ :=
        mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le cψ cφ)
          (add_nonneg (norm_nonneg _) (norm_nonneg _))
    _ ≤ (‖toEuclidean_fromVec ψ‖ + ‖toEuclidean_fromVec φ‖) * ‖cψ - cφ‖ :=
        mul_le_mul_of_nonneg_right
          (show ‖cψ‖ + ‖cφ‖ ≤
              ‖toEuclidean_fromVec ψ‖ + ‖toEuclidean_fromVec φ‖ from
            add_le_add (norm_toEuclidean_collapse_le ψ S) (norm_toEuclidean_collapse_le φ S))
          (norm_nonneg _)
    _ ≤ (‖toEuclidean_fromVec ψ‖ + ‖toEuclidean_fromVec φ‖)
          * ‖toEuclidean_fromVec (ψ - φ)‖ :=
        mul_le_mul_of_nonneg_left hcollapseNorm (add_nonneg (norm_nonneg _) (norm_nonneg _))

theorem measureProb_sub_le_two_mul_l2 (ψ φ : QState I) (S : Finset I)
    (hψ : Normalized ψ) (hφ : Normalized φ) :
    |MeasureProb ψ S - MeasureProb φ S| ≤ 2 * ‖toEuclidean_fromVec (ψ - φ)‖ := by
  have h := measureProb_sub_le_l2 ψ φ S
  rw [(normalized_iff_norm_toEuclidean_fromVec ψ).mp hψ,
    (normalized_iff_norm_toEuclidean_fromVec φ).mp hφ] at h
  calc |MeasureProb ψ S - MeasureProb φ S| ≤ (1 + 1) * ‖toEuclidean_fromVec (ψ - φ)‖ := h
    _ = 2 * ‖toEuclidean_fromVec (ψ - φ)‖ := by ring

theorem measureProb_applyGate_sub_le_two_mul_l2 (U : Matrix I I ℂ) (ψ φ : QState I)
    (S : Finset I) (hU : U ∈ Matrix.unitaryGroup I ℂ) (hψ : Normalized ψ)
    (hφ : Normalized φ) :
    |MeasureProb (ApplyGate U ψ) S - MeasureProb (ApplyGate U φ) S|
      ≤ 2 * ‖toEuclidean_fromVec (ψ - φ)‖ := by
  have h := measureProb_sub_le_two_mul_l2 (ApplyGate U ψ) (ApplyGate U φ) S
    (normalized_applyGate hU hψ) (normalized_applyGate hU hφ)
  rw [applyGate_sub_applyGate] at h
  have hnorm : ‖toEuclidean_fromVec (ApplyGate U (ψ - φ))‖
      = ‖toEuclidean_fromVec (ψ - φ)‖ := by
    rw [← toEuclideanCLM_applyGate U (ψ - φ)]
    exact norm_toEuclideanCLM_of_mem_unitaryGroup hU _
  rwa [hnorm] at h

end Qatlib.Concepts.SpectralReadout.PhaseReadout
