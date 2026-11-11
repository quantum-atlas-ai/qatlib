/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.RationalFlow.SourceMeanSum
import Qatlib.Concepts.EffectiveGauge.HopfAtlas.UnitSourceMoment

set_option backward.isDefEq.respectTransparency false

/-! # Same-execution error of the finite original-source curvature mean -/

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff BigOperators
namespace Qatlib.Concepts.EffectiveGauge.RationalFlow
open Qatlib.Concepts.EffectiveGauge.HopfAtlas

/-- Original `sourceMeanGrid_mem` guarantee for the `SourceMeanError` construction; the complete source hypotheses are retained. -/
theorem sourceMeanGrid_mem (N : ℕ) (index : SourceMeanIndex) :
    index ∈ sourceMeanGrid N ↔ index.1<N ∧ index.2.1<N ∧ index.2.2<N := by
  rcases index with ⟨k,l,m⟩
  simp [sourceMeanGrid,List.mem_flatMap,List.mem_map,List.mem_range]

/-- Original `sourceMeanUnitPoint_mem` guarantee for the `SourceMeanError` construction; the complete source hypotheses are retained. -/
theorem sourceMeanUnitPoint_mem (N : ℕ) (hN : 0<N) (index : SourceMeanIndex)
    (hi : index ∈ sourceMeanGrid N) : ∀ i, (sourceMeanUnitPoint N index i : ℝ) ∈ Icc 0 1 := by
  have hidx := (sourceMeanGrid_mem N index).mp hi
  intro i
  have hc : sourceMeanIndexCoord index i<N := by
    fin_cases i
    · exact hidx.1
    · exact hidx.2.1
    · exact hidx.2.2
  simpa only [sourceMeanUnitPoint,Rat.cast_div,Rat.cast_natCast] using
    meanLeftNode_mem N hN (sourceMeanIndexCoord index i) hc

/-- Original `sourceMeanUnitPoint_cast` guarantee for the `SourceMeanError` construction; the complete source hypotheses are retained. -/
theorem sourceMeanUnitPoint_cast (N : ℕ) (k l m : ℕ) :
    rationalSpatialPoint (sourceMeanUnitPoint N (k,l,m))=
      meanTensorSpatial ((k : ℝ)/(N : ℝ),(l : ℝ)/(N : ℝ),(m : ℝ)/(N : ℝ)) := by
  ext i
  fin_cases i <;> simp [rationalSpatialPoint,sourceMeanUnitPoint,sourceMeanIndexCoord,meanTensorSpatial]

/-- Every label actually consumed by the full mean decoder is a legal
physical rational query of order zero or one. -/
theorem sourceMeanSchedule_legal (m1 m2 : ℚ) (N b : ℕ) (hN : 0<N) :
    ∀ q ∈ sourceMeanSchedule m1 m2 N b,
      ∀ i, 0 ≤ (q.1.1 i : ℝ) ∧ (q.1.1 i : ℝ) ≤ physicalPeriod := by
  intro q hq
  simp only [sourceMeanSchedule,List.mem_flatMap] at hq
  obtain ⟨index,hi,hq⟩ := hq
  rw [sourceMeanPacketSchedule_eq] at hq
  exact sourceFirstJetSchedule_legal m1 m2 _ b (sourceMeanUnitPoint_mem N hN index hi) q hq

/-- Original `meanGridAverage_sub_bound` guarantee for the `SourceMeanError` construction; the complete source hypotheses are retained. -/
private theorem meanGridAverage_sub_bound (N : ℕ) (hN : 0<N) (A B : ℕ → ℕ → ℕ → ℝ)
    (E : ℝ) (hAB : ∀ k<N, ∀ l<N, ∀ m<N, |A k l m-B k l m| ≤ E) :
    |(∑ k ∈ Finset.range N, ∑ l ∈ Finset.range N, ∑ m ∈ Finset.range N, A k l m)/(N : ℝ)^3-
      (∑ k ∈ Finset.range N, ∑ l ∈ Finset.range N, ∑ m ∈ Finset.range N, B k l m)/(N : ℝ)^3| ≤ E := by
  have hn : (0 : ℝ)<N := by exact_mod_cast hN
  rw [← sub_div,abs_div,abs_of_pos (pow_pos hn 3)]
  apply (div_le_iff₀ (pow_pos hn 3)).mpr
  simp_rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ k ∈ Finset.range N, ∑ l ∈ Finset.range N, ∑ m ∈ Finset.range N, |A k l m-B k l m| := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro k _
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro l _
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.range N, ∑ _l ∈ Finset.range N, ∑ _m ∈ Finset.range N, E := by
      apply Finset.sum_le_sum
      intro k hk
      apply Finset.sum_le_sum
      intro l hl
      apply Finset.sum_le_sum
      intro m hm
      exact hAB k (Finset.mem_range.mp hk) l (Finset.mem_range.mp hl) m (Finset.mem_range.mp hm)
    _ = E*(N : ℝ)^3 := by simp; ring

/-- Finite noisy-node replacement in the same common-denominator packet
average. Accuracy comes from the original physical source, not packet input. -/
theorem sourceMeanPacketAverage_error (v : SpatialPoint → SpatialPoint)
    (hv : ContDiff ℝ ∞ v) (hu : ∀ x, ‖v x‖=1)
    (source : RationalJetSource) (hs : OriginalFirstJetAccurate v source)
    (m1 m2 : ℚ) (hm1 : 0 ≤ m1) (hm2 : 0 ≤ m2)
    (hb : SourceAllRescalingBounds v (m1 : ℝ) (m2 : ℝ))
    (N b : ℕ) (hN : 0<N) (hprec : (2^b : ℝ)⁻¹ ≤ 1/64) (i j : Fin 3) :
    |(sourceMeanPacketAverage N (b+2)
        (fun index => roundedSourceFirstJet source m1 m2 (sourceMeanUnitPoint N index) b) i j : ℝ)-
      meanTensorLeftSum N (fun p => sourceCurvatureMoment (unitCoordinateSpin v) i j
        (meanTensorSpatial p))| ≤ 2*(2^b : ℝ)⁻¹*(7*(m1 : ℝ)+1)^2 := by
  rw [meanTensorLeftSum_eq]
  simp only [sourceMeanPacketAverage,Rat.cast_div,Rat.cast_sum,Rat.cast_mul,Rat.cast_pow,Rat.cast_natCast]
  apply meanGridAverage_sub_bound N hN
  intro k hk l hl m hm
  let index : SourceMeanIndex := (k,l,m)
  let a := sourceMeanUnitPoint N index
  have ha : ∀ r, (a r : ℝ) ∈ Icc 0 1 :=
    sourceMeanUnitPoint_mem N hN index ((sourceMeanGrid_mem N index).mpr ⟨hk,hl,hm⟩)
  have herr := roundedSourceCurvature_error v hv hu source hs m1 m2 hm1 hm2 hb a ha b hprec i j
  rw [← sourceCurvature_unit_value v hv] at herr
  have hweight : |(a i : ℝ)| ≤ 1 := by rw [abs_of_nonneg (ha i).1]; exact (ha i).2
  have hw := mul_le_mul hweight herr (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  rw [one_mul,← abs_mul,mul_sub] at hw
  rw [← sourceMeanUnitPoint_cast N k l m]
  exact hw

/-- The actual finite program returns three rational negative moments of
the fixed exact source, with both genuine quadrature and finite-sample error. -/
theorem sourceMeanUnitExecution_error (v : SpatialPoint → SpatialPoint)
    (hv : ContDiff ℝ ∞ v) (hu : ∀ x, ‖v x‖=1)
    (source : RationalJetSource) (hs : OriginalFirstJetAccurate v source)
    (m1 m2 : ℚ) (hm1 : 0 ≤ m1) (hm2 : 0 ≤ m2)
    (hb : SourceAllRescalingBounds v (m1 : ℝ) (m2 : ℝ))
    (N b : ℕ) (hN : 0<N) (hprec : (2^b : ℝ)⁻¹ ≤ 1/64) :
    ∃ result, sourceMeanUnitExecution source m1 m2 N b=some result ∧ ∀ j,
      |(result j : ℝ)+unitCubeIntegral
        (sourceCurvatureMoment (unitCoordinateSpin v) (sourceMeanMomentAxis j) j)| ≤
      3*((7*(m1 : ℝ))^2/2+(7*(m1 : ℝ))*(49*(m2 : ℝ)))/(N : ℝ)+
        2*(2^b : ℝ)⁻¹*(7*(m1 : ℝ)+1)^2 := by
  refine ⟨_,sourceMeanUnitExecution_eq source m1 m2 N b hN,?_⟩
  intro j
  have hquad := unitSourceMoment_quadrature_error v hv hu (m1 : ℝ) (m2 : ℝ)
    (by exact_mod_cast hm1) (by exact_mod_cast hm2) hb (sourceMeanMomentAxis j) j N hN
  have hpacket := sourceMeanPacketAverage_error v hv hu source hs m1 m2 hm1 hm2 hb
    N b hN hprec (sourceMeanMomentAxis j) j
  push_cast
  have ht := abs_sub_le (unitCubeIntegral
    (sourceCurvatureMoment (unitCoordinateSpin v) (sourceMeanMomentAxis j) j))
    (meanTensorLeftSum N (fun p => sourceCurvatureMoment (unitCoordinateSpin v)
      (sourceMeanMomentAxis j) j (meanTensorSpatial p)))
    (sourceMeanPacketAverage N (b+2)
      (fun index => roundedSourceFirstJet source m1 m2 (sourceMeanUnitPoint N index) b)
      (sourceMeanMomentAxis j) j : ℝ)
  rw [abs_sub_comm (meanTensorLeftSum N _)] at ht
  simpa only [neg_add_eq_sub] using ht.trans (add_le_add hquad hpacket)

end Qatlib.Concepts.EffectiveGauge.RationalFlow
