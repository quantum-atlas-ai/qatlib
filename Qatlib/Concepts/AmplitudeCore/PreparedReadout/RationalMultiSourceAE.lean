/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule
import Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSource.DenseHistoryThreeSourceAE
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Concepts.AmplitudeCore.PreparedReadout.RationalMultiSourceAE

open Matrix
open scoped Classical BigOperators
set_option warningAsError false

variable {H : Type} [Fintype H] [DecidableEq H]

noncomputable def instructions (T B eps : ℚ) (Aword : List (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Step H))
    (seed : H) (S : Finset H) :
    List (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Step (Fin (Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule.grid T B eps) × (Bool × H))) :=
  Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE.instructions (Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule.grid T B eps) Aword seed S

def decode (T B eps : ℚ) (z : Fin (Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule.grid T B eps)) : ℚ :=
  T * Qatlib.Concepts.AmplitudeCore.PreparedReadout.nativeAEDecode (Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule.grid T B eps)
    (Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule.decoderBits T eps) z

noncomputable def amplitude (U : Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Source → Matrix H H ℂ) (Aword : List (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Step H))
    (seed : H) (S : Finset H) : ℝ := Qatlib.Foundations.PureStateMath.MeasureProb (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.evaluate U Aword *ᵥ Qatlib.Foundations.PureStateMath.Ket seed) S

noncomputable def output (T B eps : ℚ) (U : Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Source → Matrix H H ℂ)
    (Aword : List (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Step H)) (seed : H) (S : Finset H) :
    Qatlib.Foundations.PureStateMath.QState (Fin (Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule.grid T B eps) × (Bool × H)) :=
  Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.evaluate (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE.oracle (Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule.grid T B eps) U)
    (Qatlib.Concepts.AmplitudeCore.PreparedReadout.RationalMultiSourceAE.instructions T B eps Aword seed S) *ᵥ
      Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE.input (Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule.grid T B eps)
        (Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule.grid_pos T B eps) seed

theorem amplitude_bounds (U : Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Source → Matrix H H ℂ) (Aword : List (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Step H))
    (seed : H) (S : Finset H) (hU : ∀ s, U s ∈ Matrix.unitaryGroup H ℂ)
    (hw : Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.WellFormed Aword) :
    0 ≤ Qatlib.Concepts.AmplitudeCore.PreparedReadout.RationalMultiSourceAE.amplitude U Aword seed S ∧ Qatlib.Concepts.AmplitudeCore.PreparedReadout.RationalMultiSourceAE.amplitude U Aword seed S ≤ 1 :=
  ⟨Qatlib.Foundations.PureStateMath.measureProb_nonneg _ _, Qatlib.Foundations.BornMetrics.EventProbability.measureProb_le_one
    (Qatlib.Foundations.PureStateMath.normalized_applyGate (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.evaluate_unitary U Aword hw hU) (Qatlib.Foundations.PureStateMath.normalized_ket seed)) _⟩

theorem success_actual_mass (T B eps : ℚ) (hT : 0 < T) (heps : 0 < eps)
    (U : Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Source → Matrix H H ℂ) (Aword : List (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Step H)) (seed : H) (S : Finset H)
    (hU : ∀ s, U s ∈ Matrix.unitaryGroup H ℂ) (hw : Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.WellFormed Aword)
    (hpB : (T : ℝ) * Qatlib.Concepts.AmplitudeCore.PreparedReadout.RationalMultiSourceAE.amplitude U Aword seed S ≤ (B : ℝ)) :
    Qatlib.Foundations.PureStateMath.MeasureProb (Qatlib.Concepts.AmplitudeCore.PreparedReadout.RationalMultiSourceAE.output T B eps U Aword seed S)
      (Finset.univ.filter (fun z =>
        |(Qatlib.Concepts.AmplitudeCore.PreparedReadout.RationalMultiSourceAE.decode T B eps z.1 : ℝ) - (T : ℝ) * Qatlib.Concepts.AmplitudeCore.PreparedReadout.RationalMultiSourceAE.amplitude U Aword seed S| ≤
          5*(eps : ℝ)/8)) ≥ 8/Real.pi^2 := by
  let M := Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule.grid T B eps
  let k := Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule.decoderBits T eps
  let p :=
      Qatlib.Concepts.AmplitudeCore.PreparedReadout.RationalMultiSourceAE.amplitude U Aword seed S
  let P : Fin M → Prop := fun z =>
    |(Qatlib.Concepts.AmplitudeCore.PreparedReadout.nativeAEDecode M k z : ℝ)-p| ≤
      Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule.radius M p + ((2 : ℝ)⁻¹)^k
  have hl : Qatlib.Foundations.PureStateMath.MeasureProb (Qatlib.Concepts.AmplitudeCore.PreparedReadout.RationalMultiSourceAE.output T B eps U Aword seed S)
      (Finset.univ.filter (fun z => P z.1)) ≥ 8/Real.pi^2 := by
    change Qatlib.Foundations.PureStateMath.MeasureProb (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE.output M
      (Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule.grid_pos T B eps) U Aword seed S)
      (Finset.univ.filter (fun z => P z.1)) ≥ _
    rw [Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE.event_eq_aeLaw M
      (Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule.two_le_grid T B eps) U Aword seed S hU hw P]
    simpa only [P, p, Qatlib.Concepts.AmplitudeCore.PreparedReadout.RationalMultiSourceAE.amplitude, Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule.radius] using!
      Qatlib.Concepts.AmplitudeCore.PreparedReadout.native_ae_same_record_bhmt_success H M k
        (Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule.two_le_grid T B eps)
        (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.evaluate U Aword) seed S (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.evaluate_unitary U Aword hw hU)
  apply hl.trans
  apply Qatlib.Foundations.BornMetrics.EventProbability.measureProb_mono
  intro z hz
  have hdev := (Finset.mem_filter.mp hz).2
  have hb :=
      Qatlib.Concepts.AmplitudeCore.PreparedReadout.RationalMultiSourceAE.amplitude_bounds U Aword seed S hU hw
  have hs :=
      Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule.statistical_budget T B eps hT heps p hb.1 hb.2 hpB
  have ht : (0 : ℝ) ≤ T := by exact_mod_cast hT.le
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  change |((T * Qatlib.Concepts.AmplitudeCore.PreparedReadout.nativeAEDecode M k z.1 : ℚ) : ℝ) -
      (T : ℝ)*p| ≤ _
  push_cast
  rw [← mul_sub, abs_mul, abs_of_nonneg ht]
  exact (mul_le_mul_of_nonneg_left hdev ht).trans hs

theorem success_to_center (T B eps : ℚ) (hT : 0 < T) (heps : 0 < eps)
    (U : Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Source → Matrix H H ℂ) (Aword : List (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Step H)) (seed : H) (S : Finset H)
    (hU : ∀ s, U s ∈ Matrix.unitaryGroup H ℂ) (hw : Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.WellFormed Aword)
    (hpB : (T : ℝ)*Qatlib.Concepts.AmplitudeCore.PreparedReadout.RationalMultiSourceAE.amplitude U Aword seed S ≤ (B : ℝ))
    (mu : ℝ) (hbias : |(T : ℝ)*Qatlib.Concepts.AmplitudeCore.PreparedReadout.RationalMultiSourceAE.amplitude U Aword seed S - mu| ≤ (eps : ℝ)/4) :
    Qatlib.Foundations.PureStateMath.MeasureProb (Qatlib.Concepts.AmplitudeCore.PreparedReadout.RationalMultiSourceAE.output T B eps U Aword seed S)
      (Finset.univ.filter (fun z => |(Qatlib.Concepts.AmplitudeCore.PreparedReadout.RationalMultiSourceAE.decode T B eps z.1 : ℝ)-mu| ≤ 7*(eps : ℝ)/8)) ≥
        8/Real.pi^2 := by
  apply (Qatlib.Concepts.AmplitudeCore.PreparedReadout.RationalMultiSourceAE.success_actual_mass T B eps hT heps U Aword seed S hU hw hpB).trans
  apply Qatlib.Foundations.BornMetrics.EventProbability.measureProb_mono
  intro z hz
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  have ht :=
      abs_sub_le (Qatlib.Concepts.AmplitudeCore.PreparedReadout.RationalMultiSourceAE.decode T B eps z.1 : ℝ) ((T : ℝ)*Qatlib.Concepts.AmplitudeCore.PreparedReadout.RationalMultiSourceAE.amplitude U Aword seed S) mu
  have hg := (Finset.mem_filter.mp hz).2
  linarith

theorem resources (T B eps : ℚ)
    (Aword : List (Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.Step H))
    (seed : H) (S : Finset H)
    (hw : Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.WellFormed Aword) :
    Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.WellFormed (Qatlib.Concepts.AmplitudeCore.PreparedReadout.RationalMultiSourceAE.instructions T B eps Aword seed S) ∧
      (∀ s, Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.queryCount s
        (Qatlib.Concepts.AmplitudeCore.PreparedReadout.RationalMultiSourceAE.instructions T B eps Aword seed S) =
        (2*Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule.grid T B eps-1)*Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.queryCount s Aword) ∧
      Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.gateCount (Qatlib.Concepts.AmplitudeCore.PreparedReadout.RationalMultiSourceAE.instructions T B eps Aword seed S) =
        (2*Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule.grid T B eps-1)*Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryOracleWord.gateCount Aword +
          4*(Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule.grid T B eps-1)+2 :=
  Qatlib.Concepts.AmplitudeCore.PreparedReadout.MultiSourceAmplitudeEstimation.DenseHistoryThreeSourceAE.resources _
    (Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule.grid_pos T B eps) Aword seed S hw

end Qatlib.Concepts.AmplitudeCore.PreparedReadout.RationalMultiSourceAE
