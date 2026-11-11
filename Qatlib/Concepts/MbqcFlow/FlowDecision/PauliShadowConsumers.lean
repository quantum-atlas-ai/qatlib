/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PauliClifford.ExactRank.PauliShadowStatistics

/-!
# Concrete Pauli shadow estimates

Evaluates Pauli shadow statistics on the zero-basis pure state and the maximally mixed qubit.
The coefficient vector `thetaZ` selects the Pauli Z observable, giving explicit means,
variances, and outcome probabilities.

The module also specializes weighted independent sampling and a physical median-of-means
concentration bound with operation counts. These constructions belong to the classical shadow
framework of [HuangKuengPreskill2020].

## Main statements

* `pauli_non_iid_weighted_consumer`: a weighted example with two different input states.
* `pauli_shadow_physical_mom_consumer`: a many-observable deviation bound and
  measurement-resource counts.

## References

* [Huang et al., 2020][HuangKuengPreskill2020]
-/

open Qatlib.Foundations.PureStateMath
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.PauliClifford.ExactRank

namespace Qatlib.Concepts.MbqcFlow.FlowDecision

open Matrix
open scoped ComplexOrder

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

/-- The zero-basis pure state and the maximally mixed qubit are density operators, and the
latter is not pure. -/
theorem pauli_weighted_consumer_inputs :
    IsDensityOperator (outerProduct (Ket (0:Fin 2))) ∧ IsDensityOperator ((1/2:ℂ) • (1:Operator 2)) ∧ ¬ IsPureDensityOperator ((1/2:ℂ) • (1:Operator 2)) := by
  refine ⟨isDensityOperator_outerProduct (normalized_ket 0), ⟨?_, ?_⟩, ?_⟩
  · exact Matrix.PosSemidef.smul Matrix.PosSemidef.one (by
      rw [show (1/2 : ℂ) = ((1/2 : ℝ) : ℂ) from by rw [Complex.ofReal_div]; norm_num]
      exact RCLike.ofReal_nonneg.mpr (show (0:ℝ) ≤ 1/2 by norm_num))
  · rw [Matrix.trace_smul, smul_eq_mul, Matrix.trace_one, Fintype.card_fin]
    norm_num [Complex.ofReal_div]
  · rintro ⟨_, hidem⟩
    have h := congrFun (congrFun hidem 0) 0
    rw [Matrix.mul_apply, Fin.sum_univ_two] at h
    simp [Matrix.smul_apply] at h

/-- The Pauli Z expectation of the zero-basis pure state equals one. -/
theorem pauliExpectation_z_outerProduct_ket_zero :
    pauliExpectation 2 (outerProduct (Ket (0 : Fin 2))) = 1 := by
  rw [pauliExpectation, pauliMatrix_two, trace_pauliZ_mul]
  simp [outerProduct, Qatlib.Foundations.PureStateMath.Ket]

/-- The Pauli Z expectation of the maximally mixed qubit equals zero. -/
theorem pauliExpectation_z_half :
    pauliExpectation 2 ((1/2:ℂ) • (1 : Operator 2)) = 0 := by
  rw [pauliExpectation, pauliMatrix_two, trace_pauliZ_mul]
  simp [Matrix.smul_apply]

/-- The Pauli coefficient vector equal to one on the Z axis and zero on the other axes. -/
def thetaZ : Fin 3 → ℝ := fun a => if a = 2 then 1 else 0

/-- The sum of the squared coefficients of `thetaZ` equals one. -/
theorem thetaZ_sq_sum : ∑ a : Fin 3, (thetaZ a)^2 = 1 := by
  have h1 : ∀ a : Fin 3, (thetaZ a)^2 = thetaZ a := fun a => by
    show (if a = 2 then (1:ℝ) else 0)^2 = if a = 2 then 1 else 0
    split_ifs <;> norm_num
  rw [Finset.sum_congr rfl fun a _ => h1 a]
  simp only [thetaZ]
  rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]

/-- Weighting the Pauli expectations by `thetaZ` extracts the specified Z expectation. -/
theorem thetaZ_weighted_expectation (ρ : Operator 2) (e : ℝ)
    (he : pauliExpectation 2 ρ = e) :
    ∑ a : Fin 3, thetaZ a * pauliExpectation a ρ = e := by
  simp only [thetaZ, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
  exact he

/-- The Z shadow statistic has mean one on the zero-basis pure state. -/
theorem expect_pure_z (h₀ : IsDensityOperator (outerProduct (Ket (0 : Fin 2)))) :
    (pauliRecordDist (outerProduct (Ket (0 : Fin 2))) h₀).expect
      (pauliSnapshotValue 0 thetaZ) = 1 := by
  rw [(pauli_shadow_mean_second_moment _ h₀ 0 thetaZ).2.1, pauliObservable_trace_re _ h₀]
  rw [thetaZ_weighted_expectation _ 1 pauliExpectation_z_outerProduct_ket_zero]
  ring

/-- The Z shadow statistic has mean zero on the maximally mixed qubit. -/
theorem expect_mixed_z (h₁ : IsDensityOperator ((1/2:ℂ) • (1 : Operator 2))) :
    (pauliRecordDist ((1/2:ℂ) • (1 : Operator 2)) h₁).expect
      (pauliSnapshotValue 0 thetaZ) = 0 := by
  rw [(pauli_shadow_mean_second_moment _ h₁ 0 thetaZ).2.1, pauliObservable_trace_re _ h₁]
  rw [thetaZ_weighted_expectation _ 0 pauliExpectation_z_half]
  ring

/-- The Z shadow statistic has variance two on the zero-basis pure state. -/
theorem variance_pure_z (h₀ : IsDensityOperator (outerProduct (Ket (0 : Fin 2)))) :
    (pauliRecordDist (outerProduct (Ket (0 : Fin 2))) h₀).variance
      (pauliSnapshotValue 0 thetaZ) = 2 := by
  rw [(pauli_shadow_mean_second_moment _ h₀ 0 thetaZ).2.2.2.1, thetaZ_sq_sum,
    thetaZ_weighted_expectation _ 1 pauliExpectation_z_outerProduct_ket_zero]
  ring

/-- The Z shadow statistic has variance three on the maximally mixed qubit. -/
theorem variance_mixed_z (h₁ : IsDensityOperator ((1/2:ℂ) • (1 : Operator 2))) :
    (pauliRecordDist ((1/2:ℂ) • (1 : Operator 2)) h₁).variance
      (pauliSnapshotValue 0 thetaZ) = 3 := by
  rw [(pauli_shadow_mean_second_moment _ h₁ 0 thetaZ).2.2.2.1, thetaZ_sq_sum,
    thetaZ_weighted_expectation _ 0 pauliExpectation_z_half]
  ring

/-- The Z-axis positive outcome has probability one third on the zero-basis pure state. -/
theorem prob_pure_z_plus (h₀ : IsDensityOperator (outerProduct (Ket (0 : Fin 2)))) :
    (pauliRecordDist (outerProduct (Ket (0 : Fin 2))) h₀).prob (2, true) = 1/3 := by
  show instrumentProb pauliShadowRecordInstrument _ (2, true) = 1/3
  rw [(pauli_record_kraus_and_mass.2 _ (2, true)).2]
  have htr : Matrix.trace (PauliProjector 2 true * outerProduct (Ket (0 : Fin 2))) = 1 := by
    have h1 : PauliProjector 2 true = (1/2 : ℂ) • (1 + pauliZ) := by
      have h := axis_leaf_operator 2 true
      rw [pauliBasisMatrix_two, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one] at h
      rw [← h]
      exact projector_zero_eq
    rw [h1, Matrix.smul_mul, Matrix.add_mul, Matrix.one_mul,
      Matrix.trace_smul, smul_eq_mul, Matrix.trace_add]
    have h2 : Matrix.trace (pauliZ * outerProduct (Ket (0 : Fin 2))) = 1 := by
      rw [trace_pauliZ_mul]
      simp [outerProduct, Qatlib.Foundations.PureStateMath.Ket]
    have h3 : Matrix.trace (outerProduct (Ket (0 : Fin 2))) = 1 := h₀.2
    rw [h2, h3]
    norm_num
  rw [htr]
  norm_num

/-- The Z-axis positive outcome has probability one sixth on the maximally mixed qubit. -/
theorem prob_mixed_z_plus (h₁ : IsDensityOperator ((1/2:ℂ) • (1 : Operator 2))) :
    (pauliRecordDist ((1/2:ℂ) • (1 : Operator 2)) h₁).prob (2, true) = 1/6 := by
  show instrumentProb pauliShadowRecordInstrument _ (2, true) = 1/6
  rw [(pauli_record_kraus_and_mass.2 _ (2, true)).2]
  have htr : Matrix.trace (PauliProjector 2 true * ((1/2:ℂ) • (1 : Operator 2))) = 1/2 := by
    have h1 : PauliProjector 2 true = (1/2 : ℂ) • (1 + pauliZ) := by
      have h := axis_leaf_operator 2 true
      rw [pauliBasisMatrix_two, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one] at h
      rw [← h]
      exact projector_zero_eq
    rw [h1, Matrix.smul_mul, Matrix.add_mul, Matrix.one_mul,
      Matrix.trace_smul, smul_eq_mul, Matrix.trace_add]
    have h2 : Matrix.trace (pauliZ * ((1/2:ℂ) • (1 : Operator 2))) = 0 := by
      rw [trace_pauliZ_mul]
      simp [Matrix.smul_apply]
    have h3 : Matrix.trace ((1/2:ℂ) • (1 : Operator 2)) = 1 := h₁.2
    rw [h2, h3]
    norm_num [Complex.ofReal_div]
  rw [htr]
  norm_num [Complex.ofReal_div]

/-- For independent Pauli records from the zero-basis and maximally mixed states with respective
weights one third and two thirds, proves that the distributions and weights differ and that
the weighted Z statistic has mean one third and variance `14 / 9`. -/
theorem pauli_non_iid_weighted_consumer
    (h₀ : IsDensityOperator (outerProduct (Ket (0 : Fin 2)))) (h₁ : IsDensityOperator ((1/2:ℂ) • (1:Operator 2))) :
    let p : Fin 2 → FinDist (Fin 3 × Bool) :=
        fun i => if i=0 then pauliRecordDist (outerProduct (Ket (0 : Fin 2))) h₀ else pauliRecordDist ((1/2:ℂ) • (1:Operator 2)) h₁
    let w : Fin 2 → ℝ := fun i => if i=0 then 1/3 else 2/3
    let θ : Fin 3 → ℝ := fun a => if a=2 then 1 else 0
    p 0 ≠ p 1 ∧ w 0 ≠ w 1 ∧
    (independentSampleLaw p).expect (weightedSampleSum w (fun _ => pauliSnapshotValue 0 θ)) = 1/3 ∧
    (independentSampleLaw p).variance (weightedSampleSum w (fun _ => pauliSnapshotValue 0 θ)) = 14/9 := by
  intro p w θ
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    have h2 := congrArg (fun d : FinDist (Fin 3 × Bool) => d.prob (2, true)) h
    change (pauliRecordDist (outerProduct (Ket (0 : Fin 2))) h₀).prob (2, true)
        = (pauliRecordDist ((1/2:ℂ) • (1 : Operator 2)) h₁).prob (2, true) at h2
    rw [prob_pure_z_plus h₀, prob_mixed_z_plus h₁] at h2
    norm_num at h2
  · show (if (0 : Fin 2) = 0 then (1/3 : ℝ) else 2/3) ≠ (if (1 : Fin 2) = 0 then 1/3 else 2/3)
    simp only [if_true, if_neg (by decide : (1 : Fin 2) ≠ 0)]
    norm_num
  · show (independentSampleLaw p).expect (weightedSampleSum w (fun _ => pauliSnapshotValue 0 θ)) = 1/3
    rw [independent_weighted_expectation, Fin.sum_univ_two]
    have hw0 : w 0 = 1/3 := rfl
    have hw1 : w 1 = 2/3 := rfl
    have hp0 : p 0 = pauliRecordDist (outerProduct (Ket (0 : Fin 2))) h₀ := rfl
    have hp1 : p 1 = pauliRecordDist ((1/2:ℂ) • (1 : Operator 2)) h₁ := rfl
    rw [hw0, hw1, hp0, hp1]
    show (1/3) * (pauliRecordDist (outerProduct (Ket (0 : Fin 2))) h₀).expect
          (pauliSnapshotValue 0 thetaZ)
        + (2/3) * (pauliRecordDist ((1/2:ℂ) • (1 : Operator 2)) h₁).expect
          (pauliSnapshotValue 0 thetaZ) = 1/3
    rw [expect_pure_z h₀, expect_mixed_z h₁]
    norm_num
  · show (independentSampleLaw p).variance (weightedSampleSum w (fun _ => pauliSnapshotValue 0 θ)) = 14/9
    rw [independent_weighted_variance, Fin.sum_univ_two]
    have hw0 : w 0 = 1/3 := rfl
    have hw1 : w 1 = 2/3 := rfl
    have hp0 : p 0 = pauliRecordDist (outerProduct (Ket (0 : Fin 2))) h₀ := rfl
    have hp1 : p 1 = pauliRecordDist ((1/2:ℂ) • (1 : Operator 2)) h₁ := rfl
    rw [hw0, hw1, hp0, hp1]
    show ((1/3)^2) * (pauliRecordDist (outerProduct (Ket (0 : Fin 2))) h₀).variance
          (pauliSnapshotValue 0 thetaZ)
        + ((2/3)^2) * (pauliRecordDist ((1/2:ℂ) • (1 : Operator 2)) h₁).variance
          (pauliSnapshotValue 0 thetaZ) = 14/9
    rw [variance_pure_z h₀, variance_mixed_z h₁]
    norm_num

/-- Under the stated block-size variance budget, bounds the physical probability that any of `M`
median-of-means estimates deviates by more than `ε` by `M * 3 ^ (K / 2) / 2 ^ K`. It also
gives the exact fresh-measurement resource counts. -/
theorem pauli_shadow_physical_mom_consumer (ρ : Operator 2) (hρ : IsDensityOperator ρ)
    (L K M : ℕ) (c : Fin M → ℝ) (θ : Fin M → Fin 3 → ℝ) (ε : ℝ)
    (hL : 0 < L) (hK : 0 < K) (hε : 0 < ε)
    (hbud : ∀ j, 12*(∑ a, (θ j a)^2) ≤ (L:ℝ)*ε^2) :
    (∑ ω ∈ Finset.univ.filter (fun ω : Fin K → Fin L → Fin 3 × Bool => ∃ j : Fin M, ε < |(pauliRecordDist ρ hρ).medianOfMeans (pauliSnapshotValue (c j) (θ j)) ω - (Matrix.trace (pauliObservable (c j) (θ j) * ρ)).re|), pauliGroupedBornWeight ρ ω) ≤ (M:ℝ)*3^(K/2)/2^K ∧
    (∀ axes : Fin (K*L) → Fin 3, pauliFreshResourceCounts axes = (K*L,2*(K*L),K*L,0)) := by
  refine ⟨?_, fun axes => pauli_fresh_actual_resources axes⟩
  calc (∑ ω ∈ Finset.univ.filter (fun ω : Fin K → Fin L → Fin 3 × Bool => ∃ j : Fin M,
          ε < |(pauliRecordDist ρ hρ).medianOfMeans (pauliSnapshotValue (c j) (θ j)) ω -
            (Matrix.trace (pauliObservable (c j) (θ j) * ρ)).re|), pauliGroupedBornWeight ρ ω)
      = ∑ ω ∈ Finset.univ.filter (fun ω : Fin K → Fin L → Fin 3 × Bool => ∃ j : Fin M,
          ε < |(pauliRecordDist ρ hρ).medianOfMeans (pauliSnapshotValue (c j) (θ j)) ω -
            (Matrix.trace (pauliObservable (c j) (θ j) * ρ)).re|),
          ∏ k, (pauliRecordDist ρ hρ).probOf (ω k) :=
        Finset.sum_congr rfl fun ω _ => pauliGroupedBornWeight_eq_probOf ρ hρ ω
    _ ≤ (M:ℝ)*3^(K/2)/2^K :=
        pauli_shadow_many_observable_concentration ρ hρ L K M c θ ε hL hK hε hbud

end Qatlib.Concepts.MbqcFlow.FlowDecision
