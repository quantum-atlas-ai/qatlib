/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ClassShadows20.LowerBound.StatisticsDefs
import Qatlib.Concepts.MeasureStats.MedianOfMeans.MedianOfMeansSubgoalHuan
import Qatlib.Concepts.ShadowModels.ShadowVariance.PauliQuadraticVarianceSharpSubgoalHuan
import Qatlib.Concepts.MeasureStats.MedianOfMeans.MedianOfMeansSubgoalStat
import Qatlib.Concepts.ShadowModels.ShadowVariance.PauliQuadraticVarianceSharpSubgoalStat
import Qatlib.Concepts.QuantumGibbs.DetailedBalance.RejectionInstrumentSubgoalQuan
import Qatlib.Concepts.QuantumGibbs.DetailedBalance.RejectionInstrumentSubgoalStat
import Mathlib.NumberTheory.Real.Irrational

/-!
# Finite statistical witnesses

`degree_zero_design_correct` verifies the singleton identity ensemble at degree zero, and
`no_rat_sq_two` records that no rational number has square two. `clause33` combines finite
moment and parameter witnesses with tuple and pilot identities, imported statistical
propositions, and explicit statements separating selected resource counts.

These constructions support the treatment in [HuangKuengPreskill2020].

## Main statements

* `degree_zero_design_correct`: verifies a degree-zero design in every dimension.
* `clause33`: assembles the finite statistical and resource propositions.

## References

* [Huang et al., 2020][HuangKuengPreskill2020]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.ProbabilityCore.Concentration.FiniteDecisionTree
open Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.LinearLearning.ConcisePipeline

open Qatlib.Concepts.MeasureStats.MedianOfMeans
open Qatlib.Concepts.MonteCarloMean.PilotVariance
open Qatlib.Concepts.ShadowModels.ShadowChannel
open Qatlib.Concepts.ShadowModels.ShadowVariance
open Qatlib.Concepts.ShadowModels.UStatBackend
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuantumGibbs.DetailedBalance

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.ClassShadows20.LowerBound

open Qatlib.Concepts.AmplitudeSearch.Amplification
open Qatlib.Concepts.MeasureStats.MedianOfMeans Qatlib.Concepts.QuantumGibbs.DetailedBalance
open scoped Classical ENNReal BigOperators

/-- The singleton identity ensemble is a correct finite design of degree zero in every
dimension. -/
theorem degree_zero_design_correct (d : ℕ) :
    FiniteDesign.Correct (⟨1, fun _ => (1 : Operator d), 0⟩ : FiniteDesign d) := by
  refine ⟨?_, ?_⟩
  · intro i
    exact (Matrix.unitaryGroup (Fin d) ℂ).one_mem
  · refine ⟨by norm_num, by norm_num, ?_⟩
    intro ρ σ _hρ _hσ
    simp [haarOverlapMoment]

/-- No rational number, cast to the reals, has square equal to two. -/
theorem no_rat_sq_two : nativeRationalNotRealRamSqrt := by
  intro q h
  have habs : Real.sqrt ((q : ℝ) ^ 2) = Real.sqrt 2 := by rw [h]
  have hq : |(q : ℝ)| = Real.sqrt 2 := by
    simpa [Real.sqrt_sq_eq_abs] using! habs
  have hcast : ((|q| : ℚ) : ℝ) = Real.sqrt 2 := by
    rw [Rat.cast_abs]
    exact hq
  exact absurd hcast.symm (irrational_sqrt_two.ne_rat (|q| : ℚ))

/-- Collects finite design and qubit moment witnesses, parameter-record witnesses, tuple and
pilot identities, and the sharp Pauli variance, median-of-means, and rejection-instrument
propositions. It also supplies a polynomially bounded resource-record family and proves the
three stated rational and resource-count distinctions. -/
theorem clause33 :

  (∀ d : ℕ, ∃ D : FiniteDesign d, FiniteDesign.Correct D) ∧

  (∃ f : Fin 24 → Operator 2,
    (∀ i, f i ∈ Matrix.unitaryGroup (Fin 2) ℂ) ∧
      (∀ Pp : Operator 2, IsPureDensityOperator Pp → ∀ A : Operator 2,
        (∑ i, (Matrix.trace (A * Matrix.conjTranspose (f i) * Pp * f i)).re) / 24 =
          (Matrix.trace A).re / 2) ∧
      (∀ Pp : Operator 2, IsPureDensityOperator Pp → ∀ A B : Operator 2,
        A.IsHermitian → B.IsHermitian →
        (∑ i, (Matrix.trace (A * Matrix.conjTranspose (f i) * Pp * f i)).re *
            (Matrix.trace (B * Matrix.conjTranspose (f i) * Pp * f i)).re) / 24 =
          ((Matrix.trace A).re * (Matrix.trace B).re +
            (Matrix.trace (A * B)).re) / 6)) ∧

  (∀ d : ℕ, ∃ (p : PackingCertificate d) (w : Theorem5Wrapper d),
    w.pack = p ∧ PackingCertificate.Correct p ∧ Theorem5Wrapper.Correct w) ∧

  (∀ (C : ℝ) (family : ℕ), 0 < C →
    ∃ L : SharpConstantLedger, SharpConstantLedger.Correct L ∧
      L.C = C ∧ L.family = family) ∧

  (Qatlib.Concepts.ShadowModels.ShadowVariance.PauliQuadraticVarianceSharpSubgoal) ∧

  (∀ δ : ℝ, 0 < δ → δ < 1 →
    ∃ b : ShotBudget, b.δ = δ ∧ ShotBudget.Correct b ∧ ShotBudget.LogDeltaOptimal b) ∧

  (∀ (X : Type) [Fintype X] (m r : ℕ), 0 < m → r ≤ m →
    ∃ t : HigherOrderTransport X, t.m = m ∧ t.r = r ∧
      HigherOrderTransport.Correct t) ∧

  (∀ (m r : ℕ), (higherUTuples m r).length = m.descFactorial r) ∧

  (∀ (I : Type) (N h : ℕ), 0 < N → 0 < h →
    ∃ p : PilotBudget I, p.N = N ∧ p.h = h ∧ PilotBudget.Correct p) ∧

  (∀ (I : Type) (N : ℕ) (f : I → ℚ) (omega : Fin N → I),
    pilotMoments N f omega =
      ((∑ i, f (omega i)) / N, (∑ i, (f (omega i)) ^ 2) / N, N)) ∧

  (Qatlib.Concepts.MeasureStats.MedianOfMeans.MedianOfMeansSubgoal) ∧

  (∀ k : ℕ, 0 < k →
    ∃ x : MixedFeedback, x.k = k ∧ MixedFeedback.Correct x) ∧

  (Qatlib.Concepts.QuantumGibbs.DetailedBalance.RejectionInstrumentSubgoal) ∧

  (∃ R : ℕ → StatResources,
    (∀ n : ℕ, (R n).inputLen = n) ∧ StatResources.PolyBounded R) ∧

  (nativeRationalNotRealRamSqrt) ∧

  (macroCountsNotBitComplexity) ∧

  (tableCellsNotPeakSpace) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro d
    exact ⟨⟨1, fun _ => 1, 0⟩, degree_zero_design_correct d⟩
  · exact qubit_conjugation_two_design_exists
  · intro d
    refine ⟨⟨1, 1⟩, ⟨⟨1, 1⟩, 1⟩, rfl, ⟨by norm_num, by norm_num⟩,
        ⟨⟨by norm_num, by norm_num⟩, by norm_num⟩⟩
  · intro C family hC
    exact ⟨⟨C, family⟩, hC, rfl, rfl⟩
  · exact Qatlib.Concepts.ShadowModels.ShadowVariance.pauliQuadraticVarianceSharpSubgoal
  · intro δ hδ hδ1
    refine ⟨⟨δ, max 1 (Nat.ceil (Real.log (1 / δ)))⟩, rfl, ⟨hδ, hδ1, ?_⟩, ?_⟩
    · exact lt_of_lt_of_le (by norm_num) (le_max_left 1 _)
    · show max 1 (Nat.ceil (Real.log (1 / δ))) ≥ Nat.ceil (Real.log (1 / δ))
      exact le_max_right 1 _
  · intro X _inst m r hm hr
    exact ⟨⟨m, r, fun _ => 0⟩, rfl, rfl, hm, hr⟩
  · exact higherUTuples_length
  · intro I N h hN hh
    exact ⟨⟨N, h, fun _ => 0⟩, rfl, rfl, hN, hh⟩
  · intro I N f omega
    exact pilotMoments_eq N f omega
  · exact Qatlib.Concepts.MeasureStats.MedianOfMeans.medianOfMeansSubgoal
  · intro k hk
    exact ⟨⟨k, 1⟩, rfl, hk, by norm_num, by norm_num⟩
  · exact Qatlib.Concepts.QuantumGibbs.DetailedBalance.rejectionInstrumentSubgoal
  · refine ⟨fun n => ⟨n, 0, 0⟩, ?_, 1, 0, ?_⟩
    · intro n
      rfl
    · intro n
      constructor <;> norm_num
  · exact no_rat_sq_two
  · intro macros arith
    exact ⟨macros + arith + 1, by omega, by omega⟩
  · intro cells
    have hr : List.range 1 = [0] := rfl
    refine ⟨1, 1, fun _ => cells + 1, ?_⟩
    have hcalc : peakSpaceOf 1 1 (fun _ => cells + 1) = cells + 1 := by
      simp only [peakSpaceOf, hr, List.foldr_cons, List.foldr_nil, Nat.max_zero, Nat.mul_one]
    rw [hcalc]
    omega

end Qatlib.Papers.ClassShadows20.LowerBound
