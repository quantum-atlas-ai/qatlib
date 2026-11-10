/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SdpDuality.ConeSeparation.MatrixOptimizationDefs
import Qatlib.Concepts.MatrixWeights.WeightsCore
import Mathlib.Tactic.FinCases
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.MatrixWeights.WeightsCore
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false

open Qatlib.Concepts.SdpDuality.ConeSeparation  Matrix
open Qatlib.Concepts.SdpDuality.ConeSeparation
open Qatlib.Concepts.SdpMmwSolver.OracleError
open Qatlib
open scoped Matrix.Norms.L2Operator BigOperators ComplexOrder MatrixOrder

namespace Qatlib.Concepts.SdpDuality.ConeSeparation.MatrixOptimizationRefutations

theorem sdpRoundOracleFailure_refuted :
    ¬ SdpRoundOracleFailure 1 1 (fun _ => (0 : Operator 1)) (0 : Operator 1)
      (fun _ => (1 : ℝ)) (1 : ℝ) (1 : ℝ) (0.1 : ℝ) (0.1 : ℝ)
      (fun _ _ => (0 : ℝ)) 0 := by
  intro h
  have hprem : (∑ i : Fin 1, (0 : ℝ) *
        (Matrix.trace
          ((fun _ => (0 : Operator 1)) i *
            mmwState 1 (sdpDualPayoff 1 1 (fun _ => (0 : Operator 1)) (0 : Operator 1)
              (1 : ℝ) (fun _ _ => (0 : ℝ))) (0.1 : ℝ) 0)).re) ≥
      (Matrix.trace
        ((0 : Operator 1) *
          mmwState 1 (sdpDualPayoff 1 1 (fun _ => (0 : Operator 1)) (0 : Operator 1)
            (1 : ℝ) (fun _ _ => (0 : ℝ))) (0.1 : ℝ) 0)).re -
        3 * (1 : ℝ) * 0.1 := by
    have h0 : ∀ (M : Operator 1), (Matrix.trace ((0 : Operator 1) * M)).re = 0 := by
      intro M
      rw [Matrix.zero_mul, Matrix.trace_zero]
      simp
    simp [mul_zero, Finset.sum_const_zero, h0]
    norm_num
  have hconcl := h (fun _ => (0 : ℝ)) (fun _ => le_rfl) hprem
  simp only [mul_zero, Finset.sum_const_zero] at hconcl
  norm_num at hconcl
open Qatlib.Concepts.RationalScan.Step2Scan Qatlib.Concepts.SdpDuality.ConeSeparation

theorem thresholdGoal_refuted : ¬
    (∀ (D m s : ℕ) (A : Fin m → Operator D) (Cv : Operator D) (b : Fin m → ℝ)
        (y : ℕ → Fin m → ℝ) (j₀ : Fin m) (t : ℕ) (α R δ ε κ ν η ξ : ℝ),
      SdpInstance D m A Cv b j₀ R →
      HasSdpSparseInputs s A Cv →
      0 < δ → δ ≤ 1 → 2 ≤ α → α ≤ R →
      0 < ε → ε ≤ δ / (16 * R) →
      0 < κ → 0 < ν → κ + ν = ε →
      0 < η → η ≤ 1 → 1 < ξ →
      (∀ u < t, certificateObjective m b (y u) ≤ widthSampled α R ε) →
      ∃ (γ Nmax M L : ℕ) (run₀ : Step2Run m γ Nmax M L) (timeout : TimeoutSupport),
        γ = step2Gamma m κ R ∧
        Nmax = step2GridMax α κ ∧
        M = step2SampleM D m R ξ (κ + ν) ∧
        L = step2SampleL D m ξ (κ + ν) ∧
        Step2Run.legal b run₀ α R κ ν s ∧
        Step2LoopLegal D m γ Nmax M A Cv b
          (mmwState D (sdpDualPayoff D m A Cv α y) η t) run₀.loop κ R ν ∧
        run₀.scan.roundVector m κ run₀.loop = y t ∧
        step2GoodFailProb m γ Nmax M b run₀.loop.law run₀.loop.estA κ R ν ≤
          step2GoodFailBound γ Nmax M κ ν R ∧
        TimeoutSupport.legal timeout ∧
        (∀ (run : Step2Run m γ Nmax M L),
          Step2Loop.sameProgram run.loop run₀.loop →
          Step2Run.legal b run α R κ ν s →
          Step2UnifiedGoodEvent A Cv b
              (mmwState D (sdpDualPayoff D m A Cv α y) η t) run.loop κ R ν →
            ((∀ (k : Fin γ) (N : Fin Nmax),
              run.scan = Step2Scan.hit k N →
                (∀ i, 0 ≤ run.scan.roundVector m κ run.loop i) ∧
                (∑ i, b i * run.scan.roundVector m κ run.loop i ≤
                  sdpSampledWidthBudget α R κ ν) ∧
                (sdpSampledSeparationSlack α κ ν +
                    (Matrix.trace
                      (Cv * mmwState D (sdpDualPayoff D m A Cv α y) η t)).re ≤
                  ∑ i, run.scan.roundVector m κ run.loop i *
                    (Matrix.trace
                      (A i * mmwState D (sdpDualPayoff D m A Cv α y) η t)).re)) ∧
              (run.scan = Step2Scan.noOutput →
                SdpRoundOracleFailure D m A Cv b α R ε η y t ∧
                (∃ X : Operator D, LargerWitness D m A Cv b X δ α R)))) ∧
        (step2CeilOverBound α κ →
          (Nmax : ℕ) < step2CeilGridPoint α κ ∧
            (∀ N : Fin Nmax, step2Mass κ N ≤ α)) ∧
        noOutputUnconditionalBoundary) := by
  intro hall
  set A0 : Fin 1 → Operator 1 := fun _ => (1 : Operator 1)
  set Cv0 : Operator 1 := 0
  set b0 : Fin 1 → ℝ := fun _ => 2
  set y0 : ℕ → Fin 1 → ℝ := fun _ _ => 0
  have h := hall 1 1 1 A0 Cv0 b0 y0 0 0 (2 : ℝ) (2 : ℝ) (1 : ℝ)
    ((3 : ℝ) / 100) ((3 : ℝ) / 200) ((3 : ℝ) / 200) ((1 : ℝ) / 2) ((3 : ℝ) / 2)
  have hSdp : SdpInstance 1 1 A0 Cv0 b0 0 (2 : ℝ) := by
    show SdpInstance 1 1 (fun _ => (1 : Operator 1)) (0 : Operator 1)
      (fun _ => (2 : ℝ)) 0 (2 : ℝ)
    refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_, ?_, ?_, rfl, rfl⟩
    · intro i
      show ((1 : Operator 1)).IsHermitian ∧ ‖(1 : Operator 1)‖ ≤ 1
      exact ⟨Matrix.isHermitian_one, norm_one.le⟩
    · show ((0 : Operator 1)).IsHermitian
      exact Matrix.isHermitian_zero
    · show ‖(0 : Operator 1)‖ ≤ 1
      simp
    · intro i
      refine ⟨by norm_num, by norm_num⟩
  have hSparse : HasSdpSparseInputs 1 A0 Cv0 := by
    show HasSdpSparseInputs 1 (fun _ => (1 : Operator 1)) (0 : Operator 1)
    refine ⟨by norm_num, ?_, ?_⟩
    · intro i r
      apply Finset.card_le_one.mpr
      intro a _ b _
      exact (Fin.fin_one_eq_zero a).trans (Fin.fin_one_eq_zero b).symm
    · intro r
      apply Finset.card_le_one.mpr
      intro a _ b _
      exact (Fin.fin_one_eq_zero a).trans (Fin.fin_one_eq_zero b).symm
  have hδ0 : (0:ℝ) < 1 := by norm_num
  have hδ1 : (1:ℝ) ≤ 1 := by norm_num
  have hα : (2:ℝ) ≤ 2 := by norm_num
  have hαR : (2:ℝ) ≤ 2 := by norm_num
  have hε0 : (0:ℝ) < (3:ℝ)/100 := by norm_num
  have hεδ : ((3:ℝ)/100) ≤ (1:ℝ) / (16 * 2) := by norm_num
  have hκ0 : (0:ℝ) < (3:ℝ)/200 := by norm_num
  have hν0 : (0:ℝ) < (3:ℝ)/200 := by norm_num
  have hκν : ((3:ℝ)/200) + (3:ℝ)/200 = (3:ℝ)/100 := by norm_num
  have hη0 : (0:ℝ) < (1:ℝ)/2 := by norm_num
  have hη1 : ((1:ℝ)/2) ≤ 1 := by norm_num
  have hξ : (1:ℝ) < (3:ℝ)/2 := by norm_num
  have hhist : ∀ u < (0:ℕ),
      certificateObjective 1 b0 (y0 u) ≤ widthSampled (2:ℝ) (2:ℝ) ((3:ℝ)/100) := by
    intro u hu
    exact absurd hu (Nat.not_lt_zero u)
  obtain ⟨γ, Nmax, M, L, run₀, timeout, hγ, hNmax, hM, hL, hlegal, hloop, hround,
      hprob, hto, huniv, hceil, hbound⟩ := h hSdp hSparse hδ0 hδ1 hα hαR hε0 hεδ
      hκ0 hν0 hκν hη0 hη1 hξ hhist

  have hγ0 : γ = 0 := by
    rw [hγ]
    show step2Gamma 1 ((3:ℝ)/200) (2:ℝ) = 0
    simp [step2Gamma, Real.log_one]
  subst hγ0

  have hscan : run₀.scan = Step2Scan.noOutput := by
    cases h : run₀.scan with
    | hit k N => exact absurd k.2 (Nat.not_lt_zero _)
    | noOutput => rfl

  have hsame : Step2Loop.sameProgram run₀.loop run₀.loop := ⟨rfl, rfl, rfl⟩
  have hres := huniv run₀ hsame hlegal ⟨hloop, by
    intro k N
    exact absurd k.2 (Nat.not_lt_zero _)⟩

  have hfail := (hres.2 hscan).1

  have hprem : (∑ i : Fin 1, (fun _ => (0:ℝ)) i *
        (Matrix.trace (A0 i * mmwState 1 (sdpDualPayoff 1 1 A0 Cv0 (2:ℝ) y0)
          ((1:ℝ)/2) 0)).re) ≥
      (Matrix.trace (Cv0 * mmwState 1 (sdpDualPayoff 1 1 A0 Cv0 (2:ℝ) y0)
        ((1:ℝ)/2) 0)).re - 3 * (2:ℝ) * ((3:ℝ)/100) := by
    have h0 : ∀ (M : Operator 1), (Matrix.trace (Cv0 * M)).re = 0 := by
      intro M
      show (Matrix.trace ((0 : Operator 1) * M)).re = 0
      rw [Matrix.zero_mul, Matrix.trace_zero]
      simp
    simp [zero_mul, Finset.sum_const_zero, h0]
    norm_num
  have hconcl := hfail (fun _ => (0:ℝ)) (fun _ => le_rfl) hprem
  simp only [zero_mul, Finset.sum_const_zero] at hconcl
  norm_num at hconcl
open Qatlib.Concepts.RationalScan.Step2Scan Qatlib.Concepts.SdpDuality.ConeSeparation
set_option maxHeartbeats 800000
private noncomputable def A0 : Fin 2 → Operator 1 :=
  fun i => if i = 0 then -(1 : Operator 1) else (1 : Operator 1)
private noncomputable def Cv0 : Operator 1 := 0
private def b0 : Fin 2 → ℝ := fun i => if i = 0 then (1:ℝ) else (2:ℝ)
private noncomputable def y0 : ℕ → Fin 2 → ℝ := fun _ _ => (17:ℝ) / 24

private theorem hA0 : A0 0 = -(1 : Operator 1) := if_pos rfl

private theorem hA1 : A0 1 = (1 : Operator 1) := if_neg (by decide)

private theorem hb0 : b0 0 = (1:ℝ) := if_pos rfl

private theorem hb1 : b0 1 = (2:ℝ) := if_neg (by decide)

private theorem hfin2_clause12 : ∀ i : Fin 2, i = 0 ∨ i = 1 := by
  intro i
  fin_cases i <;> simp

theorem clause12_refuted : ¬ (
  ∀ (D m s Q T : ℕ) (A : Fin m → Operator D) (Cv : Operator D) (b : Fin m → ℝ)
      (y : ℕ → Fin m → ℝ) (j₀ : Fin m) (α R δ ε η ξ : ℝ),
    SdpInstance D m A Cv b j₀ R →
    HasSdpSparseInputs s A Cv →
    0 < T → 0 < Q → 2 ≤ α → α ≤ R →
    0 < δ → δ ≤ 1 → 0 < ε → 2 * R * ε ≤ 1 / 2 → 2 * R * ε ≤ δ / 2 →
    0 < η → η ≤ 1 → η + ε ≤ δ / (8 * R) → 1 < ξ →
    (∀ t < T, (∀ i, 0 ≤ y t i) ∧
      certificateObjective m b (y t) ≤ widthSampled α R ε ∧ 0 < ∑ i, y t i) →
    ∃ (q : ℕ → Fin m → ℝ) (idx : ℕ → Fin Q → Fin m) (estA : ℕ → Fin m → ℝ)
        (estC : ℕ → ℝ) (ρt : ℕ → Operator D) (h pe : ℝ)
        (copies meas copiesO oracle : ℝ) (Lsamples : ℕ)
        (fail : RunEventLedger) (budget : ℝ)
        (prog : BackendProgram (Fin m)) (tvErr : ℝ) (cost : IntCost)
        (copyLedger : HistoryCopyLedger),

      (∀ t < T,
        q t = (fun i => y t i / (∑ j, y t j)) ∧
        SparsifySample.independent ⟨q t, idx t⟩ ∧
        SparsifySample.boundedSummands A ⟨q t, idx t⟩ (∑ j, y t j) α ∧
        sparsifyOperatorError A Cv (y t) ⟨q t, idx t⟩ α (∑ j, y t j)
          (sparsifyDeviation (T : ℝ))) ∧

      (∀ t < T,
        IsDensityOperator (ρt t) ∧
        ApproxGibbsError D (ρt t) (mmwState D (sdpDualPayoff D m A Cv α y) η t) ε ∧
        (∀ i, |estA t i - (Matrix.trace (A i * ρt t)).re| ≤ h) ∧
        |estC t - (Matrix.trace (Cv * ρt t)).re| ≤ h) ∧
      ExpectationEstimationBudget D m s h pe copies meas copiesO oracle ∧

      RunEventLedger.legal fail budget ∧
      (∃ sparsFail gibbsFail estFail : ℝ,
        0 ≤ sparsFail ∧ 0 ≤ gibbsFail ∧ 0 ≤ estFail ∧
        sparsFail ≤ (∑ t ∈ Finset.range T,
          matrixHoeffdingTail D Q (sparsifyDeviation (T : ℝ))
            (sparsifySummandBound (∑ i, y t i) α)) ∧
        gibbsFail ≤ (T : ℝ) * sourceFailureTail ξ (D : ℝ) (m : ℝ) ∧
        estFail ≤ (T : ℝ) * 2 * pe ∧
        fail.unionFail ≤ sparsFail + gibbsFail + estFail) ∧

      MixtureSamplingProcess m T (dualCertificate m δ α R j₀ y T)
        (sdpDualSampleDist m δ α R j₀ y T) (mixtureWeights m δ α R j₀ y T)
        (mixtureComponents m j₀ y T) ∧
      BackendProgram.legal prog ∧
      0 < sdpDualSampleScale m δ α R j₀ y T ∧
      0 ≤ tvErr ∧
      lawTV (SamplerTree.law prog.out) (sdpDualSampleDist m δ α R j₀ y T) ≤ tvErr ∧
      ((∑ i, (sdpDualSampleScale m δ α R j₀ y T * prog.out.law i) • A i) - Cv +
        (2 * sdpDualSampleScale m δ α R j₀ y T * tvErr) • (1 : Operator D)).PosSemidef ∧
      (∑ i, (sdpDualSampleScale m δ α R j₀ y T * prog.out.law i) * b i ≤
        (1 + δ) * α + sdpDualSampleScale m δ α R j₀ y T * R * (2 * tvErr)) ∧
      (certificateObjective m b (dualCertificate m δ α R j₀ y T) ≤ (1 + δ) * α) ∧

      HistoryCopyLedger.legal T Q Lsamples copyLedger ∧
      IntCost.le (BackendProgram.cost prog) cost ∧
      ((cost.queries : ℝ) ≤
        ((copyLedger.gibbsCalls + copyLedger.measCopies) * s + copyLedger.sampleDraws)) ∧
      (cost.gates ≤ Nat.ceil copies + Nat.ceil meas + Nat.ceil copiesO + Nat.ceil oracle + 2)

  ) := by
  intro hall
  have hSdp : SdpInstance 1 2 A0 Cv0 b0 1 (2:ℝ) := by
    refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      obtain hi | hi := hfin2_clause12 i
      · subst hi
        rw [hA0]
        exact ⟨Matrix.isHermitian_one.neg, by rw [norm_neg]; exact norm_one.le⟩
      · subst hi
        rw [hA1]
        exact ⟨Matrix.isHermitian_one, norm_one.le⟩
    · show Cv0.IsHermitian
      exact Matrix.isHermitian_zero
    · show ‖(0 : Operator 1)‖ ≤ 1
      simp
    · intro i
      obtain hi | hi := hfin2_clause12 i
      · subst hi; rw [hb0]; norm_num
      · subst hi; rw [hb1]; norm_num
    · show A0 1 = 1
      exact hA1
    · show b0 1 = 2
      exact hb1
  have hSparse : HasSdpSparseInputs 1 A0 Cv0 := by
    refine ⟨by norm_num, ?_, ?_⟩
    · intro i r
      apply Finset.card_le_one.mpr
      intro a _ b _
      exact (Fin.fin_one_eq_zero a).trans (Fin.fin_one_eq_zero b).symm
    · intro r
      apply Finset.card_le_one.mpr
      intro a _ b _
      exact (Fin.fin_one_eq_zero a).trans (Fin.fin_one_eq_zero b).symm
  have hT : (0:ℕ) < 2 := by norm_num
  have hQ : (0:ℕ) < 1 := by norm_num
  have hα : (2:ℝ) ≤ 2 := by norm_num
  have hαR : (2:ℝ) ≤ 2 := by norm_num
  have hδ0 : (0:ℝ) < 1 := by norm_num
  have hδ1 : (1:ℝ) ≤ 1 := by norm_num
  have hε0 : (0:ℝ) < (1:ℝ)/64 := by norm_num
  have hε1 : 2 * (2:ℝ) * ((1:ℝ)/64) ≤ 1 / 2 := by norm_num
  have hε2 : 2 * (2:ℝ) * ((1:ℝ)/64) ≤ 1 / 2 := by norm_num
  have hη0 : (0:ℝ) < (1:ℝ)/64 := by norm_num
  have hη1 : ((1:ℝ)/64) ≤ 1 := by norm_num
  have hηε : ((1:ℝ)/64) + (1:ℝ)/64 ≤ 1 / (8 * (2:ℝ)) := by norm_num
  have hξ : (1:ℝ) < 2 := by norm_num
  have hhist : ∀ t < (2:ℕ), (∀ i, 0 ≤ y0 t i) ∧
      certificateObjective 2 b0 (y0 t) ≤ widthSampled (2:ℝ) (2:ℝ) ((1:ℝ)/64) ∧
      0 < ∑ i, y0 t i := by
    intro t ht
    refine ⟨?_, ?_, ?_⟩
    · intro i
      show (0:ℝ) ≤ (17:ℝ)/24
      norm_num
    · show (∑ i : Fin 2, ((17:ℝ)/24) * b0 i) ≤ widthSampled (2:ℝ) (2:ℝ) ((1:ℝ)/64)
      rw [Fin.sum_univ_two, hb0, hb1]
      norm_num [widthSampled]
    · show 0 < ∑ i : Fin 2, ((17:ℝ)/24)
      norm_num
  obtain ⟨q, idx, estA, estC, ρt, h, pe, copies, meas, copiesO, oracle, Lsamples,
      fail, budget, prog, tvErr, cost, copyLedger, hspars, _⟩ :=
    hall 1 2 1 1 2 A0 Cv0 b0 y0 1 (2:ℝ) (2:ℝ) (1:ℝ) ((1:ℝ)/64) ((1:ℝ)/64) (2:ℝ)
      hSdp hSparse hT hQ hα hαR hδ0 hδ1 hε0 hε1 hε2 hη0 hη1 hηε hξ hhist
  have h4 := (hspars 0 (by norm_num)).2.2.2
  change ‖sdpScaledSparsifiedPayoff 1 2 1 A0 Cv0 2 (∑ j, y0 0 j) (idx 0) -
      sourceScaledPayoff A0 Cv0 2 (y0 0)‖ ≤ sparsifyDeviation ((2:ℕ):ℝ) at h4
  have hy0 : (∑ j : Fin 2, y0 0 j) = ((17:ℝ)/12) := by
    show (∑ j : Fin 2, ((17:ℝ)/24)) = ((17:ℝ)/12)
    norm_num
  rw [hy0] at h4
  have hsumA : (∑ i : Fin 2, y0 0 i • A0 i) = 0 := by
    show (∑ i : Fin 2, ((17:ℝ)/24) • A0 i) = 0
    rw [Fin.sum_univ_two, hA0, hA1, smul_neg, neg_add_cancel]
  have hd : sdpScaledSparsifiedPayoff 1 2 1 A0 Cv0 2 ((17:ℝ)/12) (idx 0) -
      sourceScaledPayoff A0 Cv0 2 (y0 0) =
      (4 * (2:ℝ))⁻¹ • (((17:ℝ)/12) • (((1:ℝ):ℝ)⁻¹ • (∑ j : Fin 1, A0 (idx 0 j))) -
        (∑ i : Fin 2, y0 0 i • A0 i)) := by
    unfold sdpScaledSparsifiedPayoff sourceScaledPayoff
    module
  obtain hidx | hidx := hfin2_clause12 (idx 0 0)
  · have hnorm : ‖sdpScaledSparsifiedPayoff 1 2 1 A0 Cv0 2 ((17:ℝ)/12) (idx 0) -
        sourceScaledPayoff A0 Cv0 2 (y0 0)‖ = ((17:ℝ)/96) := by
      rw [hd, hsumA, sub_zero, Fin.sum_univ_one, inv_one, one_smul, hidx, hA0, smul_neg,
        norm_smul, norm_neg, norm_smul, norm_one, mul_one, Real.norm_eq_abs, Real.norm_eq_abs]
      norm_num
    rw [hnorm] at h4
    norm_num [sparsifyDeviation] at h4
  · have hnorm : ‖sdpScaledSparsifiedPayoff 1 2 1 A0 Cv0 2 ((17:ℝ)/12) (idx 0) -
        sourceScaledPayoff A0 Cv0 2 (y0 0)‖ = ((17:ℝ)/96) := by
      rw [hd, hsumA, sub_zero, Fin.sum_univ_one, inv_one, one_smul, hidx, hA1,
        norm_smul, norm_smul, norm_one, mul_one, Real.norm_eq_abs, Real.norm_eq_abs]
      norm_num
    rw [hnorm] at h4
    norm_num [sparsifyDeviation] at h4
end Qatlib.Concepts.SdpDuality.ConeSeparation.MatrixOptimizationRefutations
