/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
import Qatlib.Concepts.AdversaryBounds.AdvDuality.UnboundedExecutionRemainderDefs
import Qatlib.Concepts.AdversaryBounds.AdvDuality.ExecutionRemainder
import Mathlib.Topology.Order.MonotoneConvergence
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.FairRandomBits.RationalReject
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
open Qatlib.Concepts.ClassicalTape.FairCoinTape
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Concepts.AdversaryBounds.AdvDuality.CappedFeedback
open Qatlib.Concepts.AdversaryBounds.AdvDuality.CoinCode
open Qatlib.Concepts.AdversaryBounds.AdvDuality.FairFeedback
open Qatlib.Concepts.AdversaryBounds.AdvDuality.HybridCounts
open Qatlib.Concepts.AdversaryBounds.AdvDuality.HybridLeaf
open Qatlib.Concepts.AdversaryBounds.AdvDuality.HybridProgram
open Qatlib.Concepts.AdversaryBounds.AdvDuality.HybridProgram.Path
open Qatlib.Concepts.AdversaryBounds.AdvDuality.NativeTape
open Qatlib.Concepts.ShadowModels.ShadowChannel

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality
open scoped ENNReal
namespace CappedFeedback
open Classical
variable {D N : ℕ}

theorem compile_legal (M : CappedFeedback D N) (cap : ℕ) (hM : M.Legal) :
    (M.compile cap).Legal := hM

theorem timeout (M : CappedFeedback D N) (cap : ℕ) (O : Operator D)
    (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ) (hM : M.Legal) (ρ : Operator D)
    (hb : ∀ i, weightTotal (M.weights i) ≤ 2 ^ M.width i) :
    (∑ z : (M.compile cap).Outcome, instrumentProb (M.instrument cap O hO hM) ρ z *
      (if rejectionOutcome (((M.compile cap).record O z).value.1) = .inr () then 1 else 0)) =
    ∑ i : Fin (observedLeafCount M.first),
      instrumentProb (observedInstrument O hO M.first hM.1) ρ i *
        (rationalRejectMass (M.weights i) (M.width i) ^ cap).toReal := by
  change (∑ z : (M.compile cap).Outcome,
    instrumentProb ((M.compile cap).instrument O hO (M.compile_legal cap hM)) ρ z *
      (if rejectionOutcome (((M.compile cap).path z.1 z.2.1).1.1) = .inr () then 1 else 0)) = _
  have he := (M.compile cap).classical_event O hO (M.compile_legal cap hM) ρ
    (fun _ x => rejectionOutcome x.1.1 = .inr ())
  dsimp only at he
  convert! he using 1
  · apply Finset.sum_congr rfl
    intro z _
    by_cases hz : rejectionOutcome (((M.compile cap).path z.1 z.2.1).1.1) = Sum.inr ()
    <;> simp only [hz, ↓reduceIte]
  · apply Finset.sum_congr rfl
    intro i _
    rw [show (M.compile cap).choose i = weightedSampler (M.weights i) (M.width i) cap from rfl,
      weightedSampler_timeout _ _ _ (hb i)]
    rfl

theorem return_mass (M : CappedFeedback D N) (cap : ℕ) (O : Operator D)
    (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ) (hM : M.Legal) (ρ : Operator D)
    (hW : ∀ i, 0 < weightTotal (M.weights i))
    (hb : ∀ i, weightTotal (M.weights i) ≤ 2 ^ M.width i) (j : Fin N) :
    (∑ z : (M.compile cap).Outcome, instrumentProb (M.instrument cap O hO hM) ρ z *
      (if rejectionOutcome (((M.compile cap).record O z).value.1) = .inl j then 1 else 0)) =
    ∑ i : Fin (observedLeafCount M.first),
      instrumentProb (observedInstrument O hO M.first hM.1) ρ i *
        ((M.weights i j : ℝ≥0∞) / (weightTotal (M.weights i) : ℝ≥0∞) *
          (1 - rationalRejectMass (M.weights i) (M.width i) ^ cap)).toReal := by
  change (∑ z : (M.compile cap).Outcome,
    instrumentProb ((M.compile cap).instrument O hO (M.compile_legal cap hM)) ρ z *
      (if rejectionOutcome (((M.compile cap).path z.1 z.2.1).1.1) = .inl j then 1 else 0)) = _
  have he := (M.compile cap).classical_event O hO (M.compile_legal cap hM) ρ
    (fun _ x => rejectionOutcome x.1.1 = .inl j)
  dsimp only at he
  convert! he using 1
  · apply Finset.sum_congr rfl
    intro z _
    by_cases hz : rejectionOutcome (((M.compile cap).path z.1 z.2.1).1.1) = Sum.inl j
    <;> simp only [hz, ↓reduceIte]
  · apply Finset.sum_congr rfl
    intro i _
    rw [show (M.compile cap).choose i = weightedSampler (M.weights i) (M.width i) cap from rfl,
      weightedSampler_return _ _ _ (hW i) (hb i)]
    rfl

theorem expected_reads (M : CappedFeedback D N) (cap : ℕ) (O : Operator D)
    (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ) (hM : M.Legal) (ρ : Operator D)
    (hW : ∀ i, 0 < weightTotal (M.weights i))
    (hb : ∀ i, weightTotal (M.weights i) ≤ 2 ^ M.width i) :
    (∑ z : (M.compile cap).Outcome, instrumentProb (M.instrument cap O hO hM) ρ z *
      (((M.compile cap).record O z).coinWord.length : ℝ)) =
    ∑ i : Fin (observedLeafCount M.first),
      instrumentProb (observedInstrument O hO M.first hM.1) ρ i *
        ((M.width i : ℝ≥0∞) * ∑ t ∈ Finset.range cap,
          rationalRejectMass (M.weights i) (M.width i) ^ t).toReal := by
  change (∑ z : (M.compile cap).Outcome,
    instrumentProb ((M.compile cap).instrument O hO (M.compile_legal cap hM)) ρ z *
      (((M.compile cap).codeWord z).length : ℝ)) = _
  have he := (M.compile cap).classical_expectation_toReal O hO (M.compile_legal cap hM) ρ
    (fun _ x => (x.2 : ℝ)) (by intros; exact Nat.cast_nonneg _)
  dsimp only at he
  rw [he]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  simp only [ENNReal.ofReal_natCast]
  change (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost (weightedSampler (M.weights i) (M.width i) cap).law).toReal = _
  rw [(weightedSampler_expectations _ _ _ (hW i) (hb i)).1]

theorem path_read_bound (M : CappedFeedback D N) (cap : ℕ)
    (z : (M.compile cap).Outcome) :
    ((M.compile cap).codeWord z).length ≤ M.width z.1 * cap := by
  let p := (M.compile cap).choose z.1
  let x := p.paths.get z.2.1
  have hr : p.run x.2 = (.ret x.1, x.2.length) :=
    CoinCode.paths_run p x (List.get_mem _ _)
  have hh : (p.run x.2).2 = x.2.length := congrArg Prod.snd hr
  calc
    ((M.compile cap).codeWord z).length = (p.run x.2).2 := hh.symm
    _ ≤ p.depth := CoinCode.run_reads_le_depth _ _
    _ ≤ M.width z.1 * cap := weightedSampler_depth_le _ _ _

open scoped ComplexOrder

theorem expectedReadCost_eq (M : CappedFeedback D N) (cap : ℕ) (O : Operator D)
    (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ) (hM : M.Legal) (ρ : Operator D)
    (hρ : ρ.PosSemidef) (hW : ∀ i, 0 < weightTotal (M.weights i))
    (hb : ∀ i, weightTotal (M.weights i) ≤ 2 ^ M.width i) :
    M.expectedReadCost cap O hO hM ρ =
    ∑ i : Fin (observedLeafCount M.first),
      ENNReal.ofReal (instrumentProb (observedInstrument O hO M.first hM.1) ρ i) *
        ((M.width i : ℝ≥0∞) * ∑ t ∈ Finset.range cap,
          rationalRejectMass (M.weights i) (M.width i) ^ t) := by
  unfold expectedReadCost
  change ENNReal.ofReal (∑ z : (M.compile cap).Outcome,
    instrumentProb ((M.compile cap).instrument O hO (M.compile_legal cap hM)) ρ z *
      (((M.compile cap).codeWord z).length : ℝ)) = _
  have he := (M.compile cap).classical_expectation_ofReal O hO (M.compile_legal cap hM) ρ hρ
    (fun _ x => (x.2 : ℝ)) (by intros; exact Nat.cast_nonneg _)
  dsimp only at he
  rw [he]
  apply Finset.sum_congr rfl
  intro i _
  simp only [ENNReal.ofReal_natCast]
  change _ * Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost
      (weightedSampler (M.weights i) (M.width i) cap).law = _
  rw [(weightedSampler_expectations _ _ _ (hW i) (hb i)).1]
  rfl

theorem timeout_tendsto_zero (M : CappedFeedback D N) (O : Operator D)
    (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ) (hM : M.Legal) (ρ : Operator D)
    (hW : ∀ i, 0 < weightTotal (M.weights i))
    (hb : ∀ i, weightTotal (M.weights i) ≤ 2 ^ M.width i) :
    Filter.Tendsto (fun cap => M.timeoutMass cap O hO hM ρ) Filter.atTop (nhds 0) := by
  have hi (i : Fin (observedLeafCount M.first)) :
      Filter.Tendsto (fun cap => (rationalRejectMass (M.weights i) (M.width i) ^ cap).toReal)
        Filter.atTop (nhds (0 : ℝ)) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
      (weightedSampler_timeout_tendsto_zero (M.weights i) (M.width i) (hW i) (hb i))
    simpa only [weightedSampler_timeout _ _ _ (hb i), ENNReal.toReal_zero] using! h
  have hzero : Filter.Tendsto
      (fun cap => ∑ i : Fin (observedLeafCount M.first),
        instrumentProb (observedInstrument O hO M.first hM.1) ρ i *
          (rationalRejectMass (M.weights i) (M.width i) ^ cap).toReal)
      Filter.atTop (nhds (0 : ℝ)) := by
    convert! tendsto_finsetSum Finset.univ (fun i _ =>
      (tendsto_const_nhds (x := instrumentProb (observedInstrument O hO M.first hM.1) ρ i)).mul
        (hi i)) using 1
    simp
  have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hzero
  simpa only [timeoutMass, M.timeout _ O hO hM ρ hb, ENNReal.ofReal_zero] using! h

theorem neverMass_eq_zero (M : CappedFeedback D N) (O : Operator D)
    (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ) (hM : M.Legal) (ρ : Operator D)
    (hW : ∀ i, 0 < weightTotal (M.weights i))
    (hb : ∀ i, weightTotal (M.weights i) ≤ 2 ^ M.width i) :
    M.neverMass O hO hM ρ = 0 := by
  apply le_antisymm ?_ bot_le
  exact ge_of_tendsto (M.timeout_tendsto_zero O hO hM ρ hW hb)
    (Filter.Eventually.of_forall fun cap => iInf_le _ cap)

theorem expectedReadCost_limit (M : CappedFeedback D N) (O : Operator D)
    (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ) (hM : M.Legal) (ρ : Operator D)
    (hρ : ρ.PosSemidef) (hW : ∀ i, 0 < weightTotal (M.weights i))
    (hb : ∀ i, weightTotal (M.weights i) ≤ 2 ^ M.width i) :
    Filter.Tendsto (fun cap => M.expectedReadCost cap O hO hM ρ) Filter.atTop
      (nhds (M.limitingReadCost O hO hM ρ)) ∧ M.limitingReadCost O hO hM ρ < ⊤ := by
  have hi (i : Fin (observedLeafCount M.first)) :=
    weightedSampler_expected_reads_limit (M.weights i) (M.width i) (hW i) (hb i)
  constructor
  · have ht := tendsto_finsetSum Finset.univ (fun i _ =>
      ENNReal.Tendsto.const_mul (a := ENNReal.ofReal
        (instrumentProb (observedInstrument O hO M.first hM.1) ρ i)) (hi i).1
          (Or.inr ENNReal.ofReal_ne_top))
    convert! ht using 1
    funext cap
    rw [M.expectedReadCost_eq cap O hO hM ρ hρ hW hb]
    apply Finset.sum_congr rfl
    intro i _
    rw [(weightedSampler_expectations _ _ _ (hW i) (hb i)).1]
  · unfold limitingReadCost
    exact ENNReal.sum_lt_top.mpr (fun i _ => ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hi i).2)

theorem expectedReadCost_mono (M : CappedFeedback D N) (O : Operator D)
    (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ) (hM : M.Legal) (ρ : Operator D)
    (hρ : ρ.PosSemidef) (hW : ∀ i, 0 < weightTotal (M.weights i))
    (hb : ∀ i, weightTotal (M.weights i) ≤ 2 ^ M.width i) :
    Monotone (fun cap => M.expectedReadCost cap O hO hM ρ) := by
  intro a b hab
  (try dsimp only)
  rw [M.expectedReadCost_eq a O hO hM ρ hρ hW hb,
    M.expectedReadCost_eq b O hO hM ρ hρ hW hb]
  apply Finset.sum_le_sum
  intro i _
  gcongr

theorem expectedReadCost_iSup (M : CappedFeedback D N) (O : Operator D)
    (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ) (hM : M.Legal) (ρ : Operator D)
    (hρ : ρ.PosSemidef) (hW : ∀ i, 0 < weightTotal (M.weights i))
    (hb : ∀ i, weightTotal (M.weights i) ≤ 2 ^ M.width i) :
    (⨆ cap, M.expectedReadCost cap O hO hM ρ) = M.limitingReadCost O hO hM ρ := by
  exact tendsto_nhds_unique
    (tendsto_atTop_iSup (M.expectedReadCost_mono O hO hM ρ hρ hW hb))
    (M.expectedReadCost_limit O hO hM ρ hρ hW hb).1

end CappedFeedback

theorem rejectingFeedback_legal : rejectingFeedback.Legal := by
  constructor
  · exact measuredFeedback_legal.1
  · intro i a
    rcases a with ⟨a,t⟩
    cases a with
    | inr s => trivial
    | inl x => exact measuredFeedback_legal.2 i (some x.1, 0)

theorem rejectingFeedback_weights_positive :
    ∀ i, 0 < weightTotal (rejectingFeedback.weights i) := by
  intro i
  change Fin 2 at i
  fin_cases i <;> decide +kernel

theorem rejectingFeedback_capacity :
    ∀ i, weightTotal (rejectingFeedback.weights i) ≤ 2 ^ rejectingFeedback.width i := by
  intro i
  change Fin 2 at i
  fin_cases i <;> decide +kernel

theorem rejectingFeedback_rejectMass (i : Fin 2) :
    rationalRejectMass (rejectingFeedback.weights i) (rejectingFeedback.width i) =
      if i = 0 then 0 else 1 / 4 := by
  change rationalRejectMass
    (fun j : Fin 2 => if i.val = 0 then (if j = 0 then 1 else 0) else (if j = 0 then 1 else 2))
    (if i.val = 0 then 0 else 2) = _
  fin_cases i <;> norm_num [rationalRejectMass, coinRejectMass, weightTotal, Fin.sum_univ_two]

noncomputable def rejectingInstrument (cap : ℕ) := rejectingFeedback.instrument cap
  measuredFeedbackFlip measuredFeedbackFlip_unitary rejectingFeedback_legal

theorem rejectingFeedback_timeout (cap : ℕ) :
    rejectingFeedback.timeoutMass (cap + 1) measuredFeedbackFlip measuredFeedbackFlip_unitary
      rejectingFeedback_legal measuredFeedbackInput = (1 / 2 : ℝ≥0∞) * (1 / 4 : ℝ≥0∞) ^ (cap + 1) := by
  unfold CappedFeedback.timeoutMass
  rw [CappedFeedback.timeout _ _ _ _ _ _ rejectingFeedback_capacity]
  change ENNReal.ofReal (∑ i : Fin 2,
    instrumentProb (observedInstrument measuredFeedbackFlip measuredFeedbackFlip_unitary
      measuredFeedbackFirst rejectingFeedback_legal.1) measuredFeedbackInput i *
      (rationalRejectMass (rejectingFeedback.weights i) (rejectingFeedback.width i) ^ (cap + 1)).toReal) = _
  simp only [measuredFeedback_first_probability _ measuredFeedbackFlip_unitary,
    rejectingFeedback_rejectMass, Fin.sum_univ_two]
  norm_num [ENNReal.ofReal_div_of_pos]

theorem rejectingFeedback_limitingReadCost :
    rejectingFeedback.limitingReadCost measuredFeedbackFlip measuredFeedbackFlip_unitary
      rejectingFeedback_legal measuredFeedbackInput = 4 / 3 := by
  unfold CappedFeedback.limitingReadCost
  change (∑ i : Fin 2, ENNReal.ofReal
    (instrumentProb (observedInstrument measuredFeedbackFlip measuredFeedbackFlip_unitary
      measuredFeedbackFirst rejectingFeedback_legal.1) measuredFeedbackInput i) *
      ((rejectingFeedback.width i : ℝ≥0∞) / (1 - rationalRejectMass
        (rejectingFeedback.weights i) (rejectingFeedback.width i)))) = _
  simp only [measuredFeedback_first_probability _ measuredFeedbackFlip_unitary,
    rejectingFeedback_rejectMass, Fin.sum_univ_two]
  have hw0 : rejectingFeedback.width (0 : Fin 2) = 0 := rfl
  have hw1 : rejectingFeedback.width (1 : Fin 2) = 2 := rfl
  rw [hw0, hw1]
  norm_num [ENNReal.ofReal_div_of_pos]
  have hs : (1 : ℝ≥0∞) - (4 : ℝ≥0∞)⁻¹ = 3 / 4 := by
    calc
      _ = ENNReal.ofReal 1 - ENNReal.ofReal (1 / 4) := by
        norm_num [ENNReal.ofReal_div_of_pos]
      _ = ENNReal.ofReal (1 - 1 / 4) :=
        (ENNReal.ofReal_sub 1 (by norm_num : (0 : ℝ) ≤ 1 / 4)).symm
      _ = _ := by norm_num [ENNReal.ofReal_div_of_pos]

  rw [hs, div_eq_mul_inv,
    ENNReal.inv_div (Or.inl (by norm_num)) (Or.inl (by norm_num)),
    ← mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]

theorem rejectingFeedback_never_zero :
    rejectingFeedback.neverMass measuredFeedbackFlip measuredFeedbackFlip_unitary
      rejectingFeedback_legal measuredFeedbackInput = 0 :=
  rejectingFeedback.neverMass_eq_zero _ _ _ _
    rejectingFeedback_weights_positive rejectingFeedback_capacity

theorem rejectingFeedback_expectedReadCost_iSup :
    (⨆ cap, rejectingFeedback.expectedReadCost cap measuredFeedbackFlip measuredFeedbackFlip_unitary
      rejectingFeedback_legal measuredFeedbackInput) = 4 / 3 := by
  rw [CappedFeedback.expectedReadCost_iSup _ _ _ _ _ measuredFeedbackInput_density.1.1
    rejectingFeedback_weights_positive rejectingFeedback_capacity, rejectingFeedback_limitingReadCost]

theorem rejectingPending_record :
    (rejectingFeedback.compile 1).record measuredFeedbackFlip rejectingPending =
      ⟨(.inr (2, 2), 1), true, false, [true, true], 0, 0, 1, [(2, 1)], []⟩ := rfl

theorem rejectingRecovered_record :
    (rejectingFeedback.compile 2).record measuredFeedbackFlip rejectingRecovered =
      ⟨(.inl (0, 4, 3), 2), true, true, [true, true, false, false], 0, 1, 1, [(2, 1)], []⟩ := rfl

open scoped ComplexOrder

theorem rejectingPending_state :
    (rejectingInstrument 1).branch rejectingPending measuredFeedbackInput =
      ((1 / 8 : ℝ) : ℂ) • Projector (Finset.univ.filter fun i : Fin 2 => i = 1) := by
  have hp : ((rejectingFeedback.compile 1).prefixLeaf measuredFeedbackFlip rejectingPending.1).operator =
      Projector (Finset.univ.filter fun i : Fin 2 => i = 1) :=
    measuredFeedback_first_operator measuredFeedbackFlip (1 : Fin 2)
  have hs :
      ((rejectingFeedback.compile 1).suffixLeaf measuredFeedbackFlip rejectingPending).operator = 1 := rfl
  rw [rejectingInstrument, CappedFeedback.instrument, FairFeedback.branch_law, hs, hp]
  have hw : CoinCode.wordWeight ((rejectingFeedback.compile 1).codeWord rejectingPending) = 1 / 4 := by
    change (1 / 2 : ℝ) ^ 2 = 1 / 4
    norm_num
  rw [hw]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [conjBranch_apply, Matrix.mul_apply,
    Fin.sum_univ_two, Matrix.conjTranspose_apply, measuredFeedbackInput, Projector,
    Matrix.smul_apply, Matrix.one_apply]

theorem rejectingRecovered_coherence :
    ((rejectingInstrument 2).branch rejectingRecovered measuredFeedbackInput) 0 1 = -1 / 64 := by
  have hp : ((rejectingFeedback.compile 2).prefixLeaf measuredFeedbackFlip rejectingRecovered.1).operator =
      Projector (Finset.univ.filter fun i : Fin 2 => i = 1) :=
    measuredFeedback_first_operator measuredFeedbackFlip (1 : Fin 2)
  have hs : ((rejectingFeedback.compile 2).suffixLeaf measuredFeedbackFlip rejectingRecovered).operator =
      Qatlib.Concepts.GateVocabulary.GateVocab.hadamardFin := by
    change (1 : Operator 2) * Qatlib.Concepts.GateVocabulary.GateVocab.hadamardFin = _
    exact one_mul _
  rw [rejectingInstrument, CappedFeedback.instrument, FairFeedback.branch_law, hs, hp]
  have hw : CoinCode.wordWeight ((rejectingFeedback.compile 2).codeWord rejectingRecovered) = 1 / 16 := by
    change (1 / 2 : ℝ) ^ 4 = 1 / 16
    norm_num
  rw [hw]
  change ((((1 / 16 : ℝ) : ℂ)) • conjBranch Qatlib.Concepts.GateVocabulary.GateVocab.hadamardFin
    (conjBranch (Projector (Finset.univ.filter fun i : Fin 2 => i = 1)) measuredFeedbackInput)) 0 1 = _
  norm_num [conjBranch_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
    measuredFeedbackHadamard_apply, measuredFeedbackInput, Projector, Matrix.smul_apply, Matrix.one_apply]
  ring_nf
  rw [inv_pow, sqrt2_sq]
  norm_num

namespace NativeTape

variable {Γ Λ : Type} [Inhabited Γ]

theorem run_path [Inhabited Λ] (M : Program Γ Λ) (n : ℕ) (bs : List Bool) (cfg : Turing.TM0.Cfg Γ Λ) :
    Path M cfg (run M n bs cfg).trace (run M n bs cfg).cfg := by
  induction n generalizing bs cfg with
  | zero => cases h : M cfg.q cfg.Tape.head <;> simp only [run, h] <;> exact .nil cfg
  | succ n ih =>
    cases h : M cfg.q cfg.Tape.head with
    | halt => simp only [run, h]; exact .nil cfg
    | det q s =>
      simp only [run, h, Result.prepend]
      apply Path.cons _ (ih bs (advance cfg (q,s)))
      constructor
      · simp [h]
      · rw [TM0_step_apply]; simp [table, h, advance]
    | coin k =>
      cases bs with
      | nil => simp only [run, h]; exact .nil cfg
      | cons b bs =>
        simp only [run, h, Result.prepend]
        apply Path.cons _ (ih bs (advance cfg (k b)))
        constructor
        · simp [h]
        · rw [TM0_step_apply]; simp [table, h, advance]

theorem run_account (M : Program Γ Λ) (n : ℕ) (bs : List Bool) (cfg : Turing.TM0.Cfg Γ Λ) :
    bs = (run M n bs cfg).bits ++ (run M n bs cfg).unread := by
  induction n generalizing bs cfg with
  | zero => cases h : M cfg.q cfg.Tape.head <;> simp [run, h, Result.bits]
  | succ n ih =>
    cases h : M cfg.q cfg.Tape.head with
    | halt => simp [run, h, Result.bits]
    | det q s => simpa [run, h, Result.bits, Result.prepend] using! ih bs (advance cfg (q,s))
    | coin k => cases bs with
      | nil => simp [run, h, Result.bits]
      | cons b bs => simpa [run, h, Result.bits, Result.prepend] using! congrArg (List.cons b) (ih bs (advance cfg (k b)))

theorem run_steps_le (M : Program Γ Λ) (n : ℕ) (bs : List Bool) (cfg : Turing.TM0.Cfg Γ Λ) :
    (run M n bs cfg).steps ≤ n := by
  induction n generalizing bs cfg with
  | zero => cases h : M cfg.q cfg.Tape.head <;> simp [run, h, Result.steps]
  | succ n ih =>
    cases h : M cfg.q cfg.Tape.head with
    | halt => simp [run, h, Result.steps]
    | det q s => simpa [run, h, Result.steps, Result.prepend] using! Nat.succ_le_succ (ih bs (advance cfg (q,s)))
    | coin k => cases bs with
      | nil => simp [run, h, Result.steps]
      | cons b bs => simpa [run, h, Result.steps, Result.prepend] using! Nat.succ_le_succ (ih bs (advance cfg (k b)))

theorem run_fuel_steps (M : Program Γ Λ) (n : ℕ) (bs : List Bool) (cfg : Turing.TM0.Cfg Γ Λ)
    (h : (run M n bs cfg).stop = .fuel) : (run M n bs cfg).steps = n := by
  induction n generalizing bs cfg with
  | zero => cases hc : M cfg.q cfg.Tape.head <;> simp_all [run, Result.steps]
  | succ n ih =>
    cases hc : M cfg.q cfg.Tape.head with
    | halt => simp [run, hc] at h
    | det q s => simpa [run, hc, Result.steps, Result.prepend] using! congrArg Nat.succ (ih bs (advance cfg (q,s)) (by simpa [run, hc, Result.prepend] using! h))
    | coin k => cases bs with
      | nil => simp [run, hc] at h
      | cons b bs => simpa [run, hc, Result.steps, Result.prepend] using! congrArg Nat.succ (ih bs (advance cfg (k b)) (by simpa [run, hc, Result.prepend] using! h))

theorem resume_prepend (M : Program Γ Λ) (n : ℕ) (r : Result Γ Λ) (e : Tick Γ Λ) :
    resume M n (r.prepend e) = (resume M n r).prepend e := by
  by_cases h : r.stop = .fuel <;> simp [resume, Result.prepend, h]

theorem run_add (M : Program Γ Λ) (n m : ℕ) (bs : List Bool) (cfg : Turing.TM0.Cfg Γ Λ) :
    run M (n+m) bs cfg = resume M m (run M n bs cfg) := by
  induction n generalizing bs cfg with
  | zero => cases h : M cfg.q cfg.Tape.head <;> cases m <;> simp [run, h, resume]
  | succ n ih =>
    rw [Nat.succ_add]
    cases h : M cfg.q cfg.Tape.head with
    | halt => simp [run, h, resume]
    | det q s => simp only [run, h, resume_prepend]; rw [ih]
    | coin k => cases bs with
      | nil => simp [run, h, resume]
      | cons b bs => simp only [run, h, resume_prepend]; rw [ih]

theorem run_halted [Inhabited Λ] (M : Program Γ Λ) (n : ℕ) (bs : List Bool) (cfg : Turing.TM0.Cfg Γ Λ)
    (h : (run M n bs cfg).stop = .halted) :
    Turing.TM0.step (table M false) (run M n bs cfg).cfg = none := by
  suffices hm : M (run M n bs cfg).cfg.q (run M n bs cfg).cfg.Tape.head = .halt by
    rw [TM0_step_eq_none]; simp [table, hm]
  induction n generalizing bs cfg with
  | zero => cases hc : M cfg.q cfg.Tape.head <;> simp_all [run]
  | succ n ih =>
    cases hc : M cfg.q cfg.Tape.head with
    | halt => simp [run, hc]
    | det q s => simpa [run, hc, Result.prepend] using! ih bs (advance cfg (q,s)) (by simpa [run, hc, Result.prepend] using! h)
    | coin k => cases bs with
      | nil => simp [run, hc] at h
      | cons b bs => simpa [run, hc, Result.prepend] using! ih bs (advance cfg (k b)) (by simpa [run, hc, Result.prepend] using! h)

theorem run_needBits (M : Program Γ Λ) (n : ℕ) (bs : List Bool) (cfg : Turing.TM0.Cfg Γ Λ)
    (h : (run M n bs cfg).stop = .needBits) :
    (∃ k, M (run M n bs cfg).cfg.q (run M n bs cfg).cfg.Tape.head = .coin k) ∧
      (run M n bs cfg).unread = [] ∧ (run M n bs cfg).steps < n := by
  induction n generalizing bs cfg with
  | zero => cases hc : M cfg.q cfg.Tape.head <;> simp_all [run]
  | succ n ih =>
    cases hc : M cfg.q cfg.Tape.head with
    | halt => simp [run, hc] at h
    | det q s =>
      obtain ⟨hk, hu, ht⟩ := ih bs (advance cfg (q,s)) (by simpa [run, hc, Result.prepend] using! h)
      simpa only [run, hc, Result.prepend, Result.steps, List.length_cons] using!
          ⟨hk, hu, Nat.succ_lt_succ ht⟩
    | coin k => cases bs with
      | nil => simp [run, hc, Result.steps]
      | cons b bs =>
        obtain ⟨hk, hu, ht⟩ :=
            ih bs (advance cfg (k b)) (by simpa [run, hc, Result.prepend] using! h)
        simpa only [run, hc, Result.prepend, Result.steps, List.length_cons] using!
            ⟨hk, hu, Nat.succ_lt_succ ht⟩

theorem supply_prepend (M : Program Γ Λ) (n : ℕ) (more : List Bool) (r : Result Γ Λ) (e : Tick Γ Λ) :
    supply M (n+1) more (r.prepend e) = (supply M n more r).prepend e := by
  by_cases h : r.stop = .needBits <;>
    simp [supply, Result.prepend, Result.steps, h, Nat.succ_sub_succ_eq_sub]

theorem run_append (M : Program Γ Λ) (n : ℕ) (bs more : List Bool) (cfg : Turing.TM0.Cfg Γ Λ) :
    run M n (bs++more) cfg = supply M n more (run M n bs cfg) := by
  induction n generalizing bs cfg with
  | zero => cases h : M cfg.q cfg.Tape.head <;> simp [run, h, supply]
  | succ n ih =>
    cases h : M cfg.q cfg.Tape.head with
    | halt => simp [run, h, supply]
    | det q s => simp only [run, h, supply_prepend]; rw [ih]
    | coin k => cases bs with
      | nil => cases more <;> simp [run, h, supply, Result.steps]
      | cons b bs => simp only [List.cons_append, run, h, supply_prepend]; rw [ih]

theorem run_spin (n : ℕ) (bs : List Bool) (cfg : Turing.TM0.Cfg Γ Unit) :
    (run spin n bs cfg).stop = .fuel ∧ (run spin n bs cfg).steps = n ∧
    (run spin n bs cfg).bits = [] ∧ (run spin n bs cfg).unread = bs := by
  induction n generalizing cfg with
  | zero => simp [run, spin, Result.steps, Result.bits]
  | succ n ih => simpa [run, spin, Result.prepend, Result.steps, Result.bits] using! ih (advance cfg ((), .move .right))

theorem run_halt_iff (M : Program Γ Λ) (n : ℕ) (bs : List Bool) (cfg : Turing.TM0.Cfg Γ Λ) :
    (run M n bs cfg).stop = .halted ↔
      M (run M n bs cfg).cfg.q (run M n bs cfg).cfg.Tape.head = .halt := by
  induction n generalizing bs cfg with
  | zero => cases h : M cfg.q cfg.Tape.head <;> simp [run, h]
  | succ n ih =>
    cases h : M cfg.q cfg.Tape.head with
    | halt => simp [run, h]
    | det q s => simpa [run, h, Result.prepend] using! ih bs (advance cfg (q,s))
    | coin k => cases bs with
      | nil => simp [run, h]
      | cons b bs => simpa [run, h, Result.prepend] using! ih bs (advance cfg (k b))

theorem steps_le_paid (r : Result Γ Λ) (price : Tick Γ Λ → ℕ)
    (h : ∀ e ∈ r.trace, 1 ≤ price e) : r.steps ≤ (r.trace.map price).sum := by
  have hl (es : List (Tick Γ Λ)) : (∀ e ∈ es, 1 ≤ price e) → es.length ≤ (es.map price).sum := by
    induction es with
    | nil => simp
    | cons e es ih =>
      intro hp
      have he := hp e (by simp)
      have ht := ih (fun x hx => hp x (by simp [hx]))
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      omega
  exact hl r.trace h

theorem run_fuel_iff (M : Program Γ Λ) (n : ℕ) (bs : List Bool) (cfg : Turing.TM0.Cfg Γ Λ) :
    (run M n bs cfg).stop = .fuel ↔ (run M n bs cfg).steps = n ∧
      M (run M n bs cfg).cfg.q (run M n bs cfg).cfg.Tape.head ≠ .halt := by
  constructor
  · intro h
    refine ⟨run_fuel_steps M n bs cfg h, ?_⟩
    intro hc
    have hh := (run_halt_iff M n bs cfg).mpr hc
    simp [h] at hh
  · rintro ⟨hs,hc⟩
    have hh : (run M n bs cfg).stop ≠ .halted := fun h => hc ((run_halt_iff M n bs cfg).mp h)
    cases ht : (run M n bs cfg).stop with
    | halted => exact False.elim (hh ht)
    | fuel => rfl
    | needBits => have hn := (run_needBits M n bs cfg ht).2.2; omega

theorem run_halted_add (M : Program Γ Λ) (n m : ℕ) (bs : List Bool) (cfg : Turing.TM0.Cfg Γ Λ)
    (h : (run M n bs cfg).stop = .halted) : run M (n+m) bs cfg = run M n bs cfg := by
  rw [run_add]
  simp [resume, h]

theorem run_fuel_add (M : Program Γ Λ) (n m : ℕ) (bs : List Bool) (cfg : Turing.TM0.Cfg Γ Λ)
    (h : (run M n bs cfg).stop = .fuel) :
    let r := run M n bs cfg
    let s := run M m r.unread r.cfg
    run M (n+m) bs cfg = { s with trace := r.trace ++ s.trace } := by
  rw [run_add]
  simp [resume, h]

theorem run_fuel_add_observe (M : Program Γ Λ) (n m : ℕ) (bs : List Bool) (cfg : Turing.TM0.Cfg Γ Λ)
    (h : (run M n bs cfg).stop = .fuel) :
    let r := run M n bs cfg
    let s := run M m r.unread r.cfg
    (run M (n+m) bs cfg).observe = (s.cfg,s.stop,s.unread,r.bits++s.bits,r.steps+s.steps) := by
  (try dsimp only)
  rw [run_fuel_add M n m bs cfg h]
  simp [Result.observe, Result.bits, Result.steps, List.filterMap_append]

theorem Result.observe_eq_iff (r : Result Γ Λ) (cfg : Turing.TM0.Cfg Γ Λ) (s : Stop)
    (raw bits : List Bool) (n : ℕ) :
    r.observe = (cfg,s,raw,bits,n) ↔ r.cfg = cfg ∧ r.stop = s ∧ r.unread = raw ∧ r.bits = bits ∧ r.steps = n := by
  simp [Result.observe]

theorem fuel_before (M : Program Γ Λ) (N n : ℕ) (bs : List Bool) (cfg : Turing.TM0.Cfg Γ Λ)
    (hs : (run M N bs cfg).steps = N) (hn : n < N) : (run M n bs cfg).stop = .fuel := by
  by_contra hh
  have he := run_add M n (N-n) bs cfg
  have hsum : n+(N-n) = N := by omega
  rw [hsum] at he
  simp only [resume,if_neg hh] at he
  rw [he] at hs
  have hl := run_steps_le M n bs cfg
  omega

theorem mass_le_map {α β : Type} (p : PMF α) (f : α → β) (a : α) :
    p a ≤ p.map f (f a) := by
  classical
  rw [PMF.map_apply]
  exact (by simpa using (ENNReal.le_tsum (f := fun x => if f a = f x then p x else 0) a :
    (if f a = f a then p a else 0) ≤ ∑' x, if f a = f x then p x else 0))

theorem law_run_lower (M : Program Γ Λ) (n : ℕ) (bs : List Bool) (cfg : Turing.TM0.Cfg Γ Λ)
    (hs : (run M n bs cfg).stop ≠ .needBits) (hu : (run M n bs cfg).unread = []) :
    (1 / 2 : ℝ≥0∞)^bs.length ≤ law M n cfg (run M n bs cfg) := by
  induction n generalizing bs cfg with
  | zero =>
    cases hc : M cfg.q cfg.Tape.head <;> simp_all [run,law,PMF.pure_apply]
  | succ n ih =>
    cases hc : M cfg.q cfg.Tape.head with
    | halt => simp_all [run,law,PMF.pure_apply]
    | det q s =>
      simp only [run,hc,Result.prepend] at hs hu
      exact (ih bs (advance cfg (q,s)) hs hu).trans
        (by simpa only [run,law,hc] using! (mass_le_map
          (law M n (advance cfg (q,s))) (Result.prepend (cfg,none)) (run M n bs (advance cfg (q,s)))))
    | coin k =>
      cases bs with
      | nil => simp [run,hc] at hs
      | cons b bs =>
        simp only [run,hc,Result.prepend] at hs hu
        have hi := ih bs (advance cfg (k b)) hs hu
        have hm := mass_le_map (law M n (advance cfg (k b)))
          (Result.prepend (cfg,some b)) (run M n bs (advance cfg (k b)))
        simp only [law,hc,run,List.length_cons,pow_succ']
        rw [PMF.bind_apply]
        apply le_trans (mul_le_mul_right (hi.trans hm) (1/2 : ℝ≥0∞))
        convert! ENNReal.le_tsum b using 1
        simp only [PMF.uniformOfFintype'_apply,Fintype.card_bool,Nat.cast_ofNat,one_div]

theorem pmf_eq_of_apply_le {α : Type} (p q : PMF α) (h : ∀ a, p a ≤ q a) : p = q := by
  apply PMF.ext
  intro a
  apply le_antisymm (h a)
  by_contra hn
  have ht := ENNReal.tsum_lt_tsum (by rw [p.tsum_coe]; exact ENNReal.one_ne_top) h (lt_of_not_ge hn)
  simp only [p.tsum_coe,q.tsum_coe,lt_self_iff_false] at ht

theorem map_eq_of_mass_le {α β : Type} (p : PMF α) (q : PMF β) (f : α → β)
    (hf : Function.Injective f) (h : ∀ a, p a ≤ q (f a)) : p.map f = q := by
  classical
  apply pmf_eq_of_apply_le
  intro b
  rw [PMF.map_apply]
  by_cases hb : ∃ a, f a = b
  · obtain ⟨a,rfl⟩ := hb
    rw [tsum_eq_single a]
    · simpa using! h a
    · intro a' hn
      have he : f a ≠ f a' := fun he => hn (hf he.symm)
      simp [he]
  · have he : ∀ a, b ≠ f a := fun a he => hb ⟨a,he.symm⟩
    simp only [if_neg (he _),tsum_zero,zero_le]

theorem law_support_run (M : Program Γ Λ) (n : ℕ) (cfg : Turing.TM0.Cfg Γ Λ)
    (r : Result Γ Λ) (hr : r ∈ (law M n cfg).support) :
    run M n r.bits cfg = r ∧ r.unread = [] ∧ r.stop ≠ .needBits := by
  induction n generalizing cfg r with
  | zero =>
    cases hc : M cfg.q cfg.Tape.head <;>
      simp only [law,hc,PMF.mem_support_pure_iff] at hr <;> subst r <;>
      simp [Result.bits,run,hc]
  | succ n ih =>
    cases hc : M cfg.q cfg.Tape.head with
    | halt =>
      simp only [law,hc,PMF.mem_support_pure_iff] at hr
      subst r
      simp [Result.bits,run,hc]
    | det q s =>
      obtain ⟨t,ht,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp (by simpa only [law,hc] using! hr)
      obtain ⟨he,hu,hs⟩ := ih (advance cfg (q,s)) t ht
      simpa [run,hc,Result.bits,Result.prepend,he] using!
        (show (run M n t.bits (advance cfg (q,s))).prepend (cfg,none) = t.prepend (cfg,none) ∧
          t.unread = [] ∧ t.stop ≠ .needBits from ⟨congrArg (Result.prepend (cfg,none)) he,hu,hs⟩)
    | coin k =>
      obtain ⟨b,_,ht⟩ := (PMF.mem_support_bind_iff _ _ _).mp (by simpa only [law,hc] using! hr)
      obtain ⟨t,ht',heq⟩ := (PMF.mem_support_map_iff (Result.prepend (cfg,some b))
        (law M n (advance cfg (k b))) r).mp ht
      subst r
      obtain ⟨he,hu,hs⟩ := ih (advance cfg (k b)) t ht'
      simpa [run,hc,Result.bits,Result.prepend,he] using!
        (show (run M n t.bits (advance cfg (k b))).prepend (cfg,some b) = t.prepend (cfg,some b) ∧
          t.unread = [] ∧ t.stop ≠ .needBits from ⟨congrArg (Result.prepend (cfg,some b)) he,hu,hs⟩)

theorem law_eq_pathLaw {α : Type} (M : Program Γ Λ) (n : ℕ) (cfg : Turing.TM0.Cfg Γ Λ)
    (p : CoinCode α)
    (hc : ∀ z ∈ p.paths, (run M n z.2 cfg).unread = [] ∧ (run M n z.2 cfg).stop ≠ .needBits) :
    p.pathLaw.map (fun i => run M n (p.paths.get i).2 cfg) = law M n cfg := by
  apply map_eq_of_mass_le
  · intro i j he
    apply p.paths_word_get_injective
    have hi := run_account M n (p.paths.get i).2 cfg
    have hj := run_account M n (p.paths.get j).2 cfg
    rw [(hc _ (List.get_mem _ _)).1,List.append_nil] at hi
    rw [(hc _ (List.get_mem _ _)).1,List.append_nil] at hj
    exact hi.trans ((congrArg Result.bits he).trans hj.symm)
  · intro i
    rw [CoinCode.pathLaw_apply]
    exact law_run_lower M n (p.paths.get i).2 cfg
      (hc _ (List.get_mem _ _)).2 (hc _ (List.get_mem _ _)).1

theorem mem_support_law_iff (M : Program Γ Λ) (n : ℕ) (cfg : Turing.TM0.Cfg Γ Λ)
    (r : Result Γ Λ) : r ∈ (law M n cfg).support ↔
      run M n r.bits cfg = r ∧ r.unread = [] ∧ r.stop ≠ .needBits := by
  constructor
  · exact law_support_run M n cfg r
  · rintro ⟨he,hu,hs⟩
    have hl := law_run_lower M n r.bits cfg (by rwa [he]) (by rwa [he])
    rw [he] at hl
    rw [PMF.mem_support_iff]
    exact ne_of_gt (lt_of_lt_of_le (ENNReal.pow_pos (by norm_num : (0 : ℝ≥0∞) < 1/2) _) hl)

theorem law_eq_pure_of_run_nil (M : Program Γ Λ) (n : ℕ) (cfg : Turing.TM0.Cfg Γ Λ)
    (hs : (run M n [] cfg).stop ≠ .needBits) : law M n cfg = PMF.pure (run M n [] cfg) := by
  have hu : (run M n [] cfg).unread = [] := by
    have ha := run_account M n [] cfg
    exact (List.append_eq_nil_iff.mp ha.symm).2
  have hl : 1 ≤ law M n cfg (run M n [] cfg) := by
    simpa using! law_run_lower M n [] cfg hs hu
  apply Eq.symm
  apply pmf_eq_of_apply_le
  intro r
  by_cases he : r = run M n [] cfg
  · subst r
    simpa using! hl
  · simp [PMF.pure_apply,he]

theorem law_support_path [Inhabited Λ] (M : Program Γ Λ) (n : ℕ) (cfg : Turing.TM0.Cfg Γ Λ)
    (r : Result Γ Λ) (hr : r ∈ (law M n cfg).support) : Path M cfg r.trace r.cfg := by
  have he := (law_support_run M n cfg r hr).1
  have hp := run_path M n r.bits cfg
  rwa [he] at hp

theorem law_support_steps (M : Program Γ Λ) (n : ℕ) (cfg : Turing.TM0.Cfg Γ Λ)
    (r : Result Γ Λ) (hr : r ∈ (law M n cfg).support) : r.steps ≤ n := by
  have he := (law_support_run M n cfg r hr).1
  have hp := run_steps_le M n r.bits cfg
  rwa [he] at hp

theorem law_spin (n : ℕ) (cfg : Turing.TM0.Cfg Γ Unit) :
    law spin n cfg = PMF.pure (run spin n [] cfg) := by
  apply law_eq_pure_of_run_nil
  have h := (run_spin n [] cfg).1
  simp [h]

@[simp] theorem Result.appendTrace_nil : (Result.appendTrace [] : Result Γ Λ → Result Γ Λ) = _root_.id := rfl

theorem continueLaw_prepend (M : Program Γ Λ) (m : ℕ) (r : Result Γ Λ) (e : Tick Γ Λ) :
    continueLaw M m (r.prepend e) = (continueLaw M m r).map (Result.prepend e) := by
  by_cases h : r.stop = .fuel <;>
    simp only [continueLaw,Result.prepend,h,↓reduceIte,PMF.map_comp,PMF.pure_map]
  all_goals rfl

theorem law_add (M : Program Γ Λ) (n m : ℕ) (cfg : Turing.TM0.Cfg Γ Λ) :
    law M (n+m) cfg = (law M n cfg).bind (continueLaw M m) := by
  induction n generalizing cfg with
  | zero =>
    cases hc : M cfg.q cfg.Tape.head <;> cases m <;>
      simp [law,hc,continueLaw,Result.appendTrace_nil,PMF.map_id]
  | succ n ih =>
    rw [Nat.succ_add]
    cases hc : M cfg.q cfg.Tape.head with
    | halt => simp [law,hc,continueLaw]
    | det q s => simp only [law,hc,ih,PMF.map_bind,PMF.bind_map,Function.comp_def,continueLaw_prepend]
    | coin k => simp only [law,hc,ih,PMF.map_bind,PMF.bind_map,PMF.bind_bind,Function.comp_def,continueLaw_prepend]

theorem truncate_continue (M : Program Γ Λ) (n m : ℕ) (cfg : Turing.TM0.Cfg Γ Λ)
    (r s : Result Γ Λ) (hr : r ∈ (law M n cfg).support) (hs : s ∈ (continueLaw M m r).support) :
    truncate M n cfg s = r := by
  obtain ⟨he,hu,hn⟩ := law_support_run M n cfg r hr
  by_cases hf : r.stop = .fuel
  · obtain ⟨t,_,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp (by simpa only [continueLaw,hf,↓reduceIte] using! hs)
    have ha := run_append M n r.bits t.bits cfg
    rw [he] at ha
    simp only [supply,if_neg hn,hu,List.nil_append] at ha
    change {run M n ((Result.appendTrace r.trace t).bits) cfg with unread := []} = r
    have hb : (Result.appendTrace r.trace t).bits = r.bits++t.bits := by
      simp [Result.bits,Result.appendTrace,List.filterMap_append]
    rw [hb,ha]
    change {r with unread := []} = r
    rw [← hu]
  · have hs' : s = r := by simpa [continueLaw,hf] using! hs
    subst s
    simp only [truncate,he]
    rw [← hu]

theorem expectation_le_on_support {α : Type} (p : PMF α) (f g : α → ℝ≥0∞)
    (h : ∀ a ∈ p.support, f a ≤ g a) : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation p f ≤ Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation p g := by
  unfold Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
  apply ENNReal.tsum_le_tsum
  intro a
  by_cases ha : p a = 0
  · simp [ha]
  · exact mul_le_mul_right (h a (by rwa [PMF.mem_support_iff])) (p a)

theorem continueLaw_steps_le (M : Program Γ Λ) (m : ℕ) (r s : Result Γ Λ)
    (hs : s ∈ (continueLaw M m r).support) : r.steps ≤ s.steps := by
  by_cases hf : r.stop = .fuel
  · obtain ⟨t,_,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp (by simpa only [continueLaw,hf,↓reduceIte] using! hs)
    simp [Result.steps,Result.appendTrace]
  · have he : s = r := by simpa [continueLaw,hf] using! hs
    simp [he]

theorem continueLaw_reads_le (M : Program Γ Λ) (m : ℕ) (r s : Result Γ Λ)
    (hs : s ∈ (continueLaw M m r).support) : r.bits.length ≤ s.bits.length := by
  by_cases hf : r.stop = .fuel
  · obtain ⟨t,_,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp (by simpa only [continueLaw,hf,↓reduceIte] using! hs)
    simp [Result.bits,Result.appendTrace,List.filterMap_append]
  · have he : s = r := by simpa [continueLaw,hf] using! hs
    simp [he]

theorem bind_congr_support {α β : Type} (p : PMF α) (f g : α → PMF β)
    (h : ∀ a ∈ p.support, f a = g a) : p.bind f = p.bind g := by
  apply PMF.ext
  intro b
  simp only [PMF.bind_apply]
  apply tsum_congr
  intro a
  by_cases ha : p a = 0
  · simp [ha]
  · rw [h a (by rwa [PMF.mem_support_iff])]

theorem map_eq_pure_on_support {α β : Type} (p : PMF α) (f : α → β) (b : β)
    (h : ∀ a ∈ p.support, f a = b) : p.map f = PMF.pure b := by
  calc
    _ = p.bind (fun _ => PMF.pure b) := bind_congr_support p _ _ (fun a ha => by simp [h a ha])
    _ = _ := PMF.bind_const p _

theorem law_truncate (M : Program Γ Λ) (n m : ℕ) (cfg : Turing.TM0.Cfg Γ Λ) :
    (law M (n+m) cfg).map (truncate M n cfg) = law M n cfg := by
  rw [law_add,PMF.map_bind]
  calc
    _ = (law M n cfg).bind PMF.pure := bind_congr_support _ _ _ (fun r hr =>
      map_eq_pure_on_support _ _ _ (fun s hs => truncate_continue M n m cfg r s hr hs))
    _ = _ := PMF.bind_pure _

theorem law_expectation_le_add (M : Program Γ Λ) (n m : ℕ) (cfg : Turing.TM0.Cfg Γ Λ)
    (F : Result Γ Λ → ℝ≥0∞)
    (h : ∀ r ∈ (law M n cfg).support, ∀ s ∈ (continueLaw M m r).support, F r ≤ F s) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (law M n cfg) F ≤ Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (law M (n+m) cfg) F := by
  rw [law_add,Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_bind]
  apply expectation_le_on_support
  intro r hr
  have he := expectation_le_on_support (continueLaw M m r) (fun _ => F r) F (h r hr)
  rwa [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_const] at he

theorem law_steps_mean_mono (M : Program Γ Λ) (cfg : Turing.TM0.Cfg Γ Λ) :
    Monotone (fun n => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (law M n cfg) (fun r => (r.steps : ℝ≥0∞))) := by
  intro n N hN
  obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le hN
  apply law_expectation_le_add
  intro r _ s hs
  exact_mod_cast continueLaw_steps_le M m r s hs

theorem law_reads_mean_mono (M : Program Γ Λ) (cfg : Turing.TM0.Cfg Γ Λ) :
    Monotone (fun n => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (law M n cfg) (fun r => (r.bits.length : ℝ≥0∞))) := by
  intro n N hN
  obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le hN
  apply law_expectation_le_add
  intro r _ s hs
  exact_mod_cast continueLaw_reads_le M m r s hs

theorem law_fuel_antitone (M : Program Γ Λ) (cfg : Turing.TM0.Cfg Γ Λ) :
    Antitone (fun n => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (law M n cfg) (fun r => r.stop = .fuel)) := by
  classical
  intro n N hN
  obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le hN
  (try dsimp only)
  rw [law_add,Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_eq,Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_bind,Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_eq]
  apply expectation_le_on_support
  intro r _
  by_cases hf : r.stop = .fuel
  · simp only [hf,↓reduceIte]
    exact Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_le_one _ _
  · simp [continueLaw,hf]

theorem law_halted_event_mono (M : Program Γ Λ) (cfg : Turing.TM0.Cfg Γ Λ)
    (P : Turing.TM0.Cfg Γ Λ → Prop) :
    Monotone (fun n => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (law M n cfg) (fun r => r.stop = .halted ∧ P r.cfg)) := by
  classical
  intro n N hN
  obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le hN
  (try dsimp only)
  rw [Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_eq,Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_eq]
  apply law_expectation_le_add
  intro r _ s hs
  by_cases hp : r.stop = .halted ∧ P r.cfg
  · have hf : r.stop ≠ .fuel := by simp [hp.1]
    have he : s = r := by simpa [continueLaw,hf] using! hs
    subst s
    exact le_rfl
  · simp [hp]

theorem expectation_congr_support {α : Type} (p : PMF α) (f g : α → ℝ≥0∞)
    (h : ∀ a ∈ p.support, f a = g a) : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation p f = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation p g := by
  apply le_antisymm
  · exact expectation_le_on_support p f g (fun a ha => (h a ha).le)
  · exact expectation_le_on_support p g f (fun a ha => (h a ha).ge)

theorem iSup_mul_budget (f : ℕ → ℝ≥0∞) (hf : Monotone f) (c : ℕ) (hc : 0 < c) :
    (⨆ n, f n) = ⨆ n, f (c*n) := by
  apply le_antisymm
  · apply iSup_le
    intro n
    have hn : n ≤ c*n := by simpa using! Nat.mul_le_mul_right n (show 1 ≤ c from hc)
    exact (hf hn).trans (le_iSup (fun n => f (c*n)) n)
  · exact iSup_le (fun n => le_iSup f (c*n))

theorem iInf_mul_budget (f : ℕ → ℝ≥0∞) (hf : Antitone f) (c : ℕ) (hc : 0 < c) :
    (⨅ n, f n) = ⨅ n, f (c*n) := by
  apply le_antisymm
  · exact le_iInf (fun n => iInf_le f (c*n))
  · apply le_iInf
    intro n
    have hn : n ≤ c*n := by simpa using! Nat.mul_le_mul_right n (show 1 ≤ c from hc)
    exact (iInf_le (fun n => f (c*n)) n).trans (hf hn)

theorem finishedMass_mono (M : Program Γ Λ) (cfg : Turing.TM0.Cfg Γ Λ) (r : Result Γ Λ) :
    Monotone (fun n => finishedMass M n cfg r) := by
  intro n N hN
  obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le hN
  (try dsimp only)
  by_cases hr : r.stop = .halted
  · simp only [finishedMass,if_pos hr]
    rw [law_add,PMF.bind_apply]
    simpa [continueLaw,hr] using (ENNReal.le_tsum (f := fun a => law M n cfg a * continueLaw M m a r) r :
      law M n cfg r * continueLaw M m r r ≤ ∑' a, law M n cfg a * continueLaw M m a r)
  · simp [finishedMass,hr]

theorem tsum_iSup_nat_mono {α : Type} (f : ℕ → α → ℝ≥0∞) (h : ∀ a, Monotone (fun n => f n a)) :
    (∑' a, ⨆ n, f n a) = ⨆ n, ∑' a, f n a := by
  have hs (s : Finset α) : (∑ a ∈ s, ⨆ n, f n a) = ⨆ n, ∑ a ∈ s, f n a := by
    apply Eq.symm
    apply iSup_eq_of_tendsto
    · intro n N hn
      exact Finset.sum_le_sum (fun a _ => h a hn)
    · exact tendsto_finsetSum s (fun a _ => tendsto_atTop_iSup (h a))
  rw [ENNReal.tsum_eq_iSup_sum]
  simp_rw [hs]
  rw [iSup_comm]
  simp only [← ENNReal.tsum_eq_iSup_sum]

theorem finishedMass_sum (M : Program Γ Λ) (n : ℕ) (cfg : Turing.TM0.Cfg Γ Λ) :
    (∑' r, finishedMass M n cfg r) = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (law M n cfg) (fun r => r.stop = .halted) := by
  classical
  rw [Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_eq]
  unfold Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
  apply tsum_congr
  intro r
  by_cases hr : r.stop = .halted <;> simp [finishedMass,hr]

theorem haltedMass_sum (M : Program Γ Λ) (cfg : Turing.TM0.Cfg Γ Λ) :
    (∑' r, haltedMass M cfg r) = ⨆ n, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (law M n cfg) (fun r => r.stop = .halted) := by
  unfold haltedMass
  rw [tsum_iSup_nat_mono _ (finishedMass_mono M cfg)]
  simp only [finishedMass_sum]

theorem haltedMass_sum_le_one (M : Program Γ Λ) (cfg : Turing.TM0.Cfg Γ Λ) :
    (∑' r, haltedMass M cfg r) ≤ 1 := by
  rw [haltedMass_sum]
  exact iSup_le (fun n => Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_le_one _ _)

theorem law_halt_add_fuel (M : Program Γ Λ) (n : ℕ) (cfg : Turing.TM0.Cfg Γ Λ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (law M n cfg) (fun r => r.stop = .halted) +
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (law M n cfg) (fun r => r.stop = .fuel) = 1 := by
  classical
  rw [Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_eq,Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_eq,← Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_add]
  calc
    _ = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (law M n cfg) (fun _ => 1) := by
      apply expectation_congr_support
      intro r hr
      have hn := (law_support_run M n cfg r hr).2.2
      cases hs : r.stop <;> simp_all
    _ = _ := Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_const _ _

theorem neverMass_eq_iInf_fuel (M : Program Γ Λ) (cfg : Turing.TM0.Cfg Γ Λ) :
    neverMass M cfg = ⨅ n, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (law M n cfg) (fun r => r.stop = .fuel) := by
  unfold neverMass
  rw [haltedMass_sum,ENNReal.sub_iSup ENNReal.one_ne_top]
  congr 1
  funext n
  exact (ENNReal.eq_sub_of_add_eq
    (ne_top_of_le_ne_top ENNReal.one_ne_top (Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_le_one _ _))
    (add_comm _ _ |>.trans (law_halt_add_fuel M n cfg))).symm

theorem terminalMass_sum (M : Program Γ Λ) (cfg : Turing.TM0.Cfg Γ Λ) :
    (∑' z, terminalMass M cfg z) = 1 := by
  rw [← (Equiv.optionEquivSumPUnit.{0,0} (Result Γ Λ)).symm.tsum_eq (terminalMass M cfg)]
  rw [Summable.tsum_sum ENNReal.summable ENNReal.summable]
  simp only [Equiv.optionEquivSumPUnit_symm_inl,Equiv.optionEquivSumPUnit_symm_inr,terminalMass]
  have hp (c : ℝ≥0∞) : (∑' _ : PUnit.{1}, c) = c := by simp [tsum_fintype]
  rw [hp]
  rw [neverMass,add_comm]
  exact tsub_add_cancel_of_le (haltedMass_sum_le_one M cfg)

noncomputable def terminalLaw (M : Program Γ Λ) (cfg : Turing.TM0.Cfg Γ Λ) : PMF (Option (Result Γ Λ)) :=
  ⟨terminalMass M cfg,ENNReal.summable.hasSum_iff.mpr (terminalMass_sum M cfg)⟩

@[simp] theorem terminalLaw_some (M : Program Γ Λ) (cfg : Turing.TM0.Cfg Γ Λ) (r : Result Γ Λ) :
    terminalLaw M cfg (some r) = haltedMass M cfg r := rfl

@[simp] theorem terminalLaw_none (M : Program Γ Λ) (cfg : Turing.TM0.Cfg Γ Λ) :
    terminalLaw M cfg none = neverMass M cfg := rfl

theorem run_halted_at_steps (M : Program Γ Λ) (n : ℕ) (bs : List Bool) (cfg : Turing.TM0.Cfg Γ Λ)
    (hs : (run M n bs cfg).stop = .halted) :
    run M (run M n bs cfg).steps bs cfg = run M n bs cfg := by
  induction n generalizing bs cfg with
  | zero => cases hc : M cfg.q cfg.Tape.head <;> simp_all [run,Result.steps]
  | succ n ih =>
    cases hc : M cfg.q cfg.Tape.head with
    | halt => simp [run,hc,Result.steps]
    | det q s =>
      have hh := ih bs (advance cfg (q,s)) (by simpa only [run,hc,Result.prepend] using! hs)
      simpa only [run,hc,Result.prepend,Result.steps,List.length_cons] using!
        congrArg (Result.prepend (cfg,none)) hh
    | coin k => cases bs with
      | nil => simp [run,hc] at hs
      | cons b bs =>
        have hh := ih bs (advance cfg (k b)) (by simpa only [run,hc,Result.prepend] using! hs)
        simpa only [run,hc,Result.prepend,Result.steps,List.length_cons] using!
          congrArg (Result.prepend (cfg,some b)) hh

theorem haltedMass_ne_zero_iff (M : Program Γ Λ) (cfg : Turing.TM0.Cfg Γ Λ) (r : Result Γ Λ) :
    haltedMass M cfg r ≠ 0 ↔ r.stop = .halted ∧ ∃ n, r ∈ (law M n cfg).support := by
  classical
  by_cases hr : r.stop = .halted
  · simp only [haltedMass,finishedMass,hr,↓reduceIte,ne_eq,PMF.mem_support_iff,true_and]
    constructor
    · intro h
      by_contra hn
      push Not at hn
      apply h
      simp [hn]
    · rintro ⟨n,hn⟩ he
      have hl := le_iSup (fun n => law M n cfg r) n
      rw [he] at hl
      exact hn (le_zero_iff.mp hl)
  · simp [haltedMass,finishedMass,hr]

theorem terminalLaw_support_some (M : Program Γ Λ) (cfg : Turing.TM0.Cfg Γ Λ) (r : Result Γ Λ) :
    some r ∈ (terminalLaw M cfg).support ↔ r.stop = .halted ∧ ∃ n, r ∈ (law M n cfg).support := by
  rw [PMF.mem_support_iff,terminalLaw_some,haltedMass_ne_zero_iff]

theorem terminalLaw_first_stop [Inhabited Λ] (M : Program Γ Λ) (cfg : Turing.TM0.Cfg Γ Λ)
    (r : Result Γ Λ) (hr : some r ∈ (terminalLaw M cfg).support) :
    run M r.steps r.bits cfg = r ∧ r.unread = [] ∧ r.stop = .halted ∧
      Path M cfg r.trace r.cfg ∧ ∀ k < r.steps, (run M k r.bits cfg).stop = .fuel := by
  obtain ⟨hs,n,hn⟩ := (terminalLaw_support_some M cfg r).mp hr
  obtain ⟨he,hu,_⟩ := law_support_run M n cfg r hn
  have hc := run_halted_at_steps M n r.bits cfg (by rwa [he])
  rw [he] at hc
  refine ⟨hc,hu,hs,law_support_path M n cfg r hn,?_⟩
  intro k hk
  exact fuel_before M r.steps k r.bits cfg (by rw [hc]) hk

theorem terminalLaw_expectation_some (M : Program Γ Λ) (cfg : Turing.TM0.Cfg Γ Λ)
    (F : Result Γ Λ → ℝ≥0∞) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (terminalLaw M cfg) (fun z => match z with | none => 0 | some r => F r) =
      ∑' r, haltedMass M cfg r * F r := by
  unfold Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
  rw [← (Equiv.optionEquivSumPUnit.{0,0} (Result Γ Λ)).symm.tsum_eq]
  rw [Summable.tsum_sum ENNReal.summable ENNReal.summable]
  simp only [Equiv.optionEquivSumPUnit_symm_inl,Equiv.optionEquivSumPUnit_symm_inr,
    terminalLaw_some,mul_zero,tsum_zero,add_zero]

theorem terminalLaw_halted_expectation (M : Program Γ Λ) (cfg : Turing.TM0.Cfg Γ Λ)
    (F : Result Γ Λ → ℝ≥0∞) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (terminalLaw M cfg) (fun z => match z with | none => 0 | some r => F r) =
      ⨆ n, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (law M n cfg) (fun r => if r.stop = .halted then F r else 0) := by
  classical
  rw [terminalLaw_expectation_some]
  simp only [haltedMass,ENNReal.iSup_mul]
  rw [tsum_iSup_nat_mono (fun n r => finishedMass M n cfg r * F r)
    (fun r n N hn => mul_le_mul_left (finishedMass_mono M cfg r hn) (F r))]
  congr 1
  funext n
  unfold Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
  apply tsum_congr
  intro r
  by_cases hr : r.stop = .halted <;> simp [finishedMass,hr]

theorem terminalLaw_event_some (M : Program Γ Λ) (cfg : Turing.TM0.Cfg Γ Λ)
    (P : Result Γ Λ → Prop) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (terminalLaw M cfg) (fun z => match z with | none => False | some r => P r) =
      ⨆ n, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (law M n cfg) (fun r => r.stop = .halted ∧ P r) := by
  classical
  rw [Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_eq]
  have hh := terminalLaw_halted_expectation M cfg (fun r => if P r then 1 else 0)
  convert! hh using 1
  · apply Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_congr
    intro z
    cases z <;> simp
  · congr 1
    funext n
    rw [Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_eq]
    apply Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_congr
    intro r
    by_cases hr : r.stop = .halted <;> by_cases hp : P r <;> simp [hr,hp]

theorem law_complete_terminal (M : Program Γ Λ) (n : ℕ) (cfg : Turing.TM0.Cfg Γ Λ)
    (h : ∀ r ∈ (law M n cfg).support, r.stop = .halted) :
    (law M n cfg).map some = terminalLaw M cfg := by
  apply map_eq_of_mass_le _ _ _ (Option.some_injective _)
  intro r
  rw [terminalLaw_some]
  by_cases hr : law M n cfg r = 0
  · simp [hr]
  · have hs := h r (by rwa [PMF.mem_support_iff])
    exact le_iSup_of_le n (by simp [finishedMass,hs])

theorem pmf_eq_pure_of_one {α : Type} (p : PMF α) (a : α) (h : 1 ≤ p a) : p = PMF.pure a := by
  classical
  symm
  apply pmf_eq_of_apply_le
  intro b
  by_cases he : b = a
  · subst b
    simpa using! h
  · simp [PMF.pure_apply,he]

theorem terminalLaw_spin (cfg : Turing.TM0.Cfg Γ Unit) : terminalLaw spin cfg = PMF.pure none := by
  apply pmf_eq_pure_of_one
  rw [terminalLaw_none,neverMass_eq_iInf_fuel]
  simp only [law_spin,Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_eq,Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_pure,(run_spin _ [] _).1,↓reduceIte,iInf_const]
  exact le_rfl

theorem law_halted_expectation_mono (M : Program Γ Λ) (cfg : Turing.TM0.Cfg Γ Λ)
    (F : Result Γ Λ → ℝ≥0∞) :
    Monotone (fun n => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (law M n cfg) (fun r => if r.stop = .halted then F r else 0)) := by
  intro n N hN
  unfold Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
  apply ENNReal.tsum_le_tsum
  intro r
  by_cases hr : r.stop = .halted
  · simp only [if_pos hr]
    have hm := finishedMass_mono M cfg r hN
    simp only [finishedMass,if_pos hr] at hm
    exact mul_le_mul_left hm _
  · simp [hr]

end NativeTape

end Qatlib.Concepts.AdversaryBounds.AdvDuality
