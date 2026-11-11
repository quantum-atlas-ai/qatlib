/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CrouzeixLS26.AccessLower.BlockOutputSupportLower
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Constructor.SlackPromise
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Constructor.BasisFrame
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Constructor.ConstructorPromise
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Constructor.FrameTransport
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Constructor.TranslatedPromise
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.AnswerTransport
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Constructor.TruncatedPromise
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.ExpectedCost
import Qatlib.Concepts.QueryComplexity.AdversarySearch.MarkedSupport.MarkedColumns
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.BudgetTruncation
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.InputHybrid
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.OutputReadout
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.PreparedRepeat
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.Program
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.SourceWordTransport
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointAmplify
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointTranscript
import Qatlib.Foundations.OpCalculus.ContourCalc.NumericalRange
import Qatlib.Foundations.OpCalculus.ContourCalc.NumericalRangeConvex

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.BlockEncoding
/-! Readout slack for a budget-truncated finite constructor. The actual
conditional error 9/64 leaves success 55/64; good-record mass 5/8 therefore
still yields one-shot success at least 8/15. The same actual 1001-repetition
majority and joint hybrid are used, with no conditional renormalization. -/
set_option autoImplicit false
noncomputable section
open Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Constructor Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointAmplify Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointTranscript Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol Qatlib.Concepts.QueryComplexity.AdversarySearch.MarkedSupport Qatlib.Foundations.OpCalculus.ContourCalc
namespace Qatlib.Papers.CrouzeixLS26.AccessLower.BlockSampling
open Qatlib Matrix Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol MarkedHalmos ConstructorReadout
open scoped BigOperators Classical ComplexOrder
/-- The restricted-access construction satisfies `slack_constructor_vote_success` under the complete displayed premises. -/
theorem slack_constructor_vote_success {D R : ℕ} {I : Type}
    (O : Bool → Operator D) (hO : ∀ mode,O mode∈Matrix.unitaryGroup (Fin D) ℂ) (S : ℝ → Fin R)
    (P : Program D R) (words : Path P → List (OutputGate D)) (φ : Path P → I → Fin D)
    (i j : I) (τ : ℝ) (n : ℕ) (truth : Bool)
    (ρ : Operator D) (hρ : ρ.PosSemidef) (ht : (Matrix.trace ρ).re=1)
    (G : Finset (Path P))
    (hG : 5/8 ≤ ∑ p∈G,(pathLaw (fun mode => unitaryChannel (O mode) (hO mode)) S P ρ hρ ht).prob p)
    (hgood : ∀ p∈G,55/64 ≤ (sampleLaw O hO (φ p j) (words p)).probEvent (L := n)
      (fun ω => sampleVote τ (fun b => b=φ p i) ω=truth)) :
    8/15 ≤ (pathLaw (fun mode => unitaryChannel (O mode) (hO mode)) S
      (bind P (fun p => repeatReadout R (φ p j) (words p) n)) ρ hρ ht).expect
        (indicator (fun q => outputVote τ P words φ i j n q=truth)) := by
  let E : Path P × (Fin n → Fin D) → Prop := fun pq => sampleVote τ (fun b => b=φ pq.1 i) pq.2=truth
  change 8/15 ≤ (pathLaw (fun mode => unitaryChannel (O mode) (hO mode)) S
    (bind P (fun p => repeatReadout R (φ p j) (words p) n)) ρ hρ ht).expect
      (indicator (fun q => E ((constructorReadoutEquiv P words (fun p => φ p j) n).symm q)))
  rw [constructor_repeat_expect O hO S P words (fun p => φ p j) n ρ hρ ht E]
  have hh := joint_success
    (pathLaw (fun mode => unitaryChannel (O mode) (hO mode)) S P ρ hρ ht)
    (fun p => tupleLaw (sampleLaw O hO (φ p j) (words p)) n) E G (55/64) (5/8)
    (by norm_num) hG (by
      intro p hp
      simpa only [E,tupleLaw,Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent] using hgood p hp)
  norm_num at hh ⊢
  linarith

/-- The restricted-access construction satisfies `slack_baseline_constructor_success` under the complete displayed premises. -/
theorem slack_baseline_constructor_success {D R : ℕ} {I : Type} [Fintype I] [DecidableEq I]
    (O : Bool → Operator D) (hO : ∀ mode,O mode∈Matrix.unitaryGroup (Fin D) ℂ) (S : ℝ → Fin R)
    (P : Program D R) (words : Path P → List (OutputGate D)) (φ : Path P → I → Fin D)
    (T : Matrix I I ℂ) (i j : I) (τ : ℝ) (hτ : 0<τ) (hτ1 : τ ≤ 1/4)
    (n : ℕ) (hn : 0<n) (hbudget : 16/τ^2 ≤ (n : ℝ))
    (ρ : Operator D) (hρ : ρ.PosSemidef) (ht : (Matrix.trace ρ).re=1)
    (G : Finset (Path P))
    (hG : 5/8 ≤ ∑ p∈G,(pathLaw (fun mode => unitaryChannel (O mode) (hO mode)) S P ρ hρ ht).prob p)
    (hgood : ∀ p∈G,BlockEncoding T (wordMatrix O (words p))
      (basisFrame (φ p)) (basisFrame (φ p)) 1 (τ/100))
    (hentry : T i j=(4/5 : ℂ)) :
    8/15 ≤ (pathLaw (fun mode => unitaryChannel (O mode) (hO mode)) S
      (bind P (fun p => repeatReadout R (φ p j) (words p) n)) ρ hρ ht).expect
        (indicator (fun q => outputVote τ P words φ i j n q=true)) := by
  apply slack_constructor_vote_success O hO S P words φ i j τ n true ρ hρ ht G hG
  intro p hp
  have hb := baseline_block_sampling_error O hO (φ p) (words p) T i j τ hτ hτ1 n hn hbudget (hgood p hp) hentry
  have hs := sampleVote_partition (sampleLaw O hO (φ p j) (words p)) τ (fun b => b=φ p i) n
  linarith

/-- The restricted-access construction satisfies `slack_hidden_constructor_success` under the complete displayed premises. -/
theorem slack_hidden_constructor_success {D R : ℕ} {I : Type} [Fintype I] [DecidableEq I]
    (O : Bool → Operator D) (hO : ∀ mode,O mode∈Matrix.unitaryGroup (Fin D) ℂ) (S : ℝ → Fin R)
    (P : Program D R) (words : Path P → List (OutputGate D)) (φ : Path P → I → Fin D)
    (T : Matrix I I ℂ) (i j : I) (τ : ℝ) (hτ : 0<τ) (hτ1 : τ ≤ 1/4)
    (n : ℕ) (hn : 0<n) (hbudget : 16/τ^2 ≤ (n : ℝ))
    (ρ : Operator D) (hρ : ρ.PosSemidef) (ht : (Matrix.trace ρ).re=1)
    (G : Finset (Path P))
    (hG : 5/8 ≤ ∑ p∈G,(pathLaw (fun mode => unitaryChannel (O mode) (hO mode)) S P ρ hρ ht).prob p)
    (hgood : ∀ p∈G,BlockEncoding T (wordMatrix O (words p))
      (basisFrame (φ p)) (basisFrame (φ p)) 1 (τ/100))
    (hentry : T i j=(((4/(5*(1+2*τ)) : ℝ)) : ℂ)) :
    8/15 ≤ (pathLaw (fun mode => unitaryChannel (O mode) (hO mode)) S
      (bind P (fun p => repeatReadout R (φ p j) (words p) n)) ρ hρ ht).expect
        (indicator (fun q => outputVote τ P words φ i j n q=false)) := by
  apply slack_constructor_vote_success O hO S P words φ i j τ n false ρ hρ ht G hG
  intro p hp
  have hb := hidden_block_sampling_error O hO (φ p) (words p) T i j τ hτ hτ1 n hn hbudget (hgood p hp) hentry
  have hs := sampleVote_partition (sampleLaw O hO (φ p j) (words p)) τ (fun b => b=φ p i) n
  linarith

/-- The restricted-access construction satisfies `slack_baseline_majority_error` under the complete displayed premises. -/
theorem slack_baseline_majority_error {D R : ℕ} {I : Type} [Fintype I] [DecidableEq I]
    (O : Bool → Operator D) (hO : ∀ mode,O mode∈Matrix.unitaryGroup (Fin D) ℂ) (S : ℝ → Fin R)
    (P : Program D R) (words : Path P → List (OutputGate D)) (φ : Path P → I → Fin D)
    (T : Matrix I I ℂ) (i j : I) (τ : ℝ) (hτ : 0<τ) (hτ1 : τ ≤ 1/4)
    (n : ℕ) (hn : 0<n) (hbudget : 16/τ^2 ≤ (n : ℝ)) (r0 : Fin D)
    (G : Finset (Path P))
    (hG : 5/8 ≤ ∑ p∈G,(preparedLaw (fun mode => unitaryChannel (O mode) (hO mode)) S r0 P).prob p)
    (hgood : ∀ p∈G,BlockEncoding T (wordMatrix O (words p))
      (basisFrame (φ p)) (basisFrame (φ p)) 1 (τ/100))
    (hentry : T i j=(4/5 : ℂ))
    (ρ : Operator D) (hρ : ρ.PosSemidef) (ht : (Matrix.trace ρ).re=1) :
    let C := bind P (fun p => repeatReadout R (φ p j) (words p) n)
    (∑ q∈Finset.univ.filter (fun q => programMajority r0 C (outputVote τ P words φ i j n) q≠true),
      (pathLaw (fun mode => unitaryChannel (O mode) (hO mode)) S
        (repeatPrepared r0 C 1001) ρ hρ ht).prob q) ≤ 1/3 := by
  dsimp only
  apply programMajority_error
  exact slack_baseline_constructor_success O hO S P words φ T i j τ hτ hτ1 n hn hbudget
    (basisDensity r0) (basisDensity_pos r0) (basisDensity_trace_re r0) G hG hgood hentry

/-- The restricted-access construction satisfies `slack_hidden_majority_error` under the complete displayed premises. -/
theorem slack_hidden_majority_error {D R : ℕ} {I : Type} [Fintype I] [DecidableEq I]
    (O : Bool → Operator D) (hO : ∀ mode,O mode∈Matrix.unitaryGroup (Fin D) ℂ) (S : ℝ → Fin R)
    (P : Program D R) (words : Path P → List (OutputGate D)) (φ : Path P → I → Fin D)
    (T : Matrix I I ℂ) (i j : I) (τ : ℝ) (hτ : 0<τ) (hτ1 : τ ≤ 1/4)
    (n : ℕ) (hn : 0<n) (hbudget : 16/τ^2 ≤ (n : ℝ)) (r0 : Fin D)
    (G : Finset (Path P))
    (hG : 5/8 ≤ ∑ p∈G,(preparedLaw (fun mode => unitaryChannel (O mode) (hO mode)) S r0 P).prob p)
    (hgood : ∀ p∈G,BlockEncoding T (wordMatrix O (words p))
      (basisFrame (φ p)) (basisFrame (φ p)) 1 (τ/100))
    (hentry : T i j=(((4/(5*(1+2*τ)) : ℝ)) : ℂ))
    (ρ : Operator D) (hρ : ρ.PosSemidef) (ht : (Matrix.trace ρ).re=1) :
    let C := bind P (fun p => repeatReadout R (φ p j) (words p) n)
    (∑ q∈Finset.univ.filter (fun q => programMajority r0 C (outputVote τ P words φ i j n) q≠false),
      (pathLaw (fun mode => unitaryChannel (O mode) (hO mode)) S
        (repeatPrepared r0 C 1001) ρ hρ ht).prob q) ≤ 1/3 := by
  dsimp only
  apply programMajority_error
  exact slack_hidden_constructor_success O hO S P words φ T i j τ hτ hτ1 n hn hbudget
    (basisDensity r0) (basisDensity_pos r0) (basisDensity_trace_re r0) G hG hgood hentry

/-- The restricted-access construction satisfies `slack_literal_block_output_budget` under the complete displayed premises. -/
theorem slack_literal_block_output_budget (W : Type) [Fintype W] [DecidableEq W]
    (H : ℕ) (hH : 0<H) (N : ℕ) (hN : 0<N) (τ : ℝ) (hτ : 0<τ) (hτ1 : τ ≤ 1/4)
    (normal : ℝ → ℂ) (hnormal : ∀ a,‖normal a‖=1)
    (P : Program (queryDim W N) (H+1))
    (words : Path P → List (OutputGate (queryDim W N)))
    (φ : Path P → System N → Fin (queryDim W N)) (r0 : Fin (queryDim W N))
    (n : ℕ) (hn : 0<n) (hbudget : 16/τ^2 ≤ (n : ℝ)) (quse s : ℕ)
    (hq : ∀ p,wordQueries (words p) ≤ quse) (hs : ∀ p,(pathCharge P p).2 ≤ s)
    (hbase : slackConstructorPromise (finiteBaseline W N) (finiteBaseline_unitary W N hN) (fun _ => 0)
      P words φ (literalOutput (⟨0,hN⟩ : Fin N) 0) τ r0)
    (hhidden : ∀ h : Fin H × Fin N,slackConstructorPromise (familyOracle W τ h)
      (familyOracle_unitary W τ hτ.le hτ1 h) (labelResponse τ normal h)
      P words φ (literalOutput h.2 (spikePoint H τ h.1)) τ r0) :
    1/3 ≤ 4*((1001*(queryDepth P+n*quse) : ℕ) : ℝ)/Real.sqrt N+
      ((1001*s : ℕ) : ℝ)*(5*Real.sqrt τ+1/(H : ℝ)) := by
  let Q := reductionProgram P words φ (.inl true) n r0
  let vote := reductionVote τ P words φ (.inl false) (.inl true) n r0
  let ρ := basisDensity r0
  let μ := Qatlib.Concepts.QueryComplexity.AdversarySearch.MarkedSupport.jointMarkedPrior (Qatlib.Concepts.QueryComplexity.AdversarySearch.MarkedSupport.markLaw H hH) N hN
  let p0 := pathLaw (fun mode => unitaryChannel (finiteBaseline W N mode)
    (finiteBaseline_unitary W N hN mode)) (fun _ => 0) Q ρ (basisDensity_pos r0) (basisDensity_trace_re r0)
  let ph := fun h : Fin H × Fin N => pathLaw (fun mode => unitaryChannel (familyOracle W τ h mode)
    (familyOracle_unitary W τ hτ.le hτ1 h mode)) (labelResponse τ normal h)
    Q ρ (basisDensity_pos r0) (basisDensity_trace_re r0)
  apply decision_joint_budget μ p0 ph vote
  · rcases hbase with ⟨G,hG,hgood⟩
    exact slack_baseline_majority_error (finiteBaseline W N) (finiteBaseline_unitary W N hN)
      (fun _ => 0) P words φ (literalOutput (⟨0,hN⟩ : Fin N) 0) (.inl false) (.inl true)
      τ hτ hτ1 n hn hbudget r0 G hG hgood (literalOutput_baseline_entry _) ρ
      (basisDensity_pos r0) (basisDensity_trace_re r0)
  · intro h
    rcases hhidden h with ⟨G,hG,hgood⟩
    exact slack_hidden_majority_error (familyOracle W τ h) (familyOracle_unitary W τ hτ.le hτ1 h)
      (labelResponse τ normal h) P words φ (literalOutput h.2 (spikePoint H τ h.1))
      (.inl false) (.inl true) τ hτ hτ1 n hn hbudget r0 G hG hgood
      (literalOutput_hidden_entry _ _ _ hτ.le) ρ (basisDensity_pos r0) (basisDensity_trace_re r0)
  · have hb := rational_family_support_hybrid H hH N hN τ hτ.le hτ1 normal hnormal
      Q ρ (basisDensity_pos r0) (basisDensity_trace_re r0) (1001*s)
      (reduction_support_cap P words φ (.inl true) n s r0 hs)
    have hd : (queryDepth Q : ℝ) ≤ (1001*(queryDepth P+n*quse) : ℕ) := by
      exact_mod_cast reduction_depth P words φ (.inl true) n quse r0 hq
    have he := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hd (by norm_num : (0 : ℝ) ≤ 4))
      (Real.sqrt_nonneg (N : ℝ))
    have ht := hb.trans (add_le_add he le_rfl)
    have hsym : (∑ hp,|(Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointTranscript.jointLaw μ (fun _ => p0)).prob hp-
        (Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointTranscript.jointLaw μ ph).prob hp|)=
        ∑ hp,|(Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointTranscript.jointLaw μ ph).prob hp-
          (Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointTranscript.jointLaw μ (fun _ => p0)).prob hp| := by
      apply Finset.sum_congr rfl
      intro hp _
      exact abs_sub_comm _ _
    rw [hsym]
    exact ht

end Qatlib.Papers.CrouzeixLS26.AccessLower.BlockSampling
