/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CrouzeixLS26.AccessLower.BlockSamplingReadout
import Qatlib.Papers.CrouzeixLS26.AccessLower.RationalPhaseSupport
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Constructor.ConstructorPromise
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Constructor.BasisFrame
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Constructor.FrameTransport
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Constructor.SlackPromise
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
/-! A necessary query/support tradeoff for the actual Jordan/Halmos family
and one fixed finite constructor with known coordinate output frames. The
literal output specification uses the TRUE numerical-range maximum. The
same-program block guarantee, actual sampling/majority success and derived
marked-oracle/support hybrid imply a constant distinguishing budget.

Constructor correctness is the reductio premise, not an algorithm supplied
by this theorem. All failed records remain. This finite known-frame result
supplies neither arbitrary-machine normal forms nor variable-width/frame or
expected-budget transport. It does not cover free M/global boundary data,
classical matrix access, coherent support, or settle original G1–G4. -/

set_option autoImplicit false
noncomputable section
open Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Constructor Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointAmplify Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointTranscript Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol Qatlib.Concepts.QueryComplexity.AdversarySearch.MarkedSupport Qatlib.Foundations.OpCalculus.ContourCalc
namespace Qatlib.Papers.CrouzeixLS26.AccessLower.BlockSampling
open Qatlib Matrix Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol MarkedHalmos
open scoped BigOperators Classical ComplexOrder

/-- A single fixed Boolean decoder distinguishes the baseline and every
hidden input. The register H is analysis-only, held with the complete record. -/
theorem decision_joint_budget {H T : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
    (μ : FinDist H) (p0 : FinDist T) (p : H → FinDist T) (vote : T → Bool) (δ : ℝ)
    (hb : (∑ t∈Finset.univ.filter (fun t => vote t≠true),p0.prob t) ≤ 1/3)
    (hh : ∀ h,(∑ t∈Finset.univ.filter (fun t => vote t≠false),(p h).prob t) ≤ 1/3)
    (hj : (∑ ht,|(Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointTranscript.jointLaw μ (fun _ => p0)).prob ht-
      (Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointTranscript.jointLaw μ p).prob ht|)/2 ≤ δ) : 1/3 ≤ δ := by
  let E : Finset (H × T) := Finset.univ.filter (fun ht => vote ht.2=true)
  have hfactor (q : H → FinDist T) :
      (∑ ht∈E,(Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointTranscript.jointLaw μ q).prob ht)=
        ∑ h,μ.prob h*(∑ t∈Finset.univ.filter (fun t => vote t=true),(q h).prob t) := by
    rw [Finset.sum_filter,Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro h _
    rw [Finset.mul_sum,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro t _
    by_cases hv : vote t=true <;> simp [Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointTranscript.jointLaw,hv]
  have heq : (∑ t∈Finset.univ.filter (fun t => vote t=true),p0.prob t)+
      (∑ t∈Finset.univ.filter (fun t => vote t≠true),p0.prob t)=1 := by
    rw [Finset.sum_filter,Finset.sum_filter,←Finset.sum_add_distrib]
    calc
      _ = ∑ t,p0.prob t := by
        apply Finset.sum_congr rfl
        intro t _
        by_cases hv : vote t=true <;> simp [hv]
      _ = 1 := p0.sum_one
  have hb0 : (2/3 : ℝ) ≤ ∑ t∈Finset.univ.filter (fun t => vote t=true),p0.prob t := by linarith
  have hbase : (2/3 : ℝ) ≤ ∑ ht∈E,(Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointTranscript.jointLaw μ (fun _ => p0)).prob ht := by
    rw [hfactor,←Finset.sum_mul,μ.sum_one,one_mul]
    exact hb0
  have hhidden : (∑ ht∈E,(Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointTranscript.jointLaw μ p).prob ht) ≤ 1/3 := by
    rw [hfactor]
    calc
      _ ≤ ∑ h,μ.prob h*(1/3) := by
        apply Finset.sum_le_sum
        intro h _
        apply mul_le_mul_of_nonneg_left _ (μ.nonneg h)
        have hs : (Finset.univ.filter (fun t => vote t=true))=
            Finset.univ.filter (fun t => vote t≠false) := by
          ext t
          cases hv : vote t <;> simp [hv]
        rw [hs]
        exact hh h
      _ = 1/3 := by rw [←Finset.sum_mul,μ.sum_one,one_mul]
  have hcond : (∑ h,μ.prob h*((∑ t,|p0.prob t-(p h).prob t|)/2)) ≤ δ := by
    rw [←Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointTranscript.joint_variation_identity μ (fun _ => p0) p]
    exact hj
  have ht := Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointTranscript.hidden_event_transfer μ (fun _ => p0) p E δ hcond
  linarith

/-- Literal normalization by the TRUE polynomial-X maximum. This is a
correctness specification, never an extra scalar input to the program. -/
def literalOutput {N : ℕ} (w : Fin N) (z : ℂ) : Matrix (System N) (System N) ℂ :=
  (1/((5/2 : ℝ)*sSup ((fun a : ℂ => ‖a‖) '' Qatlib.Foundations.OpCalculus.ContourCalc.matrixNumericalRange (target w z)))) • target w z

/-- The restricted-access construction satisfies `literalOutput_baseline_entry` under the complete displayed premises. -/
theorem literalOutput_baseline_entry {N : ℕ} (w : Fin N) :
    literalOutput w 0 (.inl false) (.inl true)=(4/5 : ℂ) := by
  unfold literalOutput
  rw [(target_actual_maximum w 0).csSup_eq]
  norm_num [target,compressedTarget,Qatlib.Papers.CrouzeixLS26.AccessLower.SharedOracleInputLower.jordan]

/-- The restricted-access construction satisfies `literalOutput_hidden_entry` under the complete displayed premises. -/
theorem literalOutput_hidden_entry {H N : ℕ} (w : Fin N) (k : Fin H) (τ : ℝ) (hτ : 0 ≤ τ) :
    literalOutput w (spikePoint H τ k) (.inl false) (.inl true)=((4/(5*(1+2*τ)) : ℝ) : ℂ) := by
  unfold literalOutput
  rw [(spike_actual_maximum w τ k hτ).csSup_eq]
  norm_num [target,compressedTarget,Qatlib.Papers.CrouzeixLS26.AccessLower.SharedOracleInputLower.jordan]
  field_simp
  ring


/-- Construction for family Oracle in the block output support lower model. -/
def familyOracle (W : Type) [Fintype W] [DecidableEq W] {H N : ℕ}
    (τ : ℝ) (h : Fin H × Fin N) : Bool → Operator (queryDim W N) :=
  finiteOracle W h.2 (spikePoint H τ h.1)

/-- The restricted-access construction satisfies `familyOracle_unitary` under the complete displayed premises. -/
theorem familyOracle_unitary (W : Type) [Fintype W] [DecidableEq W] {H N : ℕ}
    (τ : ℝ) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1/4) (h : Fin H × Fin N) (mode : Bool) :
    familyOracle W τ h mode∈Matrix.unitaryGroup (Fin (queryDim W N)) ℂ :=
  finiteOracle_unitary W h.2 _ (spikePoint_normSq_le_one H τ h.1 hτ hτ1) mode

/-- Necessary costs for a single fixed finite constructor and known output
frame in the actual hard input family. No whole-program distance, visibility,
free maximum, returned-description law or readout success is supplied. -/
theorem literal_block_output_budget (W : Type) [Fintype W] [DecidableEq W]
    (H : ℕ) (hH : 0<H) (N : ℕ) (hN : 0<N) (τ : ℝ) (hτ : 0<τ) (hτ1 : τ ≤ 1/4)
    (normal : ℝ → ℂ) (hnormal : ∀ a,‖normal a‖=1)
    (P : Program (queryDim W N) (H+1))
    (words : Path P → List (OutputGate (queryDim W N)))
    (φ : Path P → System N → Fin (queryDim W N)) (r0 : Fin (queryDim W N))
    (n : ℕ) (hn : 0<n) (hbudget : 16/τ^2 ≤ (n : ℝ)) (quse s : ℕ)
    (hq : ∀ p,wordQueries (words p) ≤ quse) (hs : ∀ p,(pathCharge P p).2 ≤ s)
    (hbase : constructorPromise (finiteBaseline W N) (finiteBaseline_unitary W N hN) (fun _ => 0)
      P words φ (literalOutput (⟨0,hN⟩ : Fin N) 0) τ r0)
    (hhidden : ∀ h : Fin H × Fin N,constructorPromise (familyOracle W τ h)
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
    exact baseline_majority_error (finiteBaseline W N) (finiteBaseline_unitary W N hN)
      (fun _ => 0) P words φ (literalOutput (⟨0,hN⟩ : Fin N) 0) (.inl false) (.inl true)
      τ hτ hτ1 n hn hbudget r0 G hG hgood (literalOutput_baseline_entry _) ρ
      (basisDensity_pos r0) (basisDensity_trace_re r0)
  · intro h
    rcases hhidden h with ⟨G,hG,hgood⟩
    exact hidden_majority_error (familyOracle W τ h) (familyOracle_unitary W τ hτ.le hτ1 h)
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
