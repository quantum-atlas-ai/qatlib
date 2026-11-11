/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.BudgetTruncation
import Qatlib.Papers.CrouzeixLS26.AccessLower.BudgetSamplingReadout
import Qatlib.Papers.CrouzeixLS26.AccessLower.FrozenOutputWordTransport
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Constructor.TruncatedPromise
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.ExpectedCost
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Constructor.BasisFrame
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Constructor.ConstructorPromise
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Constructor.FrameTransport
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Constructor.SlackPromise
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Constructor.TranslatedPromise
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.AnswerTransport
import Qatlib.Concepts.QueryComplexity.AdversarySearch.MarkedSupport.MarkedColumns
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
open Qatlib.Concepts.AdaptiveCP.BranchTrace
/-! Expected-query lower bounds for the actual finite constructor. Source
preparation, the returned query word, and classical support calls are charged
under the same actual complete-record law, including failed outputs. Finite
tree truncation supplies the worst-path caps; no tail coupling or distance
certificate is an input. This does not cover general unbounded machines,
branch-varying quantum dimensions, or free-M positive models. -/
set_option autoImplicit false
set_option maxRecDepth 2048
noncomputable section


open Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Constructor Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointAmplify Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointTranscript Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol Qatlib.Concepts.QueryComplexity.AdversarySearch.MarkedSupport Qatlib.Foundations.OpCalculus.ContourCalc
namespace Qatlib.Papers.CrouzeixLS26.AccessLower.BlockSampling
open Qatlib Matrix Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol MarkedHalmos
open scoped BigOperators Classical ComplexOrder

/-- Actual baseline/every-hidden expected costs suffice. The all-path caps
are consequences of finite execution truncation, not premises on P. -/
theorem label_expected_precision_cost_lower (W : Type) [Fintype W] [DecidableEq W]
    (t : ℕ) (ht : 2 ≤ t) (normal : ℝ → ℂ) (hnormal : ∀ a,‖normal a‖=1)
    (P : Program (queryDim W (precisionMarks t)) (t+1))
    (words : Path P → List (OutputGate (queryDim W (precisionMarks t))))
    (φ : Path P → System (precisionMarks t) → Fin (queryDim W (precisionMarks t)))
    (r0 : Fin (queryDim W (precisionMarks t))) (B : ℝ)
    (hbase : constructorPromise (finiteBaseline W (precisionMarks t))
      (finiteBaseline_unitary W (precisionMarks t) (precisionMarks_pos t ht)) (fun _ => 0)
      P words φ (literalOutput (⟨0,precisionMarks_pos t ht⟩ : Fin (precisionMarks t)) 0) (precisionTau t) r0)
    (hhidden : ∀ h : Fin t × Fin (precisionMarks t),constructorPromise (familyOracle W (precisionTau t) h)
      (familyOracle_unitary W (precisionTau t) (precision_budget t ht).1.le (precision_budget t ht).2.1 h)
      (labelResponse (precisionTau t) normal h) P words φ
      (literalOutput h.2 (spikePoint t (precisionTau t) h.1)) (precisionTau t) r0)
    (hcost0 : expectedCost (fun mode => unitaryChannel (finiteBaseline W (precisionMarks t) mode)
      (finiteBaseline_unitary W (precisionMarks t) (precisionMarks_pos t ht) mode)) (fun _ => 0) r0 P
      (fun p => wordQueries (words p)) ≤ B)
    (hcosth : ∀ h : Fin t × Fin (precisionMarks t),expectedCost
      (fun mode => unitaryChannel (familyOracle W (precisionTau t) h mode)
        (familyOracle_unitary W (precisionTau t) (precision_budget t ht).1.le (precision_budget t ht).2.1 h mode))
      (labelResponse (precisionTau t) normal h) r0 P (fun p => wordQueries (words p)) ≤ B) :
    (t : ℝ)/192192 ≤ ((3*Nat.ceil (24*B) : ℕ) : ℝ) := by
  let K := Nat.ceil (24*B)
  let Q := truncateProgram P K K
  let ws := truncatedWords P words K
  let fs := truncatedFrame P φ r0 K
  have hK : 24*B ≤ (K : ℝ) := Nat.le_ceil _
  have hp := precision_budget t ht
  have hb := slack_literal_block_output_budget W t (by omega) (precisionMarks t)
    (precisionMarks_pos t ht) (precisionTau t) hp.1 hp.2.1 normal hnormal Q ws fs r0
    (precisionSamples t) hp.2.2.1 hp.2.2.2.le K K
    (truncatedWords_queries P words K) (truncate_support_le P K K)
    (truncated_constructorPromise _ _ _ P words φ _ _ r0 B K hbase hcost0 hK)
    (fun h => truncated_constructorPromise _ _ _ P words φ _ _ r0 B K (hhidden h) (hcosth h) hK)
  have hl := precision_cost_of_budget t (queryDepth Q) K K ht hb
  have hcap : queryDepth Q+K+K ≤ 3*K := by
    have hd := truncate_depth_le P K K
    change queryDepth Q ≤ K at hd
    omega
  exact hl.trans (by exact_mod_cast hcap)

/-- Uniform expected total cost in the actual point-answer input family.
The use charge may be a typed word count or the original Frozen source count. -/
def precisionExpectedBound (W : Type) [Fintype W] [DecidableEq W]
    (t : ℕ) (ht : 2 ≤ t) (R : ℕ) (encode : ℝ → ℝ → Fin R) (normal : ℝ → ℂ)
    (P : Program (queryDim W (precisionMarks t)) R) (use : Path P → ℕ)
    (r0 : Fin (queryDim W (precisionMarks t))) (B : ℝ) : Prop :=
  expectedCost (fun mode => unitaryChannel (finiteBaseline W (precisionMarks t) mode)
    (finiteBaseline_unitary W (precisionMarks t) (precisionMarks_pos t ht) mode))
    (pointAnswer encode normal (⟨0,precisionMarks_pos t ht⟩ : Fin (precisionMarks t)) 0) r0 P use ≤ B ∧
  ∀ h : Fin t × Fin (precisionMarks t),expectedCost
    (fun mode => unitaryChannel (familyOracle W (precisionTau t) h mode)
      (familyOracle_unitary W (precisionTau t) (precision_budget t ht).1.le (precision_budget t ht).2.1 h mode))
    (pointAnswer encode normal h.2 (spikePoint t (precisionTau t) h.1)) r0 P use ≤ B

/-- No counterfactual-path upper bound is needed on the original finite
point-answer constructor or its returned word. -/
theorem point_expected_precision_cost_lower (W : Type) [Fintype W] [DecidableEq W]
    (t : ℕ) (ht : 2 ≤ t) (R : ℕ) (encode : ℝ → ℝ → Fin R)
    (normal : ℝ → ℂ) (hnormal : ∀ a,‖normal a‖=1)
    (P : Program (queryDim W (precisionMarks t)) R)
    (words : Path P → List (OutputGate (queryDim W (precisionMarks t))))
    (φ : Path P → System (precisionMarks t) → Fin (queryDim W (precisionMarks t)))
    (r0 : Fin (queryDim W (precisionMarks t))) (B : ℝ)
    (hc : precisionPromise W t ht R encode normal P words φ r0)
    (hcost : precisionExpectedBound W t ht R encode normal P (fun p => wordQueries (words p)) r0 B) :
    (t : ℝ)/192192 ≤ ((3*Nat.ceil (24*B) : ℕ) : ℝ) := by
  let decode := fun a l => encode a (decodeLabel t (precisionTau t) (normal a) l)
  let Q := translateAnswerMap decode P
  let ws := fun q => words (translatedPath decode P q)
  let fs := fun q => φ (translatedPath decode P q)
  have hzero : (fun a => decode a (0 : Fin (t+1)))=
      pointAnswer encode normal (⟨0,precisionMarks_pos t ht⟩ : Fin (precisionMarks t)) 0 := by
    funext a
    exact congrArg (encode a) (decode_zero_is_baseline _ _ _ (hnormal a))
  have hdecode (h : Fin t × Fin (precisionMarks t)) :
      (fun a => decode a (labelResponse (precisionTau t) normal h a))=
        pointAnswer encode normal h.2 (spikePoint t (precisionTau t) h.1) := by
    funext a
    exact congrArg (encode a) (label_decode_exact _ normal h a (hnormal a))
  apply label_expected_precision_cost_lower W t ht normal hnormal Q ws fs r0 B
  · apply translated_constructorPromise decode
    rw [hzero]
    exact hc.1
  · intro h
    apply translated_constructorPromise decode
    rw [hdecode h]
    exact hc.2 h
  · dsimp only [Q,ws]
    rw [translated_expectedCost decode _ _ r0 P (fun p => wordQueries (words p)),hzero]
    exact hcost.1
  · intro h
    dsimp only [Q,ws]
    rw [translated_expectedCost decode _ _ r0 P (fun p => wordQueries (words p)),hdecode h]
    exact hcost.2 h

/-- The restricted-access construction satisfies `precisionExpectedBound_nonneg` under the complete displayed premises. -/
theorem precisionExpectedBound_nonneg (W : Type) [Fintype W] [DecidableEq W]
    (t : ℕ) (ht : 2 ≤ t) (R : ℕ) (encode : ℝ → ℝ → Fin R) (normal : ℝ → ℂ)
    (P : Program (queryDim W (precisionMarks t)) R) (use : Path P → ℕ)
    (r0 : Fin (queryDim W (precisionMarks t))) (B : ℝ)
    (hcost : precisionExpectedBound W t ht R encode normal P use r0 B) : 0 ≤ B :=
  (expectedCost_nonneg _ _ r0 P use).trans hcost.1

/-- The restricted-access construction satisfies `precisionExpectedBound_mono` under the complete displayed premises. -/
theorem precisionExpectedBound_mono (W : Type) [Fintype W] [DecidableEq W]
    (t : ℕ) (ht : 2 ≤ t) (R : ℕ) (encode : ℝ → ℝ → Fin R) (normal : ℝ → ℂ)
    (P : Program (queryDim W (precisionMarks t)) R) (use use' : Path P → ℕ)
    (r0 : Fin (queryDim W (precisionMarks t))) (B : ℝ)
    (hle : ∀ p,use p ≤ use' p)
    (hcost : precisionExpectedBound W t ht R encode normal P use' r0 B) :
    precisionExpectedBound W t ht R encode normal P use r0 B :=
  ⟨(expectedCost_mono _ _ r0 P use use' hle).trans hcost.1,
    fun h => (expectedCost_mono _ _ r0 P use use' hle).trans (hcost.2 h)⟩

/-- The raw Frozen returned source, actual point replies and known static
frames feed the expected bound. Illegal bad code remains and costs its raw
query count; safe compilation and frame normalization can only reduce it. -/
theorem source_expected_precision_cost_lower (W : Type) [Fintype W] [DecidableEq W]
    (t : ℕ) (ht : 2 ≤ t) (R : ℕ) (encode : ℝ → ℝ → Fin R)
    (normal : ℝ → ℂ) (hnormal : ∀ a,‖normal a‖=1)
    (P : Program (queryDim W (precisionMarks t)) R)
    (cs : Path P → List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep (Fin (queryDim W (precisionMarks t)))))
    (L Rf : Path P → Matrix (Fin (queryDim W (precisionMarks t))) (System (precisionMarks t)) ℂ)
    (r0 : Fin (queryDim W (precisionMarks t))) (B : ℝ)
    (hc : sourcePrecisionPromise W t ht R encode normal P cs L Rf r0)
    (hcost : precisionExpectedBound W t ht R encode normal P
      (fun p => Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount (cs p)) r0 B) :
    (t : ℝ)/192192 ≤ 72*B+3 := by
  let φ := standardSlots W (precisionMarks t) r0
  have hφ := standardSlots_injective W (precisionMarks t) r0
  let ws := fun p => coordinateWord φ hφ (L p) (Rf p) (safeSourceWord (cs p))
  have hinv : finiteBaseline W (precisionMarks t) false=
      (finiteBaseline W (precisionMarks t) true).conjTranspose := by
    have hd : controlledBaseline (precisionMarks t) false=
        (controlledBaseline (precisionMarks t) true).conjTranspose := by
      simp only [controlledBaseline,Matrix.blockDiagonal_conjTranspose]
      congr 1
      funext c
      cases c <;> simp [directedBaseline]
    have hw : workspaceBaseline W (precisionMarks t) false=
        (workspaceBaseline W (precisionMarks t) true).conjTranspose := by
      simp only [workspaceBaseline,tensorGate_conjTranspose,Matrix.conjTranspose_one,hd]
    unfold finiteBaseline
    rw [hw]
    rfl
  have hp : precisionPromise W t ht R encode normal P ws (fun _ => φ) r0 := by
    constructor
    · apply framedPromise_coordinate φ hφ
      exact sourceFramedPromise_transport _ _ hinv _ P cs L Rf _ _ r0 hc.1
    · intro h
      apply framedPromise_coordinate φ hφ
      exact sourceFramedPromise_transport _ _ (finiteOracle_inverse_mode W h.2 (spikePoint t (precisionTau t) h.1))
        _ P cs L Rf _ _ r0 (hc.2 h)
  have hq : ∀ p,wordQueries (ws p) ≤ Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount (cs p) := by
    intro p
    rw [coordinateWord_queries]
    exact safeSourceWord_queries_le (cs p)
  have hc' := precisionExpectedBound_mono W t ht R encode normal P _ _ r0 B hq hcost
  have hl := point_expected_precision_cost_lower W t ht R encode normal hnormal P ws (fun _ => φ) r0 B hp hc'
  have hB := precisionExpectedBound_nonneg W t ht R encode normal P _ r0 B hcost
  have hk := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ 24*B)
  push_cast at hl
  linarith

/-- Even an eventual polynomial bound on the actual expected raw source
cost is impossible in this finite classical point model. The bit rule and
all source programs/frames are fixed before each hidden input. -/
theorem no_polynomial_expected_source_constructor (W : ℕ → Type)
    [∀ k,Fintype (W k)] [∀ k,DecidableEq (W k)]
    (normal : ℕ → ℝ → ℂ) (hnormal : ∀ k a,‖normal k a‖=1)
    (P : ∀ k,Program (queryDim (W k) (precisionMarks (2^k))) (2^(2*k+10)))
    (cs : ∀ k,Path (P k) → List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep (Fin (queryDim (W k) (precisionMarks (2^k))))))
    (L Rf : ∀ k,Path (P k) → Matrix (Fin (queryDim (W k) (precisionMarks (2^k)))) (System (precisionMarks (2^k))) ℂ)
    (r0 : ∀ k,Fin (queryDim (W k) (precisionMarks (2^k)))) (B : ℕ → ℝ)
    (hc : ∀ k (hk : 1 ≤ k),sourcePrecisionPromise (W k) (2^k) (precision_two_pow k hk)
      (2^(2*k+10)) (supportBits (2*k+7)) (normal k) (P k) (cs k) (L k) (Rf k) (r0 k))
    (hcost : ∀ k (hk : 1 ≤ k),precisionExpectedBound (W k) (2^k) (precision_two_pow k hk)
      (2^(2*k+10)) (supportBits (2*k+7)) (normal k) (P k)
      (fun p => Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount (cs k p)) (r0 k) (B k))
    (C : ℝ) (d K : ℕ) (hpoly : ∀ k,K ≤ k → B k ≤ C*(k : ℝ)^d) : False := by
  refine exponential_cost_not_polynomial (fun k => Nat.ceil (72*B k+3)) ?_ (72*|C|+4) d (max K 1) ?_
  · intro k hk
    have hb := source_expected_precision_cost_lower (W k) (2^k) (precision_two_pow k hk)
      (2^(2*k+10)) (supportBits (2*k+7)) (normal k) (hnormal k) (P k) (cs k) (L k) (Rf k)
      (r0 k) (B k) (hc k hk) (hcost k hk)
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using hb.trans (Nat.le_ceil (72*B k+3))
  · intro k hk
    have hk1 : 1 ≤ k := (le_max_right K 1).trans hk
    have hkK : K ≤ k := (le_max_left K 1).trans hk
    have hB := precisionExpectedBound_nonneg (W k) (2^k) (precision_two_pow k hk1)
      (2^(2*k+10)) (supportBits (2*k+7)) (normal k) (P k) _ (r0 k) (B k) (hcost k hk1)
    have hceil := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ 72*B k+3)
    have hpow : (1 : ℝ) ≤ (k : ℝ)^d := one_le_pow₀ (by exact_mod_cast hk1)
    have hupper := (hpoly k hkK).trans
      (mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg (Nat.cast_nonneg k) d))
    nlinarith

end Qatlib.Papers.CrouzeixLS26.AccessLower.BlockSampling
