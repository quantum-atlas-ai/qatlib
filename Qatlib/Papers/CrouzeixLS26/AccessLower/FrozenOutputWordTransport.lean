/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CrouzeixLS26.AccessLower.KnownFrameOutputTransport
import Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointWord
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.SourceWordTransport
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Constructor.BasisFrame
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Constructor.ConstructorPromise
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
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointAmplify
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointTranscript
import Qatlib.Foundations.OpCalculus.ContourCalc.NumericalRange
import Qatlib.Foundations.OpCalculus.ContourCalc.NumericalRangeConvex

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.BlockEncoding
/-! Actual Frozen AdjointStep output words enter the finite point-output lower
bound with known static matrix frames. Operator-product source order becomes
chronological output order; both query directions stay paid. The real Frozen
adjoint circuit supplies inverse semantics and retains its query count.
Coordinate normalization of that inverse swaps the left and right frames.

Known invalid source gate lists use an empty-word fallback on their existing
records. Only good records require legal source gates and block correctness.
This mathematical validation uses no hidden oracle data; it is not finite-time
matrix legality, primitive synthesis or a universal machine normal form.
Variable branch dimensions, oracle-dependent/approximate frames and expected
budgets remain open, as do the positive given-M model and original G1–G4. -/

set_option autoImplicit false
noncomputable section


open Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Constructor Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointAmplify Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointTranscript Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol Qatlib.Concepts.QueryComplexity.AdversarySearch.MarkedSupport Qatlib.Foundations.OpCalculus.ContourCalc
namespace Qatlib.Papers.CrouzeixLS26.AccessLower.BlockSampling
open Qatlib Matrix Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol MarkedHalmos SignalProcessing
open scoped BigOperators Classical ComplexOrder

/-- The restricted-access construction satisfies `source_baseline_inverse_mode` under the complete displayed premises. -/
private theorem source_baseline_inverse_mode (W : Type) [Fintype W] [DecidableEq W] (N : ℕ) :
    finiteBaseline W N false=(finiteBaseline W N true).conjTranspose := by
  have hd : controlledBaseline N false=(controlledBaseline N true).conjTranspose := by
    simp only [controlledBaseline,Matrix.blockDiagonal_conjTranspose]
    congr 1
    funext c
    cases c <;> simp [directedBaseline]
  have hw : workspaceBaseline W N false=(workspaceBaseline W N true).conjTranspose := by
    simp only [workspaceBaseline,tensorGate_conjTranspose,Matrix.conjTranspose_one,hd]
  unfold finiteBaseline
  rw [hw]
  rfl

/-- The original frozen operator-product source word is the returned object.
Correctness requires valid source gates on good records only. -/
def sourcePrecisionPromise (W : Type) [Fintype W] [DecidableEq W]
    (t : ℕ) (ht : 2 ≤ t) (R : ℕ) (encode : ℝ → ℝ → Fin R) (normal : ℝ → ℂ)
    (P : Program (queryDim W (precisionMarks t)) R)
    (cs : Path P → List (AdjointStep (Fin (queryDim W (precisionMarks t)))))
    (L Rf : Path P → Matrix (Fin (queryDim W (precisionMarks t))) (System (precisionMarks t)) ℂ)
    (r0 : Fin (queryDim W (precisionMarks t))) : Prop :=
  sourceFramedPromise (finiteBaseline W (precisionMarks t))
    (finiteBaseline_unitary W (precisionMarks t) (precisionMarks_pos t ht))
    (pointAnswer encode normal (⟨0,precisionMarks_pos t ht⟩ : Fin (precisionMarks t)) 0)
    P cs L Rf (literalOutput (⟨0,precisionMarks_pos t ht⟩ : Fin (precisionMarks t)) 0)
      (precisionTau t) r0 ∧
  ∀ h : Fin t × Fin (precisionMarks t),sourceFramedPromise (familyOracle W (precisionTau t) h)
    (familyOracle_unitary W (precisionTau t) (precision_budget t ht).1.le (precision_budget t ht).2.1 h)
    (pointAnswer encode normal h.2 (spikePoint t (precisionTau t) h.1)) P cs L Rf
    (literalOutput h.2 (spikePoint t (precisionTau t) h.1)) (precisionTau t) r0

/-- The restricted-access construction satisfies `source_precision_cost_lower` under the complete displayed premises. -/
theorem source_precision_cost_lower (W : Type) [Fintype W] [DecidableEq W]
    (t : ℕ) (ht : 2 ≤ t) (R : ℕ) (encode : ℝ → ℝ → Fin R)
    (normal : ℝ → ℂ) (hnormal : ∀ a,‖normal a‖=1)
    (P : Program (queryDim W (precisionMarks t)) R)
    (cs : Path P → List (AdjointStep (Fin (queryDim W (precisionMarks t)))))
    (L Rf : Path P → Matrix (Fin (queryDim W (precisionMarks t))) (System (precisionMarks t)) ℂ)
    (r0 : Fin (queryDim W (precisionMarks t))) (quse s : ℕ)
    (hq : ∀ p,adjointQueryCount (cs p) ≤ quse) (hs : ∀ p,(pathCharge P p).2 ≤ s)
    (hc : sourcePrecisionPromise W t ht R encode normal P cs L Rf r0) :
    (t : ℝ)/192192 ≤ ((queryDepth P+quse+s : ℕ) : ℝ) := by
  have hp : framedPrecisionPromise W t ht R encode normal P (fun p => safeSourceWord (cs p)) L Rf r0 := by
    constructor
    · exact sourceFramedPromise_transport _ _ (source_baseline_inverse_mode W _) _ P cs L Rf _ _ r0 hc.1
    · intro h
      exact sourceFramedPromise_transport _ _ (finiteOracle_inverse_mode W h.2 (spikePoint t (precisionTau t) h.1))
        _ P cs L Rf _ _ r0 (hc.2 h)
  have hq' : ∀ p,wordQueries (safeSourceWord (cs p)) ≤ quse :=
    fun p => (safeSourceWord_queries_le (cs p)).trans (hq p)
  exact framed_precision_cost_lower W t ht R encode normal hnormal P _ L Rf r0 quse s hq' hs hp

/-- Eventual polynomial queries are impossible for actual frozen source
words with known static matrix frames and the certified linear-bit point rule. -/
theorem no_polynomial_source_constructor (W : ℕ → Type)
    [∀ k,Fintype (W k)] [∀ k,DecidableEq (W k)]
    (normal : ℕ → ℝ → ℂ) (hnormal : ∀ k a,‖normal k a‖=1)
    (P : ∀ k,Program (queryDim (W k) (precisionMarks (2^k))) (2^(2*k+10)))
    (cs : ∀ k,Path (P k) → List (AdjointStep (Fin (queryDim (W k) (precisionMarks (2^k))))))
    (L Rf : ∀ k,Path (P k) → Matrix (Fin (queryDim (W k) (precisionMarks (2^k)))) (System (precisionMarks (2^k))) ℂ)
    (r0 : ∀ k,Fin (queryDim (W k) (precisionMarks (2^k))))
    (quse s : ℕ → ℕ)
    (hq : ∀ k p,adjointQueryCount (cs k p) ≤ quse k)
    (hs : ∀ k p,(pathCharge (P k) p).2 ≤ s k)
    (hc : ∀ k (hk : 1 ≤ k),sourcePrecisionPromise (W k) (2^k) (precision_two_pow k hk)
      (2^(2*k+10)) (supportBits (2*k+7)) (normal k) (P k) (cs k) (L k) (Rf k) (r0 k))
    (C : ℝ) (d K : ℕ)
    (hpoly : ∀ k,K ≤ k → ((queryDepth (P k)+quse k+s k : ℕ) : ℝ) ≤ C*(k : ℝ)^d) : False := by
  apply exponential_cost_not_polynomial (fun k => queryDepth (P k)+quse k+s k) _ C d K hpoly
  intro k hk
  have hb := source_precision_cost_lower (W k) (2^k) (precision_two_pow k hk)
    (2^(2*k+10)) (supportBits (2*k+7)) (normal k) (hnormal k) (P k) (cs k) (L k) (Rf k)
    (r0 k) (quse k) (s k) (hq k) (hs k) (hc k hk)
  simpa only [Nat.cast_pow,Nat.cast_ofNat] using hb

end Qatlib.Papers.CrouzeixLS26.AccessLower.BlockSampling
