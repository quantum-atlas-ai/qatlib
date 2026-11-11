/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CrouzeixLS26.AccessLower.PointSupportBits
import Qatlib.Concepts.ChoiKraus.ChoiKrausChar.ChannelStructure
import Qatlib.Concepts.ChannelTheory.Stinespring.ChannelStructureStinespring
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Constructor.FrameTransport
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Constructor.BasisFrame
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Constructor.ConstructorPromise
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

open Qatlib.Concepts.BlockEncoding.LCU

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Papers.CrouzeixLS26.AccessLower.Coordinate
open Qatlib.Concepts.BlockEncoding
/-! Static known left/right output frames reduce to the actual coordinate-
readout program without changing oracle/support queries. The alignments are
derived from frozen unitary column completion and depend only on the record's
known frame matrices and a fixed slot map, never the hidden oracle or target.
Invalid failed frames use a unitary identity fallback; no record is removed.
The actual finite point-output precision lower bound follows for these frames.

The noncomputable known-matrix choices enlarge the lower-bound simulator's
power. They are not efficient frame production, finite-gate synthesis or a
positive query algorithm. Oracle-dependent frames, record-varying dimension,
approximate frame production, original-machine normal forms and expected
budgets remain outside this result. Original G1–G4 stay unchanged. -/

set_option autoImplicit false
noncomputable section



open Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Constructor Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointAmplify Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointTranscript Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol Qatlib.Concepts.QueryComplexity.AdversarySearch.MarkedSupport Qatlib.Foundations.OpCalculus.ContourCalc
namespace Qatlib.Papers.CrouzeixLS26.AccessLower.BlockSampling
open Qatlib Matrix Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol MarkedHalmos
open scoped BigOperators Classical ComplexOrder

/-- Fixed known output slots in the same actual oracle workspace. The only
selected spectator value comes from the known initial basis label. -/
def standardSlots (W : Type) [Fintype W] [DecidableEq W] (N : ℕ)
    (r0 : Fin (queryDim W N)) (i : System N) : Fin (queryDim W N) :=
  finiteEquiv W N ⟨⟨splitBasis N (false,i),true⟩,((finiteEquiv W N).symm r0).2⟩

/-- The restricted-access construction satisfies `standardSlots_injective` under the complete displayed premises. -/
theorem standardSlots_injective (W : Type) [Fintype W] [DecidableEq W] (N : ℕ)
    (r0 : Fin (queryDim W N)) : Function.Injective (standardSlots W N r0) := by
  intro i j hij
  have h1 := (finiteEquiv W N).injective hij
  have h2 := congrArg (fun p : QueryBasis W N => p.1.1) h1
  exact congrArg Prod.snd ((splitBasis N).injective h2)

/-- Actual baseline/every-hidden literal correctness with record-dependent
known frames, fixed before the hidden parameter. No alignment witness is input. -/
def framedPrecisionPromise (W : Type) [Fintype W] [DecidableEq W]
    (t : ℕ) (ht : 2 ≤ t) (R : ℕ) (encode : ℝ → ℝ → Fin R) (normal : ℝ → ℂ)
    (P : Program (queryDim W (precisionMarks t)) R)
    (words : Path P → List (OutputGate (queryDim W (precisionMarks t))))
    (L Rf : Path P → Matrix (Fin (queryDim W (precisionMarks t))) (System (precisionMarks t)) ℂ)
    (r0 : Fin (queryDim W (precisionMarks t))) : Prop :=
  framedPromise (finiteBaseline W (precisionMarks t))
    (finiteBaseline_unitary W (precisionMarks t) (precisionMarks_pos t ht))
    (pointAnswer encode normal (⟨0,precisionMarks_pos t ht⟩ : Fin (precisionMarks t)) 0)
    P words L Rf (literalOutput (⟨0,precisionMarks_pos t ht⟩ : Fin (precisionMarks t)) 0)
      (precisionTau t) r0 ∧
  ∀ h : Fin t × Fin (precisionMarks t),framedPromise (familyOracle W (precisionTau t) h)
    (familyOracle_unitary W (precisionTau t) (precision_budget t ht).1.le (precision_budget t ht).2.1 h)
    (pointAnswer encode normal h.2 (spikePoint t (precisionTau t) h.1)) P words L Rf
    (literalOutput h.2 (spikePoint t (precisionTau t) h.1)) (precisionTau t) r0

/-- The restricted-access construction satisfies `framed_precision_cost_lower` under the complete displayed premises. -/
theorem framed_precision_cost_lower (W : Type) [Fintype W] [DecidableEq W]
    (t : ℕ) (ht : 2 ≤ t) (R : ℕ) (encode : ℝ → ℝ → Fin R)
    (normal : ℝ → ℂ) (hnormal : ∀ a,‖normal a‖=1)
    (P : Program (queryDim W (precisionMarks t)) R)
    (words : Path P → List (OutputGate (queryDim W (precisionMarks t))))
    (L Rf : Path P → Matrix (Fin (queryDim W (precisionMarks t))) (System (precisionMarks t)) ℂ)
    (r0 : Fin (queryDim W (precisionMarks t))) (quse s : ℕ)
    (hq : ∀ p,wordQueries (words p) ≤ quse) (hs : ∀ p,(pathCharge P p).2 ≤ s)
    (hc : framedPrecisionPromise W t ht R encode normal P words L Rf r0) :
    (t : ℝ)/192192 ≤ ((queryDepth P+quse+s : ℕ) : ℝ) := by
  let φ := standardSlots W (precisionMarks t) r0
  have hφ := standardSlots_injective W (precisionMarks t) r0
  let gs := fun p => coordinateWord φ hφ (L p) (Rf p) (words p)
  have hp : precisionPromise W t ht R encode normal P gs (fun _ => φ) r0 := by
    constructor
    · exact framedPromise_coordinate φ hφ _ _ _ P words L Rf _ _ r0 hc.1
    · intro h
      exact framedPromise_coordinate φ hφ _ _ _ P words L Rf _ _ r0 (hc.2 h)
  have hq' : ∀ p,wordQueries (gs p) ≤ quse := by
    intro p
    dsimp [gs]
    rw [coordinateWord_queries]
    exact hq p
  exact point_precision_cost_lower W t ht R encode normal hnormal P gs (fun _ => φ) r0 quse s hq' hs hp

/-- Actual rounded point answers and arbitrary known static output frames
at each precision. The frame normalizers contain no hidden oracle data. -/
theorem no_polynomial_framed_point_constructor (W : ℕ → Type)
    [∀ k,Fintype (W k)] [∀ k,DecidableEq (W k)]
    (normal : ℕ → ℝ → ℂ) (hnormal : ∀ k a,‖normal k a‖=1)
    (P : ∀ k,Program (queryDim (W k) (precisionMarks (2^k))) (2^(2*k+10)))
    (words : ∀ k,Path (P k) → List (OutputGate (queryDim (W k) (precisionMarks (2^k)))))
    (L Rf : ∀ k,Path (P k) → Matrix (Fin (queryDim (W k) (precisionMarks (2^k)))) (System (precisionMarks (2^k))) ℂ)
    (r0 : ∀ k,Fin (queryDim (W k) (precisionMarks (2^k))))
    (quse s : ℕ → ℕ)
    (hq : ∀ k p,wordQueries (words k p) ≤ quse k)
    (hs : ∀ k p,(pathCharge (P k) p).2 ≤ s k)
    (hc : ∀ k (hk : 1 ≤ k),framedPrecisionPromise (W k) (2^k) (precision_two_pow k hk)
      (2^(2*k+10)) (supportBits (2*k+7)) (normal k) (P k) (words k) (L k) (Rf k) (r0 k))
    (C : ℝ) (d K : ℕ)
    (hpoly : ∀ k,K ≤ k → ((queryDepth (P k)+quse k+s k : ℕ) : ℝ) ≤ C*(k : ℝ)^d) : False := by
  apply exponential_cost_not_polynomial (fun k => queryDepth (P k)+quse k+s k) _ C d K hpoly
  intro k hk
  have hb := framed_precision_cost_lower (W k) (2^k) (precision_two_pow k hk)
    (2^(2*k+10)) (supportBits (2*k+7)) (normal k) (hnormal k) (P k) (words k) (L k) (Rf k)
    (r0 k) (quse k) (s k) (hq k) (hs k) (hc k hk)
  simpa only [Nat.cast_pow,Nat.cast_ofNat] using hb

end Qatlib.Papers.CrouzeixLS26.AccessLower.BlockSampling
