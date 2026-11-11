/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CrouzeixLS26.AccessLower.BlockOutputReadout
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointTranscript
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointAmplify
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
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.SourceWordTransport
import Qatlib.Foundations.OpCalculus.ContourCalc.NumericalRange
import Qatlib.Foundations.OpCalculus.ContourCalc.NumericalRangeConvex

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Papers.CrouzeixLS26.AccessLower.Coordinate
/-! Success amplification for the fixed-normalization block-output reduction.
The finite constructor-output law is an input; the readout law and query ledger
are computed from the actual prepared AE execution. This does not construct a
constructor, compile its controlled descriptions, or prove the adaptive
input-oracle/support hybrid. -/
set_option autoImplicit false
set_option maxRecDepth 2048
noncomputable section
open Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Constructor Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointAmplify Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointTranscript Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol Qatlib.Concepts.QueryComplexity.AdversarySearch.MarkedSupport Qatlib.Foundations.OpCalculus.ContourCalc
namespace Qatlib.Papers.CrouzeixLS26.AccessLower.ConstructorReadout
open Qatlib
open scoped BigOperators Classical
/-- This is the same classifier in both instances; truth occurs only in the
correctness theorem. Ties are assigned to the hidden case. -/
def aeVote (t : ℝ) (M : ℕ) (z : Fin M) : Bool := decide (Qatlib.Papers.CrouzeixLS26.AccessLower.BlockReadout.threshold t<aeEstimate M z)

/-- Every returned description is unitary, including bad/failure outputs. Only
the good set is required to encode the fixed target. The law samples a fresh
constructor and its actual prepared AE circuit independently on each repeat. -/
theorem randomized_constructor_readout {D K I : Type}
    [Fintype D] [DecidableEq D] [Fintype K] [DecidableEq K] [Fintype I] [DecidableEq I]
    (μ : FinDist D) (U : D → Matrix (K × I) (K × I) ℂ)
    (hU : ∀ d, U d ∈ Matrix.unitaryGroup (K × I) ℂ) (G : Finset D) (hG : 2/3≤∑ d∈G,μ.prob d)
    (T : Matrix I I ℂ) (k0 : K) (i j : I) (k : ℕ) (hk : 2≤k) (truth : Bool)
    (hgood : ∀ d∈G, Qatlib.Concepts.BlockEncoding.BlockEncoding T (U d) (encodingFiber k0) (encodingFiber k0)
      1 (Qatlib.Papers.CrouzeixLS26.AccessLower.BlockReadout.dyadicTau k/100))
    (hentry : T i j=(if truth then (4/5 : ℂ) else
      ((4/(5*(1+2*Qatlib.Papers.CrouzeixLS26.AccessLower.BlockReadout.dyadicTau k)) : ℝ) : ℂ))) :
    let M := Qatlib.Papers.CrouzeixLS26.AccessLower.BlockReadout.aeReadoutGrid k
    let hM := (Qatlib.Papers.CrouzeixLS26.AccessLower.BlockReadout.dyadic_readout_budget k hk).2.2.1
    let L := Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointTranscript.jointLaw μ (fun d => aeLaw M (U d) (k0,j) {(k0,i)} (hU d) hM)
    L.probEvent (L := 1001) (fun ω => Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg
      (indicator (fun dz : D × Fin M => aeVote (Qatlib.Papers.CrouzeixLS26.AccessLower.BlockReadout.dyadicTau k) M dz.2=truth)) ω≤1/2)≤1/3 := by
  let M := Qatlib.Papers.CrouzeixLS26.AccessLower.BlockReadout.aeReadoutGrid k
  let hM := (Qatlib.Papers.CrouzeixLS26.AccessLower.BlockReadout.dyadic_readout_budget k hk).2.2.1
  let P := fun d => aeLaw M (U d) (k0,j) {(k0,i)} (hU d) hM
  let C := fun dz : D × Fin M => aeVote (Qatlib.Papers.CrouzeixLS26.AccessLower.BlockReadout.dyadicTau k) M dz.2=truth
  apply independent_majority_failure
  apply constructor_ae_success μ P C G hG
  intro d hd
  cases truth with
  | true =>
    have he : T i j=(4/5 : ℂ) := by simpa using hentry
    have hh := (Qatlib.Papers.CrouzeixLS26.AccessLower.BlockReadout.baseline_dyadic_decision T (U d) k0 i j k hk (hgood d hd) he).1
    simpa [P,C,M,hM,aeVote] using hh
  | false =>
    have he : T i j=((4/(5*(1+2*Qatlib.Papers.CrouzeixLS26.AccessLower.BlockReadout.dyadicTau k)) : ℝ) : ℂ) := by simpa using hentry
    have hh := (Qatlib.Papers.CrouzeixLS26.AccessLower.BlockReadout.hidden_dyadic_decision T (U d) k0 i j k hk (hgood d hd) he).1
    have hs : Finset.univ.filter (fun z : Fin M => aeEstimate M z<Qatlib.Papers.CrouzeixLS26.AccessLower.BlockReadout.threshold (Qatlib.Papers.CrouzeixLS26.AccessLower.BlockReadout.dyadicTau k))⊆
        Finset.univ.filter (fun z : Fin M => C (d,z)) := by
      intro z hz
      simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hz ⊢
      simpa [C,aeVote] using hz.le
    exact hh.trans (Finset.sum_le_sum_of_subset_of_nonneg hs (fun z _ _ => (P d).nonneg z))

/-- The readout ledger counts actual forward/backward preparation accesses;
the query implementing the known success projector is not charged as an A
oracle. Compilation of controlled descriptions is a separate semantic bridge. -/
theorem repeated_access_charge {H : Type} [Fintype H] [DecidableEq H]
    (M qpre quse : ℕ) (hM : 0<M) :
    (∑ _ : Fin 1001, (qpre+aeForwardAccesses (aeAccessWord (I := H) M)*quse+
      aeBackwardAccesses (aeAccessWord (I := H) M)*quse))=1001*(qpre+(2*M-1)*quse) := by
  have hc : qpre+aeForwardAccesses (aeAccessWord (I := H) M)*quse+
      aeBackwardAccesses (aeAccessWord (I := H) M)*quse=qpre+(2*M-1)*quse := by
    rw [add_assoc,Qatlib.Papers.CrouzeixLS26.AccessLower.BlockReadout.ae_access_charge M quse hM]
  simp_rw [hc]
  norm_num only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat]

end Qatlib.Papers.CrouzeixLS26.AccessLower.ConstructorReadout
