/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.GeneralAdversaryDefs
import Mathlib.Algebra.Order.Floor.Semiring
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.AdaptiveQueryPurification
import Qatlib.Concepts.AdversaryBounds.AdvDuality.KrausCircuitCompile
import Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedRelabel
import Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedPairedExecution
import Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedPurification
import Qatlib.Concepts.AdversaryBounds.AdvDuality.DensityPurification
import Qatlib.Concepts.AdversaryBounds.AdvDuality.KrausCircuitMixed
import Qatlib.Foundations.PureStateMath.BornBridge.PhyslibStates
import Qatlib.Concepts.Execution.CircuitCompile.InstrumentCircuitTransport
import Qatlib.Concepts.AdversaryBounds.AdvDuality.VariableKrausStatistics
import Qatlib.Concepts.AdversaryBounds.AdvDuality.InstrumentMachinePrefix
import Qatlib.Concepts.AdversaryBounds.AdvDuality.GeneralAdversaryPhaseOracle

/-!
# Compiling adaptive circuits for adversary bounds

This module constructs phase query simulations that store observed branch states in a history
register. `phase_observed_full_branch_purification` and `phase_kraus_full_branch_purification`
preserve the corresponding query depth or budget, while event transport identifies the simulated
readout with the original execution mass. The constructions use the quantum operation and
dilation framework described in [Watrous2018].

These simulations transfer general adversary query bounds to observed, Kraus, and instrument
circuits, including mixed inputs and decoded outputs [HoyerLeeSpalek2007]. Query truncation and
a tail estimate then give bounds in terms of expected queries, with constants `128` for exact
computation and `512` for error at most `1 / 16`.

## Main statements

* `phase_observed_full_branch_purification`: a unitary simulation retaining every observed
  branch state.
* `phase_instrument_mixed_value_bound`: the general adversary value bounds the instrument query
  budget with the stated error factor.
* `instrument_event_sub_expected_le_truncate`: the event mass lost under truncation is bounded
  by the expected query count divided by the next query threshold.
* `phase_instrument_small_error_expected_value_bound`: a uniform mean query bound `T` implies
  `advPmValue input f ≤ ENNReal.ofReal (512 * T)`.

## References

* [Watrous, 2018][Watrous2018]
* [Hoyer, Lee, and Spalek, 2007][HoyerLeeSpalek2007]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal ComplexConjugate
open Qatlib
open Qatlib

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.ShadowModels.ShadowChannel
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.Execution.CircuitCompile
open Qatlib.Concepts.GateVocabulary.GateVocab
open Qatlib.Concepts.QueryComplexity.AdaptiveQuery
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.BlockEncoding.StateBlockEncoding

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality
variable {X W : Type} [Fintype X] [DecidableEq X] [Fintype W] [DecidableEq W]
variable {n q : ℕ} [NeZero q]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000
noncomputable section

/-- The phase padding word is unitary and contains exactly one query and two gates. -/
theorem phasePaddingWord_cost {n q : ℕ} {W H : Type}
    [Fintype W] [DecidableEq W] [Fintype H] [DecidableEq H] (active : H → Bool) :
    IsUnitaryCircuit (phasePaddingWord (n := n) (q := q) (W := W) active) ∧
      QueryCount (phasePaddingWord (n := n) (q := q) (W := W) active) = 1 ∧
      GateCount (phasePaddingWord (n := n) (q := q) (W := W) active) = 2 := by
  refine ⟨?_, rfl, rfl⟩
  simp only [phasePaddingWord, isUnitaryCircuit_gate, isUnitaryCircuit_query, isUnitaryCircuit_nil,
    and_true, and_self]
  exact permMatrix_unitary (phasePaddingSwap_involutive active)
end
noncomputable section

/-- The padding word multiplies each amplitude by the phase of the answer register in active
sectors and the auxiliary register otherwise. -/
theorem phasePaddingWord_raw {n q : ℕ} [NeZero q] {W H : Type}
    [Fintype W] [DecidableEq W] [Fintype H] [DecidableEq H]
    (active : H → Bool) (input : Fin n → Fin q) (v : QState (PhasePaddingSpace n q W H))
    (r : PhasePaddingSpace n q W H) :
    Run (phaseOracle (W := W × H × Fin q) input) (phasePaddingWord active) v r =
      phaseFactor (input r.1.1) (if active r.2.2.1 then r.1.2 else r.2.2.2) * v r := by
  change (permMatrix (phasePaddingSwap active) *ᵥ
    (phaseOracle input *ᵥ (permMatrix (phasePaddingSwap active) *ᵥ v))) r = _
  have hs (u : QState (PhasePaddingSpace n q W H)) (p : PhasePaddingSpace n q W H) :
      (permMatrix (phasePaddingSwap active) *ᵥ u) p = u (phasePaddingSwap active p) :=
    applyGate_permMatrix (phasePaddingSwap_involutive active) u p
  rw [hs, phaseOracle_mulVec, hs, phasePaddingSwap_involutive]
  rcases r with ⟨⟨i,p⟩,w,h,z⟩
  cases ha : active h <;> simp [phasePaddingSwap, phaseFactor, ha]
end
noncomputable section

/-- On an embedded state with zero auxiliary register, phase padding applies the query phase
only in active history sectors. -/
theorem phasePaddingWord_frame {n q : ℕ} [NeZero q] {W H : Type}
    [Fintype W] [DecidableEq W] [Fintype H] [DecidableEq H]
    (active : H → Bool) (input : Fin n → Fin q)
    (v : QState ((Fin n × Fin q) × (W × H))) :
    Run (phaseOracle (W := W × H × Fin q) input) (phasePaddingWord active) (phasePaddingInput v) =
      phasePaddingInput (fun r => (if active r.2.2 then phaseFactor (input r.1.1) r.1.2 else 1) * v r) := by
  ext r
  rw [phasePaddingWord_raw]
  rcases r with ⟨⟨i,p⟩,w,h,z⟩
  cases ha : active h <;> by_cases hz : z = 0 <;>
    simp [phasePaddingInput, ha, hz, phaseFactor]
end
noncomputable section

/-- Embedding into the phase padding space preserves normalization. -/
theorem phasePaddingInput_normalized {n q : ℕ} [NeZero q] {W H : Type}
    [Fintype W] [Fintype H] (v : QState ((Fin n × Fin q) × (W × H))) (hv : Normalized v) :
    Normalized (phasePaddingInput v) := by
  have hs (a : Fin n × Fin q) (w : W) (h : H) :
      (∑ z : Fin q, ‖if z = 0 then v (a,w,h) else 0‖ ^ 2) = ‖v (a,w,h)‖ ^ 2 := by
    rw [Finset.sum_eq_single 0]
    · simp
    · intro z _ hz; simp [hz]
    · simp
  simp only [Normalized, phasePaddingInput, Fintype.sum_prod_type]
  simp only [hs]
  simpa only [Normalized, Fintype.sum_prod_type] using! hv
end
variable {X W : Type} [Fintype X] [DecidableEq X] [Fintype W] [DecidableEq W]
variable {n q : ℕ} [NeZero q]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000
variable {n q : ℕ} [NeZero q] {W H : Type} [Fintype W] [Fintype H] [DecidableEq W] [DecidableEq H]
noncomputable section
/-- Reassociate the query, workspace, history, and auxiliary answer registers into
`PhasePaddingSpace`. -/
def phaseHistoryLayout : ((((Fin n × Fin q) × W) × H) × Fin q) ≃ PhasePaddingSpace n q W H where
  toFun x := (x.1.1.1,x.1.1.2,x.1.2,x.2)
  invFun x := (((x.1,x.2.1),x.2.2.1),x.2.2.2)
  left_inv _ := rfl
  right_inv _ := rfl
end
noncomputable section
/-- Extend a history space operator by the identity on the auxiliary answer register and reindex
into the padding layout. -/
def phaseHistoryLift
    (U : Matrix (((Fin n × Fin q) × W) × H) (((Fin n × Fin q) × W) × H) ℂ) :
    Matrix (PhasePaddingSpace n q W H) (PhasePaddingSpace n q W H) ℂ :=
  Matrix.reindex phaseHistoryLayout phaseHistoryLayout (TensorGate U 1)
end
noncomputable section
omit [NeZero q] in

/-- Extending and reindexing a unitary history operator gives a unitary padding space operator. -/
theorem phaseHistoryLift_unitary
    {U : Matrix (((Fin n × Fin q) × W) × H) (((Fin n × Fin q) × W) × H) ℂ}
    (hU : U ∈ Matrix.unitaryGroup _ ℂ) :
    phaseHistoryLift U ∈ Matrix.unitaryGroup _ ℂ :=
  unitaryGroup_reindex phaseHistoryLayout (tensorGate_unitary hU (Submonoid.one_mem _))
end
noncomputable section
/-- Reassociate a state with a history register and embed it with the auxiliary answer register
fixed to zero. -/
def phaseHistoryInput (v : QState (((Fin n × Fin q) × W) × H)) :
    QState (PhasePaddingSpace n q W H) :=
  phasePaddingInput (fun x => v ((x.1,x.2.1),x.2.2))
end
noncomputable section
omit [DecidableEq W] [DecidableEq H] in

/-- Applying a lifted history operator to an embedded state agrees with embedding the original
operator's output. -/
theorem apply_phaseHistoryLift
    (U : Matrix (((Fin n × Fin q) × W) × H) (((Fin n × Fin q) × W) × H) ℂ)
    (v : QState (((Fin n × Fin q) × W) × H)) :
    ApplyGate (phaseHistoryLift U) (phaseHistoryInput v) =
      phaseHistoryInput (ApplyGate U v) := by
  funext x
  simp only [phaseHistoryLift, ApplyGate, Matrix.mulVec, dotProduct,
    Matrix.reindex_apply, Matrix.submatrix_apply, phaseHistoryLayout,
    Equiv.coe_fn_symm_mk, TensorGate, Matrix.kronecker_apply,
    phaseHistoryInput, phasePaddingInput, Fintype.sum_prod_type]
  simp only [Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  by_cases hz : x.2.2.2 = 0 <;> simp [hz]
end
noncomputable section

/-- Phase padding on an embedded history subspace applies the query phase exactly in the
original active sectors. -/
theorem run_phasePadding_embedded {K : Type} [Fintype K] [DecidableEq K]
    (e : K ↪ H) (active : K → Bool) (input : Fin n → Fin q)
    (v : QState (((Fin n × Fin q) × W) × K)) :
    Run (phaseOracle (W := W × H × Fin q) input)
      (phasePaddingWord (adaptiveEmbeddedActive e active))
      (phaseHistoryInput (adaptiveHistoryCoordinateMatrix e *ᵥ v)) =
      phaseHistoryInput (adaptiveHistoryCoordinateMatrix e *ᵥ
        (fun y => (if active y.2 then phaseFactor (input y.1.1.1) y.1.1.2 else 1) * v y)) := by
  rw [phaseHistoryInput, phasePaddingWord_frame]
  funext x
  simp only [phasePaddingInput, phaseHistoryInput]
  by_cases hh : ∃ k, e k = x.2.2.1
  · obtain ⟨k,hk⟩ := hh
    rw [← hk]
    simp only [adaptiveEmbeddedActive_image, adaptiveHistoryCoordinateMatrix_apply_image]
  · have hzero (u : QState (((Fin n × Fin q) × W) × K)) :
        (adaptiveHistoryCoordinateMatrix e *ᵥ u) ((x.1,x.2.1),x.2.2.1) = 0 :=
      adaptiveHistoryCoordinateMatrix_apply_outside e u _ _ (fun k he => hh ⟨k,he⟩)
    simp only [hzero, mul_zero]
end
noncomputable section
/-- Build a circuit from an initial lifted gate followed by successive padded queries and lifted
frontier gates. -/
def phaseFrontierLayerWord
    (U0 : Matrix (((Fin n × Fin q) × W) × H) (((Fin n × Fin q) × W) × H) ℂ)
    (Us : ℕ → Matrix (((Fin n × Fin q) × W) × H) (((Fin n × Fin q) × W) × H) ℂ)
    (active : ℕ → H → Bool) : ℕ → Circuit (PhasePaddingSpace n q W H)
  | 0 => [.gate (phaseHistoryLift U0)]
  | k+1 => phaseFrontierLayerWord U0 Us active k ++
      (phasePaddingWord (active k) ++ [.gate (phaseHistoryLift (Us k))])
end
noncomputable section
omit [NeZero q] in

/-- With unitary frontier gates, the circuit of `k` layers is unitary with `k` queries and `1 +
3 * k` gates. -/
theorem phaseFrontierLayerWord_cost
    (U0 : Matrix (((Fin n × Fin q) × W) × H) (((Fin n × Fin q) × W) × H) ℂ)
    (Us : ℕ → Matrix (((Fin n × Fin q) × W) × H) (((Fin n × Fin q) × W) × H) ℂ)
    (active : ℕ → H → Bool)
    (hU0 : U0 ∈ Matrix.unitaryGroup _ ℂ)
    (hUs : ∀ j, Us j ∈ Matrix.unitaryGroup _ ℂ) (k : ℕ) :
    IsUnitaryCircuit (phaseFrontierLayerWord U0 Us active k) ∧
      QueryCount (phaseFrontierLayerWord U0 Us active k) = k ∧
      GateCount (phaseFrontierLayerWord U0 Us active k) = 1 + 3*k := by
  induction k with
  | zero => simp [phaseFrontierLayerWord, phaseHistoryLift_unitary hU0]
  | succ k ih =>
    have hp := phasePaddingWord_cost (n := n) (q := q) (W := W) (active k)
    refine ⟨?_, ?_, ?_⟩
    · apply (isUnitaryCircuit_append _ _).mpr
      refine ⟨ih.1, (isUnitaryCircuit_append _ _).mpr ⟨hp.1, ?_⟩⟩
      simpa using! phaseHistoryLift_unitary (hUs k)
    · simp only [phaseFrontierLayerWord, queryCount_append, ih.2.1, hp.2.1,
        queryCount_gate, queryCount_nil, add_zero]
    · simp only [phaseFrontierLayerWord, gateCount_append, ih.2.2, hp.2.2,
        gateCount_gate, gateCount_nil]
      omega
end
noncomputable section

/-- Under the initialization and advancement identities, the layered circuit realizes the
embedded adaptive frontier state. -/
theorem run_phaseFrontierLayerWord
    (P : ObservedCircuit ((Fin n × Fin q) × W))
    (e : ∀ j, adaptiveFrontierType P j ↪ H) (blank : H)
    (U0 : Matrix (((Fin n × Fin q) × W) × H) (((Fin n × Fin q) × W) × H) ℂ)
    (Us : ℕ → Matrix (((Fin n × Fin q) × W) × H) (((Fin n × Fin q) × W) × H) ℂ)
    (hinit : ∀ ψ : QState ((Fin n × Fin q) × W),
      ApplyGate U0 (fun x => if x.2 = blank then ψ x.1 else 0) =
        adaptiveHistoryCoordinateMatrix (e 0) *ᵥ adaptiveFrontierRun 1 P 0 ψ)
    (hstep : ∀ j (v : QState (((Fin n × Fin q) × W) × adaptiveFrontierType P j)),
      ApplyGate (Us j) (adaptiveHistoryCoordinateMatrix (e j) *ᵥ v) =
        adaptiveHistoryCoordinateMatrix (e (j+1)) *ᵥ adaptiveFrontierAdvance P j v)
    (input : Fin n → Fin q) (ψ : QState ((Fin n × Fin q) × W)) (k : ℕ) :
    Run (phaseOracle (W := W × H × Fin q) input)
      (phaseFrontierLayerWord U0 Us
        (fun j => adaptiveEmbeddedActive (e j) (adaptiveFrontierActive P j)) k)
      (phaseHistoryInput (fun x => if x.2 = blank then ψ x.1 else 0)) =
      phaseHistoryInput (adaptiveHistoryCoordinateMatrix (e k) *ᵥ
        adaptiveFrontierRun (phaseOracle (W := W) input) P k ψ) := by
  induction k with
  | zero =>
    rw [phaseFrontierLayerWord, run_gate, run_nil, apply_phaseHistoryLift, hinit,
      adaptiveFrontierRun_zero_eq 1 (phaseOracle (W := W) input)]
  | succ k ih =>
    rw [phaseFrontierLayerWord, run_append, ih, run_append,
      run_phasePadding_embedded, run_gate, run_nil, apply_phaseHistoryLift]
    have hq : (fun y => (if adaptiveFrontierActive P k y.2 then
        phaseFactor (input y.1.1.1) y.1.1.2 else 1) *
        adaptiveFrontierRun (phaseOracle (W := W) input) P k ψ y) =
        adaptiveFrontierQuery (phaseOracle (W := W) input) P k
          (adaptiveFrontierRun (phaseOracle (W := W) input) P k ψ) := by
      funext y
      simp only [adaptiveFrontierQuery, ApplyGate, phaseOracle_mulVec]
      split_ifs <;> simp [phaseFactor]
    rw [hq, hstep, adaptiveFrontierAdvance_query]
end
noncomputable section

/-- Every well formed observed circuit has a unitary phase query simulation packing all branch
states into a history register. Its query count is the observed query depth and its gate
count is one plus three times that depth. -/
theorem phase_observed_full_branch_purification
    (P : ObservedCircuit ((Fin n × Fin q) × W)) (hP : observedWellFormed P) :
    ∃ (R : ℕ) (C : Circuit (PhasePaddingSpace n q W (Fin (R+1)))),
      IsUnitaryCircuit C ∧ QueryCount C = observedQueryDepth P ∧
      GateCount C = 1 + 3 * observedQueryDepth P ∧
      ∀ (input : Fin n → Fin q) (ψ : QState ((Fin n × Fin q) × W)),
      let ts := observedTraces (phaseOracle (W := W) input) P ψ
      ts.length ≤ R+1 ∧
      ∀ x : PhasePaddingSpace n q W (Fin (R+1)),
        Run (phaseOracle (W := W × Fin (R+1) × Fin q) input) C
          (phaseHistoryInput (fun y => if y.2 = 0 then ψ y.1 else 0)) x =
          if x.2.2.2 = 0 then
            (ts.getD x.2.2.1.val (emptyObservedTrace _)).state (x.1,x.2.1) else 0 := by
  let R := observedTreeNodes P
  let e := adaptiveHistorySlots P
  obtain ⟨U0,hU0,hinit⟩ := adaptiveFrontierInitial_transport P hP (0 : Fin (R+1)) (e 0)
  have htrans (j : ℕ) := adaptiveFrontierLayer_transport P hP j (e j) (e (j+1))
  choose Us hUs hstep using htrans
  let C := phaseFrontierLayerWord U0 Us
    (fun j => adaptiveEmbeddedActive (e j) (adaptiveFrontierActive P j)) (observedQueryDepth P)
  have hc := phaseFrontierLayerWord_cost U0 Us
    (fun j => adaptiveEmbeddedActive (e j) (adaptiveFrontierActive P j)) hU0 hUs
    (observedQueryDepth P)
  refine ⟨R,C,hc.1,hc.2.1,hc.2.2,?_⟩
  intro input ψ
  have he := adaptiveFrontierEnumeration_final (phaseOracle (W := W) input)
    P (observedQueryDepth P) le_rfl ψ
  have hlen := congrArg List.length he
  simp only [List.length_map] at hlen
  refine ⟨?_,?_⟩
  · rw [← hlen, adaptiveFrontierEnumeration_length]
    exact (adaptiveFrontier_card_le_nodes P _).trans (Nat.le_add_right _ _)
  · intro x
    have hr := run_phaseFrontierLayerWord P e (0 : Fin (R+1)) U0 Us hinit hstep
      input ψ (observedQueryDepth P)
    change Run _ C _ x = _
    rw [hr]
    simp only [phaseHistoryInput,phasePaddingInput]
    rw [adaptiveFrontier_final_coordinate]
end
noncomputable section
omit [DecidableEq W] [DecidableEq H] in

/-- Embedding a history state into the padding space preserves its branch mass. -/
theorem phaseHistoryInput_mass (v : QState (((Fin n × Fin q) × W) × H)) :
    branchMass (phaseHistoryInput v) = branchMass v := by
  have hs (a : Fin n × Fin q) (w : W) (h : H) :
      (∑ z : Fin q, ‖if z = 0 then v ((a,w),h) else 0‖ ^ 2) = ‖v ((a,w),h)‖ ^ 2 := by
    rw [Finset.sum_eq_single 0]
    · simp
    · intro z _ hz; simp [hz]
    · simp
  simp only [branchMass,MeasureProb,BornProb,phaseHistoryInput,phasePaddingInput,
    Fintype.sum_prod_type,hs]
end
noncomputable section

/-- Measuring an event on a packed trace history gives the sum of the selected trace masses when
the history register fits the list. -/
theorem phasePackedTrace_readout
    (ts : List (BranchTrace ((Fin n × Fin q) × W))) (K : ℕ) (hK : ts.length ≤ K)
    (event : BranchTrace ((Fin n × Fin q) × W) → Bool) :
    MeasureProb (phaseHistoryInput (fun x : ((Fin n × Fin q) × W) × Fin K =>
      (ts.getD x.2.val (emptyObservedTrace _)).state x.1))
      (Finset.univ.filter (fun x => event (ts.getD x.2.2.1.val (emptyObservedTrace _)))) =
      (ts.map (fun t => if event t then branchMass t.state else 0)).sum := by
  let vs := ts.map (fun t => if event t then t.state else 0)
  let v := phaseHistoryInput (fun x : ((Fin n × Fin q) × W) × Fin K =>
    (ts.getD x.2.val (emptyObservedTrace _)).state x.1)
  let E : Finset (PhasePaddingSpace n q W (Fin K)) := Finset.univ.filter
    (fun x => event (ts.getD x.2.2.1.val (emptyObservedTrace _)))
  have hc : Collapse v E = phaseHistoryInput (fun x : ((Fin n × Fin q) × W) × Fin K =>
      (vs.getD x.2.val 0) x.1) := by
    funext x
    rw [collapse_apply]
    have hv := List.getD_map ts (emptyObservedTrace _) (fun t => if event t then t.state else 0)
      (n := x.2.2.1.val)
    have hdefault : (if event (emptyObservedTrace ((Fin n × Fin q) × W)) then
        (emptyObservedTrace ((Fin n × Fin q) × W)).state else 0) = (0 : QState _) := by
      simp only [emptyObservedTrace,ite_self]
    rw [hdefault] at hv
    change vs.getD x.2.2.1.val 0 = _ at hv
    simp only [phaseHistoryInput,phasePaddingInput]
    rw [hv]
    simp only [E,v,Finset.mem_filter,Finset.mem_univ,true_and,phaseHistoryInput,phasePaddingInput]
    cases event (ts.getD x.2.2.1.val (emptyObservedTrace _)) <;> simp
  change MeasureProb v E = _
  calc
    MeasureProb v E = branchMass (Collapse v E) := by
      rw [branchMass,measureProb_collapse,Finset.inter_univ]
    _ = branchMass (phaseHistoryInput (fun x : ((Fin n × Fin q) × W) × Fin K =>
        (vs.getD x.2.val 0) x.1)) := congrArg branchMass hc
    _ = branchMass (fun x : ((Fin n × Fin q) × W) × Fin K =>
        (vs.getD x.2.val 0) x.1) := phaseHistoryInput_mass _
    _ = (vs.map branchMass).sum := adaptiveListHistory_mass vs K
      (by simpa only [vs,List.length_map] using! hK)
    _ = _ := by
      simp only [vs,List.map_map,Function.comp_def]
      congr 1
      apply List.map_congr_left
      intro t _
      cases event t <;> simp [branchMass,MeasureProb,BornProb]
end
noncomputable section
/-- The padding space basis event selecting history indices whose syntactic observed branches
accept. -/
def phaseObservedHistoryEvent (P : ObservedCircuit ((Fin n × Fin q) × W)) (R : ℕ) :
    Finset (PhasePaddingSpace n q W (Fin (R+1))) :=
  Finset.univ.filter (fun x => ((observedBranchWords P).map Prod.fst).getD x.2.2.1.val false)
end
noncomputable section

/-- A circuit satisfying the packed branch state formula has history event probability equal to
the original observed acceptance mass. -/
theorem phase_observed_acceptance_transport
    (P : ObservedCircuit ((Fin n × Fin q) × W)) (R : ℕ)
    (C : Circuit (PhasePaddingSpace n q W (Fin (R+1))))
    (input : Fin n → Fin q) (ψ : QState ((Fin n × Fin q) × W))
    (hlen : (observedTraces (phaseOracle (W := W) input) P ψ).length ≤ R+1)
    (hstate : ∀ x,
      Run (phaseOracle (W := W × Fin (R+1) × Fin q) input) C
        (phaseHistoryInput (fun y => if y.2 = 0 then ψ y.1 else 0)) x =
      if x.2.2.2 = 0 then
        ((observedTraces (phaseOracle (W := W) input) P ψ).getD
          x.2.2.1.val (emptyObservedTrace _)).state (x.1,x.2.1) else 0) :
    MeasureProb (Run (phaseOracle (W := W × Fin (R+1) × Fin q) input) C
      (phaseHistoryInput (fun y => if y.2 = 0 then ψ y.1 else 0)))
      (phaseObservedHistoryEvent P R) = observedAcceptance (phaseOracle (W := W) input) P ψ := by
  let ts := observedTraces (phaseOracle (W := W) input) P ψ
  have he : phaseObservedHistoryEvent P R =
      Finset.univ.filter (fun x => (ts.getD x.2.2.1.val (emptyObservedTrace _)).accepted) := by
    ext x
    simp only [phaseObservedHistoryEvent,Finset.mem_filter,Finset.mem_univ,true_and]
    have hh := List.getD_map ts (emptyObservedTrace _) BranchTrace.accepted (n := x.2.2.1.val)
    rw [observedBranchWords_accepted] at hh
    change ((observedBranchWords P).map Prod.fst).getD x.2.2.1.val false = _ at hh
    rw [hh]
  rw [funext hstate,he]
  change MeasureProb (phaseHistoryInput (fun x : ((Fin n × Fin q) × W) × Fin (R+1) =>
    (ts.getD x.2.val (emptyObservedTrace _)).state x.1)) _ = _
  rw [phasePackedTrace_readout ts (R+1) hlen BranchTrace.accepted]
  exact observedEventMass_accepted _ P ψ
end
noncomputable section
omit [DecidableEq W] in

/-- Embedding a normalized initial state with blank history zero gives a normalized padding
space state. -/
theorem phaseHistory_initial_normalized (R : ℕ) (ψ : QState ((Fin n × Fin q) × W))
    (hψ : Normalized ψ) :
    Normalized (phaseHistoryInput (H := Fin (R+1)) (fun y => if y.2 = 0 then ψ y.1 else 0)) := by
  change branchMass _ = 1
  rw [phaseHistoryInput_mass]
  have hs (i : (Fin n × Fin q) × W) :
      (∑ h : Fin (R+1), ‖if h = 0 then ψ i else 0‖ ^ 2) = ‖ψ i‖ ^ 2 := by
    rw [Finset.sum_eq_single 0]
    · simp
    · intro h _ hh; simp [hh]
    · simp
  simp only [branchMass,MeasureProb,BornProb,Fintype.sum_prod_type,hs]
  simpa only [Normalized,Fintype.sum_prod_type] using! hψ
end
variable {X W : Type} [Fintype X] [DecidableEq X] [Fintype W] [DecidableEq W]
variable {n q : ℕ} [NeZero q]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000
variable {n q : ℕ} [NeZero q] {W H : Type}
variable {n q : ℕ} [NeZero q] {W : Type} [Fintype W]
noncomputable section
/-- Read the Boolean return flag of the syntactic branch indexed by the history register,
defaulting to false. -/
def phaseObservedReturnLabel (P : ObservedCircuit ((Fin n × Fin q) × W)) (R : ℕ)
    (x : PhasePaddingSpace n q W (Fin (R+1))) : Bool :=
  ((observedBranchWords P).map Prod.fst).getD x.2.2.1.val false
end
noncomputable section

/-- Under the packed branch state formula, the return label POVM probability equals the mass of
observed branches returning that Boolean. -/
theorem phase_observed_return_transport
    (P : ObservedCircuit ((Fin n × Fin q) × W)) (R : ℕ)
    (C : Circuit (PhasePaddingSpace n q W (Fin (R+1))))
    (input : Fin n → Fin q) (ψ : QState ((Fin n × Fin q) × W)) (b : Bool)
    (hlen : (observedTraces (phaseOracle (W := W) input) P ψ).length ≤ R+1)
    (hstate : ∀ x,
      Run (phaseOracle (W := W × Fin (R+1) × Fin q) input) C
        (phaseHistoryInput (fun y => if y.2 = 0 then ψ y.1 else 0)) x =
      if x.2.2.2 = 0 then
        ((observedTraces (phaseOracle (W := W) input) P ψ).getD
          x.2.2.1.val (emptyObservedTrace _)).state (x.1,x.2.1) else 0) :
    povmProb (labelPovm (phaseObservedReturnLabel P R)) b
      (Run (phaseOracle (W := W × Fin (R+1) × Fin q) input) C
        (phaseHistoryInput (fun y => if y.2 = 0 then ψ y.1 else 0))) =
      observedEventMass (phaseOracle (W := W) input) P ψ (fun t => decide (t.accepted = b)) := by
  let ts := observedTraces (phaseOracle (W := W) input) P ψ
  have he : outcomeEvent (phaseObservedReturnLabel P R) b =
      Finset.univ.filter (fun x => decide ((ts.getD x.2.2.1.val (emptyObservedTrace _)).accepted = b)) := by
    ext x
    simp only [outcomeEvent,Finset.mem_filter,Finset.mem_univ,true_and]
    have hh := List.getD_map ts (emptyObservedTrace _) BranchTrace.accepted (n := x.2.2.1.val)
    rw [observedBranchWords_accepted] at hh
    change ((observedBranchWords P).map Prod.fst).getD x.2.2.1.val false = _ at hh
    simp only [phaseObservedReturnLabel,hh,decide_eq_true_eq]
  rw [labelPovm_povmProb,funext hstate,he]
  change MeasureProb (phaseHistoryInput (fun x : ((Fin n × Fin q) × W) × Fin (R+1) =>
    (ts.getD x.2.val (emptyObservedTrace _)).state x.1)) _ = _
  rw [phasePackedTrace_readout ts (R+1) hlen (fun t => decide (t.accepted = b))]
  rfl
end
noncomputable section

/-- A successful observed phase query circuit computing a Boolean function satisfies the general
adversary bound with the binary output error factor [HoyerLeeSpalek2007]. -/
theorem phase_observed_binary_query_lower_bound
    {X : Type} [Fintype X] [DecidableEq X]
    (input : X → Fin n → Fin q) (f : X → Bool) (Gamma : Matrix X X ℂ)
    (P : ObservedCircuit ((Fin n × Fin q) × W)) (hP : observedWellFormed P)
    (ψ : QState ((Fin n × Fin q) × W)) (hψ : Normalized ψ)
    (eps : ℝ) (he0 : 0 ≤ eps) (he1 : eps ≤ 1/2)
    (hG : Gamma.IsHermitian) (hz : ∀ x y, f x = f y → Gamma x y = 0)
    (hsuccess : ∀ x, 1-eps ≤ observedEventMass (phaseOracle (W := W) (input x)) P ψ
      (fun t => decide (t.accepted = f x))) :
    (1-2*Real.sqrt (eps*(1-eps))) * ‖Gamma‖ ≤
      2 * (observedQueryDepth P : ℝ) * maxFilterNorm input Gamma := by
  obtain ⟨R,C,hC,hq,_,hstates⟩ := phase_observed_full_branch_purification P hP
  let ψ' := phaseHistoryInput (H := Fin (R+1)) (fun y => if y.2 = 0 then ψ y.1 else 0)
  let out := labelPovm (phaseObservedReturnLabel P R)
  have hrun : IsBoundedErrorRun input f C ψ' out eps := by
    refine ⟨?_,phaseHistory_initial_normalized R ψ hψ,isPovm_labelPovm _,he0,he1,?_⟩
    · convert! hC using 1
    intro x
    have ht := phase_observed_return_transport P R C (input x) ψ (f x)
      (hstates (input x) ψ).1 (hstates (input x) ψ).2
    exact ht.symm ▸ hsuccess x
  have hb := phase_povm_binary_query_lower_bound q n X (W × Fin (R+1) × Fin q) Bool
    input f Gamma C ψ' out eps hG hz hrun (by decide)
  simpa only [hq] using! hb
end
variable {X W : Type} [Fintype X] [DecidableEq X] [Fintype W] [DecidableEq W]
variable {n q : ℕ} [NeZero q]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000
variable {n q : ℕ} [NeZero q] {W H : Type}
variable {n q : ℕ} [NeZero q] {W : Type} [Fintype W]
variable {n q d s : ℕ} [NeZero q] {W : Type} [Fintype W]
noncomputable section
/-- Reassociate an encoded query register and Kraus ancilla into a query register with an
enlarged workspace. -/
def phaseKrausLayout (e : Fin d ≃ (Fin n × Fin q) × W) :
    (Fin d × Fin s) ≃ (Fin n × Fin q) × (W × Fin s) :=
  (Equiv.prodCongr e (Equiv.refl (Fin s))).trans (Equiv.prodAssoc _ _ _)
end
noncomputable section
/-- The phase oracle relabeled onto the finite dimensional data register by the given register
equivalence. -/
def phaseKrausOracle (e : Fin d ≃ (Fin n × Fin q) × W) (input : Fin n → Fin q) : Operator d :=
  relabelGate e.symm (phaseOracle (W := W) input)
end
noncomputable section
omit [Fintype W] in

/-- Tensoring the encoded phase oracle with an identity ancilla and relabeling gives the phase
oracle on the enlarged workspace. -/
theorem phaseKrausOracle_extend (e : Fin d ≃ (Fin n × Fin q) × W) (input : Fin n → Fin q) :
    relabelGate (phaseKrausLayout (s := s) e) (TensorGate (phaseKrausOracle e input) (1 : Operator s)) =
      phaseOracle (W := W × Fin s) input := by
  ext x y
  change (phaseOracle (W := W) input (e (e.symm (x.1,x.2.1)))
      (e (e.symm (y.1,y.2.1)))) * (1 : Operator s) x.2.2 y.2.2 = _
  simp only [Equiv.apply_symm_apply,phaseOracle,Matrix.of_apply,Matrix.one_apply]
  rcases x with ⟨a,w,r⟩
  rcases y with ⟨b,v,t⟩
  by_cases ha : a = b
  · subst b
    by_cases hw : w = v
    · subst v
      by_cases hr : r = t <;> simp [hr]
    · simp [hw]
  · simp [ha]
end
noncomputable section

/-- Compile a well formed Kraus circuit into an observed circuit and relabel it into the
enlarged phase query register layout. -/
def phaseKrausObserved (e : Fin d ≃ (Fin n × Fin q) × W) (zero : Fin s)
    (P : KrausCircuit d s) (hP : krausCircuitWellFormed P) :
    ObservedCircuit ((Fin n × Fin q) × (W × Fin s)) :=
  relabelObserved (phaseKrausLayout e) (compileKrausCircuit zero P hP)
end
noncomputable section
omit [NeZero q] in

/-- The observed circuit compiled from a well formed Kraus circuit is well formed. -/
theorem phaseKrausObserved_legal (e : Fin d ≃ (Fin n × Fin q) × W) (zero : Fin s)
    (P : KrausCircuit d s) (hP : krausCircuitWellFormed P) :
    observedWellFormed (phaseKrausObserved e zero P hP) :=
  relabelObserved_wellFormed _ _ (compileKrausCircuit_wellFormed zero P hP)
end
noncomputable section
omit [NeZero q] in

/-- The compiled observed circuit's query depth equals the original Kraus circuit budget. -/
theorem phaseKrausObserved_depth (e : Fin d ≃ (Fin n × Fin q) × W) (zero : Fin s)
    (P : KrausCircuit d s) (hP : krausCircuitWellFormed P) :
    observedQueryDepth (phaseKrausObserved e zero P hP) = krausCircuitBudget P := by
  rw [observedQueryDepth_eq_budget,phaseKrausObserved,relabelObserved_budget,compileKrausCircuit_budget]
end
noncomputable section
/-- Tensor a pure data state with a fixed Kraus ancilla basis state and relabel into the
enlarged phase query register. -/
def phaseKrausInput (e : Fin d ≃ (Fin n × Fin q) × W) (zero : Fin s)
    (ψ : QState (Fin d)) : QState ((Fin n × Fin q) × (W × Fin s)) :=
  relabelState (phaseKrausLayout e) (TensorState ψ (Ket zero))
end
noncomputable section
omit [NeZero q] in

/-- The relabeled data state with a fixed Kraus ancilla is normalized when the original state is
normalized. -/
theorem phaseKrausInput_normalized (e : Fin d ≃ (Fin n × Fin q) × W) (zero : Fin s)
    (ψ : QState (Fin d)) (hψ : Normalized ψ) : Normalized (phaseKrausInput e zero ψ) :=
  normalized_relabelState _ (normalized_tensorState hψ (normalized_ket zero))
end
noncomputable section

/-- The compiled observed traces are the original Kraus traces embedded with the fixed ancilla
and relabeled into the phase query layout. -/
theorem phaseKrausObserved_traces (e : Fin d ≃ (Fin n × Fin q) × W) (zero : Fin s)
    (P : KrausCircuit d s) (hP : krausCircuitWellFormed P) (input : Fin n → Fin q)
    (ψ : QState (Fin d)) :
    observedTraces (phaseOracle (W := W × Fin s) input) (phaseKrausObserved e zero P hP)
      (phaseKrausInput e zero ψ) =
    (krausCircuitTraces (phaseKrausOracle e input) P ψ).map
      (fun t => relabelObservedTrace (phaseKrausLayout e) (embedKrausPureTrace zero t)) := by
  rw [← phaseKrausOracle_extend e input,phaseKrausObserved,phaseKrausInput,
    relabelObserved_traces,compileKrausCircuit_traces,List.map_map]
  rfl
end
noncomputable section

/-- The sum of pure Kraus branch masses selected by an event on return flags and measurement
records. -/
def krausPureEventMass (O : Operator d) (P : KrausCircuit d s) (ψ : QState (Fin d))
    (event : Bool → List (ℕ × ℕ) → Bool) : ℝ :=
  ((krausCircuitTraces O P ψ).map fun t => if event t.accepted t.outcomes then branchMass t.state else 0).sum
end
noncomputable section

/-- Compiling and relabeling a Kraus circuit preserves the mass of every event on return flags
and measurement records. -/
theorem phaseKrausObserved_event (e : Fin d ≃ (Fin n × Fin q) × W) (zero : Fin s)
    (P : KrausCircuit d s) (hP : krausCircuitWellFormed P) (input : Fin n → Fin q)
    (ψ : QState (Fin d)) (event : Bool → List (ℕ × ℕ) → Bool) :
    observedEventMass (phaseOracle (W := W × Fin s) input) (phaseKrausObserved e zero P hP)
      (phaseKrausInput e zero ψ) (fun t => event t.accepted t.outcomes) =
      krausPureEventMass (phaseKrausOracle e input) P ψ event := by
  have hm (v : QState (Fin d)) :
      branchMass (relabelState (phaseKrausLayout (s := s) e) (TensorState v (Ket zero))) =
        branchMass v := by
    have hr : branchMass (relabelState (phaseKrausLayout (s := s) e) (TensorState v (Ket zero))) =
        branchMass (TensorState v (Ket zero)) := by
      change (∑ i, BornProb _ i) = ∑ i, BornProb _ i
      simp only [bornProb_relabelState]
      exact (phaseKrausLayout (s := s) e).symm.sum_comp _
    rw [hr]
    change MeasureProb _ Finset.univ = _
    rw [← Finset.univ_product_univ,measureProb_tensorState_left (normalized_ket zero)]
  simp only [observedEventMass,phaseKrausObserved_traces,List.map_map,Function.comp_def,
    relabelObservedTrace,embedKrausPureTrace,hm,krausPureEventMass]
end
noncomputable section

/-- Embed the relabeled data and Kraus ancilla state into blank history zero with auxiliary
phase register zero. -/
def phaseKrausDeferredInput (e : Fin d ≃ (Fin n × Fin q) × W) (zero : Fin s)
    (R : ℕ) (ψ : QState (Fin d)) :
    QState (PhasePaddingSpace n q (W × Fin s) (Fin (R+1))) :=
  phaseHistoryInput (fun y => if y.2 = 0 then phaseKrausInput e zero ψ y.1 else 0)
end
noncomputable section

/-- The deferred Kraus input is normalized whenever the original data state is normalized. -/
theorem phaseKrausDeferredInput_normalized (e : Fin d ≃ (Fin n × Fin q) × W) (zero : Fin s)
    (R : ℕ) (ψ : QState (Fin d)) (hψ : Normalized ψ) :
    Normalized (phaseKrausDeferredInput e zero R ψ) :=
  phaseHistory_initial_normalized R _ (phaseKrausInput_normalized e zero ψ hψ)
end
noncomputable section

/-- A well formed Kraus circuit has a unitary phase query simulation packing its embedded branch
states into history sectors. Its query count equals the Kraus budget and its gate count is
one plus three times that budget. -/
theorem phase_kraus_full_branch_purification
    (e : Fin d ≃ (Fin n × Fin q) × W) (zero : Fin s)
    (P : KrausCircuit d s) (hP : krausCircuitWellFormed P) :
    ∃ (R : ℕ) (C : Circuit (PhasePaddingSpace n q (W × Fin s) (Fin (R+1)))),
      IsUnitaryCircuit C ∧ QueryCount C = krausCircuitBudget P ∧
      GateCount C = 1+3*krausCircuitBudget P ∧
      ∀ (input : Fin n → Fin q) (ψ : QState (Fin d)),
        let ts := (krausCircuitTraces (phaseKrausOracle e input) P ψ).map
          (fun t => relabelObservedTrace (phaseKrausLayout e) (embedKrausPureTrace zero t))
        ts.length ≤ R+1 ∧ ∀ x,
          Run (phaseOracle (W := (W × Fin s) × Fin (R+1) × Fin q) input) C
            (phaseKrausDeferredInput e zero R ψ) x =
          if x.2.2.2 = 0 then
            (ts.getD x.2.2.1.val (emptyObservedTrace _)).state (x.1,x.2.1) else 0 := by
  obtain ⟨R,C,hC,hq,hg,hs⟩ := phase_observed_full_branch_purification
    (phaseKrausObserved e zero P hP) (phaseKrausObserved_legal e zero P hP)
  rw [phaseKrausObserved_depth] at hq hg
  refine ⟨R,C,hC,hq,hg,?_⟩
  intro input ψ
  simpa only [phaseKrausObserved_traces,phaseKrausDeferredInput] using!
      hs input (phaseKrausInput e zero ψ)
end
noncomputable section

/-- For an output separating Hermitian witness, a successful Boolean Kraus circuit satisfies the
binary error adversary bound in terms of its query budget [HoyerLeeSpalek2007]. -/
theorem phase_kraus_binary_query_lower_bound
    {X : Type} [Fintype X] [DecidableEq X]
    (e : Fin d ≃ (Fin n × Fin q) × W) (zero : Fin s)
    (input : X → Fin n → Fin q) (f : X → Bool) (Gamma : Matrix X X ℂ)
    (P : KrausCircuit d s) (hP : krausCircuitWellFormed P)
    (ψ : QState (Fin d)) (hψ : Normalized ψ) (eps : ℝ) (he0 : 0 ≤ eps) (he1 : eps ≤ 1/2)
    (hG : Gamma.IsHermitian) (hz : ∀ x y, f x = f y → Gamma x y = 0)
    (hsuccess : ∀ x, 1-eps ≤ krausPureEventMass (phaseKrausOracle e (input x)) P ψ
      (fun b _ => decide (b = f x))) :
    (1-2*Real.sqrt (eps*(1-eps))) * ‖Gamma‖ ≤
      2 * (krausCircuitBudget P : ℝ) * maxFilterNorm input Gamma := by
  have hlegal : observedWellFormed (phaseKrausObserved e zero P hP) :=
    phaseKrausObserved_legal e zero P hP
  have hs (x : X) : 1-eps ≤ observedEventMass (phaseOracle (W := W × Fin s) (input x))
      (phaseKrausObserved e zero P hP) (phaseKrausInput e zero ψ)
      (fun t => decide (t.accepted = f x)) := by
    rw [phaseKrausObserved_event e zero P hP (input x) ψ (fun b _ => decide (b = f x))]
    exact hsuccess x
  let D0 : DecidableEq ((Fin n × Fin q) × (W × Fin s)) := inferInstance
  have hs' (D : DecidableEq ((Fin n × Fin q) × (W × Fin s))) :
      ∀ x, 1-eps ≤ @observedEventMass ((Fin n × Fin q) × (W × Fin s)) _ D
        (phaseOracle (W := W × Fin s) (input x)) (phaseKrausObserved e zero P hP)
        (phaseKrausInput e zero ψ) (fun t => decide (t.accepted = f x)) := by
    have hD : D = D0 := Subsingleton.elim _ _
    rw [hD]
    exact hs
  have h := phase_observed_binary_query_lower_bound input f Gamma
    (phaseKrausObserved e zero P hP) (by convert! hlegal using 1) (phaseKrausInput e zero ψ)
    (phaseKrausInput_normalized e zero ψ hψ) eps he0 he1 hG hz (hs' _)
  simpa only [phaseKrausObserved_depth] using! h
end
noncomputable section
/-- Replace a pure trace's state by its outer product while preserving its return flag, counts,
and measurement record. -/
def krausOuterTrace (t : BranchTrace (Fin d)) : MixedBranchTrace d :=
  ⟨outerProduct t.state,t.accepted,t.queries,t.gates,t.measurements,t.outcomes⟩
end
noncomputable section

/-- Kraus mixed execution on a pure outer product equals the outer product conversion of every
pure execution trace. -/
theorem krausMixedTraces_outer (O : Operator d) (P : KrausCircuit d s) (ψ : QState (Fin d)) :
    krausCircuitMixedTraces O P (outerProduct ψ) =
      (krausCircuitTraces O P ψ).map krausOuterTrace := by
  induction P generalizing ψ with
  | halt b => rfl
  | step action P ih =>
    cases action <;>
      simp only [krausCircuitMixedTraces,krausCircuitTraces,conjBranch_outerProduct,ih,
        List.map_map,Function.comp_def,krausOuterTrace,ApplyGate]
  | instrument K next ih =>
    simp only [krausCircuitMixedTraces,krausCircuitTraces,conjBranch_outerProduct,ih,
      List.map_flatten,List.map_ofFn,List.map_map,Function.comp_def,krausOuterTrace,ApplyGate]
end
noncomputable section

/-- Pure Kraus event mass equals mixed event mass on the initial state's outer product. -/
theorem krausPureEventMass_eq_mixed (O : Operator d) (P : KrausCircuit d s)
    (ψ : QState (Fin d)) (event : Bool → List (ℕ × ℕ) → Bool) :
    krausPureEventMass O P ψ event = krausCircuitEventMass O P (outerProduct ψ) event := by
  simp only [krausCircuitEventMass,krausMixedTraces_outer,krausPureEventMass,
    List.map_map,Function.comp_def,krausOuterTrace,mixedMass,trace_outerProduct,Complex.ofReal_re]
  rfl
end
noncomputable section

/-- A fitting padded Kraus compilation preserves instrument event mass on a pure input after
restoring the original measurement record. -/
theorem phase_instrument_padded_event
    (e : Fin d ≃ (Fin n × Fin q) × W) (zero : Fin s)
    (P : InstrumentCircuit d) (hP : instrumentCircuitWellFormed P)
    (hfit : variableKrausFits s (compileInstrumentCircuit P))
    (input : Fin n → Fin q) (ψ : QState (Fin d))
    (event : Bool → List (ℕ × ℕ) → Bool) :
    let K := padVariableKraus s (compileInstrumentCircuit P)
    let hK := padVariableKraus_wellFormed _ s hfit (compileInstrumentCircuit_wellFormed P hP)
    observedEventMass (phaseOracle (W := W × Fin s) input) (phaseKrausObserved e zero K hK)
      (phaseKrausInput e zero ψ)
      (fun t => event t.accepted (restoreInstrumentRecord P
        (restoreVariableKrausRecord (compileInstrumentCircuit P) t.outcomes))) =
      instrumentCircuitEventMass (phaseKrausOracle e input) P (outerProduct ψ) event := by
  (try dsimp only)
  rw [phaseKrausObserved_event e zero _ _ input ψ (fun b rec =>
      event b (restoreInstrumentRecord P (restoreVariableKrausRecord (compileInstrumentCircuit P) rec))),
    krausPureEventMass_eq_mixed,
    variableKraus_padding_event (phaseKrausOracle e input) (compileInstrumentCircuit P) s hfit
      (outerProduct ψ) (fun b rec => event b (restoreInstrumentRecord P rec)),
    instrumentCircuit_compile_event]
end
noncomputable section

/-- The maximum number of queries along an instrument circuit branch, taking the supremum over
instrument outcomes. -/
def instrumentCircuitQueryBudget : InstrumentCircuit d → ℕ
  | .halt _ => 0
  | .step (.gate _) P => instrumentCircuitQueryBudget P
  | .step .query P => instrumentCircuitQueryBudget P + 1
  | .instrument _ _ next => Finset.univ.sup (fun o => instrumentCircuitQueryBudget (next o))
end
noncomputable section

/-- Compiling an instrument circuit to a variable Kraus circuit does not exceed its instrument
query budget. -/
theorem instrument_compile_budget_le (P : InstrumentCircuit d) :
    variableKrausBudget (compileInstrumentCircuit P) ≤ instrumentCircuitQueryBudget P := by
  induction P with
  | halt b => exact le_rfl
  | step action P ih =>
    cases action with
    | gate G => exact ih
    | query => exact Nat.add_le_add_right ih 1
  | instrument a I next ih =>
    apply Finset.sup_le
    intro k _
    exact (ih (instrumentFineEquiv d a k).1).trans
      (Finset.le_sup (f := fun o => instrumentCircuitQueryBudget (next o)) (Finset.mem_univ _))
end
noncomputable section

/-- For an output separating Hermitian witness, a successful Boolean instrument circuit on a
normalized pure input satisfies the binary error adversary query bound [HoyerLeeSpalek2007]. -/
theorem phase_instrument_binary_query_lower_bound
    {X : Type} [Fintype X] [DecidableEq X]
    (e : Fin d ≃ (Fin n × Fin q) × W)
    (input : X → Fin n → Fin q) (f : X → Bool) (Gamma : Matrix X X ℂ)
    (P : InstrumentCircuit d) (hP : instrumentCircuitWellFormed P)
    (ψ : QState (Fin d)) (hψ : Normalized ψ) (eps : ℝ) (he0 : 0 ≤ eps) (he1 : eps ≤ 1/2)
    (hG : Gamma.IsHermitian) (hz : ∀ x y, f x = f y → Gamma x y = 0)
    (hsuccess : ∀ x, 1-eps ≤ instrumentCircuitEventMass (phaseKrausOracle e (input x)) P (outerProduct ψ)
      (fun b _ => decide (b = f x))) :
    (1-2*Real.sqrt (eps*(1-eps))) * ‖Gamma‖ ≤
      2 * (instrumentCircuitQueryBudget P : ℝ) * maxFilterNorm input Gamma := by
  let V := compileInstrumentCircuit P
  let S := variableKrausWidth V + 1
  have hfit : variableKrausFits S V := variableKraus_fits_of_width_le V S (Nat.le_add_right _ _)
  have hK := padVariableKraus_wellFormed V S hfit (compileInstrumentCircuit_wellFormed P hP)
  have hs (x : X) : 1-eps ≤ krausPureEventMass (phaseKrausOracle e (input x))
      (padVariableKraus S V) ψ (fun b _ => decide (b = f x)) := by
    rw [krausPureEventMass_eq_mixed]
    have hpad := variableKraus_padding_event (phaseKrausOracle e (input x)) V S hfit
      (outerProduct ψ) (fun b _ => decide (b = f x))
    have hcp := instrumentCircuit_compile_event (phaseKrausOracle e (input x)) P
      (outerProduct ψ) (fun b _ => decide (b = f x))
    exact (hpad.trans hcp).symm ▸ hsuccess x
  have hb := phase_kraus_binary_query_lower_bound e (0 : Fin S) input f Gamma
    (padVariableKraus S V) hK ψ hψ eps he0 he1 hG hz hs
  have hq : krausCircuitBudget (padVariableKraus S V) ≤ instrumentCircuitQueryBudget P := by
    rw [padVariableKraus_budget V S hfit]
    exact instrument_compile_budget_le P
  have hqr : (krausCircuitBudget (padVariableKraus S V) : ℝ) ≤ instrumentCircuitQueryBudget P :=
    Nat.cast_le.mpr hq
  exact hb.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hqr (by norm_num))
    (maxFilterNorm_nonneg input Gamma))
end
noncomputable section

/-- The list of decoded return flags and measurement records of observed traces is independent
of the oracle and input state. -/
theorem observedDecoder_syntax {I Y : Type} [Fintype I] [DecidableEq I]
    (O : Matrix I I ℂ) (P : ObservedCircuit I) (ψ : QState I)
    (decode : Bool → List (ℕ × ℕ) → Y) :
    (observedTraces O P ψ).map (fun t => decode t.accepted t.outcomes) =
      (observedTraces 1 P 0).map (fun t => decode t.accepted t.outcomes) := by
  rw [← observedPairedTraces_left O 1 P ψ 0,← observedPairedTraces_right O 1 P ψ 0]
  simp only [List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro t ht
  have hh := observedPairedTraces_metadata O 1 P ψ 0 t ht
  rw [hh.1,hh.2.2.2.2]
end
noncomputable section

/-- Decode the syntactic observed branch selected by a history index, using `decode false []`
when the index is absent. -/
def phaseObservedDecodedLabel {Y : Type}
    (P : ObservedCircuit ((Fin n × Fin q) × W)) (R : ℕ)
    (decode : Bool → List (ℕ × ℕ) → Y)
    (x : PhasePaddingSpace n q W (Fin (R+1))) : Y :=
  ((observedTraces 1 P 0).map (fun t => decode t.accepted t.outcomes)).getD
    x.2.2.1.val (decode false [])
end
noncomputable section

/-- Under the packed branch state formula, decoded label POVM probabilities equal the masses of
observed branches with that decoded output. -/
theorem phase_observed_decode_transport {Y : Type} [Fintype Y] [DecidableEq Y]
    (P : ObservedCircuit ((Fin n × Fin q) × W)) (R : ℕ)
    (decode : Bool → List (ℕ × ℕ) → Y)
    (C : Circuit (PhasePaddingSpace n q W (Fin (R+1))))
    (input : Fin n → Fin q) (ψ : QState ((Fin n × Fin q) × W)) (y : Y)
    (hlen : (observedTraces (phaseOracle (W := W) input) P ψ).length ≤ R+1)
    (hstate : ∀ x,
      Run (phaseOracle (W := W × Fin (R+1) × Fin q) input) C
        (phaseHistoryInput (fun z => if z.2 = 0 then ψ z.1 else 0)) x =
      if x.2.2.2 = 0 then
        ((observedTraces (phaseOracle (W := W) input) P ψ).getD
          x.2.2.1.val (emptyObservedTrace _)).state (x.1,x.2.1) else 0) :
    povmProb (labelPovm (phaseObservedDecodedLabel P R decode)) y
      (Run (phaseOracle (W := W × Fin (R+1) × Fin q) input) C
        (phaseHistoryInput (fun z => if z.2 = 0 then ψ z.1 else 0))) =
      observedEventMass (phaseOracle (W := W) input) P ψ
        (fun t => decide (decode t.accepted t.outcomes = y)) := by
  let ts := observedTraces (phaseOracle (W := W) input) P ψ
  have he : outcomeEvent (phaseObservedDecodedLabel P R decode) y =
      Finset.univ.filter (fun x => decide
        (decode (ts.getD x.2.2.1.val (emptyObservedTrace _)).accepted
          (ts.getD x.2.2.1.val (emptyObservedTrace _)).outcomes = y)) := by
    ext x
    simp only [outcomeEvent,Finset.mem_filter,Finset.mem_univ,true_and,phaseObservedDecodedLabel,
      decide_eq_true_eq]
    have hh := List.getD_map ts (emptyObservedTrace _) (fun t => decode t.accepted t.outcomes)
      (n := x.2.2.1.val)
    rw [observedDecoder_syntax] at hh
    change ((observedTraces 1 P 0).map (fun t => decode t.accepted t.outcomes)).getD
      x.2.2.1.val (decode false []) = _ at hh
    rw [hh]
  rw [labelPovm_povmProb,funext hstate,he]
  change MeasureProb (phaseHistoryInput (fun x : ((Fin n × Fin q) × W) × Fin (R+1) =>
    (ts.getD x.2.val (emptyObservedTrace _)).state x.1)) _ = _
  rw [phasePackedTrace_readout ts (R+1) hlen
    (fun t => decide (decode t.accepted t.outcomes = y))]
  rfl
end
noncomputable section

/-- A successful decoded observed circuit with normalized pure input satisfies the general
output adversary bound with error factor `1 - 2 * sqrt (eps * (1 - eps)) - 2 * eps`
[HoyerLeeSpalek2007]. -/
theorem phase_observed_query_lower_bound
    {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (input : X → Fin n → Fin q) (f : X → Y) (Gamma : Matrix X X ℂ)
    (P : ObservedCircuit ((Fin n × Fin q) × W)) (hP : observedWellFormed P)
    (decode : Bool → List (ℕ × ℕ) → Y)
    (ψ : QState ((Fin n × Fin q) × W)) (hψ : Normalized ψ)
    (eps : ℝ) (he0 : 0 ≤ eps) (he1 : eps ≤ 1/2)
    (hG : Gamma.IsHermitian) (hz : ∀ x y, f x = f y → Gamma x y = 0)
    (hsuccess : ∀ x, 1-eps ≤ observedEventMass (phaseOracle (W := W) (input x)) P ψ
      (fun t => decide (decode t.accepted t.outcomes = f x))) :
    (1-2*Real.sqrt (eps*(1-eps))-2*eps) * ‖Gamma‖ ≤
      2 * (observedQueryDepth P : ℝ) * maxFilterNorm input Gamma := by
  obtain ⟨R,C,hC,hq,_,hstates⟩ := phase_observed_full_branch_purification P hP
  let ψ' := phaseHistoryInput (H := Fin (R+1)) (fun z => if z.2 = 0 then ψ z.1 else 0)
  let out := labelPovm (phaseObservedDecodedLabel P R decode)
  have hrun : IsBoundedErrorRun input f C ψ' out eps := by
    refine ⟨?_,phaseHistory_initial_normalized R ψ hψ,isPovm_labelPovm _,he0,he1,?_⟩
    · convert! hC using 1
    intro x
    have ht := phase_observed_decode_transport P R decode C (input x) ψ (f x)
      (hstates (input x) ψ).1 (hstates (input x) ψ).2
    exact ht.symm ▸ hsuccess x
  have hb := phase_povm_query_lower_bound q n X (W × Fin (R+1) × Fin q) Y
    input f Gamma C ψ' out eps hG hz hrun
  simpa only [hq] using! hb
end
noncomputable section

/-- A successful decoded instrument circuit with normalized pure input satisfies the general
output adversary witness bound in terms of its query budget [HoyerLeeSpalek2007]. -/
theorem phase_instrument_query_lower_bound
    {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (e : Fin d ≃ (Fin n × Fin q) × W)
    (input : X → Fin n → Fin q) (f : X → Y) (Gamma : Matrix X X ℂ)
    (P : InstrumentCircuit d) (hP : instrumentCircuitWellFormed P)
    (decode : Bool → List (ℕ × ℕ) → Y)
    (ψ : QState (Fin d)) (hψ : Normalized ψ) (eps : ℝ) (he0 : 0 ≤ eps) (he1 : eps ≤ 1/2)
    (hG : Gamma.IsHermitian) (hz : ∀ x y, f x = f y → Gamma x y = 0)
    (hsuccess : ∀ x, 1-eps ≤ instrumentCircuitEventMass (phaseKrausOracle e (input x)) P (outerProduct ψ)
      (fun b rec => decide (decode b rec = f x))) :
    (1-2*Real.sqrt (eps*(1-eps))-2*eps) * ‖Gamma‖ ≤
      2 * (instrumentCircuitQueryBudget P : ℝ) * maxFilterNorm input Gamma := by
  let V := compileInstrumentCircuit P
  let S := variableKrausWidth V + 1
  have hfit : variableKrausFits S V := variableKraus_fits_of_width_le V S (Nat.le_add_right _ _)
  let K := padVariableKraus S V
  have hK : krausCircuitWellFormed K :=
    padVariableKraus_wellFormed V S hfit (compileInstrumentCircuit_wellFormed P hP)
  let Q := phaseKrausObserved e (0 : Fin S) K hK
  let psi0 := phaseKrausInput e (0 : Fin S) ψ
  let decQ := fun b rec => decode b (restoreInstrumentRecord P (restoreVariableKrausRecord V rec))
  have hs (x : X) : 1-eps ≤ observedEventMass (phaseOracle (W := W × Fin S) (input x)) Q psi0
      (fun t => decide (decQ t.accepted t.outcomes = f x)) := by
    have ht := phase_instrument_padded_event e (0 : Fin S) P hP hfit (input x) ψ
      (fun b rec => decide (decode b rec = f x))
    exact ht.symm ▸ hsuccess x
  let D0 : DecidableEq ((Fin n × Fin q) × (W × Fin S)) := inferInstance
  have hs' (D : DecidableEq ((Fin n × Fin q) × (W × Fin S))) :
      ∀ x, 1-eps ≤ @observedEventMass ((Fin n × Fin q) × (W × Fin S)) _ D
        (phaseOracle (W := W × Fin S) (input x)) Q psi0
        (fun t => decide (decQ t.accepted t.outcomes = f x)) := by
    have hD : D = D0 := Subsingleton.elim _ _
    rw [hD]
    exact hs
  have hb := phase_observed_query_lower_bound input f Gamma Q
    (by convert! phaseKrausObserved_legal e (0 : Fin S) K hK using 1) decQ psi0
    (phaseKrausInput_normalized e (0 : Fin S) ψ hψ) eps he0 he1 hG hz (hs' _)
  have hq : observedQueryDepth Q ≤ instrumentCircuitQueryBudget P := by
    rw [phaseKrausObserved_depth,padVariableKraus_budget V S hfit]
    exact instrument_compile_budget_le P
  have hqr : (observedQueryDepth Q : ℝ) ≤ instrumentCircuitQueryBudget P := Nat.cast_le.mpr hq
  exact hb.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hqr (by norm_num))
    (maxFilterNorm_nonneg input Gamma))
end
noncomputable section

/-- A successful decoded observed circuit on a density operator satisfies the general output
adversary witness bound in terms of `observedQueryBudget` [HoyerLeeSpalek2007]. -/
theorem phase_observed_mixed_query_lower_bound
    {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (e : Fin d ≃ (Fin n × Fin q) × W)
    (input : X → Fin n → Fin q) (f : X → Y) (Gamma : Matrix X X ℂ)
    (P : ObservedCircuit (Fin d)) (hP : observedWellFormed P)
    (decode : Bool → List (ℕ × ℕ) → Y)
    (rho : Operator d) (hrho : IsDensityOperator rho) (eps : ℝ) (he0 : 0 ≤ eps) (he1 : eps ≤ 1/2)
    (hG : Gamma.IsHermitian) (hz : ∀ x y, f x = f y → Gamma x y = 0)
    (hsuccess : ∀ x, 1-eps ≤ mixedObservedEventMass (phaseKrausOracle e (input x)) P rho
      (fun b rec => decide (decode b rec = f x))) :
    (1-2*Real.sqrt (eps*(1-eps))-2*eps) * ‖Gamma‖ ≤
      2 * (observedQueryBudget P : ℝ) * maxFilterNorm input Gamma := by
  obtain ⟨psi,hpsi,hmarginal⟩ := density_purification_normalized rho hrho
  let Q := relabelObserved (phaseKrausLayout (s := d) e) (liftObservedEnvironment (E := Fin d) P)
  let psi0 := relabelState (phaseKrausLayout (s := d) e) psi
  have hQ : observedWellFormed Q := relabelObserved_wellFormed _ _
    (liftObservedEnvironment_wellFormed P hP)
  have hs (x : X) : 1-eps ≤ observedEventMass (phaseOracle (W := W × Fin d) (input x)) Q psi0
      (fun t => decide (decode t.accepted t.outcomes = f x)) := by
    have hp := observed_purification_event (phaseKrausOracle e (input x)) P psi
      (fun b rec => decide (decode b rec = f x))
    have hl := relabelObserved_event (phaseKrausLayout (s := d) e)
      (TensorGate (phaseKrausOracle e (input x)) (1 : Operator d))
      (liftObservedEnvironment (E := Fin d) P) psi (fun b rec => decide (decode b rec = f x))
    rw [phaseKrausOracle_extend] at hl
    rw [hmarginal] at hp
    exact (hl.trans hp).symm ▸ hsuccess x
  let D0 : DecidableEq ((Fin n × Fin q) × (W × Fin d)) := inferInstance
  have hs' (D : DecidableEq ((Fin n × Fin q) × (W × Fin d))) :
      ∀ x, 1-eps ≤ @observedEventMass ((Fin n × Fin q) × (W × Fin d)) _ D
        (phaseOracle (W := W × Fin d) (input x)) Q psi0
        (fun t => decide (decode t.accepted t.outcomes = f x)) := by
    have hD : D = D0 := Subsingleton.elim _ _
    rw [hD]
    exact hs
  have hb := phase_observed_query_lower_bound input f Gamma Q
    (by convert! hQ using 1) decode psi0 (normalized_relabelState _ hpsi) eps he0 he1 hG hz (hs' _)
  have hq : observedQueryDepth Q = observedQueryBudget P := by
    rw [observedQueryDepth_eq_budget,relabelObserved_budget,liftObservedEnvironment_budget]
  simpa only [hq] using! hb
end
noncomputable section
/-- Identify a flattened data and Kraus ancilla index with the phase query register and enlarged
workspace layout. -/
def phaseKrausFlatLayout (e : Fin d ≃ (Fin n × Fin q) × W) :
    Fin (d*s) ≃ (Fin n × Fin q) × (W × Fin s) :=
  finProdFinEquiv.symm.trans (phaseKrausLayout e)
end
noncomputable section
omit [Fintype W] in

/-- The phase oracle in the flattened layout equals the data oracle tensored with the ancilla
identity and reindexed by `finProdFinEquiv`. -/
theorem phaseKrausFlatOracle (e : Fin d ≃ (Fin n × Fin q) × W) (input : Fin n → Fin q) :
    phaseKrausOracle (phaseKrausFlatLayout (s := s) e) input =
      relabelGate finProdFinEquiv (TensorGate (phaseKrausOracle e input) (1 : Operator s)) := by
  unfold phaseKrausOracle
  rw [← phaseKrausOracle_extend (s := s) e input,relabelGate_trans]
  congr 1
  ext x
  simp [phaseKrausFlatLayout]
end
noncomputable section

/-- A successful decoded Kraus circuit on a density operator satisfies the general output
adversary witness bound in terms of its Kraus query budget [HoyerLeeSpalek2007]. -/
theorem phase_kraus_mixed_query_lower_bound
    {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (e : Fin d ≃ (Fin n × Fin q) × W) (zero : Fin s)
    (input : X → Fin n → Fin q) (f : X → Y) (Gamma : Matrix X X ℂ)
    (P : KrausCircuit d s) (hP : krausCircuitWellFormed P)
    (decode : Bool → List (ℕ × ℕ) → Y)
    (rho : Operator d) (hrho : IsDensityOperator rho) (eps : ℝ) (he0 : 0 ≤ eps) (he1 : eps ≤ 1/2)
    (hG : Gamma.IsHermitian) (hz : ∀ x y, f x = f y → Gamma x y = 0)
    (hsuccess : ∀ x, 1-eps ≤ krausCircuitEventMass (phaseKrausOracle e (input x)) P rho
      (fun b rec => decide (decode b rec = f x))) :
    (1-2*Real.sqrt (eps*(1-eps))-2*eps) * ‖Gamma‖ ≤
      2 * (krausCircuitBudget P : ℝ) * maxFilterNorm input Gamma := by
  let flat : (Fin d × Fin s) ≃ Fin (d*s) := finProdFinEquiv
  let Q := relabelObserved flat (compileKrausCircuit zero P hP)
  let rho0 := relabelGate flat (TensorGate rho (outerProduct (Ket zero)))
  have hk := outerProduct_density (normalized_ket zero)
  have hrho0 : IsDensityOperator rho0 := by
    refine ⟨(Qatlib.Foundations.PureStateMath.BornBridge.posSemidef_tensorGate hrho.1 hk.1).submatrix flat.symm,?_⟩
    change Matrix.trace
        ((TensorGate rho (outerProduct (Ket zero))).submatrix flat.symm flat.symm) = 1
    rw [Matrix.trace_submatrix,Qatlib.Foundations.PureStateMath.BornBridge.trace_tensorGate,hrho.2,hk.2,mul_one]
  have hQ : observedWellFormed Q := relabelObserved_wellFormed flat _
    (compileKrausCircuit_wellFormed zero P hP)
  have hs (x : X) : 1-eps ≤ mixedObservedEventMass
      (phaseKrausOracle (phaseKrausFlatLayout (s := s) e) (input x)) Q rho0
      (fun b rec => decide (decode b rec = f x)) := by
    rw [phaseKrausFlatOracle]
    exact (kraus_compiled_event flat zero (phaseKrausOracle e (input x)) P hP rho
      (fun b rec => decide (decode b rec = f x))).symm ▸ hsuccess x
  have hb := phase_observed_mixed_query_lower_bound (phaseKrausFlatLayout (s := s) e)
    input f Gamma Q hQ decode rho0 hrho0 eps he0 he1 hG hz hs
  have hq : observedQueryBudget Q = krausCircuitBudget P := by
    rw [relabelObserved_budget,compileKrausCircuit_budget]
  simpa only [hq] using! hb
end
noncomputable section

/-- A successful decoded instrument circuit on a density operator satisfies the general output
adversary witness bound in terms of its instrument query budget [HoyerLeeSpalek2007]. -/
theorem phase_instrument_mixed_query_lower_bound
    {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (e : Fin d ≃ (Fin n × Fin q) × W)
    (input : X → Fin n → Fin q) (f : X → Y) (Gamma : Matrix X X ℂ)
    (P : InstrumentCircuit d) (hP : instrumentCircuitWellFormed P)
    (decode : Bool → List (ℕ × ℕ) → Y)
    (rho : Operator d) (hrho : IsDensityOperator rho) (eps : ℝ) (he0 : 0 ≤ eps) (he1 : eps ≤ 1/2)
    (hG : Gamma.IsHermitian) (hz : ∀ x y, f x = f y → Gamma x y = 0)
    (hsuccess : ∀ x, 1-eps ≤ instrumentCircuitEventMass (phaseKrausOracle e (input x)) P rho
      (fun b rec => decide (decode b rec = f x))) :
    (1-2*Real.sqrt (eps*(1-eps))-2*eps) * ‖Gamma‖ ≤
      2 * (instrumentCircuitQueryBudget P : ℝ) * maxFilterNorm input Gamma := by
  let V := compileInstrumentCircuit P
  let S := variableKrausWidth V + 1
  have hfit : variableKrausFits S V := variableKraus_fits_of_width_le V S (Nat.le_add_right _ _)
  have hK := padVariableKraus_wellFormed V S hfit (compileInstrumentCircuit_wellFormed P hP)
  let decK := fun b rec => decode b (restoreInstrumentRecord P (restoreVariableKrausRecord V rec))
  have hs (x : X) : 1-eps ≤ krausCircuitEventMass (phaseKrausOracle e (input x))
      (padVariableKraus S V) rho (fun b rec => decide (decK b rec = f x)) := by
    have hp := variableKraus_padding_event (phaseKrausOracle e (input x)) V S hfit rho
      (fun b rec => decide (decode b (restoreInstrumentRecord P rec) = f x))
    have hi := instrumentCircuit_compile_event (phaseKrausOracle e (input x)) P rho
      (fun b rec => decide (decode b rec = f x))
    exact (hp.trans hi).symm ▸ hsuccess x
  have hb := phase_kraus_mixed_query_lower_bound e (0 : Fin S) input f Gamma
    (padVariableKraus S V) hK decK rho hrho eps he0 he1 hG hz hs
  have hq : krausCircuitBudget (padVariableKraus S V) ≤ instrumentCircuitQueryBudget P := by
    rw [padVariableKraus_budget V S hfit]
    exact instrument_compile_budget_le P
  have hqr : (krausCircuitBudget (padVariableKraus S V) : ℝ) ≤ instrumentCircuitQueryBudget P :=
    Nat.cast_le.mpr hq
  exact hb.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hqr (by norm_num))
    (maxFilterNorm_nonneg input Gamma))
end
noncomputable section

/-- For successful decoded instrument computation on a density operator, the general adversary
value times half the general output error factor is bounded by the query budget
[HoyerLeeSpalek2007]. -/
theorem phase_instrument_mixed_value_bound
    {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (e : Fin d ≃ (Fin n × Fin q) × W)
    (input : X → Fin n → Fin q) (f : X → Y)
    (P : InstrumentCircuit d) (hP : instrumentCircuitWellFormed P)
    (decode : Bool → List (ℕ × ℕ) → Y)
    (rho : Operator d) (hrho : IsDensityOperator rho) (eps : ℝ) (he0 : 0 ≤ eps) (he1 : eps ≤ 1/2)
    (hsuccess : ∀ x, 1-eps ≤ instrumentCircuitEventMass (phaseKrausOracle e (input x)) P rho
      (fun b rec => decide (decode b rec = f x))) :
    ENNReal.ofReal ((1-2*Real.sqrt (eps*(1-eps))-2*eps)/2) * advPmValue input f ≤
      (instrumentCircuitQueryBudget P : ℝ≥0∞) := by
  exact adversary_value_of_multiplicative_bound input f _ _ (fun Gamma hG hz =>
    phase_instrument_mixed_query_lower_bound e input f Gamma P hP decode rho hrho eps he0 he1 hG hz hsuccess)
end
variable {X W : Type} [Fintype X] [DecidableEq X] [Fintype W] [DecidableEq W]
variable {n q : ℕ} [NeZero q]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000
variable {n q : ℕ} [NeZero q] {W H : Type}
variable {n q : ℕ} [NeZero q] {W : Type} [Fintype W]
variable {n q d s : ℕ} [NeZero q] {W : Type} [Fintype W]
variable {d : ℕ}
noncomputable section

/-- Limit an instrument circuit to the given query budget, returning false when a further query
would exceed it. -/
def truncateInstrumentQueries : InstrumentCircuit d → ℕ → InstrumentCircuit d
  | .halt b, _ => .halt b
  | .step (.gate U) P, K => .step (.gate U) (truncateInstrumentQueries P K)
  | .step .query _, 0 => .halt false
  | .step .query P, K+1 => .step .query (truncateInstrumentQueries P K)
  | .instrument s I next, K => .instrument s I (fun o => truncateInstrumentQueries (next o) K)
end
noncomputable section

/-- Truncating a well formed instrument circuit preserves well formedness. -/
theorem truncateInstrumentQueries_legal (P : InstrumentCircuit d)
    (hP : instrumentCircuitWellFormed P) (K : ℕ) :
    instrumentCircuitWellFormed (truncateInstrumentQueries P K) := by
  induction P generalizing K with
  | halt b => trivial
  | step action P ih =>
    cases action with
    | gate U => exact ⟨hP.1,ih hP.2 K⟩
    | query => cases K with
      | zero => trivial
      | succ K => exact ih hP K
  | instrument s I next ih => exact fun o => ih o (hP o) K
end
noncomputable section

/-- The query budget of a truncated instrument circuit is at most the truncation threshold. -/
theorem truncateInstrumentQueries_budget (P : InstrumentCircuit d) (K : ℕ) :
    instrumentCircuitQueryBudget (truncateInstrumentQueries P K) ≤ K := by
  induction P generalizing K with
  | halt b => exact Nat.zero_le _
  | step action P ih =>
    cases action with
    | gate U => exact ih K
    | query => cases K with
      | zero => exact le_rfl
      | succ K => exact Nat.add_le_add_right (ih K) 1
  | instrument s I next ih => exact Finset.sup_le (fun o _ => ih o K)
end
noncomputable section

/-- Every instrument execution trace has a positive semidefinite state when the input is
positive semidefinite. -/
theorem instrumentTraces_psd (O : Operator d) (P : InstrumentCircuit d)
    (rho : Operator d) (hrho : rho.PosSemidef) :
    ∀ t ∈ instrumentCircuitMixedTraces O P rho, t.state.PosSemidef := by
  induction P generalizing rho with
  | halt b => intro t ht; obtain rfl := List.mem_singleton.mp ht; exact hrho
  | step action P ih =>
    cases action with
    | gate U =>
      intro t ht
      obtain ⟨u,hu,rfl⟩ := List.mem_map.mp ht
      exact ih _ ((completelyPositive_conjBranch U).positive hrho) u hu
    | query =>
      intro t ht
      obtain ⟨u,hu,rfl⟩ := List.mem_map.mp ht
      exact ih _ ((completelyPositive_conjBranch O).positive hrho) u hu
  | instrument s I next ih =>
    intro t ht
    obtain ⟨xs,hxs,ht⟩ := List.mem_flatten.mp ht
    obtain ⟨o,rfl⟩ := List.mem_ofFn.mp hxs
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp ht
    exact ih o _ ((I.cp o).positive hrho) u hu
end
noncomputable section

/-- Every instrument execution trace has nonnegative mass on a positive semidefinite input. -/
theorem instrumentTraceMass_nonneg (O : Operator d) (P : InstrumentCircuit d)
    (rho : Operator d) (hrho : rho.PosSemidef) :
    ∀ t ∈ instrumentCircuitMixedTraces O P rho, 0 ≤ mixedMass t := by
  intro t ht
  exact (RCLike.nonneg_iff.mp (instrumentTraces_psd O P rho hrho t ht).trace_nonneg).1
end

/-- A sum over a list is nonnegative when every summand on that list is nonnegative. -/
private theorem real_list_sum_nonneg {α : Type} (xs : List α) (f : α → ℝ)
    (hf : ∀ x ∈ xs, 0 ≤ f x) : 0 ≤ (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    exact add_nonneg (hf x List.mem_cons_self)
      (ih (fun y hy => hf y (List.mem_cons_of_mem x hy)))

/-- Pointwise comparison on a list implies comparison of the corresponding real sums. -/
private theorem real_list_sum_mono {α : Type} (xs : List α) (f g : α → ℝ)
    (hfg : ∀ x ∈ xs, f x ≤ g x) : (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => exact le_rfl
  | cons x xs ih =>
    exact add_le_add (hfg x List.mem_cons_self)
      (ih (fun y hy => hfg y (List.mem_cons_of_mem x hy)))
noncomputable section

/-- Every instrument event has nonnegative mass on a positive semidefinite input. -/
theorem instrumentEventMass_nonneg (O : Operator d) (P : InstrumentCircuit d)
    (rho : Operator d) (hrho : rho.PosSemidef) (E : Bool → List (ℕ × ℕ) → Bool) :
    0 ≤ instrumentCircuitEventMass O P rho E := by
  apply real_list_sum_nonneg
  intro t ht
  split_ifs
  · exact instrumentTraceMass_nonneg O P rho hrho t ht
  · exact le_rfl
end
noncomputable section

/-- The total mass of instrument traces making at least the specified number of queries. -/
def instrumentQueryTailMass (O : Operator d) (P : InstrumentCircuit d)
    (rho : Operator d) (K : ℕ) : ℝ :=
  ((instrumentCircuitMixedTraces O P rho).map fun t => if K ≤ t.queries then mixedMass t else 0).sum
end
noncomputable section

/-- For a positive threshold and positive semidefinite input, query tail mass is at most the
expected query count divided by that threshold. -/
theorem instrumentQueryTail_le_expected (O : Operator d) (P : InstrumentCircuit d)
    (rho : Operator d) (hrho : rho.PosSemidef) (K : ℕ) (hK : 0 < K) :
    instrumentQueryTailMass O P rho K ≤ instrumentCircuitExpectedQueries O P rho / K := by
  apply (le_div_iff₀ (show (0 : ℝ) < K by exact_mod_cast hK)).mpr
  have hm := instrumentTraceMass_nonneg O P rho hrho
  unfold instrumentQueryTailMass instrumentCircuitExpectedQueries
  have hs : ∀ xs : List (MixedBranchTrace d),
      (∀ t ∈ xs, 0 ≤ mixedMass t) →
      ((xs.map fun t => if K ≤ t.queries then mixedMass t else 0).sum) * (K : ℝ) ≤
      (xs.map fun t => mixedMass t * t.queries).sum := by
    intro xs
    induction xs with
    | nil => intro _; simp
    | cons t xs ih =>
      intro hx
      have ht := hx t List.mem_cons_self
      have hi := ih (fun u hu => hx u (List.mem_cons_of_mem t hu))
      simp only [List.map_cons,List.sum_cons,add_mul]
      apply add_le_add ?_ hi
      by_cases hq : K ≤ t.queries
      · simp only [if_pos hq]
        exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hq) ht
      · simp only [if_neg hq,zero_mul]
        exact mul_nonneg ht (Nat.cast_nonneg _)
  exact hs _ hm
end
noncomputable section

/-- The mass of event traces using at most `K` queries is at most the event mass after
truncation to `K` queries. -/
theorem instrument_event_short_le_truncate (O : Operator d) (P : InstrumentCircuit d)
    (rho : Operator d) (hrho : rho.PosSemidef) (K : ℕ)
    (E : Bool → List (ℕ × ℕ) → Bool) :
    ((instrumentCircuitMixedTraces O P rho).map fun t =>
      if E t.accepted t.outcomes && decide (t.queries ≤ K) then mixedMass t else 0).sum ≤
      instrumentCircuitEventMass O (truncateInstrumentQueries P K) rho E := by
  induction P generalizing rho K E with
  | halt b => simp [truncateInstrumentQueries,instrumentCircuitEventMass,instrumentCircuitMixedTraces]
  | step action P ih =>
    cases action with
    | gate U =>
      simpa only [truncateInstrumentQueries,instrumentCircuitEventMass,instrumentCircuitMixedTraces,
        List.map_map,Function.comp_def] using!
        ih (conjBranch U rho) ((completelyPositive_conjBranch U).positive hrho) K E
    | query =>
      cases K with
      | zero =>
        have hz : ((instrumentCircuitMixedTraces O (.step .query P) rho).map fun t =>
            if E t.accepted t.outcomes && decide (t.queries ≤ 0) then mixedMass t else 0).sum = 0 := by
          simp [instrumentCircuitMixedTraces,List.map_map,Function.comp_def]
        rw [hz]
        exact instrumentEventMass_nonneg O _ rho hrho E
      | succ K =>
        simpa only [truncateInstrumentQueries,instrumentCircuitEventMass,instrumentCircuitMixedTraces,
          List.map_map,Function.comp_def,Nat.succ_eq_add_one,Nat.add_le_add_iff_right] using!
          ih (conjBranch O rho) ((completelyPositive_conjBranch O).positive hrho) K E
  | instrument s I next ih =>
    simp only [truncateInstrumentQueries,instrumentCircuitEventMass,instrumentCircuitMixedTraces,
      List.map_flatten,List.sum_flatten,List.map_map,Function.comp_def,List.map_ofFn,List.sum_ofFn]
    apply Finset.sum_le_sum
    intro o _
    exact ih o (I.branch o rho) ((I.cp o).positive hrho) K
      (fun b rec => E b ((s,o.val)::rec))
end
noncomputable section

/-- On a positive semidefinite input, truncating to `K` queries decreases event mass by at most
the expected query count divided by `K + 1`. -/
theorem instrument_event_sub_expected_le_truncate (O : Operator d) (P : InstrumentCircuit d)
    (rho : Operator d) (hrho : rho.PosSemidef) (K : ℕ)
    (E : Bool → List (ℕ × ℕ) → Bool) :
    instrumentCircuitEventMass O P rho E - instrumentCircuitExpectedQueries O P rho / (K+1 : ℕ) ≤
      instrumentCircuitEventMass O (truncateInstrumentQueries P K) rho E := by
  have hm := instrumentTraceMass_nonneg O P rho hrho
  have hsplit := real_list_sum_mono (instrumentCircuitMixedTraces O P rho)
    (fun t => if E t.accepted t.outcomes then mixedMass t else 0)
    (fun t => (if E t.accepted t.outcomes && decide (t.queries ≤ K) then mixedMass t else 0) +
      (if K+1 ≤ t.queries then mixedMass t else 0)) (by
        intro t ht
        have hmass := hm t ht
        by_cases hq : t.queries ≤ K
        · have hn : ¬ K+1 ≤ t.queries := by omega
          simp [hq,hn]
        · have hl : K+1 ≤ t.queries := by omega
          cases he : E t.accepted t.outcomes with
          | false => simpa [he,hq,hl] using! hmass
          | true => simp [he,hq,hl])
  rw [List.sum_map_add] at hsplit
  have htail := instrumentQueryTail_le_expected O P rho hrho (K+1) (Nat.succ_pos K)
  have hshort := instrument_event_short_le_truncate O P rho hrho K E
  change _ ≤ _ + instrumentQueryTailMass O P rho (K+1) at hsplit
  change instrumentCircuitEventMass O P rho E ≤ _ at hsplit
  linarith only [hsplit,htail,hshort]
end
noncomputable section

/-- If expected queries are uniformly at most `T`, truncation gives the adversary witness bound
with budget `K` and error `eps + T / (K + 1)`, provided that error is at most one half. -/
theorem phase_instrument_expected_truncation_bound
    {n q : ℕ} [NeZero q] {W X Y : Type} [Fintype W]
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (e : Fin d ≃ (Fin n × Fin q) × W)
    (input : X → Fin n → Fin q) (f : X → Y) (Gamma : Matrix X X ℂ)
    (P : InstrumentCircuit d) (hP : instrumentCircuitWellFormed P)
    (decode : Bool → List (ℕ × ℕ) → Y)
    (rho : Operator d) (hrho : IsDensityOperator rho) (eps T : ℝ) (he0 : 0 ≤ eps) (hT : 0 ≤ T)
    (K : ℕ) (hdelta : eps + T/(K+1 : ℕ) ≤ 1/2)
    (hG : Gamma.IsHermitian) (hz : ∀ x y, f x = f y → Gamma x y = 0)
    (hsuccess : ∀ x, 1-eps ≤ instrumentCircuitEventMass (phaseKrausOracle e (input x)) P rho
      (fun b rec => decide (decode b rec = f x)))
    (hexpected : ∀ x, instrumentCircuitExpectedQueries (phaseKrausOracle e (input x)) P rho ≤ T) :
    (1-2*Real.sqrt ((eps+T/(K+1 : ℕ))*(1-(eps+T/(K+1 : ℕ))))-2*(eps+T/(K+1 : ℕ))) * ‖Gamma‖ ≤
      2 * (K : ℝ) * maxFilterNorm input Gamma := by
  let delta := eps + T/(K+1 : ℕ)
  have hd0 : 0 ≤ delta := add_nonneg he0 (div_nonneg hT (Nat.cast_nonneg _))
  have hs (x : X) : 1-delta ≤ instrumentCircuitEventMass (phaseKrausOracle e (input x))
      (truncateInstrumentQueries P K) rho (fun b rec => decide (decode b rec = f x)) := by
    have hl := instrument_event_sub_expected_le_truncate (phaseKrausOracle e (input x)) P rho hrho.1 K
      (fun b rec => decide (decode b rec = f x))
    have he := div_le_div_of_nonneg_right (hexpected x) (show (0 : ℝ) ≤ (K+1 : ℕ) by positivity)
    have hsuccessx := hsuccess x
    dsimp only [delta]
    linarith
  have hb := phase_instrument_mixed_query_lower_bound e input f Gamma (truncateInstrumentQueries P K)
    (truncateInstrumentQueries_legal P hP K) decode rho hrho delta hd0 hdelta hG hz hs
  have hkr : (instrumentCircuitQueryBudget (truncateInstrumentQueries P K) : ℝ) ≤ K :=
    Nat.cast_le.mpr (truncateInstrumentQueries_budget P K)
  exact hb.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hkr (by norm_num))
    (maxFilterNorm_nonneg input Gamma))
end

/-- The general output progress factor is at least one quarter when its error parameter is at
most `1 / 16`. -/
private theorem small_error_progress_constant (delta : ℝ) (hd : delta ≤ 1/16) :
    1/4 ≤ 1-2*Real.sqrt (delta*(1-delta))-2*delta := by
  have hs : Real.sqrt (delta*(1-delta)) ≤ 1/4 :=
    (Real.sqrt_le_iff).mpr ⟨by norm_num,by nlinarith [sq_nonneg delta]⟩
  linarith
noncomputable section

/-- For exact decoded instrument computation with uniform expected query bound `T`, every output
separating Hermitian witness satisfies `‖Gamma‖ ≤ 128 * T * maxFilterNorm input Gamma`. -/
theorem phase_instrument_exact_expected_lower_bound
    {n q : ℕ} [NeZero q] {W X Y : Type} [Fintype W]
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (e : Fin d ≃ (Fin n × Fin q) × W)
    (input : X → Fin n → Fin q) (f : X → Y) (Gamma : Matrix X X ℂ)
    (P : InstrumentCircuit d) (hP : instrumentCircuitWellFormed P)
    (decode : Bool → List (ℕ × ℕ) → Y)
    (rho : Operator d) (hrho : IsDensityOperator rho) (T : ℝ) (hT : 0 ≤ T)
    (hG : Gamma.IsHermitian) (hz : ∀ x y, f x = f y → Gamma x y = 0)
    (hsuccess : ∀ x, 1 ≤ instrumentCircuitEventMass (phaseKrausOracle e (input x)) P rho
      (fun b rec => decide (decode b rec = f x)))
    (hexpected : ∀ x, instrumentCircuitExpectedQueries (phaseKrausOracle e (input x)) P rho ≤ T) :
    ‖Gamma‖ ≤ 128*T*maxFilterNorm input Gamma := by
  let K := Nat.floor (16*T)
  let delta := T/(K+1 : ℕ)
  have hfloor : (K : ℝ) ≤ 16*T := Nat.floor_le (by positivity)
  have hfloor' : 16*T < (K : ℝ)+1 := Nat.lt_floor_add_one (16*T)
  have hden : (0 : ℝ) < (K+1 : ℕ) := by positivity
  have hd : delta ≤ 1/16 := by
    apply (div_le_iff₀ hden).mpr
    norm_cast at hden
    push_cast
    linarith
  have hcoef := small_error_progress_constant delta hd
  have hb := phase_instrument_expected_truncation_bound e input f Gamma P hP decode rho hrho 0 T
    (by norm_num) hT K (by dsimp only [delta] at hd; linarith) hG hz
    (by simpa only [sub_zero] using! hsuccess) hexpected
  simp only [zero_add] at hb
  have hc : (1/4 : ℝ)*‖Gamma‖ ≤ 2*(K : ℝ)*maxFilterNorm input Gamma :=
    (mul_le_mul_of_nonneg_right hcoef (norm_nonneg Gamma)).trans hb
  have hq := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hfloor (show (0 : ℝ) ≤ 2 by norm_num)) (maxFilterNorm_nonneg input Gamma)
  nlinarith
end
noncomputable section

/-- Exact decoded instrument computation with uniform expected query bound `T` satisfies
`advPmValue input f ≤ ENNReal.ofReal (128 * T)`. -/
theorem phase_instrument_exact_expected_value_bound
    {n q : ℕ} [NeZero q] {W X Y : Type} [Fintype W]
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (e : Fin d ≃ (Fin n × Fin q) × W)
    (input : X → Fin n → Fin q) (f : X → Y)
    (P : InstrumentCircuit d) (hP : instrumentCircuitWellFormed P)
    (decode : Bool → List (ℕ × ℕ) → Y)
    (rho : Operator d) (hrho : IsDensityOperator rho) (T : ℝ) (hT : 0 ≤ T)
    (hsuccess : ∀ x, 1 ≤ instrumentCircuitEventMass (phaseKrausOracle e (input x)) P rho
      (fun b rec => decide (decode b rec = f x)))
    (hexpected : ∀ x, instrumentCircuitExpectedQueries (phaseKrausOracle e (input x)) P rho ≤ T) :
    advPmValue input f ≤ ENNReal.ofReal (128*T) := by
  unfold advPmValue
  apply iSup_le
  intro G
  have hb := phase_instrument_exact_expected_lower_bound e input f G.val P hP decode rho hrho T hT
    G.property.1 G.property.2.1 hsuccess hexpected
  have hn : 0 < ‖G.val‖ := norm_pos_iff.mpr G.property.2.2
  have hm : 0 < maxFilterNorm input G.val := by
    by_contra hh
    have hz := le_antisymm (not_lt.mp hh) (maxFilterNorm_nonneg input G.val)
    rw [hz,mul_zero] at hb
    exact (not_le_of_gt hn) hb
  rw [advPmWitnessValue,← ENNReal.ofReal_div_of_pos hm]
  exact ENNReal.ofReal_le_ofReal ((div_le_iff₀ hm).mpr hb)
end
noncomputable section

/-- For decoded instrument computation with error at most `1 / 16` and uniform expected query
bound `T`, each output separating Hermitian witness satisfies the norm bound with constant
`512`. -/
theorem phase_instrument_small_error_expected_lower_bound
    {n q : ℕ} [NeZero q] {W X Y : Type} [Fintype W]
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (e : Fin d ≃ (Fin n × Fin q) × W)
    (input : X → Fin n → Fin q) (f : X → Y) (Gamma : Matrix X X ℂ)
    (P : InstrumentCircuit d) (hP : instrumentCircuitWellFormed P)
    (decode : Bool → List (ℕ × ℕ) → Y)
    (rho : Operator d) (hrho : IsDensityOperator rho) (eps T : ℝ) (he0 : 0 ≤ eps) (he : eps ≤ 1/16) (hT : 0 ≤ T)
    (hG : Gamma.IsHermitian) (hz : ∀ x y, f x = f y → Gamma x y = 0)
    (hsuccess : ∀ x, 1-eps ≤ instrumentCircuitEventMass (phaseKrausOracle e (input x)) P rho
      (fun b rec => decide (decode b rec = f x)))
    (hexpected : ∀ x, instrumentCircuitExpectedQueries (phaseKrausOracle e (input x)) P rho ≤ T) :
    ‖Gamma‖ ≤ 512*T*maxFilterNorm input Gamma := by
  let K := Nat.floor (64*T)
  let delta := eps + T/(K+1 : ℕ)
  have hfloor : (K : ℝ) ≤ 64*T := Nat.floor_le (by positivity)
  have hfloor' : 64*T < (K : ℝ)+1 := Nat.lt_floor_add_one (64*T)
  have hden : (0 : ℝ) < (K+1 : ℕ) := by positivity
  have htail : T/(K+1 : ℕ) ≤ 1/64 := by
    apply (div_le_iff₀ hden).mpr
    push_cast
    linarith
  have hd : delta ≤ 5/64 := by dsimp only [delta]; linarith
  have hroot : Real.sqrt (delta*(1-delta)) ≤ 9/32 :=
    (Real.sqrt_le_iff).mpr ⟨by norm_num,by nlinarith [sq_nonneg delta]⟩
  have hcoef : (1/4 : ℝ) ≤ 1-2*Real.sqrt (delta*(1-delta))-2*delta := by linarith
  have hb := phase_instrument_expected_truncation_bound e input f Gamma P hP decode rho hrho eps T
    he0 hT K (by dsimp only [delta] at hd; linarith) hG hz hsuccess hexpected
  have hc : (1/4 : ℝ)*‖Gamma‖ ≤ 2*(K : ℝ)*maxFilterNorm input Gamma :=
    (mul_le_mul_of_nonneg_right hcoef (norm_nonneg Gamma)).trans hb
  have hq := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hfloor (show (0 : ℝ) ≤ 2 by norm_num)) (maxFilterNorm_nonneg input Gamma)
  nlinarith
end
noncomputable section

/-- Decoded instrument computation with error at most `1 / 16` and uniform expected query bound
`T` satisfies `advPmValue input f ≤ ENNReal.ofReal (512 * T)`. -/
theorem phase_instrument_small_error_expected_value_bound
    {n q : ℕ} [NeZero q] {W X Y : Type} [Fintype W]
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (e : Fin d ≃ (Fin n × Fin q) × W)
    (input : X → Fin n → Fin q) (f : X → Y)
    (P : InstrumentCircuit d) (hP : instrumentCircuitWellFormed P)
    (decode : Bool → List (ℕ × ℕ) → Y)
    (rho : Operator d) (hrho : IsDensityOperator rho) (eps T : ℝ) (he0 : 0 ≤ eps) (he : eps ≤ 1/16) (hT : 0 ≤ T)
    (hsuccess : ∀ x, 1-eps ≤ instrumentCircuitEventMass (phaseKrausOracle e (input x)) P rho
      (fun b rec => decide (decode b rec = f x)))
    (hexpected : ∀ x, instrumentCircuitExpectedQueries (phaseKrausOracle e (input x)) P rho ≤ T) :
    advPmValue input f ≤ ENNReal.ofReal (512*T) := by
  unfold advPmValue
  apply iSup_le
  intro G
  have hb := phase_instrument_small_error_expected_lower_bound e input f G.val P hP decode rho hrho eps T he0 he hT
    G.property.1 G.property.2.1 hsuccess hexpected
  have hn : 0 < ‖G.val‖ := norm_pos_iff.mpr G.property.2.2
  have hm : 0 < maxFilterNorm input G.val := by
    by_contra hh
    have hz := le_antisymm (not_lt.mp hh) (maxFilterNorm_nonneg input G.val)
    rw [hz,mul_zero] at hb
    exact (not_le_of_gt hn) hb
  rw [advPmWitnessValue,← ENNReal.ofReal_div_of_pos hm]
  exact ENNReal.ofReal_le_ofReal ((div_le_iff₀ hm).mpr hb)
end
end Qatlib.Concepts.AdversaryBounds.AdvDuality
