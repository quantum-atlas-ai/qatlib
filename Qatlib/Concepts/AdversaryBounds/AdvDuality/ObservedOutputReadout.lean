/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedOutputReadoutDefs

/-!
# Decoded outputs of deferred observed circuits

`adaptivePackedTraceHistory_decoded_readout` relates measurement of a packed branch history to
the sum of decoded masses of its branches. `observed_all_output_query_purification` applies this
identity to a unitary simulation of an observed circuit, preserving every decoded output mass.
This develops the deferred measurement viewpoint described in [NielsenChuang2010].

## Main statements

* `adaptivePackedTraceHistory_decoded_readout`: Decoded measurement masses agree for packed and
  separate branch histories.
* `observed_all_output_query_purification`: A unitary circuit preserves all decoded output
  masses with the stated query and gate bounds.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option autoImplicit false
noncomputable section
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement

open Qatlib.Concepts.QueryComplexity.AdaptiveQuery
open Qatlib.Concepts.QueryComplexity.AdversarySearch

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality
open scoped Classical

/-- The decoded measurement mass of a packed trace history equals the sum of the corresponding
masses of its indexed traces, provided the history capacity bounds the trace count. -/
theorem adaptivePackedTraceHistory_decoded_readout
    {n : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (ts : List (BranchTrace ((Fin n × Bool) × W))) (K : ℕ) (hK : ts.length ≤ K)
    (J : Type) [Fintype J] [DecidableEq J]
    (decode : ℕ → ((Fin n × Bool) × W) → Option J) (o : Option J) :
    MeasureProb (fun x : (Fin n × Bool) × (W × Fin K × Bool) =>
      (ts.getD x.2.2.1.val (emptyObservedTrace _)).state (x.1,x.2.1) / Real.sqrt 2)
      (Finset.univ.filter fun x => decode x.2.2.1.val (x.1,x.2.1) = o) =
      ((ts.zipIdx).map fun t => MeasureProb t.1.state
        (Finset.univ.filter fun z => decode t.2 z = o)).sum := by
  let vs : List (QState ((Fin n × Bool) × W)) := ts.zipIdx.map fun t =>
    Collapse t.1.state (Finset.univ.filter fun z => decode t.2 z = o)
  let v : QState ((Fin n × Bool) × (W × Fin K × Bool)) := fun x =>
    (ts.getD x.2.2.1.val (emptyObservedTrace _)).state (x.1,x.2.1) / Real.sqrt 2
  let E : Finset ((Fin n × Bool) × (W × Fin K × Bool)) :=
    Finset.univ.filter fun x => decode x.2.2.1.val (x.1,x.2.1) = o
  have hv (j : ℕ) : vs.getD j 0 =
      Collapse (ts.getD j (emptyObservedTrace _)).state
        (Finset.univ.filter fun z => decode j z = o) := by
    by_cases hj : j < ts.length
    · rw [List.getD_eq_getElem _ _ (by simpa [vs] using hj),
        List.getD_eq_getElem _ _ hj]
      simp only [vs,List.getElem_map,List.getElem_zipIdx,Nat.zero_add]
    · rw [List.getD_eq_default _ _ (by simpa [vs] using Nat.le_of_not_lt hj),
        List.getD_eq_default _ _ (Nat.le_of_not_lt hj)]
      funext z
      simp [emptyObservedTrace,collapse_apply]
  have hc : Collapse v E = (fun x => (vs.getD x.2.2.1.val 0) (x.1,x.2.1) / Real.sqrt 2) := by
    funext x
    rw [hv,collapse_apply,collapse_apply]
    simp only [E,v,Finset.mem_filter,Finset.mem_univ,true_and]
    split_ifs <;> simp
  change MeasureProb v E = _
  calc
    MeasureProb v E = branchMass (Collapse v E) := by
      rw [branchMass,measureProb_collapse,Finset.inter_univ]
    _ = branchMass (fun x => (vs.getD x.2.2.1.val 0) (x.1,x.2.1) / Real.sqrt 2) :=
      congrArg branchMass hc
    _ = branchMass (fun x : ((Fin n × Bool) × W) × Fin K => (vs.getD x.2.val 0) x.1) :=
      adaptiveSpareHistory_mass (fun x : ((Fin n × Bool) × W) × Fin K =>
        (vs.getD x.2.val 0) x.1)
    _ = (vs.map branchMass).sum := adaptiveListHistory_mass vs K (by simpa [vs] using hK)
    _ = _ := by
      simp only [vs,List.map_map,Function.comp_def,branchMass,measureProb_collapse,
        Finset.inter_univ]

/-- For a well-formed observed circuit with a nonempty query register, there is a unitary
circuit preserving every history-dependent decoded output mass. Its query count equals
`observedQueryDepth P`, and its gate count is at most `10 * observedTreeNodes P *
(observedQueryDepth P + 1)`, in the deferred measurement setting of [NielsenChuang2010]. -/
theorem observed_all_output_query_purification :
    ∀ (n : ℕ) (W : Type) [Fintype W] [DecidableEq W] [Nonempty W]
      (P : ObservedCircuit ((Fin n × Bool) × W)), 0 < n → observedWellFormed P →
      ∃ (R : ℕ) (C : Circuit ((Fin n × Bool) × (W × Fin (R+1) × Bool))),
      IsUnitaryCircuit C ∧ QueryCount C = observedQueryDepth P ∧
      GateCount C ≤ 10 * observedTreeNodes P * (observedQueryDepth P+1) ∧
      ∀ (J : Type) [Fintype J] [DecidableEq J]
        (decode : ℕ → ((Fin n × Bool) × W) → Option J)
        (f : Fin n → Bool) (ψ : QState ((Fin n × Bool) × W)) (o : Option J),
      MeasureProb
        (Run (workspaceBitOracle (W := W × Fin (R+1) × Bool) f) C
          (deferredObservedInput (R := R) ψ))
        (Finset.univ.filter fun z => decode z.2.2.1.val (z.1,z.2.1) = o) =
      observedDecodedMass (workspaceBitOracle (W := W) f) P ψ decode o := by
  intro n W _ _ _ P hn hP
  obtain ⟨R,C,hC,hq,hg,hfull⟩ :=
    observed_query_same_cost_full_branch_purification n W P hn hP
  refine ⟨R,C,hC,hq,hg,?_⟩
  intro J _ _ decode f ψ o
  rw [funext (hfull f ψ).2]
  exact adaptivePackedTraceHistory_decoded_readout _ (R+1) (hfull f ψ).1 J decode o

end Qatlib.Concepts.AdversaryBounds.AdvDuality
