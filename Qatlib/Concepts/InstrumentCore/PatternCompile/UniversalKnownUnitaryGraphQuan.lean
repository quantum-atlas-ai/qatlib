/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.InstrumentCore.PatternCompile.UniversalKnownUnitaryGraphStat
import Qatlib.Concepts.ClusterPatterns.ClusterCompile.UniversalLocalGraphCompilationQuan
import Qatlib.Concepts.InstrumentCore.PatternCompile.UniversalActualFinalReadoutQuan
import Qatlib.Concepts.CircuitImpl.MultiControl.NoWorkTwoLevelSynthesis

/-!
# Universal graph implementation of known unitaries

This module proves `universalKnownUnitaryGraph_answer`, combining local synthesis with graph
compilation to implement any known unitary on a nonempty qubit register. It supplies explicit
bounds on the reflection word, graph size, and branch resources, together with corrected and raw
reference-system identities.

The final readout reproduces the computational-basis event probabilities of the target unitary.
This formalizes universality in the measurement-based setting of [RaussendorfBriegel2000].

## Main statements

* `universalKnownUnitaryGraph_answer`: the full known-unitary graph compilation contract.

## References

* [Raussendorf and Briegel, 2000][RaussendorfBriegel2000]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.CircuitImpl.MultiControl
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.ClusterPatterns.ClusterCompile
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates Qatlib.Concepts.ClusterPatterns.PauliNetwork
open Qatlib.Concepts.ClusterPatterns.Preentangled
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.InstrumentCore.PatternCompile
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open scoped Classical BigOperators ComplexOrder Kronecker

/-- Tensoring a scalar multiple of `U` with the identity pulls the scalar outside `TensorGate`. -/
private theorem tensor_phase {D R : ℕ} (c : ℂ) (U : Operator D) :
    TensorGate (c • U) (1 : Operator R)=c • TensorGate U (1 : Operator R) := by
  ext p q
  simp only [TensorGate,Matrix.kroneckerMap,Matrix.of_apply,Matrix.smul_apply,smul_eq_mul]
  ring

/-- Every known unitary on at least one qubit satisfies the bounded graph compilation,
reference-branch, and decoded-readout contract `UniversalKnownUnitaryGraph`
[RaussendorfBriegel2000]. -/
theorem universalKnownUnitaryGraph_answer : UniversalKnownUnitaryGraph := by
  intro n hn U hU
  obtain ⟨gs,hgs,hlen,_,_,hrun⟩ := known_unitary_no_work_actual_local_synthesis n hn U hU
  have hmatrix : reflectionProgramMatrix gs=U := by
    ext i j
    have he := congrFun (hrun (Qatlib.Foundations.PureStateMath.Ket j)) i
    rw [run_reflectionCompile] at he
    simpa [ApplyGate,Matrix.mulVec,dotProduct,Qatlib.Foundations.PureStateMath.Ket,mul_ite] using! he
  have hlogical : mbqcLogicalMatrix gs=relabelGate (bitVecEquiv n) U := by
    rw [mbqcLogicalMatrix,hmatrix]
  let B := 768*(n+1)^3*4^n
  let G := mbqcGraphWord gs
  have hlen' : gs.length ≤ B := hlen
  have hcounts := mbqcLocalCounts_length gs
  have hL : (mbqcCompiledWord gs).length ≤ 4*B := by
    rw [mbqcCompiledWord_length]
    omega
  have hw : graphWireCount G ≤ 4*B := by
    change (networkCounts (List.ofFn (mbqcGraphWord gs))).1 ≤ 4*B
    rw [mbqcGraphWord_ofFn,mbqcCompiledWord_counts]
    (try dsimp only)
    omega
  have hlegal : networkLegal (List.ofFn G) := by
    rw [mbqcGraphWord_ofFn]
    exact mbqcCompiledWord_legal gs hgs
  have hmat : networkLogicalMatrix (List.ofFn G)=mbqcLocalScalar gs • relabelGate (bitVecEquiv n) U := by
    rw [mbqcGraphWord_ofFn,mbqcCompiledWord_matrix gs hgs,hlogical]
  refine ⟨gs,hgs,hlen,hlogical,hL,hw,hlegal,?_,?_,?_,?_⟩
  · intro h R X
    constructor
    · rw [preentangled_graph_actual_reference_branch n _ R G hlegal,hmat,tensor_phase,
        graphConj_phase _ (mbqcLocalScalar_norm gs)]
    · rw [mbqcRawReference_formula G hlegal,hmat,Matrix.mul_smul,tensor_phase,
        graphConj_phase _ (mbqcLocalScalar_norm gs)]
  · intro h
    obtain ⟨ha,hq,hg,hm,hmsg⟩ := mbqcRawLeaf_resources G h
    have hg' : (mbqcRawLeaf G h).gates ≤ 16*B := by
      change (mbqcRawLeaf G h).gates=2*(mbqcCompiledWord gs).length+2*graphWireCount G at hg
      omega
    refine ⟨ha,hq,hg',?_,?_⟩
    · change (mbqcRawLeaf G h).measurements ≤ 4*B
      rw [hm]
      exact hw
    · change (graphMessage G h).length ≤ 4*B
      rw [hmsg]
      exact hw
  · intro E h y
    have hf := mbqcReadoutLeaf_fields G E h y
    have hq := hf.2.2.2.1
    have hg := hf.2.2.2.2.1
    have hm := hf.2.2.2.2.2.1
    change (mbqcReadoutLeaf G E h y).gates=2*(mbqcCompiledWord gs).length+2*graphWireCount G at hg
    refine ⟨hq,?_,?_⟩
    · change (mbqcReadoutLeaf G E h y).gates ≤ 16*B
      omega
    · change (mbqcReadoutLeaf G E h y).measurements ≤ 4*B+1
      rw [hm]
      exact Nat.add_le_add_right hw 1
  · intro ρ hρ E
    rw [(universalActualFinalReadout_answer n _ G hlegal E).2.2.2 ρ hρ |>.2,hmat]
    unfold mbqcDensityEvent
    rw [graphConj_phase _ (mbqcLocalScalar_norm gs)]

end Qatlib.Concepts.InstrumentCore.PatternCompile
