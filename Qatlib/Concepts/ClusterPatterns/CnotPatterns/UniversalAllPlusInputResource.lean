/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.InstrumentCore.PatternCompile.UniversalAllPlusInputResource
import Qatlib.Concepts.ClusterPatterns.CnotPatterns.UniversalInputAux
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

set_option autoImplicit false
noncomputable section
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.InstrumentCore.PatternCompile
open Qatlib.Concepts.ClusterPatterns.ClusterCompile
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates Qatlib.Concepts.ClusterPatterns.PauliNetwork
open Qatlib.Concepts.ClusterPatterns.Preentangled

namespace Qatlib.Concepts.ClusterPatterns.CnotPatterns
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open scoped Classical BigOperators ComplexOrder Kronecker

theorem mbqcDensityEvent_outer {D : ℕ} (ψ : QState (Fin D)) (E : Finset (Fin D)) :
    mbqcDensityEvent (outerProduct ψ) E=MeasureProb ψ E := by
  rw [mbqcDensityEvent_diagonal]
  have ht (i : Fin D) : outerProduct ψ i i=Complex.ofReal (‖ψ i‖^2) := by
    rw [outerProduct_apply,mul_comm,← Complex.normSq_eq_conj_mul_self,
      Complex.normSq_eq_norm_sq]
  simp only [ht,Complex.ofReal_re]
  simp [MeasureProb,BornProb,Finset.sum_ite_mem]

theorem universalAllPlusInputResource_answer : UniversalAllPlusInputResource := by
  intro n _ gs hgs
  refine ⟨mbqcInputGraph_resource_independent gs,?_⟩
  intro x
  let us := mbqcClassicalInputWord gs x
  let G := mbqcInputGraph gs x
  let L := 8*n+(mbqcCompiledWord gs).length
  let w := 8*n+4*(mbqcLocalCounts gs).1+2*(mbqcLocalCounts gs).2
  let ρ := outerProduct (Uniform (Fin (2^n)))
  let ψ : QState (Fin (2^n)) :=
      fun i => (reflectionProgramMatrix gs*ᵥ Ket x) ((bitVecEquiv n).symm i)
  have hus : reflectionLegal us := mbqcClassicalInput_legal gs hgs x
  have hword : List.ofFn G=mbqcCompiledWord us := mbqcInputGraph_ofFn gs x
  have hlegal : networkLegal (List.ofFn G) := by
    rw [hword]
    exact mbqcCompiledWord_legal us hus
  have hw : graphWireCount G=w := by
    change (networkCounts (List.ofFn G)).1=w
    rw [hword,mbqcCompiledWord_counts,mbqcClassicalInput_counts]
    dsimp only [w]
    omega
  have hmat : networkLogicalMatrix (List.ofFn G)=mbqcLocalScalar us • mbqcLogicalMatrix us := by
    rw [hword,mbqcCompiledWord_matrix us hus]
  have hstate : mbqcLogicalMatrix us*ρ*(mbqcLogicalMatrix us)ᴴ=outerProduct ψ := by
    change conjBranch (mbqcLogicalMatrix us) ρ=outerProduct ψ
    rw [conjBranch_outerProduct,mbqcClassicalInput_logicalState]
  have hρ : IsDensityOperator ρ :=
    isDensityOperator_outerProduct (normalized_uniform (I := Fin (2^n)) (by simp))
  have hevent (E : Finset (Fin (2^n))) :
      mbqcDensityEvent (networkLogicalMatrix (List.ofFn G)*ρ*
        (networkLogicalMatrix (List.ofFn G))ᴴ) E=MeasureProb ψ E := by
    rw [hmat]
    unfold mbqcDensityEvent
    rw [graphConj_phase _ (mbqcLocalScalar_norm us),hstate]
    exact mbqcDensityEvent_outer ψ E
  refine ⟨hword,mbqcClassicalInput_length gs x,hlegal,hw,
    mbqcPreparedResource_eq G,mbqcAllPlusResource_density G,?_,?_⟩
  · intro h
    have hbranch : mbqcRawBranch G h ρ=(1/2 : ℂ)^w •
        (pauliFrameGate n (graphFinalFrame G h)*outerProduct ψ*
          (pauliFrameGate n (graphFinalFrame G h))ᴴ) := by
      rw [mbqcRawBranch_formula G hlegal,hw,hmat,Matrix.mul_smul,
        graphConj_phase _ (mbqcLocalScalar_norm us)]
      congr 1
      simpa only [Matrix.conjTranspose_mul,Matrix.mul_assoc] using!
        congrArg (fun A => pauliFrameGate n (graphFinalFrame G h)*A*
          (pauliFrameGate n (graphFinalFrame G h))ᴴ) hstate
    obtain ⟨ha,hq,hg,hm,hmsg⟩ := mbqcRawLeaf_resources G h
    rw [hw] at hg hm hmsg
    refine ⟨hbranch,ha,hq,hg,hm,hmsg,?_⟩
    intro E y
    have hf := mbqcReadoutLeaf_fields G E h y
    have hg' := hf.2.2.2.2.1
    have hm' := hf.2.2.2.2.2.1
    rw [hw] at hg' hm'
    exact ⟨hf.2.2.2.1,hg',hm'⟩
  · intro E
    constructor
    · rw [(universalRawFrameReadout_answer n L G hlegal).2.2.2.2 ρ hρ E |>.2]
      exact hevent E
    · rw [(universalActualFinalReadout_answer n L G hlegal E).2.2.2 ρ hρ |>.2]
      exact hevent E

end Qatlib.Concepts.ClusterPatterns.CnotPatterns
