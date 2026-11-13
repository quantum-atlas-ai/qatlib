/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ClusterPatterns.ClusterCompile.UniversalLocalGraphCompilationStat
import Qatlib.Concepts.ClusterPatterns.QubitUniversal.UniversalQubitCompilationQuan
import Qatlib.Concepts.ClusterPatterns.ClusterCompile.UniversalLocalCompilationAux

/-!
# Correctness of universal local graph compilation

This module proves that a legal list of local single-qubit and CNOT gates satisfies
`UniversalLocalGraphCompilation`. The compiled network matrix agrees with `mbqcLogicalMatrix` up
to the unit-norm scalar `mbqcLocalScalar`, so the scalar cancels in branch conjugation formulas.
The construction formalizes the gate-to-measurement translation underlying
[RaussendorfBriegel2000].

The resulting instrument has uniform history probabilities and the required joint action with
every finite reference. Its accepted leaves have zero queries and explicit bounds on gates,
measurements, and classical message length.

## Main statements

* `mbqcCompiledWord_matrix`: Identifies the compiled logical matrix up to the accumulated scalar
  phase.
* `universalLocalGraphCompilation_answer`: Establishes the full compilation specification,
  including reference semantics and resource bounds.

## References

* [Raussendorf and Briegel, 2000][RaussendorfBriegel2000]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QspSimulation.Achievability

open Qatlib.Concepts.InstrumentCore.PatternCompile
open Qatlib.Concepts.ClusterPatterns.AdaptiveEuler
open Qatlib.Concepts.ClusterPatterns.ChainFeedback
open Qatlib.Concepts.QuditTeleport.TeleportCore
open Qatlib.Concepts.ShadowModels.ShadowChannel
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates Qatlib.Concepts.ClusterPatterns.PauliNetwork
open Qatlib.Concepts.ClusterPatterns.Preentangled
open Qatlib.Concepts.ClusterPatterns.QubitUniversal

open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.ClusterPatterns.ClusterCompile
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open scoped Classical BigOperators ComplexOrder Kronecker

/-- Embedding the single-qubit identity into a tensor wire gives the full identity. -/
private theorem wire_one {n : ℕ} (i : Fin n) : tensorPauliWireGate n i (1 : Operator 2)=1 := by
  have h := congrArg (relabelGate (bitVecEquiv n)) (wireGate_one n i)
  simpa [wireGate,relabelGate] using! h

/-- Embedding a scalar multiple of a Boolean-indexed gate at a wire preserves that scalar. -/
private theorem wire_smul {n : ℕ} (i : Fin n) (c : ℂ) (U : Matrix Bool Bool ℂ) :
    wireGate n i (c • U)=c • wireGate n i U := by
  ext r s
  simp only [wireGate_apply,Matrix.smul_apply,smul_eq_mul]
  split_ifs <;> simp

/-- Boolean-register and integer-indexed embeddings of a single-qubit gate agree under register
relabeling. -/
private theorem wire_embed {n : ℕ} (i : Fin n) (U : Matrix Bool Bool ℂ) :
    tensorPauliWireGate n i (relabelGate boolEquivFin2 U)=relabelGate (bitVecEquiv n) (wireGate n i U) := by
  ext r s
  simp [wireGate,relabelGate]

/-- Embedding a scaled, relabeled single-qubit gate equals the same scalar times its relabeled
Boolean-register embedding. -/
private theorem wire_smul_numeric {n : ℕ} (i : Fin n) (c : ℂ) (U : Matrix Bool Bool ℂ) :
    tensorPauliWireGate n i (c • relabelGate boolEquivFin2 U)=
      c • relabelGate (bitVecEquiv n) (wireGate n i U) := by
  rw [← graphRelabel_smul,wire_embed,wire_smul,graphRelabel_smul]

/-- The logical matrix of a phase word on one wire is the embedded `clusterSequenceUnitary` of
that word. -/
private theorem wire_word {n : ℕ} (i : Fin n) (zs : List ℂ) :
    networkLogicalMatrix (zs.map (fun z => Sum.inl (i,z)))=
      tensorPauliWireGate n i (clusterSequenceUnitary zs) := by
  induction zs with
  | nil => exact (wire_one i).symm
  | cons z zs ih =>
    simp only [List.map_cons,networkLogicalMatrix,networkGateMatrix,ih,
      networkWireGate,tensorPauliWireGate_mul,clusterSequenceUnitary]

/-- The local expansion of a legal gate has its relabeled target matrix multiplied by the
single-qubit compilation scalar, or by one for CNOT. -/
private theorem expansion_matrix {n : ℕ} (g : ReflectionGate n) (hg : reflectionGateLegal g) :
    networkLogicalMatrix (mbqcLocalExpansion g)=
      (match g with | .inl (_,U) => mbqcQubitScalar U | .inr _ => 1) •
        relabelGate (bitVecEquiv n) (reflectionGateMatrix g) := by
  cases g with
  | inl p =>
    obtain ⟨i,U⟩ := p
    change networkLogicalMatrix ((mbqcQubitWord U).map (fun z => Sum.inl (i,z)))=_
    rw [wire_word,(universalQubitCompilation_answer U hg).2.2.2,wire_smul_numeric]
    rfl
  | inr p =>
    obtain ⟨c,t⟩ := p
    simp only [mbqcLocalExpansion,networkLogicalMatrix,networkGateMatrix,Matrix.one_mul,
      networkWireGate,clusterJ_one,wire_embed,networkCzGate,← teleportRelabelGate_mul]
    rw [mbqcCnot_matrix c t hg,one_smul]
    rfl

/-- The logical matrix of a concatenated network is the second network's matrix times the first
network's matrix. -/
private theorem network_matrix_append {n : ℕ} (as bs : List (ClusterNetworkGate n)) :
    networkLogicalMatrix (as++bs)=networkLogicalMatrix bs*networkLogicalMatrix as := by
  induction as with
  | nil => simp [networkLogicalMatrix]
  | cons a as ih => simp only [List.cons_append,networkLogicalMatrix,ih,Matrix.mul_assoc]

/-- The compiled word realizes `mbqcLogicalMatrix gs` up to the unit-norm compilation scalar. -/
theorem mbqcCompiledWord_matrix {n : ℕ} (gs : List (ReflectionGate n))
    (hgs : reflectionLegal gs) :
    networkLogicalMatrix (mbqcCompiledWord gs)=mbqcLocalScalar gs • mbqcLogicalMatrix gs := by
  induction gs with
  | nil => simp [mbqcCompiledWord,networkLogicalMatrix,mbqcLocalScalar,mbqcLogicalMatrix,
      reflectionProgramMatrix,teleportRelabelGate_one]
  | cons g gs ih =>
    have htail : reflectionLegal gs := fun g' hg' => hgs g' (List.mem_cons_of_mem g hg')
    have hg := hgs g List.mem_cons_self
    rw [mbqcCompiledWord,List.flatMap_cons,network_matrix_append]
    change networkLogicalMatrix (mbqcCompiledWord gs)*networkLogicalMatrix (mbqcLocalExpansion g)=_
    rw [ih htail,expansion_matrix g hg]
    simp only [mbqcLogicalMatrix,Matrix.smul_mul,Matrix.mul_smul,smul_smul,
      ← teleportRelabelGate_mul,reflectionProgramMatrix]
    cases g <;> simp [mbqcLocalScalar,mul_comm]

/-- A scalar in the system matrix factors out of its tensor product with the reference identity. -/
private theorem tensor_phase {D R : ℕ} (c : ℂ) (U : Operator D) :
    TensorGate (c • U) (1 : Operator R)=c • TensorGate U (1 : Operator R) := by
  ext p q
  simp only [TensorGate,Matrix.kroneckerMap,Matrix.of_apply,Matrix.smul_apply,smul_eq_mul]
  ring

/-- Every legal local gate list satisfies `UniversalLocalGraphCompilation`, including branch
semantics with finite references and the stated circuit resource bounds; see
[RaussendorfBriegel2000]. -/
theorem universalLocalGraphCompilation_answer : UniversalLocalGraphCompilation := by
  intro n gs hgs
  let G := mbqcGraphWord gs
  let a := (mbqcLocalCounts gs).1
  let b := (mbqcLocalCounts gs).2
  have hword : List.ofFn G=mbqcCompiledWord gs := mbqcGraphWord_ofFn gs
  have hlegal : networkLegal (List.ofFn G) := hword.symm ▸ mbqcCompiledWord_legal gs hgs
  have hcounts : networkCounts (List.ofFn G)=(4*a+2*b,b) := by
    rw [hword,mbqcCompiledWord_counts]
  have hw : graphWireCount G=4*a+2*b := congrArg Prod.fst hcounts
  have hmat : networkLogicalMatrix (List.ofFn G)=mbqcLocalScalar gs • mbqcLogicalMatrix gs := by
    rw [hword,mbqcCompiledWord_matrix gs hgs]
  have href (R : ℕ) (h : GraphHistory G)
      (X : Matrix (Fin (2^n) × Fin R) (Fin (2^n) × Fin R) ℂ) :
      graphActualReference true G h R X=(1/2 : ℂ)^(4*a+2*b) •
        (TensorGate (mbqcLogicalMatrix gs) (1 : Operator R)*X*
          (TensorGate (mbqcLogicalMatrix gs) (1 : Operator R))ᴴ) := by
    rw [preentangled_graph_actual_reference_branch n _ R G hlegal,hw,hmat,tensor_phase,
      graphConj_phase _ (mbqcLocalScalar_norm gs)]
  obtain ⟨I,hbr,hprob,hforget⟩ := preentangled_graph_actual_cp_instrument_and_forget n _ G hlegal
  refine ⟨mbqcCompiledWord_length gs,hword,hlegal,hcounts,mbqcLocalScalar_norm gs,hmat,href,
    ⟨I,hbr,?_,?_⟩,?_⟩
  · intro ρ hρ h
    rw [hprob ρ hρ h,hw]
  · intro R X
    rw [hforget R X,hmat,tensor_phase,graphConj_phase _ (mbqcLocalScalar_norm gs)]
  · intro h
    obtain ⟨_,ha,hq,hg,hm,hmsg,_,_,_⟩ :=
        preentangled_graph_actual_leaf_and_message_resources n _ G h
    have hL := mbqcCompiledWord_length gs
    change (mbqcCompiledWord gs).length=4*a+3*b at hL
    rw [hw] at hg hm hmsg
    change (graphProgramLeaf true G h).gates=2*(mbqcCompiledWord gs).length+
      2*(4*a+2*b)+frameCorrectionCost (graphFinalFrame G h) at hg
    have he :
        (graphProgramLeaf true G h).gates=16*a+10*b+frameCorrectionCost (graphFinalFrame G h) := by
          omega
    exact ⟨ha,hq,he,by rw [he]; exact Nat.add_le_add_left (frameCorrectionCost_le _) _,hm,hmsg⟩

end Qatlib.Concepts.ClusterPatterns.ClusterCompile
