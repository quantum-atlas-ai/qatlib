/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ClusterPatterns.Preentangled.PreentangledGraphCompiler

/-!
# Resource counts and Bell-state graph consumers

This module applies the preentangled graph compiler to resource accounting, the empty word, and
a five-vertex Bell-state preparation. It supplies explicit input and output vectors and verifies
the resulting density operators and logical channel action.

The examples connect the branch semantics to the measurement-based graph-resource construction
in [RaussendorfBriegel2000].

## Main statements

* `preentangled_graph_actual_leaf_and_message_resources`: exact branch counts, messages, and
  physical resource costs.
* `preentangled_graph_empty_word_reference_consumer`: the empty word preserves any reference
  extension.
* `preentangled_graph_five_vertex_bell_consumer`: Bell-state output, uniform branches, and
  feedback costs.

## References

* [Raussendorf and Briegel, 2000][RaussendorfBriegel2000]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.AdversaryBounds.AdvDuality

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.QuditTeleport.TeleportCore
open Qatlib.Concepts.ShadowModels.ShadowChannel
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates Qatlib.Concepts.ClusterPatterns.PauliNetwork
open Qatlib.Concepts.ClusterPatterns.WireComposition
open Qatlib.Concepts.PauliClifford.ExactRank

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

set_option autoImplicit false
open Matrix
open scoped Classical BigOperators ComplexOrder Kronecker
namespace Qatlib.Concepts.ClusterPatterns.Preentangled

/-- A preentangled graph program has `2^(graphWireCount gs)` accepting, query-free leaves, with
exact gate and measurement counts and injective measurement messages. See
[RaussendorfBriegel2000]. -/
theorem preentangled_graph_actual_leaf_and_message_resources :
    ∀ (n L : ℕ) (gs : GraphWord n L) (h : GraphHistory gs),
    observedLeafCount (graphProgram true gs)=2^(graphWireCount gs) ∧
    (graphProgramLeaf true gs h).accepted=true ∧ (graphProgramLeaf true gs h).queries=0 ∧
    (graphProgramLeaf true gs h).gates=2*L+2*graphWireCount gs+frameCorrectionCost (graphFinalFrame gs h) ∧
    (graphProgramLeaf true gs h).measurements=graphWireCount gs ∧
    (graphMessage gs h).length=graphWireCount gs ∧ Function.Injective (graphMessage gs) ∧
    (graphFreshGates n L).length=L ∧ (graphEdgeGates gs).length=L := by
  intro n L gs h
  have hc : graphSlotCount gs (List.ofFn (fun t : Fin L => t))=graphWireCount gs := by
    simp [graphSlotCount, List.map_ofFn, List.sum_ofFn, graphWireCount_eq_sum]
  obtain ⟨ha,hq,hg,hm⟩ := graphTailLeaf_resources gs h
    (List.ofFn (fun t : Fin L => t)) (zeroPauliFrame n)
  rw [hc] at hg hm
  refine ⟨graphProgram_leafCount true gs, ?_, ?_, ?_, ?_, graphMessage_length gs h,
    graphMessage_injective gs, by simp [graphFreshGates], by simp [graphEdgeGates]⟩
  · simpa only [graphProgramLeaf_eq, if_true, graphPrependLeaf_accepted] using! ha
  · simpa only [graphProgramLeaf_eq, if_true, graphPrependLeaf_queries] using! hq
  · simp only [graphProgramLeaf_eq, if_true, graphPrependLeaf_gates, hg,
      graphFreshGates, graphEdgeGates, List.length_ofFn, graphFinalFrame]
    omega
  · simpa only [graphProgramLeaf_eq, if_true, graphPrependLeaf_measurements] using! hm

/-- The Bell graph has the stated two-bit message and gate count equal to ten plus its two
outcome-dependent correction costs. -/
theorem graphBell_leaf_resources (h : GraphHistory graphBellWord) :
    graphMessage graphBellWord h=[h.1 0,h.1 2] ∧
    (graphProgramLeaf true graphBellWord h).gates=
      10+(if h.1 0 then 1 else 0)+(if h.1 2 ^^ h.1 0 then 1 else 0) := by
  refine ⟨by simp [graphMessage, graphBellWord, graphWireAt, List.ofFn_succ],?_⟩
  rw [(preentangled_graph_actual_leaf_and_message_resources 2 3 graphBellWord h).2.2.2.1]
  simp only [graphWireCount, graphFinalFrame, graphBellWord, List.ofFn_succ,
    List.ofFn_zero, List.foldl_cons, List.foldl_nil, frameCorrectionCost, Fin.sum_univ_two]
  simp [networkCounts, graphFrameAdvance, graphWireFrame, graphCzFrame, zeroPauliFrame,
    Nat.add_assoc]

/-- The empty graph word preserves every input with an arbitrary reference system, uses no
gates, and produces an empty message. See [RaussendorfBriegel2000]. -/
theorem preentangled_graph_empty_word_reference_consumer :
    ∀ (n R : ℕ) (X : Matrix (Fin (2^n) × Fin R) (Fin (2^n) × Fin R) ℂ),
    let gs : GraphWord n 0 := Fin.elim0
    (∀ h : GraphHistory gs, graphActualReference true gs h R X=X ∧
      (graphProgramLeaf true gs h).gates=0 ∧ (graphMessage gs h)=[]) := by
  intro n R X gs h
  have hm : graphMessage gs h = [] := by simp [graphMessage]
  have hl : graphProgramLeaf true gs h = ⟨1,true,0,0,0,[]⟩ := by
    simp [graphProgramLeaf, graphProgram_empty, gs, graphHistoryIndex, hm, observedKrausLeaves]
  have hlay : graphLayoutFinal gs = Fin.castAdd 0 := by
    simp [graphLayoutFinal, gs]
  refine ⟨?_, ?_, hm⟩
  · simp only [graphActualReference, hl, graphInputFrame_empty, hlay, TensorGate,
      Matrix.one_kronecker_one, Matrix.mul_one, Matrix.one_mul, Matrix.conjTranspose_one]
    exact graphDiscardReference_empty n R X
  · rw [hl]

/-- The inverse two-bit register equivalence lists the four Boolean registers in the displayed
order. -/
private theorem graphBits2 : (bitVecEquiv 2).symm=
    ![![false,false],![false,true],![true,false],![true,true]] := by
  funext r
  fin_cases r <;> decide

/-- The logical wire gate with parameter one on the first wire has the displayed scaled Hadamard
matrix. -/
private theorem graphBellH0_matrix : networkWireGate (0 : Fin 2) 1 =
    ((Real.sqrt 2 : ℂ)⁻¹) • (!![1,0,1,0;0,1,0,1;1,0,-1,0;0,1,0,-1] : Operator 4) := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    norm_num [networkWireGate,tensorPauliWireGate,tensorPauliProduct,pauliProductDensity,
      relabelGate,Matrix.reindex_apply,Matrix.submatrix_apply,Fin.prod_univ_two,clusterJ_entry,
      Matrix.smul_apply,Matrix.one_apply,smul_eq_mul,graphBits2,boolEquivFin2]

/-- The logical wire gate with parameter one on the second wire has the displayed scaled
Hadamard matrix. -/
private theorem graphBellH1_matrix : networkWireGate (1 : Fin 2) 1 =
    ((Real.sqrt 2 : ℂ)⁻¹) • (!![1,1,0,0;1,-1,0,0;0,0,1,1;0,0,1,-1] : Operator 4) := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    norm_num [networkWireGate,tensorPauliWireGate,tensorPauliProduct,pauliProductDensity,
      relabelGate,Matrix.reindex_apply,Matrix.submatrix_apply,Fin.prod_univ_two,clusterJ_entry,
      Matrix.smul_apply,Matrix.one_apply,smul_eq_mul,graphBits2,boolEquivFin2]

/-- The two-wire CZ gate is diagonal with entries one, one, one, and minus one. -/
private theorem graphBellCZ_matrix : networkCzGate (0 : Fin 2) 1=
    (!![1,0,0,0;0,1,0,0;0,0,1,0;0,0,0,-1] : Operator 4) := by
  rw [graph_cz_numeric_diagonal]
  ext r c
  fin_cases r <;> fin_cases c <;> norm_num [Matrix.diagonal_apply,graphBits2]

/-- The two-qubit product vector consisting of a zero basis state and a plus state. -/
noncomputable def graphBellInputState : QState (Fin 4) :=
  relabelState finProdFinEquiv (TensorState (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 2))
    (relabelState boolEquivFin2 (ApplyGate Hadamard (Qatlib.Foundations.PureStateMath.Ket false))))

/-- The Bell resource vector relabeled to `Fin 4`. -/
noncomputable def graphBellOutputState : QState (Fin 4) :=
  relabelState ((Equiv.prodCongr boolEquivFin2 boolEquivFin2).trans finProdFinEquiv)
    teleportBellResource

/-- The Bell example input has amplitudes `1 / √2`, `1 / √2`, zero, and zero. -/
private theorem graphBellInputState_entries : graphBellInputState=
    ![(Real.sqrt 2 : ℂ)⁻¹,(Real.sqrt 2 : ℂ)⁻¹,0,0] := by
  have hp : ((finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4).symm : Fin 4 → Fin 2 × Fin 2)=
      ![(0,0),(0,1),(1,0),(1,1)] := by
    funext r
    fin_cases r <;> decide
  rw [graphBellInputState,applyGate_hadamard_ket_false]
  funext r
  fin_cases r <;> simp [relabelState,TensorState,hp,Qatlib.Foundations.PureStateMath.Ket,Plus,hadamard_apply_false,boolEquivFin2]

/-- The Bell example output has amplitudes `1 / √2`, zero, zero, and `1 / √2`. -/
private theorem graphBellOutputState_entries : graphBellOutputState=
    ![(Real.sqrt 2 : ℂ)⁻¹,0,0,(Real.sqrt 2 : ℂ)⁻¹] := by
  have hp : (((Equiv.prodCongr boolEquivFin2 boolEquivFin2).trans finProdFinEquiv).symm :
      Fin 4 → Bool × Bool)=![(false,false),(false,true),(true,false),(true,true)] := by
    funext r
    fin_cases r <;> decide
  funext r
  rw [graphBellOutputState, relabelState, Function.comp_def,
      hp]; fin_cases r <;> simp [teleportBellResource_apply']

/-- Both the input and output matrices of the Bell example are density operators. -/
theorem graphBell_states_density : IsDensityOperator graphBellInput ∧
    IsDensityOperator graphBellOutput := by
  refine ⟨isDensityOperator_outerProduct ?_,isDensityOperator_outerProduct ?_⟩
  · exact normalized_relabelState _ (normalized_tensorState (normalized_ket (0 : Fin 2))
      (normalized_relabelState _ (normalized_applyGate hadamard_unitary (normalized_ket false))))
  · exact normalized_relabelState _ teleportBellResource_normalized

/-- The Bell-state graph word satisfies `networkLegal`. -/
theorem graphBellWord_legal : networkLegal (List.ofFn graphBellWord) := by
  simp [networkLegal,graphBellWord,List.ofFn_succ]

/-- Conjugation by the Bell word's logical network matrix maps its input density operator to the
Bell output. -/
theorem graphBell_logical_output :
    networkLogicalMatrix (List.ofFn graphBellWord)*graphBellInput*
      (networkLogicalMatrix (List.ofFn graphBellWord))ᴴ=graphBellOutput := by
  have h0 : ApplyGate (networkWireGate (0 : Fin 2) 1) graphBellInputState=
      ![(1/2 : ℂ),1/2,1/2,1/2] := by
    rw [graphBellH0_matrix,graphBellInputState_entries]
    funext r
    fin_cases r <;> simp [ApplyGate,Matrix.mulVec,dotProduct,Fin.sum_univ_four,
      Matrix.smul_apply,smul_eq_mul,sqrt2_inv_sq]
  have hcz : ApplyGate (networkCzGate (0 : Fin 2) 1) ![(1/2 : ℂ),1/2,1/2,1/2]=
      ![(1/2 : ℂ),1/2,1/2,-1/2] := by
    rw [graphBellCZ_matrix]
    funext r
    fin_cases r <;> simp [ApplyGate,Matrix.mulVec,dotProduct,Fin.sum_univ_four]
    norm_num
  have h1 : ApplyGate (networkWireGate (1 : Fin 2) 1) ![(1/2 : ℂ),1/2,1/2,-1/2]=
      graphBellOutputState := by
    rw [graphBellH1_matrix,graphBellOutputState_entries]
    funext r
    fin_cases r <;> simp [ApplyGate,Matrix.mulVec,dotProduct,Fin.sum_univ_four,
      Matrix.smul_apply,smul_eq_mul] <;> ring
  have hs : ApplyGate (networkLogicalMatrix (List.ofFn graphBellWord)) graphBellInputState=
      graphBellOutputState := by
    simp only [graphBellWord,List.ofFn_succ,List.ofFn_zero,networkLogicalMatrix,
      networkGateMatrix,Matrix.one_mul,applyGate_mul]
    change ApplyGate (networkWireGate (1 : Fin 2) 1)
      (ApplyGate (networkCzGate (0 : Fin 2) 1)
        (ApplyGate (networkWireGate (0 : Fin 2) 1) graphBellInputState))=_
    rw [h0,hcz,h1]
  change conjBranch (networkLogicalMatrix (List.ofFn graphBellWord))
    (outerProduct graphBellInputState)=outerProduct graphBellOutputState
  rw [conjBranch_outerProduct]
  exact congrArg outerProduct hs

/-- The five-vertex Bell graph has valid input and output density operators, produces the Bell
output after forgetting outcomes, and has branches of weight one quarter with explicit
messages and feedback costs. See [RaussendorfBriegel2000]. -/
theorem preentangled_graph_five_vertex_bell_consumer :
    IsDensityOperator graphBellInput ∧ IsDensityOperator graphBellOutput ∧
    networkLegal (List.ofFn graphBellWord) ∧
    (∑ h : GraphHistory graphBellWord, graphActualBranch true graphBellWord h graphBellInput)=graphBellOutput ∧
    ∀ h : GraphHistory graphBellWord,
      graphActualBranch true graphBellWord h graphBellInput=(1/4:ℂ) • graphBellOutput ∧
      graphMessage graphBellWord h=[h.1 0,h.1 2] ∧
      (graphProgramLeaf true graphBellWord h).gates=
        10+(if h.1 0 then 1 else 0)+(if h.1 2 ^^ h.1 0 then 1 else 0) := by
  refine ⟨graphBell_states_density.1,graphBell_states_density.2,graphBellWord_legal,?_,?_⟩
  · rw [graphActualBranch_forget 2 3 graphBellWord graphBellWord_legal,
      graphBell_logical_output]
  · intro h
    refine ⟨?_,(graphBell_leaf_resources h).1,(graphBell_leaf_resources h).2⟩
    rw [graphActualBranch_formula 2 3 graphBellWord graphBellWord_legal,
      graphBell_logical_output]
    norm_num [graphWireCount,graphBellWord,List.ofFn_succ,networkCounts]

end Qatlib.Concepts.ClusterPatterns.Preentangled
