/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ClusterPatterns.ClusterCompile.UniversalLocalGraphCompilationQuan
import Qatlib.Concepts.InstrumentCore.PatternCompile.UniversalActualFinalReadoutQuan
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
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.PauliClifford.ExactRank

open Qatlib.Concepts.InstrumentCore.PatternCompile
open Qatlib.Concepts.ShadowModels.ShadowChannel
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.ClusterPatterns.ClusterCompile
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates Qatlib.Concepts.ClusterPatterns.PauliNetwork
open Qatlib.Concepts.ClusterPatterns.Preentangled

namespace Qatlib.Concepts.ClusterPatterns.CnotPatterns
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open scoped Classical BigOperators ComplexOrder Kronecker

private theorem uniform_power (n : ℕ) (i : Fin (2^n)) :
    Uniform (Fin (2^n)) i=((Real.sqrt 2 : ℂ)⁻¹)^n := by
  have hsqrt (m : ℕ) : Real.sqrt ((2 : ℝ)^m)=(Real.sqrt 2)^m := by
    induction m with
    | zero => simp
    | succ n ih => rw [pow_succ,Real.sqrt_mul (by positivity),ih,pow_succ]
  simp [Uniform,hsqrt n,inv_pow]

theorem mbqcFreshPreparation_uniform (n L : ℕ) :
    (graphGateProduct (graphFreshGates n L)*graphInputFrame n L)*ᵥ Uniform (Fin (2^n))=
      Uniform (Fin (2^(n+L))) := by
  rw [graphFreshPreparation]
  funext r
  simp [Matrix.mulVec,dotProduct,graphRowLift,graphRowLiftB,uniform_power,pow_add,mul_comm]

theorem mbqcPreparedResource_eq {n L : ℕ} (G : GraphWord n L) :
    mbqcPreparedResource G=mbqcAllPlusResource G := by
  unfold mbqcPreparedResource mbqcAllPlusResource
  rw [graphGateProduct_append]
  have he := mbqcFreshPreparation_uniform n L
  have hd : graphGateProduct (graphFreshGates n L)*
      (graphInputFrame n L*outerProduct (Uniform (Fin (2^n)))*(graphInputFrame n L)ᴴ)*
      (graphGateProduct (graphFreshGates n L))ᴴ=outerProduct (Uniform (Fin (2^(n+L)))) := by
    have hp := conjBranch_outerProduct (graphGateProduct (graphFreshGates n L)*graphInputFrame n L)
      (Uniform (Fin (2^n)))
    rw [he] at hp
    change (graphGateProduct (graphFreshGates n L)*graphInputFrame n L)*
      outerProduct (Uniform (Fin (2^n)))*(graphGateProduct (graphFreshGates n L)*graphInputFrame n L)ᴴ=
      outerProduct (Uniform (Fin (2^(n+L)))) at hp
    simpa only [conjBranch,Matrix.conjTranspose_mul,Matrix.mul_assoc] using! hp
  simpa only [Matrix.conjTranspose_mul,Matrix.mul_assoc] using!
    congrArg (fun X => graphGateProduct (graphEdgeGates G)*X*(graphGateProduct (graphEdgeGates G))ᴴ) hd

private theorem mbqcGateProduct_unitary {D : ℕ} (Us : List (Operator D))
    (hUs : ∀ U ∈ Us, U ∈ Matrix.unitaryGroup (Fin D) ℂ) :
    graphGateProduct Us ∈ Matrix.unitaryGroup (Fin D) ℂ := by
  induction Us with
  | nil => exact Submonoid.one_mem _
  | cons U Us ih =>
    exact Submonoid.mul_mem _
      (ih (fun V hV => hUs V (List.mem_cons_of_mem U hV))) (hUs U List.mem_cons_self)

theorem mbqcAllPlusResource_density {n L : ℕ} (G : GraphWord n L) :
    IsDensityOperator (mbqcAllPlusResource G) := by
  have hu : graphGateProduct (graphEdgeGates G) ∈ Matrix.unitaryGroup (Fin (2^(n+L))) ℂ := by
    apply mbqcGateProduct_unitary
    intro U hU
    obtain ⟨t,rfl⟩ := List.mem_ofFn.mp hU
    exact networkCzGate_unitary _ _
  change IsDensityOperator (conjBranch (graphGateProduct (graphEdgeGates G))
    (outerProduct (Uniform (Fin (2^(n+L))))))
  have hρ := isDensityOperator_outerProduct (normalized_uniform (I := Fin (2^(n+L))) (by simp))
  refine ⟨hρ.1.mul_mul_conjTranspose_same _,?_⟩
  exact (trace_conjBranch_unitary _ hu _).trans hρ.2

private theorem mbqcCounts_append {n : ℕ} (as bs : List (ReflectionGate n)) :
    mbqcLocalCounts (as++bs)=((mbqcLocalCounts as).1+(mbqcLocalCounts bs).1,
      (mbqcLocalCounts as).2+(mbqcLocalCounts bs).2) := by
  induction as with
  | nil => simp [mbqcLocalCounts]
  | cons g as ih =>
    cases g <;> simp only [List.cons_append,mbqcLocalCounts,ih,Prod.mk.injEq] <;>
      constructor <;> first | trivial | omega

private theorem mbqcCounts_wires {n : ℕ} (ls : List (Fin n)) (Us : Fin n → Matrix Bool Bool ℂ) :
    mbqcLocalCounts (ls.map (fun i => Sum.inl (i,Us i)))=(ls.length,0) := by
  induction ls with
  | nil => rfl
  | cons i ls ih => simp [mbqcLocalCounts,ih]

theorem mbqcClassicalInput_counts {n : ℕ} (gs : List (ReflectionGate n)) (x : Reg n) :
    mbqcLocalCounts (mbqcClassicalInputWord gs x)=
      (2*n+(mbqcLocalCounts gs).1,(mbqcLocalCounts gs).2) := by
  have hh : mbqcLocalCounts (List.ofFn (fun i : Fin n => Sum.inl (i,Hadamard)))=(n,0) := by
    simpa only [List.map_ofFn,Function.comp_def,List.length_ofFn] using!
      mbqcCounts_wires (List.ofFn (fun i : Fin n => i)) (fun _ => Hadamard)
  have hx : mbqcLocalCounts (List.ofFn (fun i : Fin n => Sum.inl (i,if x i then PauliX else 1)))=(n,0) := by
    simpa only [List.map_ofFn,Function.comp_def,List.length_ofFn] using!
      mbqcCounts_wires (List.ofFn (fun i : Fin n => i)) (fun i => if x i then PauliX else 1)
  simp only [mbqcClassicalInputWord,mbqcCounts_append,hh,hx]
  apply Prod.ext <;> (try dsimp only) <;> omega

theorem mbqcClassicalInput_length {n : ℕ} (gs : List (ReflectionGate n)) (x : Reg n) :
    (mbqcCompiledWord (mbqcClassicalInputWord gs x)).length=8*n+(mbqcCompiledWord gs).length := by
  rw [mbqcCompiledWord_length,mbqcClassicalInput_counts,mbqcCompiledWord_length]
  omega

theorem mbqcInputGraph_ofFn {n : ℕ} [NeZero n] (gs : List (ReflectionGate n)) (x : Reg n) :
    List.ofFn (mbqcInputGraph gs x)=mbqcCompiledWord (mbqcClassicalInputWord gs x) := by
  have he := mbqcClassicalInput_length gs x
  apply List.ext_getElem
  · simp [he]
  · intro i hi hi'
    simp only [List.getElem_ofFn,mbqcInputGraph]
    rw [List.getD_eq_getElem _ _ hi']

theorem mbqcClassicalInput_legal {n : ℕ} (gs : List (ReflectionGate n))
    (hgs : reflectionLegal gs) (x : Reg n) : reflectionLegal (mbqcClassicalInputWord gs x) := by
  intro g hg
  simp only [mbqcClassicalInputWord,List.mem_append,List.mem_ofFn] at hg
  rcases hg with (⟨i,rfl⟩ | ⟨i,rfl⟩) | hg
  · exact hadamard_unitary
  · change (if x i then PauliX else 1) ∈ Matrix.unitaryGroup Bool ℂ
    split_ifs
    · exact pauliX_unitary
    · exact Submonoid.one_mem _
  · exact hgs g hg

def mbqcShape {n : ℕ} : ClusterNetworkGate n → Sum (Fin n) (Fin n × Fin n)
  | .inl (i,_) => .inl i
  | .inr p => .inr p

private theorem expansion_shape {n : ℕ} (g : ReflectionGate n) :
    (mbqcLocalExpansion g).map mbqcShape=
      match g with
      | .inl (i,_) => List.replicate 4 (Sum.inl i)
      | .inr (c,t) => [Sum.inl t,Sum.inr (c,t),Sum.inl t] := by
  cases g with
  | inl p => obtain ⟨i,U⟩ := p; rfl
  | inr p => obtain ⟨c,t⟩ := p; rfl

theorem mbqcClassicalInput_shape {n : ℕ} (gs : List (ReflectionGate n)) (x y : Reg n) :
    (mbqcCompiledWord (mbqcClassicalInputWord gs x)).map mbqcShape=
      (mbqcCompiledWord (mbqcClassicalInputWord gs y)).map mbqcShape := by
  simp only [mbqcCompiledWord,mbqcClassicalInputWord,List.flatMap_append,List.map_append,
    List.map_flatMap,expansion_shape]
  congr 1
  simp only [List.flatMap,List.map_ofFn,Function.comp_def]

theorem mbqcGraphEdges_shape {n L : ℕ} (G H : GraphWord n L)
    (hs : ∀ t, mbqcShape (G t)=mbqcShape (H t)) : graphEdgeGates G=graphEdgeGates H := by
  have ha : graphAdvance G=graphAdvance H := by
    funext lay t
    have ht := hs t
    cases hg : G t with
    | inl p =>
      obtain ⟨i,z⟩ := p
      cases hh : H t with
      | inl p =>
        obtain ⟨j,w⟩ := p
        simp only [hg,hh,mbqcShape,Sum.inl.injEq] at ht
        subst j
        simp only [graphAdvance,hg,hh]
      | inr p => simp [hg,hh,mbqcShape] at ht
    | inr p =>
      cases hh : H t with
      | inl q => simp [hg,hh,mbqcShape] at ht
      | inr q => simp only [graphAdvance,hg,hh]
  have hb : graphLayoutBefore G=graphLayoutBefore H := by
    funext t i
    simp only [graphLayoutBefore,ha]
  unfold graphEdgeGates
  congr 1
  funext t
  have ht := hs t
  cases hg : G t with
  | inl p =>
    obtain ⟨i,z⟩ := p
    cases hh : H t with
    | inl p =>
      obtain ⟨j,w⟩ := p
      simp only [hg,hh,mbqcShape,Sum.inl.injEq] at ht
      subst j
      simp only [graphEdgeEndpoints,hg,hh,hb]
    | inr p => simp [hg,hh,mbqcShape] at ht
  | inr p =>
    cases hh : H t with
    | inl q => simp [hg,hh,mbqcShape] at ht
    | inr q =>
      simp only [hg,hh,mbqcShape,Sum.inr.injEq] at ht
      subst q
      simp only [graphEdgeEndpoints,hg,hh,hb]

theorem mbqcInputGraph_resource_independent {n : ℕ} [NeZero n] (gs : List (ReflectionGate n))
    (x y : Reg n) : mbqcAllPlusResource (mbqcInputGraph gs x)=mbqcAllPlusResource (mbqcInputGraph gs y) := by
  have he : graphEdgeGates (mbqcInputGraph gs x)=graphEdgeGates (mbqcInputGraph gs y) := by
    apply mbqcGraphEdges_shape
    intro t
    have hs := mbqcClassicalInput_shape gs x y
    rw [← mbqcInputGraph_ofFn,← mbqcInputGraph_ofFn] at hs
    rw [List.map_ofFn,List.map_ofFn] at hs
    have ht := List.ofFn_injective hs
    exact congrFun ht t
  simp only [mbqcAllPlusResource,he]

private theorem wire_product {n : ℕ} (i : Fin n) (U : Matrix Bool Bool ℂ) :
    wireGate n i U=pauliProductDensity (fun j => if j=i then relabelGate boolEquivFin2 U else 1) := by
  ext x y
  simp [wireGate,tensorPauliWireGate,tensorPauliProduct,relabelGate,
    Matrix.reindex_apply,Matrix.submatrix_apply]

private theorem wire_table {n : ℕ} (Us : Fin n → Matrix Bool Bool ℂ)
    (is : List (Fin n)) (hnodup : is.Nodup) :
    reflectionProgramMatrix (is.map (fun i => Sum.inl (i,Us i)))=
      pauliProductDensity (fun j => if j ∈ is then relabelGate boolEquivFin2 (Us j) else 1) := by
  induction is with
  | nil => simpa only [List.map_nil,reflectionProgramMatrix,List.not_mem_nil,if_false] using!
      (pauliProductDensity_one n).symm
  | cons i is ih =>
    have hi := (List.nodup_cons.mp hnodup).1
    have hs := (List.nodup_cons.mp hnodup).2
    rw [List.map_cons,reflectionProgramMatrix,reflectionGateMatrix,ih hs,wire_product,
      pauliProductDensity_mul]
    congr 1
    funext j
    by_cases hji : j=i
    · subst j
      simp [hi]
    · by_cases hj : j ∈ is <;> simp [hji,hj]

private theorem wire_table_full (n : ℕ) (Us : Fin n → Matrix Bool Bool ℂ) :
    reflectionProgramMatrix (List.ofFn (fun i => Sum.inl (i,Us i)))=
      pauliProductDensity (fun i => relabelGate boolEquivFin2 (Us i)) := by
  have he :=
      wire_table Us (List.ofFn (fun i : Fin n => i)) (List.nodup_ofFn.mpr Function.injective_id)
  simpa [List.map_ofFn] using! he

private theorem h_table (n : ℕ) :
    reflectionProgramMatrix (List.ofFn (fun i : Fin n => Sum.inl (i,Hadamard)))=HadamardN n := by
  rw [wire_table_full]
  ext x y
  simp [pauliProductDensity,HadamardN,relabelGate,Matrix.reindex_apply,
    Matrix.submatrix_apply,boolEquivFin2]

private theorem x_table_zero (n : ℕ) (x : Reg n) :
    reflectionProgramMatrix (List.ofFn (fun i : Fin n => Sum.inl (i,if x i then PauliX else 1)))*ᵥ
      Qatlib.Foundations.PureStateMath.Ket (ZeroStr n)=Qatlib.Foundations.PureStateMath.Ket x := by
  rw [wire_table_full]
  funext y
  simp only [Matrix.mulVec,dotProduct,Qatlib.Foundations.PureStateMath.Ket,mul_ite,mul_one,mul_zero,
    Finset.sum_ite_eq',Finset.mem_univ,if_true]
  have he (i : Fin n) : relabelGate boolEquivFin2 (if x i then PauliX else 1)
      (boolEquivFin2 (y i)) (boolEquivFin2 (ZeroStr n i))=
        (1 : Operator 2) (boolEquivFin2 (y i)) (boolEquivFin2 (x i)) := by
    cases hx : x i <;> cases hy : y i <;>
      simp [relabelGate,PauliX,permMatrix,boolEquivFin2,ZeroStr]
  have hp := congrFun (congrFun (pauliProductDensity_one n) y) x
  simpa only [pauliProductDensity,Matrix.of_apply,he,Matrix.one_apply] using! hp

private theorem h_table_uniform (n : ℕ) :
    reflectionProgramMatrix (List.ofFn (fun i : Fin n => Sum.inl (i,Hadamard)))*ᵥ
      Uniform (Reg n)=Qatlib.Foundations.PureStateMath.Ket (ZeroStr n) := by
  rw [h_table,← applyGate_hadamardN_ket_zero]
  have hH : (HadamardN n)ᴴ=HadamardN n := by
    ext x y
    simp only [HadamardN,Matrix.conjTranspose_apply,Matrix.of_apply,star_prod]
    apply Finset.prod_congr rfl
    intro i _
    exact congrFun (congrFun hadamard_conjTranspose (x i)) (y i)
  have hunit : HadamardN n*HadamardN n=1 := by
    have hh := Matrix.mem_unitaryGroup_iff.mp (hadamardN_unitary n)
    simpa only [Matrix.star_eq_conjTranspose,hH] using! hh
  change (HadamardN n)*ᵥ((HadamardN n)*ᵥ Qatlib.Foundations.PureStateMath.Ket (ZeroStr n))=_
  rw [Matrix.mulVec_mulVec,hunit,Matrix.one_mulVec]

theorem mbqcClassicalInput_state {n : ℕ} (gs : List (ReflectionGate n)) (x : Reg n) :
    reflectionProgramMatrix (mbqcClassicalInputWord gs x)*ᵥ Uniform (Reg n)=
      reflectionProgramMatrix gs*ᵥ Qatlib.Foundations.PureStateMath.Ket x := by
  rw [mbqcClassicalInputWord,reflectionProgramMatrix_append,reflectionProgramMatrix_append]
  simp only [← Matrix.mulVec_mulVec]
  rw [h_table_uniform,x_table_zero]

theorem mbqcClassicalInput_logicalState {n : ℕ} (gs : List (ReflectionGate n)) (x : Reg n) :
    mbqcLogicalMatrix (mbqcClassicalInputWord gs x)*ᵥ Uniform (Fin (2^n))=
      (fun i : Fin (2^n) => (reflectionProgramMatrix gs*ᵥ Qatlib.Foundations.PureStateMath.Ket x) ((bitVecEquiv n).symm i)) := by
  have he := mbqcClassicalInput_state gs x
  funext i
  rw [mbqcLogicalMatrix]
  simp only [Matrix.mulVec,dotProduct,relabelGate,Matrix.reindex_apply,Matrix.submatrix_apply]
  rw [← (bitVecEquiv n).sum_comp]
  simpa [Uniform,Matrix.mulVec,dotProduct] using! congrFun he ((bitVecEquiv n).symm i)

end Qatlib.Concepts.ClusterPatterns.CnotPatterns
