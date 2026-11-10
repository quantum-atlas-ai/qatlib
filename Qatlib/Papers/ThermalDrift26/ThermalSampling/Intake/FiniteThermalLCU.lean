/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.UniformBqp.FiniteGateWord.FiniteThermal.FiniteThermalUniformH
import Qatlib.Concepts.UniformBqp.FiniteGateWord.FiniteThermal.FiniteThermalNativePredicate
import Qatlib.Papers.ThermalDrift26.ThermalSampling.Intake.FiniteThermalOAA
import Qatlib.Concepts.BlockEncoding.LinearCombination
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option warningAsError false
noncomputable section
namespace Qatlib.Papers.ThermalDrift26.ThermalSampling
open Qatlib Matrix Qatlib.Concepts.UniformBqp.FiniteGateWord.FiniteThermalCircuits
open scoped BigOperators

def thermalQuarterTurn : Matrix (Fin 2) (Fin 2) ℂ := ![![0,-1],![1,0]]

theorem thermalQuarterTurn_unitary : thermalQuarterTurn ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff',Matrix.star_eq_conjTranspose]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [thermalQuarterTurn,Matrix.mul_apply,Fin.sum_univ_two,Matrix.conjTranspose_apply]

def thermalUniformBranch (b ylo yhi zlo zhi : ℕ) (u : Qatlib.Foundations.PureStateMath.Reg b) : Matrix (Fin 2) (Fin 2) ℂ :=
  let v := thermalBitValue (List.ofFn u)
  if ylo≤v ∧ v<yhi then thermalQuarterTurn
  else if zlo≤v ∧ v<zhi then -1 else 1

theorem thermalUniformBranch_unitary (b ylo yhi zlo zhi : ℕ) (u : Qatlib.Foundations.PureStateMath.Reg b) :
    thermalUniformBranch b ylo yhi zlo zhi u ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  dsimp only [thermalUniformBranch]
  split_ifs
  · exact thermalQuarterTurn_unitary
  · rw [Matrix.mem_unitaryGroup_iff',Matrix.star_eq_conjTranspose]
    simp
  · simp

def thermalUniformWeight (b : ℕ) (_ : Qatlib.Foundations.PureStateMath.Reg b) : ℝ :=
    (Fintype.card (Qatlib.Foundations.PureStateMath.Reg b):ℝ)⁻¹

theorem thermalUniform_prepare (b : ℕ) :
    Qatlib.Concepts.BlockEncoding.LinearCombination.IsPrepare (Qatlib.Foundations.PureStateMath.HadamardN b) (thermalUniformWeight b) (Qatlib.Foundations.PureStateMath.ZeroStr b) := by
  refine ⟨Qatlib.Foundations.PureStateMath.hadamardN_unitary b,?_⟩
  change Qatlib.Foundations.PureStateMath.ApplyGate
      (Qatlib.Foundations.PureStateMath.HadamardN b)
      (Qatlib.Foundations.PureStateMath.Ket (Qatlib.Foundations.PureStateMath.ZeroStr b))=_
  rw [Qatlib.Foundations.PureStateMath.applyGate_hadamardN_ket_zero]
  funext u
  simp [Qatlib.Foundations.PureStateMath.Uniform,thermalUniformWeight,Real.sqrt_inv]

def thermalUniformLCU (b ylo yhi zlo zhi : ℕ) :
    Matrix (Qatlib.Foundations.PureStateMath.Reg b × Fin 2) (Qatlib.Foundations.PureStateMath.Reg b × Fin 2) ℂ :=
  Qatlib.Concepts.BlockEncoding.LinearCombination.LCUWorkspace (thermalUniformBranch b ylo yhi zlo zhi) (Qatlib.Foundations.PureStateMath.HadamardN b)

theorem thermalUniformLCU_unitary (b ylo yhi zlo zhi : ℕ) :
    thermalUniformLCU b ylo yhi zlo zhi ∈ Matrix.unitaryGroup (Qatlib.Foundations.PureStateMath.Reg b × Fin 2) ℂ := by
  have hH := Qatlib.Foundations.PureStateMath.hadamardN_unitary b
  have hHt : (Qatlib.Foundations.PureStateMath.HadamardN b)ᴴ ∈ Matrix.unitaryGroup (Qatlib.Foundations.PureStateMath.Reg b) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff',Matrix.star_eq_conjTranspose]
    simpa only [Matrix.conjTranspose_conjTranspose] using! Matrix.mem_unitaryGroup_iff.mp hH
  exact (Matrix.unitaryGroup _ ℂ).mul_mem (Qatlib.Foundations.PureStateMath.tensorGate_unitary hHt (by simp))
    ((Matrix.unitaryGroup _ ℂ).mul_mem
      (Qatlib.Concepts.BlockEncoding.LinearCombination.select_unitary _ (thermalUniformBranch_unitary b ylo yhi zlo zhi))
      (Qatlib.Foundations.PureStateMath.tensorGate_unitary hH (by simp)))

theorem thermalUniformLCU_corner (b ylo yhi zlo zhi : ℕ) (psi : Qatlib.Foundations.PureStateMath.QState (Fin 2)) :
    (fun s => (thermalUniformLCU b ylo yhi zlo zhi *ᵥ
      Qatlib.Foundations.PureStateMath.TensorState (Qatlib.Foundations.PureStateMath.Ket (Qatlib.Foundations.PureStateMath.ZeroStr b)) psi) (Qatlib.Foundations.PureStateMath.ZeroStr b,s))=
      (∑ u : Qatlib.Foundations.PureStateMath.Reg b,thermalUniformWeight b u • thermalUniformBranch b ylo yhi zlo zhi u) *ᵥ psi :=
  Qatlib.Concepts.BlockEncoding.LinearCombination.lcu_corner_apply _ (by intro u;unfold thermalUniformWeight;positivity)
    (thermalUniform_prepare b) psi

def thermalWorkspaceEquiv (b w : ℕ) :
    Qatlib.Foundations.PureStateMath.Reg ((b+1)+(w+1)) ≃ ((Qatlib.Foundations.PureStateMath.Reg b × Fin 2) × Qatlib.Foundations.PureStateMath.Reg (w+1)) :=
  (Qatlib.Foundations.PureStateMath.regAppendEquiv (b+1) (w+1)).trans
    (Equiv.prodCongr ((rotationRegisterEquiv b).trans (Equiv.prodComm _ _)) (Equiv.refl _))

def thermalWorkspaceEmbed (b w : ℕ) :
    Matrix (Qatlib.Foundations.PureStateMath.Reg ((b+1)+(w+1))) (Qatlib.Foundations.PureStateMath.Reg b × Fin 2) ℂ :=
  fun x j => if thermalWorkspaceEquiv b w x=(j,fun _ => false) then 1 else 0

def thermalSignalWire (b w : ℕ) : Fin ((b+1)+(w+1)) := Fin.castAdd (w+1) (0 : Fin (b+1))
def thermalUniformWire (b w : ℕ) (i : Fin b) : Fin ((b+1)+(w+1)) := Fin.castAdd (w+1) i.succ
def thermalWorkWire (b w : ℕ) (i : Fin (w+1)) : Fin ((b+1)+(w+1)) := Fin.natAdd (b+1) i

theorem thermalWorkspace_signal (b w : ℕ) (x : Qatlib.Foundations.PureStateMath.Reg ((b+1)+(w+1))) :
    ((thermalWorkspaceEquiv b w x).1).2=Qatlib.Foundations.PureStateMath.boolEquivFin2 (x (thermalSignalWire b w)) := rfl

theorem thermalWorkspace_uniform (b w : ℕ) (x : Qatlib.Foundations.PureStateMath.Reg ((b+1)+(w+1))) (i : Fin b) :
    ((thermalWorkspaceEquiv b w x).1).1 i=x (thermalUniformWire b w i) := rfl

theorem thermalWorkspace_work (b w : ℕ) (x : Qatlib.Foundations.PureStateMath.Reg ((b+1)+(w+1))) (i : Fin (w+1)) :
    (thermalWorkspaceEquiv b w x).2 i=x (thermalWorkWire b w i) := rfl

theorem thermalWorkspaceEmbed_column (b w : ℕ) (j : Qatlib.Foundations.PureStateMath.Reg b × Fin 2) :
    (fun x => thermalWorkspaceEmbed b w x j)=
      Qatlib.Foundations.PureStateMath.Ket ((thermalWorkspaceEquiv b w).symm (j,fun _ => false)) := by
  funext x
  simp only [thermalWorkspaceEmbed,Qatlib.Foundations.PureStateMath.Ket,Equiv.apply_eq_iff_eq_symm_apply]

theorem thermalWorkspaceEmbed_left (b w : ℕ)
    (A : Matrix (Qatlib.Foundations.PureStateMath.Reg ((b+1)+(w+1))) (Qatlib.Foundations.PureStateMath.Reg ((b+1)+(w+1))) ℂ)
    (x : Qatlib.Foundations.PureStateMath.Reg ((b+1)+(w+1))) (j : Qatlib.Foundations.PureStateMath.Reg b × Fin 2) :
    (A*thermalWorkspaceEmbed b w) x j=
      A x ((thermalWorkspaceEquiv b w).symm (j,fun _ => false)) := by
  change (A *ᵥ (fun y => thermalWorkspaceEmbed b w y j)) x=_
  rw [thermalWorkspaceEmbed_column,Qatlib.Concepts.BlockEncoding.LinearCombination.mulVec_ket_apply]

theorem thermalWorkspaceEmbed_right (b w : ℕ) (A : Matrix (Qatlib.Foundations.PureStateMath.Reg b × Fin 2) (Qatlib.Foundations.PureStateMath.Reg b × Fin 2) ℂ)
    (x : Qatlib.Foundations.PureStateMath.Reg ((b+1)+(w+1))) (j : Qatlib.Foundations.PureStateMath.Reg b × Fin 2) :
    (thermalWorkspaceEmbed b w*A) x j=
      if (thermalWorkspaceEquiv b w x).2=(fun _ => false)
      then A (thermalWorkspaceEquiv b w x).1 j else 0 := by
  by_cases hc : (thermalWorkspaceEquiv b w x).2=(fun _ => false)
  · have he (k : Qatlib.Foundations.PureStateMath.Reg b × Fin 2) : (thermalWorkspaceEquiv b w x=(k,fun _ => false)) ↔
        (thermalWorkspaceEquiv b w x).1=k ∧ (thermalWorkspaceEquiv b w x).2=(fun _ => false) :=
        Prod.ext_iff
    simp [Matrix.mul_apply,thermalWorkspaceEmbed,he,hc]
  · simp [Matrix.mul_apply,thermalWorkspaceEmbed,Prod.ext_iff,hc]

def thermalUniformWires (b w : ℕ) : List (Fin ((b+1)+(w+1))) :=
  List.ofFn (thermalUniformWire b w)

theorem thermalUniformWire_mem (b w : ℕ) (i : Fin b) :
    thermalUniformWire b w i∈thermalUniformWires b w := List.mem_ofFn.mpr ⟨i,rfl⟩

theorem thermalSignalWire_not_mem (b w : ℕ) : thermalSignalWire b w∉thermalUniformWires b w := by
  intro h
  obtain ⟨i,hi⟩ := List.mem_ofFn.mp h
  have hv := congrArg Fin.val hi
  change i.val+1=0 at hv
  omega

theorem thermalWorkWire_not_mem (b w : ℕ) (k : Fin (w+1)) :
    thermalWorkWire b w k∉thermalUniformWires b w := by
  intro h
  obtain ⟨i,hi⟩ := List.mem_ofFn.mp h
  have hv := congrArg Fin.val hi
  change i.val+1=(b+1)+k.val at hv
  have hbound := i.isLt
  omega

theorem thermalUniformWires_nodup (b w : ℕ) : (thermalUniformWires b w).Nodup := by
  apply List.nodup_ofFn.mpr
  intro i j hij
  have hv : i.val+1=j.val+1 := congrArg Fin.val hij
  exact Fin.ext (Nat.add_right_cancel hv)

theorem thermalWorkspaceEmbed_tensor (b w : ℕ) (A : Matrix (Qatlib.Foundations.PureStateMath.Reg b × Fin 2) (Qatlib.Foundations.PureStateMath.Reg b × Fin 2) ℂ) :
    Qatlib.Foundations.PureStateMath.BornBridge.relabelGate (thermalWorkspaceEquiv b w).symm
      (Qatlib.Foundations.PureStateMath.TensorGate A (1 : Matrix (Qatlib.Foundations.PureStateMath.Reg (w+1)) (Qatlib.Foundations.PureStateMath.Reg (w+1)) ℂ))*thermalWorkspaceEmbed b w=
        thermalWorkspaceEmbed b w*A := by
  ext x j
  rw [thermalWorkspaceEmbed_left,thermalWorkspaceEmbed_right]
  by_cases hc : (thermalWorkspaceEquiv b w x).2=(fun _ => false)
  all_goals simp [Qatlib.Foundations.PureStateMath.BornBridge.relabelGate,Qatlib.Foundations.PureStateMath.TensorGate,Matrix.one_apply,hc]

theorem thermalUniformHWord_physical_tensor (b w : ℕ) :
    Qatlib.Concepts.UniformBqp.FiniteGateWord.finiteCodeWordMatrix ((b+1)+(w+1)) (thermalUniformHWord (thermalUniformWires b w))=
      Qatlib.Foundations.PureStateMath.BornBridge.relabelGate (thermalWorkspaceEquiv b w).symm
        (Qatlib.Foundations.PureStateMath.TensorGate (Qatlib.Foundations.PureStateMath.TensorGate (Qatlib.Foundations.PureStateMath.HadamardN b) (1 : Matrix (Fin 2) (Fin 2) ℂ))
          (1 : Matrix (Qatlib.Foundations.PureStateMath.Reg (w+1)) (Qatlib.Foundations.PureStateMath.Reg (w+1)) ℂ)) := by
  rw [thermalUniformHWord_matrix _ (thermalUniformWires_nodup b w)]
  ext x y
  rw [thermalUniformHMatrix,thermalLocalProduct_apply]
  rw [Fin.prod_univ_add,Fin.prod_univ_succ]
  change ((if thermalSignalWire b w∈thermalUniformWires b w then Qatlib.Foundations.PureStateMath.Hadamard else 1)
      (x (thermalSignalWire b w)) (y (thermalSignalWire b w))) *
    (∏ i : Fin b,(if thermalUniformWire b w i∈thermalUniformWires b w then Qatlib.Foundations.PureStateMath.Hadamard else 1)
      (x (thermalUniformWire b w i)) (y (thermalUniformWire b w i))) *
    (∏ k : Fin (w+1),(if thermalWorkWire b w k∈thermalUniformWires b w then Qatlib.Foundations.PureStateMath.Hadamard else 1)
      (x (thermalWorkWire b w k)) (y (thermalWorkWire b w k)))=_
  simp only [thermalSignalWire_not_mem,thermalUniformWire_mem,thermalWorkWire_not_mem,if_false,if_true]
  have hs : (1 : Matrix Bool Bool ℂ) (x (thermalSignalWire b w)) (y (thermalSignalWire b w))=
      (1 : Matrix (Fin 2) (Fin 2) ℂ) (thermalWorkspaceEquiv b w x).1.2
        (thermalWorkspaceEquiv b w y).1.2 := by
    simp [Matrix.one_apply,thermalWorkspace_signal]
  have hd : (∏ i : Fin b,Qatlib.Foundations.PureStateMath.Hadamard (x (thermalUniformWire b w i)) (y (thermalUniformWire b w i)))=
      Qatlib.Foundations.PureStateMath.HadamardN b (thermalWorkspaceEquiv b w x).1.1 (thermalWorkspaceEquiv b w y).1.1 := rfl
  have ht := congrFun (congrFun (thermalLocalProduct_one (w+1))
    (thermalWorkspaceEquiv b w x).2) (thermalWorkspaceEquiv b w y).2
  rw [thermalLocalProduct_apply] at ht
  change (∏ k : Fin (w+1),(1 : Matrix Bool Bool ℂ)
      (x (thermalWorkWire b w k)) (y (thermalWorkWire b w k)))=
      (1 : Matrix (Qatlib.Foundations.PureStateMath.Reg (w+1)) (Qatlib.Foundations.PureStateMath.Reg (w+1)) ℂ)
        (thermalWorkspaceEquiv b w x).2 (thermalWorkspaceEquiv b w y).2 at ht
  rw [hs,hd,ht]
  change _ = (Qatlib.Foundations.PureStateMath.HadamardN b (thermalWorkspaceEquiv b w x).1.1 (thermalWorkspaceEquiv b w y).1.1 *
    (1 : Matrix (Fin 2) (Fin 2) ℂ) (thermalWorkspaceEquiv b w x).1.2 (thermalWorkspaceEquiv b w y).1.2) *
    (1 : Matrix (Qatlib.Foundations.PureStateMath.Reg (w+1)) (Qatlib.Foundations.PureStateMath.Reg (w+1)) ℂ) (thermalWorkspaceEquiv b w x).2 (thermalWorkspaceEquiv b w y).2
  ring

theorem thermalUniformHWord_intertwine (b w : ℕ) :
    Qatlib.Concepts.UniformBqp.FiniteGateWord.finiteCodeWordMatrix ((b+1)+(w+1)) (thermalUniformHWord (thermalUniformWires b w))*
      thermalWorkspaceEmbed b w =
    thermalWorkspaceEmbed b w*Qatlib.Foundations.PureStateMath.TensorGate (Qatlib.Foundations.PureStateMath.HadamardN b) (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [thermalUniformHWord_physical_tensor,thermalWorkspaceEmbed_tensor]

theorem thermalRect_ket_column {I J : Type*} [Fintype J] [DecidableEq J]
    (A : Matrix I J ℂ) (j : J) (i : I) :
    (A *ᵥ Qatlib.Foundations.PureStateMath.Ket j) i=A i j := by
  simp [Matrix.mulVec,dotProduct,Qatlib.Foundations.PureStateMath.Ket]

theorem thermalWorkspaceEmbed_basis (b w : ℕ) (j : Qatlib.Foundations.PureStateMath.Reg b × Fin 2) :
    thermalWorkspaceEmbed b w *ᵥ Qatlib.Foundations.PureStateMath.Ket j =
      Qatlib.Foundations.PureStateMath.Ket ((thermalWorkspaceEquiv b w).symm (j,fun _ => false)) := by
  funext x
  rw [thermalRect_ket_column]
  exact congrFun (thermalWorkspaceEmbed_column b w j) x

theorem thermalMatrix_intertwine_of_basis {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (A : Matrix I I ℂ) (G : Matrix I J ℂ) (B : Matrix J J ℂ)
    (h : ∀ j : J,A *ᵥ (G *ᵥ Qatlib.Foundations.PureStateMath.Ket j)=G *ᵥ (B *ᵥ Qatlib.Foundations.PureStateMath.Ket j)) :
    A*G=G*B := by
  ext i j
  have hh := congrFun (h j) i
  simpa only [Matrix.mulVec_mulVec,thermalRect_ket_column] using! hh

def thermalCutBits (b t : ℕ) : Qatlib.Foundations.PureStateMath.Reg b :=
  if h : t<2^b then (Qatlib.Foundations.PureStateMath.bitVecEquiv b).symm ⟨t,h⟩ else fun _ => false

def thermalCutFull (b t : ℕ) : Bool := decide (t=2^b)

def thermalCutPairs (b w t : ℕ) : List (Fin ((b+1)+(w+1)) × Bool) :=
  List.ofFn (fun i => (thermalUniformWire b w i,thermalCutBits b t i))

theorem thermalCutPairs_wires (b w t : ℕ) :
    (thermalCutPairs b w t).map Prod.fst=thermalUniformWires b w := by
  simp [thermalCutPairs,thermalUniformWires,List.map_ofFn,Function.comp_def]

theorem thermalCutPairs_cutoff (b w t : ℕ) (ht : t≤2^b) :
    thermalCutoff (thermalCutFull b t) (thermalCutPairs b w t)=t := by
  by_cases he : t=2^b
  · simp [thermalCutoff,thermalCutFull,thermalCutPairs,he]
  · have hlt : t<2^b := by omega
    simp [thermalCutoff,thermalCutFull,thermalCutPairs,thermalCutBits,he,hlt,List.map_ofFn,
      thermalBitValue_ofFn,Function.comp_def]

def thermalScratchWires (b w : ℕ) : List (Fin ((b+1)+(w+1))) :=
  List.ofFn (fun i : Fin w => thermalWorkWire b w i.succ)

def thermalFlagWire (b w : ℕ) : Fin ((b+1)+(w+1)) := thermalWorkWire b w 0

theorem thermalWorkWires_split (b w : ℕ) :
    List.ofFn (thermalWorkWire b w)=thermalFlagWire b w::thermalScratchWires b w := by
  rw [List.ofFn_succ]
  rfl

theorem thermalSignal_not_work (b w : ℕ) (i : Fin (w+1)) :
    thermalSignalWire b w≠thermalWorkWire b w i := by
  intro h
  have hv := congrArg Fin.val h
  change 0=(b+1)+i.val at hv
  omega

theorem thermalCanonical_layout (b w : ℕ) :
    (thermalUniformWires b w++thermalFlagWire b w::thermalScratchWires b w).Nodup := by
  rw [← thermalWorkWires_split,List.nodup_append]
  refine ⟨thermalUniformWires_nodup b w,?_,?_⟩
  · apply List.nodup_ofFn.mpr
    intro i j hij
    have hv : (b+1)+i.val=(b+1)+j.val := congrArg Fin.val hij
    exact Fin.ext (Nat.add_left_cancel hv)
  · intro x hx y hy hxy
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hy
    subst x
    exact thermalWorkWire_not_mem b w i hx

theorem thermalCanonical_signal_outside (b w : ℕ) :
    thermalSignalWire b w∉thermalUniformWires b w++thermalFlagWire b w::thermalScratchWires b w := by
  rw [← thermalWorkWires_split]
  intro h
  rcases List.mem_append.mp h with hc|hw
  · exact thermalSignalWire_not_mem b w hc
  · obtain ⟨i,hi⟩ := List.mem_ofFn.mp hw
    exact thermalSignal_not_work b w i hi.symm

def thermalEncoded (b w : ℕ) (j : Qatlib.Foundations.PureStateMath.Reg b × Fin 2) : Qatlib.Foundations.PureStateMath.Reg ((b+1)+(w+1)) :=
  (thermalWorkspaceEquiv b w).symm (j,fun _ => false)

theorem thermalEncoded_equiv (b w : ℕ) (j : Qatlib.Foundations.PureStateMath.Reg b × Fin 2) :
    thermalWorkspaceEquiv b w (thermalEncoded b w j)=(j,fun _ => false) :=
  (thermalWorkspaceEquiv b w).apply_symm_apply _

theorem thermalEncoded_work (b w : ℕ) (j : Qatlib.Foundations.PureStateMath.Reg b × Fin 2) (k : Fin (w+1)) :
    thermalEncoded b w j (thermalWorkWire b w k)=false :=
  congrArg (fun p => p.2 k) (thermalEncoded_equiv b w j)

theorem thermalEncoded_uniform (b w : ℕ) (j : Qatlib.Foundations.PureStateMath.Reg b × Fin 2) (i : Fin b) :
    thermalEncoded b w j (thermalUniformWire b w i)=j.1 i :=
  congrArg (fun p => p.1.1 i) (thermalEncoded_equiv b w j)

theorem thermalEncoded_signal (b w : ℕ) (j : Qatlib.Foundations.PureStateMath.Reg b × Fin 2) :
    thermalEncoded b w j (thermalSignalWire b w)=Qatlib.Foundations.PureStateMath.boolEquivFin2.symm j.2 := by
  have h : Qatlib.Foundations.PureStateMath.boolEquivFin2 (thermalEncoded b w j (thermalSignalWire b w))=j.2 :=
    congrArg (fun p => p.1.2) (thermalEncoded_equiv b w j)
  apply Qatlib.Foundations.PureStateMath.boolEquivFin2.injective
  rw [Equiv.apply_symm_apply]
  exact h

theorem thermalCutPairs_data (b w t : ℕ) (j : Qatlib.Foundations.PureStateMath.Reg b × Fin 2) :
    (thermalCutPairs b w t).map (fun p => thermalEncoded b w j p.1)=List.ofFn j.1 := by
  simp only [thermalCutPairs,List.map_ofFn,Function.comp_def]
  congr 1
  funext i
  exact thermalEncoded_uniform b w j i

def thermalSignalFlip (s : Fin 2) (hit : Bool) : Fin 2 :=
  Qatlib.Foundations.PureStateMath.boolEquivFin2 (Qatlib.Foundations.PureStateMath.boolEquivFin2.symm s ^^ hit)

theorem thermalSignal_not_uniform (b w : ℕ) (i : Fin b) :
    thermalSignalWire b w≠thermalUniformWire b w i := by
  intro h
  exact thermalSignalWire_not_mem b w (h ▸ thermalUniformWire_mem b w i)

theorem thermalEncoded_update (b w : ℕ) (j : Qatlib.Foundations.PureStateMath.Reg b × Fin 2) (hit : Bool) :
    Function.update (thermalEncoded b w j) (thermalSignalWire b w)
      (Qatlib.Foundations.PureStateMath.boolEquivFin2.symm j.2 ^^ hit)=thermalEncoded b w (j.1,thermalSignalFlip j.2 hit) := by
  apply (thermalWorkspaceEquiv b w).injective
  rw [thermalEncoded_equiv]
  apply Prod.ext
  · apply Prod.ext
    · funext i
      change Function.update (thermalEncoded b w j) (thermalSignalWire b w)
        (Qatlib.Foundations.PureStateMath.boolEquivFin2.symm j.2 ^^ hit) (thermalUniformWire b w i)=j.1 i
      rw [Function.update_of_ne (thermalSignal_not_uniform b w i).symm,thermalEncoded_uniform]
    · change Qatlib.Foundations.PureStateMath.boolEquivFin2 (Function.update (thermalEncoded b w j) (thermalSignalWire b w)
        (Qatlib.Foundations.PureStateMath.boolEquivFin2.symm j.2 ^^ hit) (thermalSignalWire b w))=thermalSignalFlip j.2 hit
      rw [Function.update_self]
      rfl
  · funext k
    change Function.update (thermalEncoded b w j) (thermalSignalWire b w)
      (Qatlib.Foundations.PureStateMath.boolEquivFin2.symm j.2 ^^ hit) (thermalWorkWire b w k)=false
    rw [Function.update_of_ne (thermalSignal_not_work b w k).symm,thermalEncoded_work]

def thermalIntervalHit (b lo hi : ℕ) (u : Qatlib.Foundations.PureStateMath.Reg b) : Bool :=
  decide (lo≤thermalBitValue (List.ofFn u) ∧ thermalBitValue (List.ofFn u)<hi)

def thermalYBranch (b lo hi : ℕ) (u : Qatlib.Foundations.PureStateMath.Reg b) : Matrix (Fin 2) (Fin 2) ℂ :=
  if thermalIntervalHit b lo hi u then thermalQuarterTurn else 1

theorem thermalYSelect_basis (b lo hi : ℕ) (j : Qatlib.Foundations.PureStateMath.Reg b × Fin 2) :
    Qatlib.Concepts.BlockEncoding.LinearCombination.Select (thermalYBranch b lo hi) *ᵥ Qatlib.Foundations.PureStateMath.Ket j=
      (if thermalIntervalHit b lo hi j.1 && Qatlib.Foundations.PureStateMath.boolEquivFin2.symm j.2 then (-1:ℂ) else 1) •
        Qatlib.Foundations.PureStateMath.Ket (j.1,thermalSignalFlip j.2 (thermalIntervalHit b lo hi j.1)) := by
  rcases j with ⟨u,s⟩
  funext p
  rcases p with ⟨v,t⟩
  rw [Qatlib.Concepts.BlockEncoding.LinearCombination.mulVec_ket_apply]
  by_cases hv : v=u
  · subst v
    cases hh : thermalIntervalHit b lo hi u <;> fin_cases s <;> fin_cases t
    all_goals norm_num [Qatlib.Concepts.BlockEncoding.LinearCombination.Select,thermalYBranch,hh,thermalQuarterTurn,thermalSignalFlip,
      Qatlib.Foundations.PureStateMath.boolEquivFin2,Qatlib.Foundations.PureStateMath.Ket]
  · simp [Qatlib.Concepts.BlockEncoding.LinearCombination.Select,hv,Qatlib.Foundations.PureStateMath.Ket,Prod.mk.injEq]

def thermalPhaseBranch (b lo hi : ℕ) (phase : Fin 4) (u : Qatlib.Foundations.PureStateMath.Reg b) : Matrix (Fin 2) (Fin 2) ℂ :=
  (if thermalIntervalHit b lo hi u then thermalFlagPhaseValue phase else 1) • 1

theorem thermalPhaseSelect_basis (b lo hi : ℕ) (phase : Fin 4) (j : Qatlib.Foundations.PureStateMath.Reg b × Fin 2) :
    Qatlib.Concepts.BlockEncoding.LinearCombination.Select (thermalPhaseBranch b lo hi phase) *ᵥ Qatlib.Foundations.PureStateMath.Ket j=
      (if thermalIntervalHit b lo hi j.1 then thermalFlagPhaseValue phase else 1) •
        Qatlib.Foundations.PureStateMath.Ket j := by
  rcases j with ⟨u,s⟩
  funext p
  rcases p with ⟨v,t⟩
  rw [Qatlib.Concepts.BlockEncoding.LinearCombination.mulVec_ket_apply]
  by_cases hv : v=u
  · subst v
    by_cases hs : t=s <;> simp [Qatlib.Concepts.BlockEncoding.LinearCombination.Select,thermalPhaseBranch,Qatlib.Foundations.PureStateMath.Ket,Matrix.one_apply,hs]
  · simp [Qatlib.Concepts.BlockEncoding.LinearCombination.Select,hv,Qatlib.Foundations.PureStateMath.Ket,Prod.mk.injEq]

theorem thermalCanonical_interval_setup (b w lo hi : ℕ) (hcap : b≤w+2)
    (horder : lo≤hi) (hhi : hi≤2^b) :
    (thermalCutPairs b w lo).map Prod.fst=(thermalCutPairs b w hi).map Prod.fst ∧
    ((thermalCutPairs b w hi).map Prod.fst++thermalFlagWire b w::thermalScratchWires b w).Nodup ∧
    (thermalCutPairs b w hi).length≤(thermalScratchWires b w).length+2 ∧
    thermalCutoff (thermalCutFull b lo) (thermalCutPairs b w lo)≤
      thermalCutoff (thermalCutFull b hi) (thermalCutPairs b w hi) := by
  refine ⟨by rw [thermalCutPairs_wires,thermalCutPairs_wires],?_,?_,?_⟩
  · rw [thermalCutPairs_wires]
    exact thermalCanonical_layout b w
  · simpa [thermalCutPairs,thermalScratchWires] using! hcap
  · rw [thermalCutPairs_cutoff b w lo (horder.trans hhi),thermalCutPairs_cutoff b w hi hhi]
    exact horder

def thermalCanonicalYSteps (b w lo hi : ℕ) : List (ThermalNativeStep ((b+1)+(w+1))) :=
  thermalNativeIntervalSelectY (thermalCutFull b lo) (thermalCutPairs b w lo)
    (thermalCutFull b hi) (thermalCutPairs b w hi) (thermalFlagWire b w) (thermalSignalWire b w)
    (thermalScratchWires b w)

def thermalCanonicalPhaseSteps (b w lo hi : ℕ) (phase : Fin 4) : List (ThermalNativeStep ((b+1)+(w+1))) :=
  thermalNativeIntervalPhase (thermalCutFull b lo) (thermalCutPairs b w lo)
    (thermalCutFull b hi) (thermalCutPairs b w hi) (thermalFlagWire b w) (thermalScratchWires b w) phase

theorem thermalEncoded_scratch (b w : ℕ) (j : Qatlib.Foundations.PureStateMath.Reg b × Fin 2) :
    ∀ v∈thermalScratchWires b w,thermalEncoded b w j v=false := by
  intro v hv
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hv
  exact thermalEncoded_work b w j i.succ

theorem thermalCanonicalY_intertwine (b w lo hi : ℕ) (hcap : b≤w+2)
    (horder : lo≤hi) (hhi : hi≤2^b) :
    Qatlib.Concepts.UniformBqp.FiniteGateWord.finiteCodeWordMatrix ((b+1)+(w+1)) (thermalNativeProgram (thermalCanonicalYSteps b w lo hi))*
      thermalWorkspaceEmbed b w=
      thermalWorkspaceEmbed b w*Qatlib.Concepts.BlockEncoding.LinearCombination.Select (thermalYBranch b lo hi) := by
  apply thermalMatrix_intertwine_of_basis
  intro j
  rw [thermalWorkspaceEmbed_basis,thermalYSelect_basis,Matrix.mulVec_smul,thermalWorkspaceEmbed_basis]
  rcases thermalCanonical_interval_setup b w lo hi hcap horder hhi with ⟨hw,hn,hlen,ho⟩
  have hsig : thermalSignalWire b w∉(thermalCutPairs b w hi).map Prod.fst++
      thermalFlagWire b w::thermalScratchWires b w := by
    rw [thermalCutPairs_wires]
    exact thermalCanonical_signal_outside b w
  have hb := thermalNativeIntervalSelectY_basis (thermalCutFull b lo) (thermalCutPairs b w lo)
    (thermalCutFull b hi) (thermalCutPairs b w hi) (thermalFlagWire b w) (thermalSignalWire b w)
    (thermalScratchWires b w) hw hn hlen ho hsig (thermalEncoded b w j)
    (thermalEncoded_scratch b w j) (thermalEncoded_work b w j 0)
  simp only [thermalCutPairs_cutoff b w lo (horder.trans hhi),thermalCutPairs_cutoff b w hi hhi,
    thermalCutPairs_data,thermalEncoded_signal,thermalEncoded_update,Qatlib.Concepts.UniformBqp.FiniteGateWord.finite_phase_word_run] at hb
  simpa only [thermalCanonicalYSteps,thermalIntervalHit,thermalEncoded,Qatlib.Foundations.PureStateMath.ApplyGate] using! hb

theorem thermalCanonicalPhase_intertwine (b w lo hi : ℕ) (phase : Fin 4) (hcap : b≤w+2)
    (horder : lo≤hi) (hhi : hi≤2^b) :
    Qatlib.Concepts.UniformBqp.FiniteGateWord.finiteCodeWordMatrix ((b+1)+(w+1)) (thermalNativeProgram (thermalCanonicalPhaseSteps b w lo hi phase))*
      thermalWorkspaceEmbed b w=
      thermalWorkspaceEmbed b w*Qatlib.Concepts.BlockEncoding.LinearCombination.Select (thermalPhaseBranch b lo hi phase) := by
  apply thermalMatrix_intertwine_of_basis
  intro j
  rw [thermalWorkspaceEmbed_basis,thermalPhaseSelect_basis,Matrix.mulVec_smul,thermalWorkspaceEmbed_basis]
  rcases thermalCanonical_interval_setup b w lo hi hcap horder hhi with ⟨hw,hn,hlen,ho⟩
  have hb := thermalNativeIntervalPhase_basis (thermalCutFull b lo) (thermalCutPairs b w lo)
    (thermalCutFull b hi) (thermalCutPairs b w hi) (thermalFlagWire b w) (thermalScratchWires b w) phase
    hw hn hlen ho (thermalEncoded b w j) (thermalEncoded_scratch b w j) (thermalEncoded_work b w j 0)
  simp only [thermalCutPairs_cutoff b w lo (horder.trans hhi),thermalCutPairs_cutoff b w hi hhi,
    thermalCutPairs_data,Qatlib.Concepts.UniformBqp.FiniteGateWord.finite_phase_word_run] at hb
  simpa only [thermalCanonicalPhaseSteps,thermalIntervalHit,thermalEncoded,Qatlib.Foundations.PureStateMath.ApplyGate,thermalPhaseBranch] using! hb

theorem thermalSelect_one {J I : Type*} [Fintype J] [Fintype I] [DecidableEq J] [DecidableEq I] :
    Qatlib.Concepts.BlockEncoding.LinearCombination.Select (fun _ : J => (1 : Matrix I I ℂ))=1 := by
  ext p q
  rcases p with ⟨a,i⟩
  rcases q with ⟨b,j⟩
  by_cases h : a=b <;> simp [Qatlib.Concepts.BlockEncoding.LinearCombination.Select,Matrix.one_apply,Prod.mk.injEq,h]

theorem thermalSelect_mul {J I : Type*} [Fintype J] [Fintype I] [DecidableEq J] [DecidableEq I]
    (A B : J → Matrix I I ℂ) : Qatlib.Concepts.BlockEncoding.LinearCombination.Select A*Qatlib.Concepts.BlockEncoding.LinearCombination.Select B=Qatlib.Concepts.BlockEncoding.LinearCombination.Select (fun j => A j*B j) := by
  ext p q
  rcases p with ⟨a,i⟩
  rcases q with ⟨b,j⟩
  simp only [Matrix.mul_apply,Fintype.sum_prod_type,Qatlib.Concepts.BlockEncoding.LinearCombination.Select,Matrix.of_apply]
  by_cases h : a=b
  · subst b
    rw [Finset.sum_eq_single a]
    · simp
    · intro k _ hk
      simp [hk,Ne.symm hk]
    · intro ha
      exact absurd (Finset.mem_univ a) ha
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : k=a
    · subst k
      simp [h]
    · simp [Ne.symm hk]

theorem thermalIntervalHit_empty (b lo : ℕ) (u : Qatlib.Foundations.PureStateMath.Reg b) : thermalIntervalHit b lo lo u=false := by
  have h : ¬(lo≤thermalBitValue (List.ofFn u) ∧ thermalBitValue (List.ofFn u)<lo) := by omega
  simp [thermalIntervalHit,h]

theorem thermalYSelect_empty (b lo : ℕ) : Qatlib.Concepts.BlockEncoding.LinearCombination.Select (thermalYBranch b lo lo)=1 := by
  have he : thermalYBranch b lo lo=(fun _ => 1) := by
    funext u
    simp [thermalYBranch,thermalIntervalHit_empty]
  rw [he,thermalSelect_one]

theorem thermalPhaseSelect_empty (b lo : ℕ) (phase : Fin 4) :
    Qatlib.Concepts.BlockEncoding.LinearCombination.Select (thermalPhaseBranch b lo lo phase)=1 := by
  have he : thermalPhaseBranch b lo lo phase=(fun _ => 1) := by
    funext u
    simp [thermalPhaseBranch,thermalIntervalHit_empty]
  rw [he,thermalSelect_one]

theorem thermalPhaseSelect_zero (b lo hi : ℕ) : Qatlib.Concepts.BlockEncoding.LinearCombination.Select (thermalPhaseBranch b lo hi 0)=1 := by
  have he : thermalPhaseBranch b lo hi 0=(fun _ => 1) := by
    funext u
    simp [thermalPhaseBranch,thermalFlagPhaseValue]
  rw [he,thermalSelect_one]

def thermalGuardedYSteps (b w lo hi : ℕ) : List (ThermalNativeStep ((b+1)+(w+1))) :=
  if lo=hi then [] else thermalCanonicalYSteps b w lo hi

def thermalGuardedPhaseSteps (b w lo hi : ℕ) (phase : Fin 4) : List (ThermalNativeStep ((b+1)+(w+1))) :=
  if lo=hi then [] else thermalCanonicalPhaseSteps b w lo hi phase

theorem thermalGuardedY_intertwine (b w lo hi : ℕ) (hcap : b≤w+2) (horder : lo≤hi) (hhi : hi≤2^b) :
    Qatlib.Concepts.UniformBqp.FiniteGateWord.finiteCodeWordMatrix ((b+1)+(w+1)) (thermalNativeProgram (thermalGuardedYSteps b w lo hi))*
      thermalWorkspaceEmbed b w=thermalWorkspaceEmbed b w*Qatlib.Concepts.BlockEncoding.LinearCombination.Select (thermalYBranch b lo hi) := by
  by_cases he : lo=hi
  · subst hi
    simp [thermalGuardedYSteps,thermalNativeProgram,Qatlib.Concepts.UniformBqp.FiniteGateWord.finiteCodeWordMatrix,thermalYSelect_empty]
  · simpa only [thermalGuardedYSteps,if_neg he] using!
      thermalCanonicalY_intertwine b w lo hi hcap horder hhi

theorem thermalGuardedPhase_intertwine (b w lo hi : ℕ) (phase : Fin 4)
    (hcap : b≤w+2) (horder : lo≤hi) (hhi : hi≤2^b) :
    Qatlib.Concepts.UniformBqp.FiniteGateWord.finiteCodeWordMatrix ((b+1)+(w+1)) (thermalNativeProgram (thermalGuardedPhaseSteps b w lo hi phase))*
      thermalWorkspaceEmbed b w=thermalWorkspaceEmbed b w*Qatlib.Concepts.BlockEncoding.LinearCombination.Select (thermalPhaseBranch b lo hi phase) := by
  by_cases he : lo=hi
  · subst hi
    simp [thermalGuardedPhaseSteps,thermalNativeProgram,Qatlib.Concepts.UniformBqp.FiniteGateWord.finiteCodeWordMatrix,thermalPhaseSelect_empty]
  · simpa only [thermalGuardedPhaseSteps,if_neg he] using!
      thermalCanonicalPhase_intertwine b w lo hi phase hcap horder hhi

theorem thermalIntertwine_mul {I J : Type*} [Fintype I] [Fintype J]
    (A B : Matrix I I ℂ) (a b : Matrix J J ℂ) (G : Matrix I J ℂ)
    (hA : A*G=G*a) (hB : B*G=G*b) : (A*B)*G=G*(a*b) := by
  rw [Matrix.mul_assoc,hB,← Matrix.mul_assoc,hA,Matrix.mul_assoc]

theorem thermalNativeProgram_append {n : ℕ} (gs hs : List (ThermalNativeStep n)) :
    thermalNativeProgram (gs++hs)=thermalNativeProgram gs++thermalNativeProgram hs := by
  simp [thermalNativeProgram,List.flatMap_append]

theorem thermalNative_fixed_program {n : ℕ} (gs : List Qatlib.Concepts.GateVocabulary.FiniteGateDescription.FiniteGateCode) :
    thermalNativeProgram (gs.map (ThermalNativeStep.fixed (n:=n)))=gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih => simpa [thermalNativeProgram,thermalNativeLower] using! congrArg (List.cons g) ih

def thermalNativeHSteps (b w : ℕ) : List (ThermalNativeStep ((b+1)+(w+1))) :=
  (thermalUniformHWord (thermalUniformWires b w)).map .fixed

theorem thermalNativeH_program (b w : ℕ) :
    thermalNativeProgram (thermalNativeHSteps b w)=thermalUniformHWord (thermalUniformWires b w) :=
  thermalNative_fixed_program _

theorem thermalNative_append_intertwine {n : ℕ} {J : Type*} [Fintype J]
    (gs hs : List (ThermalNativeStep n)) (a b : Matrix J J ℂ) (G : Matrix (Qatlib.Foundations.PureStateMath.Reg n) J ℂ)
    (hg : Qatlib.Concepts.UniformBqp.FiniteGateWord.finiteCodeWordMatrix n (thermalNativeProgram gs)*G=G*a)
    (hh : Qatlib.Concepts.UniformBqp.FiniteGateWord.finiteCodeWordMatrix n (thermalNativeProgram hs)*G=G*b) :
    Qatlib.Concepts.UniformBqp.FiniteGateWord.finiteCodeWordMatrix n (thermalNativeProgram (gs++hs))*G=G*(b*a) := by
  rw [thermalNativeProgram_append,thermalWordMatrix_append]
  exact thermalIntertwine_mul _ _ _ _ _ hh hg

theorem thermalPhaseY_product (b ylo yhi zlo zhi : ℕ) (hsep : yhi≤zlo) :
    (fun u => thermalPhaseBranch b zlo zhi 2 u*thermalYBranch b ylo yhi u)=
      thermalUniformBranch b ylo yhi zlo zhi := by
  funext u
  dsimp only [thermalPhaseBranch,thermalYBranch,thermalIntervalHit,thermalUniformBranch]
  by_cases hy : ylo≤thermalBitValue (List.ofFn u) ∧ thermalBitValue (List.ofFn u)<yhi
  · have hz : ¬(zlo≤thermalBitValue (List.ofFn u) ∧ thermalBitValue (List.ofFn u)<zhi) := by omega
    simp [hy,hz]
  · by_cases hz : zlo≤thermalBitValue (List.ofFn u) ∧ thermalBitValue (List.ofFn u)<zhi
    · simp [hy,hz,thermalFlagPhaseValue]
    · simp [hy,hz]

theorem thermalHadamardN_adjoint (b : ℕ) : (Qatlib.Foundations.PureStateMath.HadamardN b)ᴴ=Qatlib.Foundations.PureStateMath.HadamardN b := by
  ext x y
  simp only [Matrix.conjTranspose_apply,Qatlib.Foundations.PureStateMath.HadamardN,Matrix.of_apply,RCLike.star_def,map_prod]
  apply Finset.prod_congr rfl
  intro i _
  simpa only [Matrix.conjTranspose_apply,RCLike.star_def] using!
    congrFun (congrFun Qatlib.Foundations.PureStateMath.hadamard_conjTranspose (x i)) (y i)

def thermalNativeLCUSteps (b w w0 w1 pad : ℕ) : List (ThermalNativeStep ((b+1)+(w+1))) :=
  (((((thermalNativeHSteps b w ++ thermalGuardedPhaseSteps b w 0 w0 0) ++
    thermalGuardedYSteps b w w0 (w0+w1)) ++
    thermalGuardedPhaseSteps b w (w0+w1) (w0+w1+pad) 0) ++
    thermalGuardedPhaseSteps b w (w0+w1+pad) (2^b) 2) ++ thermalNativeHSteps b w)

theorem thermalNativeLCU_intertwine (b w w0 w1 pad : ℕ) (hcap : b≤w+2)
    (htotal : w0+w1+pad+pad=2^b) :
    Qatlib.Concepts.UniformBqp.FiniteGateWord.finiteCodeWordMatrix ((b+1)+(w+1)) (thermalNativeProgram (thermalNativeLCUSteps b w w0 w1 pad))*
      thermalWorkspaceEmbed b w=
      thermalWorkspaceEmbed b w*thermalUniformLCU b w0 (w0+w1) (w0+w1+pad) (2^b) := by
  have hH : Qatlib.Concepts.UniformBqp.FiniteGateWord.finiteCodeWordMatrix ((b+1)+(w+1)) (thermalNativeProgram (thermalNativeHSteps b w))*
      thermalWorkspaceEmbed b w=thermalWorkspaceEmbed b w*Qatlib.Foundations.PureStateMath.TensorGate (Qatlib.Foundations.PureStateMath.HadamardN b) (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [thermalNativeH_program]
    exact thermalUniformHWord_intertwine b w
  have h0 := thermalGuardedPhase_intertwine b w 0 w0 0 hcap (by omega) (by omega)
  have hy := thermalGuardedY_intertwine b w w0 (w0+w1) hcap (by omega) (by omega)
  have h2 := thermalGuardedPhase_intertwine b w (w0+w1) (w0+w1+pad) 0 hcap (by omega) (by omega)
  have hz := thermalGuardedPhase_intertwine b w (w0+w1+pad) (2^b) 2 hcap (by omega) (by rfl)
  rw [thermalPhaseSelect_zero] at h0 h2
  have h01 := thermalNative_append_intertwine _ _ _ _ _ hH h0
  have h012 := thermalNative_append_intertwine _ _ _ _ _ h01 hy
  have h0123 := thermalNative_append_intertwine _ _ _ _ _ h012 h2
  have h01234 := thermalNative_append_intertwine _ _ _ _ _ h0123 hz
  have hfull := thermalNative_append_intertwine _ _ _ _ _ h01234 hH
  simp only [Matrix.one_mul] at hfull
  change Qatlib.Concepts.UniformBqp.FiniteGateWord.finiteCodeWordMatrix ((b+1)+(w+1)) (thermalNativeProgram (thermalNativeLCUSteps b w w0 w1 pad))*
      thermalWorkspaceEmbed b w=thermalWorkspaceEmbed b w*
      (Qatlib.Foundations.PureStateMath.TensorGate (Qatlib.Foundations.PureStateMath.HadamardN b) (1 : Matrix (Fin 2) (Fin 2) ℂ)*
        (Qatlib.Concepts.BlockEncoding.LinearCombination.Select (thermalPhaseBranch b (w0+w1+pad) (2^b) 2)*
          (Qatlib.Concepts.BlockEncoding.LinearCombination.Select (thermalYBranch b w0 (w0+w1))*Qatlib.Foundations.PureStateMath.TensorGate (Qatlib.Foundations.PureStateMath.HadamardN b) 1))) at hfull
  have heff : thermalUniformLCU b w0 (w0+w1) (w0+w1+pad) (2^b)=
      Qatlib.Foundations.PureStateMath.TensorGate (Qatlib.Foundations.PureStateMath.HadamardN b) (1 : Matrix (Fin 2) (Fin 2) ℂ)*
        (Qatlib.Concepts.BlockEncoding.LinearCombination.Select (thermalPhaseBranch b (w0+w1+pad) (2^b) 2)*
          (Qatlib.Concepts.BlockEncoding.LinearCombination.Select (thermalYBranch b w0 (w0+w1))*Qatlib.Foundations.PureStateMath.TensorGate (Qatlib.Foundations.PureStateMath.HadamardN b) 1)) := by
    rw [thermalUniformLCU,Qatlib.Concepts.BlockEncoding.LinearCombination.LCUWorkspace,thermalHadamardN_adjoint]
    rw [← thermalPhaseY_product b w0 (w0+w1) (w0+w1+pad) (2^b) (by omega),← thermalSelect_mul]
    simp only [Matrix.mul_assoc]
  rw [heff]
  exact hfull

theorem thermalCanonicalY_legal (b w lo hi : ℕ) (hcap : b≤w+2) (horder : lo≤hi) (hhi : hi≤2^b) :
    ∀ g∈thermalCanonicalYSteps b w lo hi,thermalNativeLegal g := by
  rcases thermalCanonical_interval_setup b w lo hi hcap horder hhi with ⟨hw,hn,hlen,_⟩
  exact thermalNativeIntervalSelectY_legal _ _ _ _ _ _ _ hw hn hlen
    (thermalSignal_not_work b w 0).symm

theorem thermalCanonicalPhase_legal (b w lo hi : ℕ) (phase : Fin 4)
    (hcap : b≤w+2) (horder : lo≤hi) (hhi : hi≤2^b) :
    ∀ g∈thermalCanonicalPhaseSteps b w lo hi phase,thermalNativeLegal g := by
  rcases thermalCanonical_interval_setup b w lo hi hcap horder hhi with ⟨hw,hn,hlen,_⟩
  exact thermalNativeIntervalPhase_legal _ _ _ _ _ _ _ hw hn hlen

theorem thermalGuardedY_legal (b w lo hi : ℕ) (hcap : b≤w+2) (horder : lo≤hi) (hhi : hi≤2^b) :
    ∀ g∈thermalGuardedYSteps b w lo hi,thermalNativeLegal g := by
  by_cases he : lo=hi
  · simp [thermalGuardedYSteps,he]
  · simpa only [thermalGuardedYSteps,if_neg he] using!
      thermalCanonicalY_legal b w lo hi hcap horder hhi

theorem thermalGuardedPhase_legal (b w lo hi : ℕ) (phase : Fin 4)
    (hcap : b≤w+2) (horder : lo≤hi) (hhi : hi≤2^b) :
    ∀ g∈thermalGuardedPhaseSteps b w lo hi phase,thermalNativeLegal g := by
  by_cases he : lo=hi
  · simp [thermalGuardedPhaseSteps,he]
  · simpa only [thermalGuardedPhaseSteps,if_neg he] using!
      thermalCanonicalPhase_legal b w lo hi phase hcap horder hhi

theorem thermalNativeH_legal (b w : ℕ) : ∀ g∈thermalNativeHSteps b w,thermalNativeLegal g := by
  intro g hg
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hg
  change Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeLegal ((b+1)+(w+1)) c=true
  have hh := thermalUniformHWord_legal (thermalUniformWires b w)
  simp only [Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordLegal,List.all_eq_true] at hh
  exact hh c hc

theorem thermalNativeLCU_legal (b w w0 w1 pad : ℕ) (hcap : b≤w+2)
    (htotal : w0+w1+pad+pad=2^b) : ∀ g∈thermalNativeLCUSteps b w w0 w1 pad,thermalNativeLegal g := by
  intro g hg
  simp only [thermalNativeLCUSteps,List.mem_append] at hg
  rcases hg with ((((hg|hg)|hg)|hg)|hg)|hg
  · exact thermalNativeH_legal b w g hg
  · exact thermalGuardedPhase_legal b w 0 w0 0 hcap (by omega) (by omega) g hg
  · exact thermalGuardedY_legal b w w0 (w0+w1) hcap (by omega) (by omega) g hg
  · exact thermalGuardedPhase_legal b w (w0+w1) (w0+w1+pad) 0 hcap (by omega) (by omega) g hg
  · exact thermalGuardedPhase_legal b w (w0+w1+pad) (2^b) 2 hcap (by omega) (by rfl) g hg
  · exact thermalNativeH_legal b w g hg

theorem thermalNative_inverse_adjoint {n : ℕ} (gs : List (ThermalNativeStep n))
    (hg : ∀ g∈gs,thermalNativeLegal g) :
    Qatlib.Concepts.UniformBqp.FiniteGateWord.finiteCodeWordMatrix n (thermalNativeProgram (thermalNativeInverse gs))=
      (Qatlib.Concepts.UniformBqp.FiniteGateWord.finiteCodeWordMatrix n (thermalNativeProgram gs))ᴴ := by
  have hp : Qatlib.Concepts.UniformBqp.FiniteGateWord.finiteCodeWordMatrix n (thermalNativeProgram (thermalNativeInverse gs))*
      Qatlib.Concepts.UniformBqp.FiniteGateWord.finiteCodeWordMatrix n (thermalNativeProgram gs)=1 := by
    ext i j
    have h :=
        congrFun (thermalNative_paid_inverse gs hg (Qatlib.Foundations.PureStateMath.Ket j)).1 i
    simpa only [Qatlib.Concepts.UniformBqp.FiniteGateWord.finite_phase_word_run,Qatlib.Foundations.PureStateMath.ApplyGate,Matrix.mulVec_mulVec,
      thermalRect_ket_column,Matrix.one_apply,Qatlib.Foundations.PureStateMath.Ket] using! h
  have hu :=
      (Qatlib.Concepts.UniformBqp.FiniteGateWord.finite_code_word_determinant_invariant n _ (thermalNative_program_legal gs hg)).1
  have hunit : Qatlib.Concepts.UniformBqp.FiniteGateWord.finiteCodeWordMatrix n (thermalNativeProgram gs)*
      (Qatlib.Concepts.UniformBqp.FiniteGateWord.finiteCodeWordMatrix n (thermalNativeProgram gs))ᴴ=1 := by
    simpa only [Matrix.star_eq_conjTranspose] using! Matrix.mem_unitaryGroup_iff.mp hu
  calc
    _ = Qatlib.Concepts.UniformBqp.FiniteGateWord.finiteCodeWordMatrix n (thermalNativeProgram (thermalNativeInverse gs))*1 := by rw [Matrix.mul_one]
    _ = Qatlib.Concepts.UniformBqp.FiniteGateWord.finiteCodeWordMatrix n (thermalNativeProgram (thermalNativeInverse gs))*
        (Qatlib.Concepts.UniformBqp.FiniteGateWord.finiteCodeWordMatrix n (thermalNativeProgram gs)*(Qatlib.Concepts.UniformBqp.FiniteGateWord.finiteCodeWordMatrix n (thermalNativeProgram gs))ᴴ) := by rw [hunit]
    _ = (Qatlib.Concepts.UniformBqp.FiniteGateWord.finiteCodeWordMatrix n (thermalNativeProgram (thermalNativeInverse gs))*
        Qatlib.Concepts.UniformBqp.FiniteGateWord.finiteCodeWordMatrix n (thermalNativeProgram gs))*(Qatlib.Concepts.UniformBqp.FiniteGateWord.finiteCodeWordMatrix n (thermalNativeProgram gs))ᴴ := by
      rw [Matrix.mul_assoc]
    _ = _ := by rw [hp,Matrix.one_mul]

theorem thermalNative_expanded_inverse_adjoint {n : ℕ} (gs : List (ThermalNativeStep n))
    (hg : ∀ g∈gs,thermalNativeLegal g) :
    Qatlib.Concepts.UniformBqp.FiniteGateWord.finiteCodeWordMatrix n (thermalNativeProgram (thermalNativeInverse (thermalNativeExpandCCX gs)))=
      (Qatlib.Concepts.UniformBqp.FiniteGateWord.finiteCodeWordMatrix n (thermalNativeProgram gs))ᴴ := by
  rw [thermalNative_inverse_adjoint _ (thermalNative_expand_legal gs hg),thermalNative_expand_program]

theorem thermalNativeLCU_inverse_intertwine (b w w0 w1 pad : ℕ) (hcap : b≤w+2)
    (htotal : w0+w1+pad+pad=2^b) :
    Qatlib.Concepts.UniformBqp.FiniteGateWord.finiteCodeWordMatrix ((b+1)+(w+1)) (thermalNativeProgram (thermalNativeInverse
      (thermalNativeExpandCCX (thermalNativeLCUSteps b w w0 w1 pad))))*thermalWorkspaceEmbed b w=
      thermalWorkspaceEmbed b w*(thermalUniformLCU b w0 (w0+w1) (w0+w1+pad) (2^b))ᴴ := by
  have hl := thermalNativeLCU_legal b w w0 w1 pad hcap htotal
  rw [thermalNative_expanded_inverse_adjoint _ hl]
  have hu :=
      (Qatlib.Concepts.UniformBqp.FiniteGateWord.finite_code_word_determinant_invariant ((b+1)+(w+1)) _ (thermalNative_program_legal _ hl)).1
  have hue := thermalUniformLCU_unitary b w0 (w0+w1) (w0+w1+pad) (2^b)
  apply thermalInverse_intertwine _ _ _ _ _
  · simpa only [Matrix.star_eq_conjTranspose] using! Matrix.mem_unitaryGroup_iff'.mp hu
  · simpa only [Matrix.star_eq_conjTranspose] using! Matrix.mem_unitaryGroup_iff.mp hue
  · exact thermalNativeLCU_intertwine b w w0 w1 pad hcap htotal

theorem thermalCanonical_interval_cost (b w lo hi : ℕ) (hcap : b≤w+2)
    (horder : lo≤hi) (hhi : hi≤2^b) :
    Qatlib.Foundations.QueryWordCore.Circuit.GateCount (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit ((b+1)+(w+1)) (thermalIntervalWord
      (thermalCutFull b lo) (thermalCutPairs b w lo) (thermalCutFull b hi) (thermalCutPairs b w hi)
      (thermalFlagWire b w) (thermalScratchWires b w)))≤2+64*b^2 := by
  rcases thermalCanonical_interval_setup b w lo hi hcap horder hhi with ⟨hw,_,hlen,_⟩
  have h := (thermalIntervalWord_cost (thermalCutFull b lo) (thermalCutPairs b w lo)
    (thermalCutFull b hi) (thermalCutPairs b w hi) (thermalFlagWire b w) (thermalScratchWires b w) hw hlen).2.2
  simpa only [thermalCutPairs,List.length_ofFn] using! h

theorem thermalGuardedY_cost_bound (b w lo hi : ℕ) (hcap : b≤w+2) (horder : lo≤hi) (hhi : hi≤2^b) :
    Qatlib.Foundations.QueryWordCore.Circuit.GateCount (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit ((b+1)+(w+1)) (thermalNativeProgram (thermalGuardedYSteps b w lo hi)))≤11+128*b^2 := by
  by_cases he : lo=hi
  · simp [thermalGuardedYSteps,he,thermalNativeProgram,Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit]
  · have hc := (thermalNativeIntervalSelectY_cost (thermalCutFull b lo) (thermalCutPairs b w lo)
      (thermalCutFull b hi) (thermalCutPairs b w hi) (thermalFlagWire b w) (thermalSignalWire b w)
      (thermalScratchWires b w)).1
    have hb := thermalCanonical_interval_cost b w lo hi hcap horder hhi
    change Qatlib.Foundations.QueryWordCore.Circuit.GateCount (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit ((b+1)+(w+1))
      (thermalNativeProgram (thermalCanonicalYSteps b w lo hi)))=_ at hc
    rw [thermalGuardedYSteps,if_neg he,hc]
    omega

theorem thermalGuardedPhase_cost_bound (b w lo hi : ℕ) (phase : Fin 4)
    (hcap : b≤w+2) (horder : lo≤hi) (hhi : hi≤2^b) :
    Qatlib.Foundations.QueryWordCore.Circuit.GateCount (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit ((b+1)+(w+1)) (thermalNativeProgram
      (thermalGuardedPhaseSteps b w lo hi phase)))≤
      4+128*b^2+(if phase.val=0 then 0 else if phase.val=2 then 4 else 2) := by
  by_cases he : lo=hi
  · simp [thermalGuardedPhaseSteps,he,thermalNativeProgram,Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit]
  · have hc := (thermalNativeIntervalPhase_cost (thermalCutFull b lo) (thermalCutPairs b w lo)
      (thermalCutFull b hi) (thermalCutPairs b w hi) (thermalFlagWire b w) (thermalScratchWires b w) phase).1
    have hb := thermalCanonical_interval_cost b w lo hi hcap horder hhi
    change Qatlib.Foundations.QueryWordCore.Circuit.GateCount (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit ((b+1)+(w+1))
      (thermalNativeProgram (thermalCanonicalPhaseSteps b w lo hi phase)))=_ at hc
    rw [thermalGuardedPhaseSteps,if_neg he,hc]
    omega

theorem thermalNativeLCU_cost (b w w0 w1 pad : ℕ) (hcap : b≤w+2)
    (htotal : w0+w1+pad+pad=2^b) :
    Qatlib.Foundations.QueryWordCore.Circuit.GateCount (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit ((b+1)+(w+1)) (thermalNativeProgram (thermalNativeLCUSteps b w w0 w1 pad)))≤
      512*b^2+2*b+27 ∧
    Qatlib.Foundations.QueryWordCore.Circuit.QueryCount (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit ((b+1)+(w+1)) (thermalNativeProgram (thermalNativeLCUSteps b w w0 w1 pad)))=0 := by
  constructor
  · have h0 := thermalGuardedPhase_cost_bound b w 0 w0 0 hcap (by omega) (by omega)
    have hy := thermalGuardedY_cost_bound b w w0 (w0+w1) hcap (by omega) (by omega)
    have h2 := thermalGuardedPhase_cost_bound b w (w0+w1) (w0+w1+pad) 0 hcap (by omega) (by omega)
    have hz := thermalGuardedPhase_cost_bound b w (w0+w1+pad) (2^b) 2 hcap (by omega) (by rfl)
    change Qatlib.Foundations.QueryWordCore.Circuit.GateCount _≤4+128*b^2 at h0 h2
    change Qatlib.Foundations.QueryWordCore.Circuit.GateCount _≤4+128*b^2+4 at hz
    have hH : (thermalNativeProgram (thermalNativeHSteps b w)).length=b := by
      rw [thermalNativeH_program]
      simp [thermalUniformHWord,thermalUniformWires]
    rw [(Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit_counts _ _).2] at h0 hy h2 hz ⊢
    simp only [thermalNativeLCUSteps,thermalNativeProgram_append,List.length_append,hH]
    omega
  · exact (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit_counts _ _).1

theorem thermalNativeLCU_inverse_cost (b w w0 w1 pad : ℕ) :
    Qatlib.Foundations.QueryWordCore.Circuit.GateCount (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit ((b+1)+(w+1)) (thermalNativeProgram
      (thermalNativeInverse (thermalNativeExpandCCX (thermalNativeLCUSteps b w w0 w1 pad)))))=
    Qatlib.Foundations.QueryWordCore.Circuit.GateCount (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit ((b+1)+(w+1)) (thermalNativeProgram (thermalNativeLCUSteps b w w0 w1 pad))) ∧
    Qatlib.Foundations.QueryWordCore.Circuit.QueryCount (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit ((b+1)+(w+1)) (thermalNativeProgram
      (thermalNativeInverse (thermalNativeExpandCCX (thermalNativeLCUSteps b w w0 w1 pad)))))=0 := by
  constructor
  · simp only [(Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit_counts _ _).2,thermalNative_program_inverse_length,thermalNative_expand_program]
  · exact (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit_counts _ _).1

end Qatlib.Papers.ThermalDrift26.ThermalSampling
