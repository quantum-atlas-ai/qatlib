/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QAOASupremacy16.LocalGadget.Source
import Qatlib.Papers.QAOASupremacy16.CircuitModel.Native
set_option warningAsError false
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace Qatlib.Papers.QAOASupremacy16.LocalGadget
open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.QAOASupremacy16.CircuitDefs
open Qatlib.Foundations.MatrixAlgebra.PhaseUnitary
open Matrix
open scoped BigOperators Kronecker

theorem Htilde_unitary : Htilde ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff',Matrix.star_eq_conjTranspose]
  ext a b
  cases a <;> cases b <;>
    simp [Htilde,Matrix.mul_apply,Matrix.conjTranspose_apply,RCLike.star_def]
    <;> ring_nf <;> norm_num [sqrt2_sq]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def localH : Matrix (Bool×ι) (Bool×ι) ℂ := Hadamard ⊗ₖ (1:Matrix ι ι ℂ)

theorem localH_apply (α : QState (Bool×ι)) : ApplyGate localH α=hadamardOnFst α := by
  funext ⟨a,r⟩
  simp [localH,ApplyGate,Matrix.mulVec,dotProduct,Fintype.sum_prod_type,Matrix.one_apply,hadamardOnFst]

theorem localH_unitary : (localH:Matrix (Bool×ι) (Bool×ι) ℂ)∈Matrix.unitaryGroup (Bool×ι) ℂ :=
  Matrix.kronecker_mem_unitary hadamard_unitary (one_mem _)

theorem hadamardOnFst_normalized {α : QState (Bool×ι)} (hα : Normalized α) :
    Normalized (hadamardOnFst α) := by
  rw [← localH_apply]
  exact normalized_applyGate localH_unitary hα

def gadgetInput (α : QState (Bool×ι)) : QState (Bool×(Bool×ι)) :=
  fun p=>Ket false p.1*α p.2
omit [DecidableEq ι] in

theorem gadgetInput_normalized {α : QState (Bool×ι)} (hα : Normalized α) : Normalized (gadgetInput α) := by
  unfold Normalized gadgetInput
  simp [Fintype.sum_prod_type,Ket]
  simpa [Normalized,Fintype.sum_prod_type] using hα

def fullDiag : Matrix (Bool×(Bool×ι)) (Bool×(Bool×ι)) ℂ :=
  Matrix.diagonal fun p=>gadgetDiag p.1 p.2.1

def gadgetCircuit : Matrix (Bool×(Bool×ι)) (Bool×(Bool×ι)) ℂ :=
  ((1:Matrix Bool Bool ℂ) ⊗ₖ (Htilde ⊗ₖ (1:Matrix ι ι ℂ))) * fullDiag *
    (Hadamard ⊗ₖ (1:Matrix (Bool×ι) (Bool×ι) ℂ))

theorem gadgetCircuit_unitary : (gadgetCircuit:Matrix (Bool×(Bool×ι)) (Bool×(Bool×ι)) ℂ)
    ∈Matrix.unitaryGroup (Bool×(Bool×ι)) ℂ := by
  apply mul_mem
  · apply mul_mem
    · exact Matrix.kronecker_mem_unitary (one_mem _)
        (Matrix.kronecker_mem_unitary Htilde_unitary (one_mem _))
    · apply diagonal_unitary
      intro ⟨a,j,r⟩
      cases a <;> cases j <;> simp [gadgetDiag]
  · exact Matrix.kronecker_mem_unitary hadamard_unitary (one_mem _)

def gadgetOutput (α : QState (Bool×ι)) : QState (Bool×(Bool×ι)) :=
    ApplyGate gadgetCircuit (gadgetInput α)

theorem gadgetOutput_normalized {α : QState (Bool×ι)} (hα : Normalized α) : Normalized (gadgetOutput α) :=
  normalized_applyGate gadgetCircuit_unitary (gadgetInput_normalized hα)

theorem gadgetOutput_branch (α : QState (Bool×ι)) (a : Bool) (r : ι) :
    gadgetOutput α (a,(false,r))=gadgetState α (a,r) := by
  unfold gadgetOutput gadgetCircuit
  simp only [ApplyGate,← Matrix.mulVec_mulVec]
  simp [fullDiag,Matrix.diagonal,gadgetInput,Matrix.mulVec,dotProduct,
    Fintype.sum_prod_type,Matrix.one_apply,Ket,Plus,gadgetState]
  ring

theorem gadget_branch_mass {α : QState (Bool×ι)} (hα : Normalized α) :
    ∑ p:Bool×ι, BornProb (gadgetState α) p=1/2 := by
  have ht:=hadamardOnFst_normalized hα
  rw [gadget_identity]
  have hc : ‖(Real.sqrt 2:ℂ)⁻¹‖^2=(1/2:ℝ) := by
    rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg 2),inv_pow,Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
    norm_num
  simp only [BornProb,Pi.smul_apply,smul_eq_mul,norm_mul,mul_pow,hc]
  rw [← Finset.mul_sum,show (∑p:Bool×ι,‖hadamardOnFst α p‖^2)=1 from ht,mul_one]

theorem actual_gadget_event_mass {α : QState (Bool×ι)} (hα : Normalized α) :
    (∑ p:Bool×ι, BornProb (gadgetOutput α) (p.1,(false,p.2)))=1/2 := by
  simp only [BornProb,gadgetOutput_branch]
  exact gadget_branch_mass hα

theorem actual_gadget_conditional_born {α : QState (Bool×ι)} (hα : Normalized α) (p : Bool×ι) :
    BornProb (gadgetOutput α) (p.1,(false,p.2)) /
      (∑q:Bool×ι,BornProb (gadgetOutput α) (q.1,(false,q.2))) =
        BornProb (hadamardOnFst α) p := by
  have ht:=hadamardOnFst_normalized hα
  have hz : (0:ℝ)<∑q,BornProb (hadamardOnFst α) q := by
    change 0<(∑q,‖hadamardOnFst α q‖^2);rw[ht];norm_num
  have he:=gadget_normalized_prob_eq α hz p
  unfold normProb at he
  simp only [BornProb,gadgetOutput_branch]
  simpa only [show (∑q,BornProb (hadamardOnFst α) q)=1 from ht,div_one] using! he
end Qatlib.Papers.QAOASupremacy16.LocalGadget
