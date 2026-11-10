/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ThermalDrift26.ThermalSampling.Intake.FiniteThermalLCU
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option warningAsError false
noncomputable section
namespace Qatlib.Papers.ThermalDrift26.ThermalSampling
open Qatlib Matrix Qatlib.Concepts.UniformBqp.FiniteGateWord.FiniteThermalCircuits
open scoped BigOperators

def thermalZeroUniformProjector (b : ℕ) : Matrix (Qatlib.Foundations.PureStateMath.Reg b × Fin 2) (Qatlib.Foundations.PureStateMath.Reg b × Fin 2) ℂ :=
  Matrix.diagonal (fun j => if j.1=Qatlib.Foundations.PureStateMath.ZeroStr b then 1 else 0)

def thermalAcceptedCorner (b : ℕ) (A : Matrix (Qatlib.Foundations.PureStateMath.Reg b × Fin 2) (Qatlib.Foundations.PureStateMath.Reg b × Fin 2) ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ := fun s t => A (Qatlib.Foundations.PureStateMath.ZeroStr b,s) (Qatlib.Foundations.PureStateMath.ZeroStr b,t)

theorem thermalZeroUniformProjector_idempotent (b : ℕ) :
    thermalZeroUniformProjector b*thermalZeroUniformProjector b=thermalZeroUniformProjector b := by
  rw [thermalZeroUniformProjector,Matrix.diagonal_mul_diagonal]
  congr 1
  funext j
  split_ifs <;> norm_num

theorem thermalAcceptedCorner_filter (b : ℕ) (A : Matrix (Qatlib.Foundations.PureStateMath.Reg b × Fin 2) (Qatlib.Foundations.PureStateMath.Reg b × Fin 2) ℂ) :
    thermalAcceptedCorner b (thermalZeroUniformProjector b*A*thermalZeroUniformProjector b)=
      thermalAcceptedCorner b A := by
  ext s t
  simp [thermalAcceptedCorner,thermalZeroUniformProjector,Matrix.diagonal_mul,Matrix.mul_diagonal]

theorem thermalAcceptedCorner_product (b : ℕ)
    (A B : Matrix (Qatlib.Foundations.PureStateMath.Reg b × Fin 2) (Qatlib.Foundations.PureStateMath.Reg b × Fin 2) ℂ) :
    thermalAcceptedCorner b (A*thermalZeroUniformProjector b*B)=
      thermalAcceptedCorner b A*thermalAcceptedCorner b B := by
  ext s t
  simp [thermalAcceptedCorner,thermalZeroUniformProjector,Matrix.mul_apply,
    Matrix.diagonal,Fintype.sum_prod_type,Finset.sum_add_distrib]

theorem thermalAcceptedCorner_adjoint (b : ℕ) (A : Matrix (Qatlib.Foundations.PureStateMath.Reg b × Fin 2) (Qatlib.Foundations.PureStateMath.Reg b × Fin 2) ℂ) :
    thermalAcceptedCorner b Aᴴ=(thermalAcceptedCorner b A)ᴴ := rfl

theorem thermalAcceptedCorner_add (b : ℕ)
    (A B : Matrix (Qatlib.Foundations.PureStateMath.Reg b × Fin 2) (Qatlib.Foundations.PureStateMath.Reg b × Fin 2) ℂ) :
    thermalAcceptedCorner b (A+B)=thermalAcceptedCorner b A+thermalAcceptedCorner b B := rfl

theorem thermalAcceptedCorner_sub (b : ℕ)
    (A B : Matrix (Qatlib.Foundations.PureStateMath.Reg b × Fin 2) (Qatlib.Foundations.PureStateMath.Reg b × Fin 2) ℂ) :
    thermalAcceptedCorner b (A-B)=thermalAcceptedCorner b A-thermalAcceptedCorner b B := rfl

theorem thermalAcceptedCorner_nsmul (b k : ℕ) (A : Matrix (Qatlib.Foundations.PureStateMath.Reg b × Fin 2) (Qatlib.Foundations.PureStateMath.Reg b × Fin 2) ℂ) :
    thermalAcceptedCorner b (k • A)=k • thermalAcceptedCorner b A := rfl

theorem thermalAcceptedOAA_corner (b : ℕ) (U : Matrix (Qatlib.Foundations.PureStateMath.Reg b × Fin 2) (Qatlib.Foundations.PureStateMath.Reg b × Fin 2) ℂ)
    (hU : U∈Matrix.unitaryGroup (Qatlib.Foundations.PureStateMath.Reg b × Fin 2) ℂ) :
    thermalAcceptedCorner b (-(U*(1-2*thermalZeroUniformProjector b)*Uᴴ*
        (1-2*thermalZeroUniformProjector b)*U))=
      (3:ℕ) • thermalAcceptedCorner b U-(4:ℕ) •
        (thermalAcceptedCorner b U*(thermalAcceptedCorner b U)ᴴ*thermalAcceptedCorner b U) := by
  have hUV : U*Uᴴ=1 := by
    simpa only [Matrix.star_eq_conjTranspose] using! Matrix.mem_unitaryGroup_iff.mp hU
  have hVU : Uᴴ*U=1 := by
    simpa only [Matrix.star_eq_conjTranspose] using! Matrix.mem_unitaryGroup_iff'.mp hU
  have h := congrArg (thermalAcceptedCorner b)
    (thermalOAA_polynomial U Uᴴ (thermalZeroUniformProjector b) hUV hVU
      (thermalZeroUniformProjector_idempotent b))
  have ht : thermalZeroUniformProjector b*U*thermalZeroUniformProjector b*Uᴴ*
      thermalZeroUniformProjector b*U*thermalZeroUniformProjector b=
      thermalZeroUniformProjector b*(U*thermalZeroUniformProjector b*Uᴴ*
        thermalZeroUniformProjector b*U)*thermalZeroUniformProjector b := by
    simp only [Matrix.mul_assoc]
  rw [ht] at h
  have h3 (A : Matrix (Qatlib.Foundations.PureStateMath.Reg b × Fin 2) (Qatlib.Foundations.PureStateMath.Reg b × Fin 2) ℂ) :
      (3:Matrix (Qatlib.Foundations.PureStateMath.Reg b × Fin 2) (Qatlib.Foundations.PureStateMath.Reg b × Fin 2) ℂ)*A=(3:ℕ) • A := by
    simp only [nsmul_eq_mul,Nat.cast_ofNat]
  have h4 (A : Matrix (Qatlib.Foundations.PureStateMath.Reg b × Fin 2) (Qatlib.Foundations.PureStateMath.Reg b × Fin 2) ℂ) :
      (4:Matrix (Qatlib.Foundations.PureStateMath.Reg b × Fin 2) (Qatlib.Foundations.PureStateMath.Reg b × Fin 2) ℂ)*A=(4:ℕ) • A := by
    simp only [nsmul_eq_mul,Nat.cast_ofNat]
  rw [h3,h4] at h
  simp only [thermalAcceptedCorner_sub,thermalAcceptedCorner_nsmul,
    thermalAcceptedCorner_filter,thermalAcceptedCorner_product,thermalAcceptedCorner_adjoint] at h
  exact h

theorem thermalUniformBranch_sum (b w0 w1 pad : ℕ) (htotal : w0+w1+pad+pad=2^b) :
    (∑ u : Qatlib.Foundations.PureStateMath.Reg b,thermalUniformBranch b w0 (w0+w1) (w0+w1+pad) (2^b) u)=
      (w0:ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)+(w1:ℂ) • thermalQuarterTurn := by
  have hy := thermalUniformBits_interval_sum b w0 (w0+w1) (by omega) (by omega)
  have hz := thermalUniformBits_interval_sum b (w0+w1+pad) (2^b) (by omega) (by rfl)
  have hzlen : 2^b-(w0+w1+pad)=pad := by omega
  simp only [Nat.add_sub_cancel_left,hzlen] at hy hz
  have hbranch (u : Qatlib.Foundations.PureStateMath.Reg b) (s t : Fin 2) :
      thermalUniformBranch b w0 (w0+w1) (w0+w1+pad) (2^b) u s t=
      (1 : Matrix (Fin 2) (Fin 2) ℂ) s t+
        (if w0≤thermalBitValue (List.ofFn u) ∧ thermalBitValue (List.ofFn u)<w0+w1
          then (1:ℂ) else 0)*(thermalQuarterTurn s t-(1 : Matrix (Fin 2) (Fin 2) ℂ) s t)-
        2*(if w0+w1+pad≤thermalBitValue (List.ofFn u) ∧ thermalBitValue (List.ofFn u)<2^b
          then (1:ℂ) else 0)*(1 : Matrix (Fin 2) (Fin 2) ℂ) s t := by
    by_cases hY : w0≤thermalBitValue (List.ofFn u) ∧ thermalBitValue (List.ofFn u)<w0+w1
    · have hZ : ¬(w0+w1+pad≤thermalBitValue (List.ofFn u) ∧ thermalBitValue (List.ofFn u)<2^b) := by omega
      simp [thermalUniformBranch,hY,hZ]
    · by_cases hZ : w0+w1+pad≤thermalBitValue (List.ofFn u) ∧ thermalBitValue (List.ofFn u)<2^b
      all_goals simp [thermalUniformBranch,hY,hZ] <;> ring
  ext s t
  rw [Matrix.sum_apply]
  simp_rw [hbranch]
  rw [Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.sum_mul,← Finset.sum_mul,
    ← Finset.mul_sum,hy,hz]
  have hcard : Fintype.card (Qatlib.Foundations.PureStateMath.Reg b)=2^b := by
    simp [Qatlib.Foundations.PureStateMath.Reg]
  simp only [Finset.sum_const,Finset.card_univ,hcard,nsmul_eq_mul,Matrix.add_apply,
    Matrix.smul_apply,smul_eq_mul]
  have he : ((2^b:ℕ):ℂ)=(w0:ℂ)+w1+pad+pad := by exact_mod_cast htotal.symm
  rw [he]
  ring

theorem thermalUniformLCU_accepted (b w0 w1 pad : ℕ) (htotal : w0+w1+pad+pad=2^b) :
    thermalAcceptedCorner b (thermalUniformLCU b w0 (w0+w1) (w0+w1+pad) (2^b))=
      ((w0:ℂ)/(2^b:ℕ)) • (1 : Matrix (Fin 2) (Fin 2) ℂ)+
      ((w1:ℂ)/(2^b:ℕ)) • thermalQuarterTurn := by
  have hcard : Fintype.card (Qatlib.Foundations.PureStateMath.Reg b)=2^b := by
    simp [Qatlib.Foundations.PureStateMath.Reg]
  have hw : (∑ u : Qatlib.Foundations.PureStateMath.Reg b,thermalUniformWeight b u •
      thermalUniformBranch b w0 (w0+w1) (w0+w1+pad) (2^b) u)=
      ((w0:ℂ)/(2^b:ℕ)) • (1 : Matrix (Fin 2) (Fin 2) ℂ)+
        ((w1:ℂ)/(2^b:ℕ)) • thermalQuarterTurn := by
    simp only [thermalUniformWeight,← Finset.smul_sum,hcard]
    rw [thermalUniformBranch_sum b w0 w1 pad htotal]
    ext s t
    simp [Matrix.smul_apply,smul_eq_mul,Complex.real_smul,div_eq_mul_inv]
    ring
  ext s t
  have h := congrFun (thermalUniformLCU_corner b w0 (w0+w1) (w0+w1+pad) (2^b)
    (Qatlib.Foundations.PureStateMath.Ket t)) s
  rw [hw,Qatlib.Concepts.BlockEncoding.LinearCombination.mulVec_ket_apply] at h
  have ht : Qatlib.Foundations.PureStateMath.TensorState (Qatlib.Foundations.PureStateMath.Ket (Qatlib.Foundations.PureStateMath.ZeroStr b)) (Qatlib.Foundations.PureStateMath.Ket t)=
      Qatlib.Foundations.PureStateMath.Ket (Qatlib.Foundations.PureStateMath.ZeroStr b,t) := by
    funext p
    by_cases h1 : p.1=Qatlib.Foundations.PureStateMath.ZeroStr b <;> by_cases h2 : p.2=t
    all_goals simp [Qatlib.Foundations.PureStateMath.TensorState,Qatlib.Foundations.PureStateMath.Ket,Prod.ext_iff,h1,h2]
  rw [ht,Qatlib.Concepts.BlockEncoding.LinearCombination.mulVec_ket_apply] at h
  exact h

def thermalScaledRotation (c s : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (c:ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)+(s:ℂ) • thermalQuarterTurn

theorem thermalScaledRotation_amplify (c s : ℝ) :
    let A := (1/2:ℂ) • thermalScaledRotation c s
    (3:ℕ) • A-(4:ℕ) • (A*Aᴴ*A)=(((3-(c^2+s^2))/2:ℝ):ℂ) • thermalScaledRotation c s := by
  dsimp
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [thermalScaledRotation,thermalQuarterTurn,Matrix.mul_apply,Fin.sum_univ_two,
      Matrix.conjTranspose_apply,Matrix.one_apply,Matrix.ofNat_apply,Complex.ofReal_div,Complex.ofReal_sub,
      Complex.ofReal_add,Complex.ofReal_pow] <;> ring

def thermalUniformReflection (b : ℕ) : Matrix (Qatlib.Foundations.PureStateMath.Reg b × Fin 2) (Qatlib.Foundations.PureStateMath.Reg b × Fin 2) ℂ :=
  1-2*thermalZeroUniformProjector b

theorem thermalUniformReflection_basis (b : ℕ) (j : Qatlib.Foundations.PureStateMath.Reg b × Fin 2) :
    thermalUniformReflection b *ᵥ Qatlib.Foundations.PureStateMath.Ket j=
      (if j.1=Qatlib.Foundations.PureStateMath.ZeroStr b then (-1:ℂ) else 1) • Qatlib.Foundations.PureStateMath.Ket j := by
  funext i
  rw [Qatlib.Concepts.BlockEncoding.LinearCombination.mulVec_ket_apply]
  by_cases hij : i=j
  · subst i
    by_cases hj : j.1=Qatlib.Foundations.PureStateMath.ZeroStr b
    all_goals simp [thermalUniformReflection,thermalZeroUniformProjector,two_mul,hj,
      Qatlib.Foundations.PureStateMath.Ket]
  · simp [thermalUniformReflection,thermalZeroUniformProjector,two_mul,hij,
      Qatlib.Foundations.PureStateMath.Ket,Matrix.diagonal]

def thermalCanonicalReflectionWord (b w : ℕ) : List Qatlib.Concepts.GateVocabulary.FiniteGateDescription.FiniteGateCode :=
  thermalZeroReflection (thermalUniformWires b w) (thermalFlagWire b w) (thermalScratchWires b w)

theorem thermalCanonicalReflection_intertwine (b w : ℕ) (hcap : b≤w+2) :
    Qatlib.Concepts.UniformBqp.FiniteGateWord.finiteCodeWordMatrix ((b+1)+(w+1)) (thermalCanonicalReflectionWord b w)*
      thermalWorkspaceEmbed b w=thermalWorkspaceEmbed b w*thermalUniformReflection b := by
  apply thermalMatrix_intertwine_of_basis
  intro j
  rw [thermalWorkspaceEmbed_basis,thermalUniformReflection_basis,Matrix.mulVec_smul,
    thermalWorkspaceEmbed_basis]
  have hc : ∀ k∈thermalScratchWires b w,thermalEncoded b w j k=false := by
    intro k hk
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hk
    exact thermalEncoded_work b w j i.succ
  have hf : thermalEncoded b w j (thermalFlagWire b w)=false :=
    thermalEncoded_work b w j 0
  have hm : thermalMatch (thermalUniformWires b w) (thermalUniformWires b w)
      (thermalEncoded b w j)=true ↔ j.1=Qatlib.Foundations.PureStateMath.ZeroStr b := by
    rw [thermalZero_match_iff]
    constructor
    · intro h
      funext i
      exact (thermalEncoded_uniform b w j i).symm.trans
        (h (thermalUniformWire b w i) (thermalUniformWire_mem b w i))
    · intro h k hk
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hk
      rw [thermalEncoded_uniform,h]
      rfl
  have hr := thermalZeroReflection_basis (thermalUniformWires b w) (thermalFlagWire b w)
    (thermalScratchWires b w) (thermalCanonical_layout b w)
    (by simpa [thermalUniformWires,thermalScratchWires] using! hcap)
    (thermalEncoded b w j) hc hf
  simp only [hm] at hr
  simpa only [Qatlib.Concepts.UniformBqp.FiniteGateWord.finite_phase_word_run,Qatlib.Foundations.PureStateMath.ApplyGate,thermalCanonicalReflectionWord,
    thermalEncoded] using! hr

theorem thermalGlobalMinus_matrix {n : ℕ} (signal : Fin n) :
    Qatlib.Concepts.UniformBqp.FiniteGateWord.finiteCodeWordMatrix n (thermalGlobalMinusWord signal)= -1 := by
  ext i j
  have h := congrFun (thermalGlobalMinus_basis signal j) i
  simpa only [Qatlib.Concepts.UniformBqp.FiniteGateWord.finite_phase_word_run,Qatlib.Foundations.PureStateMath.ApplyGate,Qatlib.Concepts.BlockEncoding.LinearCombination.mulVec_ket_apply,Pi.smul_apply,smul_eq_mul,
    Matrix.neg_apply,Matrix.one_apply,Qatlib.Foundations.PureStateMath.Ket,neg_one_mul] using! h

def thermalActualOAAWord (b w w0 w1 pad : ℕ) : List Qatlib.Concepts.GateVocabulary.FiniteGateDescription.FiniteGateCode :=
  let u := thermalNativeLCUSteps b w w0 w1 pad
  thermalNativeProgram u ++ thermalCanonicalReflectionWord b w ++
    thermalNativeProgram (thermalNativeInverse (thermalNativeExpandCCX u)) ++
    thermalCanonicalReflectionWord b w ++ thermalNativeProgram u ++
    thermalGlobalMinusWord (thermalSignalWire b w)

theorem thermalActualOAA_intertwine (b w w0 w1 pad : ℕ) (hcap : b≤w+2)
    (htotal : w0+w1+pad+pad=2^b) :
    Qatlib.Concepts.UniformBqp.FiniteGateWord.finiteCodeWordMatrix ((b+1)+(w+1)) (thermalActualOAAWord b w w0 w1 pad)*
      thermalWorkspaceEmbed b w=thermalWorkspaceEmbed b w*
      (-(thermalUniformLCU b w0 (w0+w1) (w0+w1+pad) (2^b)*thermalUniformReflection b*
        (thermalUniformLCU b w0 (w0+w1) (w0+w1+pad) (2^b))ᴴ*thermalUniformReflection b*
          thermalUniformLCU b w0 (w0+w1) (w0+w1+pad) (2^b))) := by
  have hu := thermalNativeLCU_intertwine b w w0 w1 pad hcap htotal
  have hv := thermalNativeLCU_inverse_intertwine b w w0 w1 pad hcap htotal
  have hr := thermalCanonicalReflection_intertwine b w hcap
  have h1 := thermalIntertwine_mul _ _ _ _ _ hr hu
  have h2 := thermalIntertwine_mul _ _ _ _ _ hv h1
  have h3 := thermalIntertwine_mul _ _ _ _ _ hr h2
  have h4 := thermalIntertwine_mul _ _ _ _ _ hu h3
  have hm : Qatlib.Concepts.UniformBqp.FiniteGateWord.finiteCodeWordMatrix ((b+1)+(w+1))
      (thermalGlobalMinusWord (thermalSignalWire b w))*thermalWorkspaceEmbed b w=
      thermalWorkspaceEmbed b w*(-1 : Matrix (Qatlib.Foundations.PureStateMath.Reg b × Fin 2) (Qatlib.Foundations.PureStateMath.Reg b × Fin 2) ℂ) := by
    rw [thermalGlobalMinus_matrix]
    simp
  have h5 := thermalIntertwine_mul _ _ _ _ _ hm h4
  simp only [thermalActualOAAWord,thermalWordMatrix_append]
  convert! h5 using 1
  simp only [Matrix.mul_assoc,neg_mul,one_mul]

theorem thermalEncoded_target (b w : ℕ) (s : Fin 2) :
    thermalEncoded b w (Qatlib.Foundations.PureStateMath.ZeroStr b,s)=
      (rotationRegisterEquiv ((b+1)+w)).symm (s,fun _ => false) := by
  apply (thermalWorkspaceEquiv b w).injective
  rw [thermalEncoded_equiv]
  apply Prod.ext
  · apply Prod.ext
    · funext i
      change false=(Fin.cons (Qatlib.Foundations.PureStateMath.boolEquivFin2.symm s) (fun _ : Fin ((b+1)+w) => false) : Qatlib.Foundations.PureStateMath.Reg (((b+1)+w)+1))
        (Fin.castAdd (w+1) i.succ)
      rfl
    · change s=Qatlib.Foundations.PureStateMath.boolEquivFin2 ((Fin.cons (Qatlib.Foundations.PureStateMath.boolEquivFin2.symm s) (fun _ : Fin ((b+1)+w) => false) : Qatlib.Foundations.PureStateMath.Reg (((b+1)+w)+1)) 0)
      simp
  · funext k
    change false=(Fin.cons (Qatlib.Foundations.PureStateMath.boolEquivFin2.symm s) (fun _ : Fin ((b+1)+w) => false) : Qatlib.Foundations.PureStateMath.Reg (((b+1)+w)+1)) (Fin.natAdd (b+1) k)
    have he : Fin.natAdd (b+1) k=(⟨b+k.val,by omega⟩ : Fin ((b+1)+w)).succ := by
      apply Fin.ext
      simp
      omega
    rw [he,Fin.cons_succ]

theorem thermalEncoded_zero (b w : ℕ) :
    thermalEncoded b w (Qatlib.Foundations.PureStateMath.ZeroStr b,0)=(fun _ => false) := by
  rw [thermalEncoded_target]
  funext i
  refine Fin.cases ?_ (fun k => ?_) i
  · rfl
  · rfl

theorem thermalActualOAA_legal (b w w0 w1 pad : ℕ) (hcap : b≤w+2)
    (htotal : w0+w1+pad+pad=2^b) :
    Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordLegal (((b+1)+w)+1) (thermalActualOAAWord b w w0 w1 pad)=true := by
  have hu := thermalNativeLCU_legal b w w0 w1 pad hcap htotal
  have hu' := thermalNative_program_legal _ hu
  have hv := thermalNative_program_legal _
    (thermalNative_inverse_legal _ (thermalNative_expand_legal _ hu))
  have hr := thermalZeroReflection_legal (thermalUniformWires b w) (thermalFlagWire b w)
    (thermalScratchWires b w) (thermalCanonical_layout b w)
    (by simpa [thermalUniformWires,thermalScratchWires] using! hcap)
  have hm := thermalNative_program_legal _ (thermalGlobalMinus_legal (thermalSignalWire b w))
  simpa only [thermalActualOAAWord,Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordLegal,List.all_append,Bool.and_eq_true,
    thermalCanonicalReflectionWord,thermalGlobalMinusWord] using!
    And.intro (And.intro (And.intro (And.intro (And.intro hu' hr) hv) hr) hu') hm

def thermalDyadicCoefficient (b weight : ℕ) : ℝ := 2*(weight:ℝ)/(2^b:ℕ)

theorem thermalUniformLCU_accepted_scaled (b w0 w1 pad : ℕ) (htotal : w0+w1+pad+pad=2^b) :
    thermalAcceptedCorner b (thermalUniformLCU b w0 (w0+w1) (w0+w1+pad) (2^b))=
      (1/2:ℂ) • thermalScaledRotation (thermalDyadicCoefficient b w0) (thermalDyadicCoefficient b w1) := by
  rw [thermalUniformLCU_accepted b w0 w1 pad htotal]
  ext i j
  simp [thermalScaledRotation,thermalDyadicCoefficient,Matrix.smul_apply,smul_eq_mul,div_eq_mul_inv]
  ring

theorem thermalEffectiveOAA_accepted (b w0 w1 pad : ℕ) (htotal : w0+w1+pad+pad=2^b) :
    let U := thermalUniformLCU b w0 (w0+w1) (w0+w1+pad) (2^b)
    let c := thermalDyadicCoefficient b w0
    let s := thermalDyadicCoefficient b w1
    thermalAcceptedCorner b (-(U*thermalUniformReflection b*Uᴴ*thermalUniformReflection b*U))=
      (((3-(c^2+s^2))/2:ℝ):ℂ) • thermalScaledRotation c s := by
  (try dsimp only)
  rw [thermalUniformReflection,thermalAcceptedOAA_corner b _ (thermalUniformLCU_unitary _ _ _ _ _),
    thermalUniformLCU_accepted_scaled b w0 w1 pad htotal]
  exact thermalScaledRotation_amplify _ _

theorem thermalActualOAA_split_corner (b w w0 w1 pad : ℕ) (hcap : b≤w+2)
    (htotal : w0+w1+pad+pad=2^b) (s : Fin 2) :
    splitWordState ((b+1)+w) (thermalActualOAAWord b w w0 w1 pad) (s,fun _ => false)=
      thermalAcceptedCorner b
        (-(thermalUniformLCU b w0 (w0+w1) (w0+w1+pad) (2^b)*thermalUniformReflection b*
          (thermalUniformLCU b w0 (w0+w1) (w0+w1+pad) (2^b))ᴴ*thermalUniformReflection b*
            thermalUniformLCU b w0 (w0+w1) (w0+w1+pad) (2^b))) s 0 := by
  have h := congrFun (congrFun (thermalActualOAA_intertwine b w w0 w1 pad hcap htotal)
    (thermalEncoded b w (Qatlib.Foundations.PureStateMath.ZeroStr b,s))) (Qatlib.Foundations.PureStateMath.ZeroStr b,0)
  rw [thermalWorkspaceEmbed_left,thermalWorkspaceEmbed_right,thermalEncoded_equiv,if_pos rfl] at h
  change Qatlib.Concepts.UniformBqp.FiniteGateWord.finiteCodeWordMatrix _ _ (thermalEncoded b w (Qatlib.Foundations.PureStateMath.ZeroStr b,s))
    (thermalEncoded b w (Qatlib.Foundations.PureStateMath.ZeroStr b,0))=_ at h
  rw [thermalEncoded_target,thermalEncoded_zero] at h
  simpa only [splitWordState,Qatlib.Concepts.UniformBqp.FiniteGateWord.finite_phase_word_run,Qatlib.Foundations.PureStateMath.ApplyGate,Qatlib.Concepts.BlockEncoding.LinearCombination.mulVec_ket_apply,
    thermalAcceptedCorner] using! h

theorem thermalActualOAA_coefficients (b w w0 w1 pad : ℕ) (hcap : b≤w+2)
    (htotal : w0+w1+pad+pad=2^b) :
    let c := thermalDyadicCoefficient b w0
    let s := thermalDyadicCoefficient b w1
    let gamma := (3-(c^2+s^2))/2
    splitWordState ((b+1)+w) (thermalActualOAAWord b w w0 w1 pad) (0,fun _ => false)=(gamma*c:ℝ) ∧
    splitWordState ((b+1)+w) (thermalActualOAAWord b w w0 w1 pad) (1,fun _ => false)=(gamma*s:ℝ) := by
  have h0 := thermalActualOAA_split_corner b w w0 w1 pad hcap htotal 0
  have h1 := thermalActualOAA_split_corner b w w0 w1 pad hcap htotal 1
  rw [thermalEffectiveOAA_accepted b w0 w1 pad htotal] at h0 h1
  (try dsimp only)
  constructor
  · simpa [thermalScaledRotation,thermalQuarterTurn,Matrix.smul_apply,smul_eq_mul] using! h0
  · simpa [thermalScaledRotation,thermalQuarterTurn,Matrix.smul_apply,smul_eq_mul] using! h1

theorem thermalActualOAA_hclean (b w w0 w1 pad : ℕ) (hcap : b≤w+2)
    (htotal : w0+w1+pad+pad=2^b) (a e epsilon : ℝ) (ha : 0≤a)
    (hc : 0≤directCos a-thermalDyadicCoefficient b w0)
    (hs : 0≤directSin a-thermalDyadicCoefficient b w1)
    (hcE : directCos a-thermalDyadicCoefficient b w0≤e)
    (hsE : directSin a-thermalDyadicCoefficient b w1≤e) (heps : 6*e^2≤epsilon^2) :
    cleanWordErrorSq ((b+1)+w) (thermalActualOAAWord b w w0 w1 pad) a≤epsilon^2 := by
  have h := thermalActualOAA_coefficients b w w0 w1 pad hcap htotal
  exact thermalWord_hclean_of_coefficients _ _ (thermalActualOAA_legal b w w0 w1 pad hcap htotal)
    a _ _ e epsilon ha hc hs hcE hsE h.1 h.2 heps

theorem thermalActualOAA_source_cq {L d : ℕ} (F : ReflectionFamily L d)
    (p q : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Fin L)) (rho : Qatlib.Foundations.PureStateMath.DensityOperator d)
    (b w w0 w1 pad : ℕ) (hcap : b≤w+2) (htotal : w0+w1+pad+pad=2^b)
    (a e epsilon delta : ℝ) (ha : 0≤a)
    (hc : 0≤directCos a-thermalDyadicCoefficient b w0)
    (hs : 0≤directSin a-thermalDyadicCoefficient b w1)
    (hcE : directCos a-thermalDyadicCoefficient b w0≤e)
    (hsE : directSin a-thermalDyadicCoefficient b w1≤e) (heps : 6*e^2≤epsilon^2)
    (heps0 : 0≤epsilon) (hindex : (1/2:ℝ)*(∑ j : Fin L,|q.prob j-p.prob j|)≤delta) :
    (1/2:ℝ)*Matrix.traceNorm
      (jointPreparedReadout F q rho
        (wordPreparationState ((b+1)+w) (thermalActualOAAWord b w w0 w1 pad)
          (thermalActualOAA_legal b w w0 w1 pad hcap htotal)).val-
        idealJointReadoutMatrix F p a rho)≤epsilon+delta :=
  finiteWord_source_cq_budget F p q rho _ _ (thermalActualOAA_legal b w w0 w1 pad hcap htotal)
    a epsilon delta heps0 (thermalActualOAA_hclean b w w0 w1 pad hcap htotal a e epsilon
      ha hc hs hcE hsE heps) hindex

theorem thermalCanonicalReflection_cost (b w : ℕ) (hcap : b≤w+2) :
    Qatlib.Foundations.QueryWordCore.Circuit.GateCount (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit ((b+1)+(w+1)) (thermalCanonicalReflectionWord b w))≤64*b+6 := by
  have h := (thermalZeroReflection_cost (thermalUniformWires b w) (thermalFlagWire b w)
    (thermalScratchWires b w) (by simpa [thermalUniformWires,thermalScratchWires] using! hcap)).1
  simp only [thermalUniformWires,List.length_ofFn] at h
  change Qatlib.Foundations.QueryWordCore.Circuit.GateCount (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit ((b+1)+(w+1)) (thermalCanonicalReflectionWord b w))=
    2*(2*b+(if b≤1 then 1 else 15*(2*b-3)))+4 at h
  rw [h]
  split_ifs <;> omega

theorem thermalActualOAA_cost (b w w0 w1 pad : ℕ) (hcap : b≤w+2)
    (htotal : w0+w1+pad+pad=2^b) :
    Qatlib.Foundations.QueryWordCore.Circuit.GateCount (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit (((b+1)+w)+1) (thermalActualOAAWord b w w0 w1 pad))≤
      1536*b^2+134*b+103 ∧
    Qatlib.Foundations.QueryWordCore.Circuit.QueryCount (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit (((b+1)+w)+1) (thermalActualOAAWord b w w0 w1 pad))=0 := by
  constructor
  · have hu := (thermalNativeLCU_cost b w w0 w1 pad hcap htotal).1
    have hv := (thermalNativeLCU_inverse_cost b w w0 w1 pad).1
    have hr := thermalCanonicalReflection_cost b w hcap
    have hm := (thermalGlobalMinus_cost (thermalSignalWire b w)).2.1
    rw [(Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit_counts _ _).2] at hu hv hr hm ⊢
    rw [(Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit_counts _ _).2] at hv
    simp only [thermalActualOAAWord,List.length_append]
    omega
  · exact (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit_counts _ _).1

end Qatlib.Papers.ThermalDrift26.ThermalSampling
