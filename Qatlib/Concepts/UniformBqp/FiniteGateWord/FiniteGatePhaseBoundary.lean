/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GateVocabulary.FiniteGateDescription
import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge
import Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

namespace Qatlib.Concepts.UniformBqp.FiniteGateWord
open Matrix

def finiteCodeWordMatrix (n : ℕ) (gs : List FiniteGateCode) : Matrix (Reg n) (Reg n) ℂ :=
  gs.foldl (fun A g => finiteCodeMatrix n g*A) 1

def finiteGaussianScalar : ℂ := (3+4*Complex.I)/5

def finiteGaussianScalarGate : Matrix (Reg 1) (Reg 1) ℂ :=
  finiteGaussianScalar • 1

open scoped Classical Matrix.Norms.L2Operator BigOperators
set_option maxHeartbeats 800000

theorem finite_phase_wire_pow (n : ℕ) (w : Fin n) (U : Matrix Bool Bool ℂ) (k : ℕ) :
    (wireGate n w U)^k=wireGate n w (U^k) := by
  induction k with
  | zero => simp only [pow_zero,wireGate_one]
  | succ k ih => rw [pow_succ,ih,wireGate_mul,← pow_succ]

theorem finite_phase_involution_eighth {H : Type} [Fintype H] [DecidableEq H]
    (U : Matrix H H ℂ) (hU : U*U=1) : U^8=1 := by
  have h2 : U^2=1 := by simpa only [pow_two] using hU
  rw [show (8:ℕ)=2*4 by decide,pow_mul,h2,one_pow]

theorem finite_phase_rz_eighth (θ : ℝ)
    (he : Complex.exp ((8:ℂ)*((θ:ℂ)*Complex.I))=1) : (Rz θ)^8=1 := by
  unfold Rz
  rw [Matrix.diagonal_pow,← Matrix.diagonal_one]
  congr 1
  funext b
  cases b
  · simp
  · change Complex.exp ((θ:ℂ)*Complex.I)^8=1
    rw [← Complex.exp_nat_mul]
    exact he

theorem finite_phase_t_eighth : tGate^8=1 ∧ tGateAdj^8=1 := by
  constructor
  · apply finite_phase_rz_eighth
    rw [show (8:ℂ)*(((Real.pi/4:ℝ):ℂ)*Complex.I)=2*Real.pi*Complex.I by push_cast;ring]
    exact Complex.exp_two_pi_mul_I
  · apply finite_phase_rz_eighth
    rw [show (8:ℂ)*(((-(Real.pi/4):ℝ):ℂ)*Complex.I)=-(2*Real.pi*Complex.I) by push_cast;ring,
      Complex.exp_neg,Complex.exp_two_pi_mul_I,inv_one]

theorem finite_phase_generator_eighth (n : ℕ) (g : FiniteGateCode) (hg : finiteCodeLegal n g=true) :
    (finiteCodeMatrix n g)^8=1 := by
  cases g with
  | h w =>
    have hw : w<n := by simpa only [finiteCodeLegal,decide_eq_true_eq] using hg
    simp only [finiteCodeMatrix,dif_pos hw,finite_phase_wire_pow]
    rw [finite_phase_involution_eighth Hadamard hadamard_mul_self,wireGate_one]
  | x w =>
    have hw : w<n := by simpa only [finiteCodeLegal,decide_eq_true_eq] using hg
    simp only [finiteCodeMatrix,dif_pos hw,finite_phase_wire_pow]
    have hx : PauliX*PauliX=1 := permMatrix_mul_self (fun b : Bool => by cases b <;> rfl)
    rw [finite_phase_involution_eighth PauliX hx,wireGate_one]
  | t w =>
    have hw : w<n := by simpa only [finiteCodeLegal,decide_eq_true_eq] using hg
    simp only [finiteCodeMatrix,dif_pos hw,finite_phase_wire_pow]
    rw [finite_phase_t_eighth.1,wireGate_one]
  | tdg w =>
    have hw : w<n := by simpa only [finiteCodeLegal,decide_eq_true_eq] using hg
    simp only [finiteCodeMatrix,dif_pos hw,finite_phase_wire_pow]
    rw [finite_phase_t_eighth.2,wireGate_one]
  | cx c t =>
    have hw : c<n ∧ t<n ∧ c≠t := by simpa only [finiteCodeLegal,decide_eq_true_eq] using hg
    have hct : (⟨c,hw.1⟩:Fin n)≠⟨t,hw.2.1⟩ := fun h => hw.2.2 (congrArg Fin.val h)
    simp only [finiteCodeMatrix,dif_pos hw]
    apply finite_phase_involution_eighth
    exact permMatrix_mul_self (cnotUpdate_involutive n _ _ hct)

theorem finite_phase_generator_det (n : ℕ) (g : FiniteGateCode) (hg : finiteCodeLegal n g=true) :
    (Matrix.det (finiteCodeMatrix n g))^8=1 := by
  rw [← Matrix.det_pow,finite_phase_generator_eighth n g hg,Matrix.det_one]

theorem finite_phase_fold_acc (n : ℕ) (gs : List FiniteGateCode) (A : Matrix (Reg n) (Reg n) ℂ) :
    gs.foldl (fun M g => finiteCodeMatrix n g*M) A=finiteCodeWordMatrix n gs*A := by
  induction gs generalizing A with
  | nil => simp [finiteCodeWordMatrix]
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih]
    change _=(gs.foldl (fun M g => finiteCodeMatrix n g*M) (finiteCodeMatrix n g*1))*A
    rw [ih,Matrix.mul_one,Matrix.mul_assoc]

theorem finite_phase_word_cons (n : ℕ) (g : FiniteGateCode) (gs : List FiniteGateCode) :
    finiteCodeWordMatrix n (g::gs)=finiteCodeWordMatrix n gs*finiteCodeMatrix n g := by
  unfold finiteCodeWordMatrix
  rw [List.foldl_cons,Matrix.mul_one,finite_phase_fold_acc]
  rfl

theorem finite_phase_word_run (n : ℕ) (gs : List FiniteGateCode) (ψ : QState (Reg n)) :
    Run (1 : Matrix (Reg n) (Reg n) ℂ) (finiteCodeCircuit n gs) ψ=
      ApplyGate (finiteCodeWordMatrix n gs) ψ := by
  induction gs generalizing ψ with
  | nil => simp [finiteCodeCircuit,finiteCodeWordMatrix,applyGate_one]
  | cons g gs ih =>
    simp only [finiteCodeCircuit,List.map_cons,Run]
    rw [show gs.map (fun g => Step.gate (finiteCodeMatrix n g))=finiteCodeCircuit n gs from rfl,
      ih,finite_phase_word_cons,applyGate_mul]

theorem finite_code_word_determinant_invariant :
    ∀ (n : ℕ) (gs : List FiniteGateCode), finiteWordLegal n gs=true →
      finiteCodeWordMatrix n gs ∈ Matrix.unitaryGroup (Reg n) ℂ ∧
      (Matrix.det (finiteCodeWordMatrix n gs))^8=1 ∧
      QueryCount (finiteCodeCircuit n gs)=0 ∧ GateCount (finiteCodeCircuit n gs)=gs.length ∧
      ∀ ψ : QState (Reg n), Run (1 : Matrix (Reg n) (Reg n) ℂ) (finiteCodeCircuit n gs) ψ=
        ApplyGate (finiteCodeWordMatrix n gs) ψ := by
  intro n gs hg
  have hu : finiteCodeWordMatrix n gs ∈ Matrix.unitaryGroup (Reg n) ℂ ∧
      (Matrix.det (finiteCodeWordMatrix n gs))^8=1 := by
    induction gs with
    | nil => simp [finiteCodeWordMatrix]
    | cons g gs ih =>
      have hh : finiteCodeLegal n g=true ∧ finiteWordLegal n gs=true := by
        simpa only [finiteWordLegal,List.all_cons,Bool.and_eq_true] using hg
      have ht := ih hh.2
      rw [finite_phase_word_cons]
      exact ⟨(Matrix.unitaryGroup (Reg n) ℂ).mul_mem ht.1 (finiteCodeMatrix_unitary n g hh.1),by
        rw [Matrix.det_mul,mul_pow,ht.2,finite_phase_generator_det n g hh.1,mul_one]⟩
  exact ⟨hu.1,hu.2,(finiteCodeCircuit_counts n gs).1,(finiteCodeCircuit_counts n gs).2,
    finite_phase_word_run n gs⟩

theorem finite_phase_gaussian_norm : ‖finiteGaussianScalar‖=1 := by
  have h25 : Real.sqrt 25 = 5 := by
    rw [show (25 : ℝ) = 5 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  norm_num [finiteGaussianScalar,Complex.norm_def,Complex.normSq_apply,h25]

theorem finite_phase_gaussian_unitary : finiteGaussianScalarGate ∈ Matrix.unitaryGroup (Reg 1) ℂ := by
  have hc : star finiteGaussianScalar*finiteGaussianScalar=1 := by
    rw [RCLike.star_def,← Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq,
      finite_phase_gaussian_norm,one_pow]
    rfl
  rw [Matrix.mem_unitaryGroup_iff',Matrix.star_eq_conjTranspose,finiteGaussianScalarGate,
    Matrix.conjTranspose_smul,Matrix.conjTranspose_one,smul_mul_assoc,mul_smul_comm,
    Matrix.one_mul,smul_smul,hc,one_smul]

theorem finite_phase_gaussian_sixteen :
    (finiteGaussianScalar^16).re= -98248054847/152587890625 := by
  norm_num [finiteGaussianScalar,pow_succ,Complex.mul_re,Complex.mul_im,Complex.div_re,Complex.div_im]

theorem finite_phase_gaussian_power_gap : 1 ≤ ‖(1:ℂ)-finiteGaussianScalar^16‖ := by
  have hr : (finiteGaussianScalar^16).re ≤ 0 := by rw [finite_phase_gaussian_sixteen];norm_num
  have he : 1 ≤ ((1:ℂ)-finiteGaussianScalar^16).re := by
    simp only [Complex.sub_re,Complex.one_re];linarith
  exact he.trans (Complex.re_le_norm _)

theorem finite_phase_power_difference (a b : ℂ) (ha : ‖a‖=1) (hb : ‖b‖=1) (k : ℕ) :
    ‖a^k-b^k‖ ≤ (k:ℝ)*‖a-b‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have he : a^(k+1)-b^(k+1)=a^k*(a-b)+(a^k-b^k)*b := by rw [pow_succ,pow_succ];ring
    rw [he]
    have hn := norm_add_le (a^k*(a-b)) ((a^k-b^k)*b)
    simp only [norm_mul,norm_pow,ha,hb,one_pow,one_mul,mul_one] at hn
    have hcast : ((k+1:ℕ):ℝ)=(k:ℝ)+1 := by norm_num
    rw [hcast]
    nlinarith

theorem finite_phase_det_one_qubit (V : Matrix (Reg 1) (Reg 1) ℂ) :
    Matrix.det V=
      V ((bitVecEquiv 1).symm 0) ((bitVecEquiv 1).symm 0)*
        V ((bitVecEquiv 1).symm 1) ((bitVecEquiv 1).symm 1)-
      V ((bitVecEquiv 1).symm 0) ((bitVecEquiv 1).symm 1)*
        V ((bitVecEquiv 1).symm 1) ((bitVecEquiv 1).symm 0) := by
  rw [← Matrix.det_submatrix_equiv_self (bitVecEquiv 1).symm V,Matrix.det_fin_two]
  rfl

theorem finite_phase_gaussian_det : Matrix.det finiteGaussianScalarGate=finiteGaussianScalar^2 := by
  have hn : (bitVecEquiv 1).symm 0≠(bitVecEquiv 1).symm 1 := by
    intro h
    have he := (bitVecEquiv 1).symm.injective h
    norm_num at he
  rw [finite_phase_det_one_qubit]
  simp [finiteGaussianScalarGate,Matrix.smul_apply,hn,Ne.symm hn,pow_two]

theorem finite_phase_det_entry_bound (V : Matrix (Reg 1) (Reg 1) ℂ)
    (hV : V ∈ Matrix.unitaryGroup (Reg 1) ℂ) (δ : ℝ) (hδ : 0 ≤ δ)
    (he : ∀ i j : Reg 1, ‖(V-finiteGaussianScalarGate) i j‖ ≤ δ) :
    ‖Matrix.det V-finiteGaussianScalar^2‖ ≤ 3*δ := by
  let a : Reg 1 := (bitVecEquiv 1).symm 0
  let b : Reg 1 := (bitVecEquiv 1).symm 1
  have hab : a≠b := by
    intro h
    have ht := (bitVecEquiv 1).symm.injective h
    norm_num at ht
  have haa : ‖V a a-finiteGaussianScalar‖ ≤ δ := by
    simpa only [Matrix.sub_apply,finiteGaussianScalarGate,Matrix.smul_apply,
      smul_eq_mul,Matrix.one_apply,ite_true,mul_one] using he a a
  have hbb : ‖V b b-finiteGaussianScalar‖ ≤ δ := by
    simpa only [Matrix.sub_apply,finiteGaussianScalarGate,Matrix.smul_apply,
      smul_eq_mul,Matrix.one_apply,ite_true,mul_one] using he b b
  have hba : ‖V b a‖ ≤ δ := by
    simpa only [Matrix.sub_apply,finiteGaussianScalarGate,Matrix.smul_apply,
      smul_eq_mul,Matrix.one_apply,if_neg (Ne.symm hab),mul_zero,sub_zero] using he b a
  have hvb : ‖V b b‖ ≤ 1 := entry_norm_bound_of_unitary hV b b
  have hva : ‖V a b‖ ≤ 1 := entry_norm_bound_of_unitary hV a b
  have hp : Matrix.det V-finiteGaussianScalar^2=
      (V a a-finiteGaussianScalar)*V b b+finiteGaussianScalar*(V b b-finiteGaussianScalar)-V a b*V b a := by
    rw [finite_phase_det_one_qubit]
    change V a a*V b b-V a b*V b a-finiteGaussianScalar^2=_
    ring
  rw [hp]
  calc
    _ ≤ ‖(V a a-finiteGaussianScalar)*V b b+finiteGaussianScalar*(V b b-finiteGaussianScalar)‖+
        ‖V a b*V b a‖ := norm_sub_le _ _
    _ ≤ ‖(V a a-finiteGaussianScalar)*V b b‖+‖finiteGaussianScalar*(V b b-finiteGaussianScalar)‖+
        ‖V a b*V b a‖ := add_le_add (norm_add_le _ _) le_rfl
    _ ≤ δ+δ+δ := by
      simp only [norm_mul,finite_phase_gaussian_norm,one_mul]
      apply add_le_add
      · apply add_le_add
        · exact (mul_le_mul haa hvb (norm_nonneg _) hδ).trans_eq (mul_one δ)
        · exact hbb
      · exact (mul_le_mul hva hba (norm_nonneg _) zero_le_one).trans_eq (one_mul δ)
    _ = _ := by ring

theorem finite_phase_word_entry_gap (gs : List FiniteGateCode) (hg : finiteWordLegal 1 gs=true) :
    ∃ i j : Reg 1, (1/32:ℝ) ≤ ‖(finiteCodeWordMatrix 1 gs-finiteGaussianScalarGate) i j‖ := by
  obtain ⟨hu,hd,_,_,_⟩ := finite_code_word_determinant_invariant 1 gs hg
  by_contra h
  push Not at h
  have hb := finite_phase_det_entry_bound (finiteCodeWordMatrix 1 gs) hu (1/32) (by norm_num)
    (fun i j => (h i j).le)
  have hv : ‖Matrix.det (finiteCodeWordMatrix 1 gs)‖=1 :=
    CStarRing.norm_of_mem_unitary (Matrix.det_of_mem_unitary hu)
  have hz : ‖finiteGaussianScalar^2‖=1 := by rw [norm_pow,finite_phase_gaussian_norm,one_pow]
  have hp := finite_phase_power_difference (Matrix.det (finiteCodeWordMatrix 1 gs))
    (finiteGaussianScalar^2) hv hz 8
  have hgap : 1 ≤ ‖(Matrix.det (finiteCodeWordMatrix 1 gs))^8-(finiteGaussianScalar^2)^8‖ := by
    rw [hd,← pow_mul]
    exact finite_phase_gaussian_power_gap
  norm_num at hp hb
  linarith

theorem finite_phase_ket_entry {H : Type} [Fintype H] [DecidableEq H]
    (M : Matrix H H ℂ) (i j : H) : ApplyGate M (Qatlib.Foundations.PureStateMath.Ket j) i=M i j := by
  simp [ApplyGate,Matrix.mulVec,dotProduct,Qatlib.Foundations.PureStateMath.Ket]

theorem finite_phase_entry_le_column {H : Type} [Fintype H] [DecidableEq H]
    (M : Matrix H H ℂ) (i j : H) :
    ‖M i j‖ ≤ ‖toEuclidean_fromVec (ApplyGate M (Qatlib.Foundations.PureStateMath.Ket j))‖ := by
  have he :=
      PiLp.norm_apply_le
      (toEuclidean_fromVec (ApplyGate M (Qatlib.Foundations.PureStateMath.Ket j))) i
  change ‖ApplyGate M (Qatlib.Foundations.PureStateMath.Ket j) i‖ ≤ _ at he
  rw [finite_phase_ket_entry] at he
  exact he

theorem finite_phase_column_le_operator {H : Type} [Fintype H] [DecidableEq H]
    (M : Matrix H H ℂ) (j : H) :
    ‖toEuclidean_fromVec (ApplyGate M (Qatlib.Foundations.PureStateMath.Ket j))‖ ≤ ‖M‖ := by
  have he :=
      ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := H)) M).le_opNorm
      (toEuclidean_fromVec (Qatlib.Foundations.PureStateMath.Ket j))
  rw [toEuclideanCLM_applyGate,Matrix.l2_opNorm_toEuclideanCLM,
    (normalized_iff_norm_toEuclidean_fromVec (Qatlib.Foundations.PureStateMath.Ket j)).mp (normalized_ket j),mul_one] at he
  exact he

theorem finite_gaussian_scalar_obstruction :
    ‖finiteGaussianScalar‖=1 ∧ finiteGaussianScalarGate ∈ Matrix.unitaryGroup (Reg 1) ℂ ∧
    ∀ gs : List FiniteGateCode, finiteWordLegal 1 gs=true →
      (1/32:ℝ) ≤ ‖finiteCodeWordMatrix 1 gs-finiteGaussianScalarGate‖ ∧
      ∃ x : Reg 1, Normalized (Qatlib.Foundations.PureStateMath.Ket x) ∧
        (1/32:ℝ) ≤ ‖toEuclidean_fromVec
          (Run (1 : Matrix (Reg 1) (Reg 1) ℂ) (finiteCodeCircuit 1 gs) (Qatlib.Foundations.PureStateMath.Ket x)-
            ApplyGate finiteGaussianScalarGate (Qatlib.Foundations.PureStateMath.Ket x))‖ := by
  refine ⟨finite_phase_gaussian_norm,finite_phase_gaussian_unitary,?_⟩
  intro gs hg
  obtain ⟨i,j,he⟩ := finite_phase_word_entry_gap gs hg
  have hc := finite_phase_entry_le_column (finiteCodeWordMatrix 1 gs-finiteGaussianScalarGate) i j
  refine ⟨he.trans (hc.trans (finite_phase_column_le_operator _ j)),j,normalized_ket j,?_⟩
  rw [finite_phase_word_run]
  have ha : ApplyGate (finiteCodeWordMatrix 1 gs-finiteGaussianScalarGate) (Qatlib.Foundations.PureStateMath.Ket j)=
      ApplyGate (finiteCodeWordMatrix 1 gs) (Qatlib.Foundations.PureStateMath.Ket j)-ApplyGate finiteGaussianScalarGate (Qatlib.Foundations.PureStateMath.Ket j) := by
    simp only [ApplyGate,Matrix.sub_mulVec]
  rw [← ha]
  exact he.trans hc

theorem finite_scalar_uncontrolled_born_equivalence :
    finiteWordLegal 1 []=true ∧ QueryCount (finiteCodeCircuit 1 [])=0 ∧
      GateCount (finiteCodeCircuit 1 [])=0 ∧
      ∀ ψ : QState (Reg 1), Normalized ψ →
        Normalized (ApplyGate finiteGaussianScalarGate ψ) ∧
        ∀ E : Finset (Reg 1),
          MeasureProb (Run (1 : Matrix (Reg 1) (Reg 1) ℂ) (finiteCodeCircuit 1 []) ψ) E=
            MeasureProb (ApplyGate finiteGaussianScalarGate ψ) E := by
  have hl : finiteWordLegal 1 []=true := by rfl
  obtain ⟨_,_,hq,hg,_⟩ := finite_code_word_determinant_invariant 1 [] hl
  refine ⟨hl,hq,by simpa only [List.length_nil] using hg,?_⟩
  intro ψ hψ
  refine ⟨normalized_applyGate finite_gaussian_scalar_obstruction.2.1 hψ,?_⟩
  intro E
  have ha : ApplyGate finiteGaussianScalarGate ψ=finiteGaussianScalar•ψ := by
    simp only [finiteGaussianScalarGate,ApplyGate,Matrix.smul_mulVec,Matrix.one_mulVec]
  rw [ha,measureProb_smul,finite_gaussian_scalar_obstruction.1,one_pow,one_mul]
  rfl

end Qatlib.Concepts.UniformBqp.FiniteGateWord
