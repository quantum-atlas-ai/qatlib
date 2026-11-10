/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FermionAlgebra.CarJordanWigner.Fermion
import Qatlib.Concepts.GateVocabulary.GateVocab.GateVocabulary
import Qatlib.Concepts.LocalMachine.LocalTransport.ControlledQueryCircuit
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Tactic
import Qatlib.Concepts.PauliClifford.PauliBasis
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Matrix NormedSpace
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.GateVocabulary.GateVocab
open scoped Classical

namespace Qatlib.Papers.TranscorrChem20.MainResults.Encoding
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def testPhase : Matrix Bool Bool ℂ :=
    Matrix.diagonal (fun b => if b then -Complex.I else 1)
noncomputable def gramReadoutCircuit (C : Matrix I I ℂ) (imag : Bool) : Circuit (Bool × I) :=
  [Step.gate (TensorGate Hadamard (1 : Matrix I I ℂ)), Step.gate (controlOracle C)] ++
  (if imag then [Step.gate (TensorGate testPhase (1 : Matrix I I ℂ))] else []) ++
  [Step.gate (TensorGate Hadamard (1 : Matrix I I ℂ))]

theorem paired_readout_hadamard (v : QState (Bool×I)) (b : Bool) (i : I) :
    (TensorGate Hadamard (1 : Matrix I I ℂ) *ᵥ v) (b,i) =
      (Real.sqrt 2 : ℂ)⁻¹*(v (false,i)+(if b then -v (true,i) else v (true,i))) := by
  cases b <;> simp [Matrix.mulVec,dotProduct,TensorGate,Hadamard,Fintype.sum_prod_type,
    Matrix.one_apply,mul_ite,ite_mul]
  all_goals ring

theorem paired_readout_control (C : Matrix I I ℂ) (v : QState (Bool×I)) (b : Bool) (i : I) :
    (controlOracle C *ᵥ v) (b,i) =
      if b then (C *ᵥ (fun j => v (true,j))) i else v (false,i) := by
  cases b <;> simp [controlOracle,select,Matrix.mulVec,dotProduct,
    Fintype.sum_prod_type,Matrix.one_apply,ite_mul]

theorem paired_readout_phase (v : QState (Bool×I)) (b : Bool) (i : I) :
    (TensorGate testPhase (1 : Matrix I I ℂ) *ᵥ v) (b,i) =
      if b then -Complex.I*v (true,i) else v (false,i) := by
  cases b <;> simp [testPhase,TensorGate,Matrix.mulVec,dotProduct,
    Fintype.sum_prod_type,Matrix.one_apply,mul_ite,ite_mul]

theorem gramReadoutCircuit_amplitude (C : Matrix I I ℂ) (psi : QState I) (imag b : Bool) (i : I) :
    (Run 1 (gramReadoutCircuit C imag) (TensorState (Qatlib.Foundations.PureStateMath.Ket false) psi)) (b,i) =
      (psi i+(if b then -1 else 1)*(if imag then -Complex.I else 1)*(C *ᵥ psi) i)/2 := by
  have hs : ((Real.sqrt 2 : ℂ)⁻¹)^2 = 1/2 := by
    rw [inv_pow,sqrt2_sq]
    norm_num
  have hc : (C *ᵥ (fun j => (Real.sqrt 2 : ℂ)⁻¹*psi j)) =
      (Real.sqrt 2 : ℂ)⁻¹ • (C *ᵥ psi) := by
    rw [show (fun j => (Real.sqrt 2 : ℂ)⁻¹*psi j) = (Real.sqrt 2 : ℂ)⁻¹ • psi by rfl,
      Matrix.mulVec_smul]
  let a : ℂ := (Real.sqrt 2 : ℂ)⁻¹
  have h1 : TensorGate Hadamard (1 : Matrix I I ℂ) *ᵥ TensorState (Qatlib.Foundations.PureStateMath.Ket false) psi =
      (fun p : Bool×I => a*psi p.2) := by
    ext ⟨b,i⟩
    rw [paired_readout_hadamard]
    cases b <;> simp [TensorState,Qatlib.Foundations.PureStateMath.Ket,a]
  have h2 : controlOracle C *ᵥ (fun p : Bool×I => a*psi p.2) =
      (fun p : Bool×I => a*(if p.1 then (C *ᵥ psi) p.2 else psi p.2)) := by
    ext ⟨b,i⟩
    rw [paired_readout_control]
    cases b
    · rfl
    · exact congrFun hc i
  have h3 : TensorGate testPhase (1 : Matrix I I ℂ) *ᵥ
      (fun p : Bool×I => a*(if p.1 then (C *ᵥ psi) p.2 else psi p.2)) =
      (fun p : Bool×I => if p.1 then a*(-Complex.I)*(C *ᵥ psi) p.2 else a*psi p.2) := by
    ext ⟨b,i⟩
    rw [paired_readout_phase]
    cases b <;> simp only [Bool.false_eq_true,if_true,if_false]
    ring
  cases imag <;> cases b <;>
    simp only [gramReadoutCircuit,Bool.false_eq_true,if_false,if_true,
      List.append_nil,List.cons_append,List.nil_append,run_gate,run_nil,ApplyGate]
  all_goals rw [h1,h2]
  all_goals first | rw [h3] | skip
  all_goals rw [paired_readout_hadamard]
  all_goals simp only [Bool.false_eq_true,if_false,if_true]
  all_goals dsimp only [a]
  all_goals ring_nf
  all_goals norm_num [hs]
  all_goals ring

theorem testPhase_unitary : testPhase ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff',Matrix.star_eq_conjTranspose]
  ext b c
  cases b <;> cases c <;> simp [testPhase,Matrix.mul_apply]

theorem paired_readout_scalar (x y : ℂ) (imag : Bool) :
    ‖(x+(if imag then -Complex.I else 1)*y)/2‖^2-
      ‖(x-(if imag then -Complex.I else 1)*y)/2‖^2 =
      if imag then (star x*y).im else (star x*y).re := by
  rw [← Complex.normSq_eq_norm_sq,← Complex.normSq_eq_norm_sq]
  cases imag <;> simp [Complex.normSq_apply,
    Complex.mul_re,Complex.mul_im]
  all_goals ring

theorem paired_gram_actual_complex_readout : ∀ (C : Matrix I I ℂ) (psi : QState I),
    C ∈ Matrix.unitaryGroup I ℂ → Normalized psi →
    (∀ imag : Bool, IsUnitaryCircuit (gramReadoutCircuit C imag) ∧
      GateCount (gramReadoutCircuit C imag)=if imag then 4 else 3) ∧
    (∀ imag : Bool, MeasureProb (Run 1 (gramReadoutCircuit C imag) (TensorState (Qatlib.Foundations.PureStateMath.Ket false) psi))
      {x | x.1=false}-MeasureProb
      (Run 1 (gramReadoutCircuit C imag) (TensorState (Qatlib.Foundations.PureStateMath.Ket false) psi)) {x | x.1=true} =
      if imag then (Qatlib.Foundations.PureStateMath.Inner psi (C *ᵥ psi)).im else (Qatlib.Foundations.PureStateMath.Inner psi (C *ᵥ psi)).re) := by
  intro C psi hC _
  constructor
  · intro imag
    constructor
    · have hH := tensorGate_unitary hadamard_unitary
        (show (1 : Matrix I I ℂ) ∈ Matrix.unitaryGroup I ℂ by simp)
      have hS := tensorGate_unitary testPhase_unitary
        (show (1 : Matrix I I ℂ) ∈ Matrix.unitaryGroup I ℂ by simp)
      cases imag
      · simp only [gramReadoutCircuit,Bool.false_eq_true,if_false,List.append_nil,
          List.cons_append,List.nil_append,isUnitaryCircuit_gate]
        exact ⟨hH,controlOracle_unitary hC,hH,isUnitaryCircuit_nil⟩
      · simp only [gramReadoutCircuit,if_true,List.cons_append,List.nil_append,isUnitaryCircuit_gate]
        exact ⟨hH,controlOracle_unitary hC,hS,hH,isUnitaryCircuit_nil⟩
    · cases imag <;> simp [gramReadoutCircuit]
  · intro imag
    simp only [MeasureProb,Finset.sum_filter,Fintype.sum_prod_type,Fintype.sum_bool,
      Bool.false_eq_true,Bool.true_eq_false,if_true,if_false,
      BornProb,gramReadoutCircuit_amplitude]
    simp only [Finset.sum_const_zero,zero_add,add_zero,one_mul,neg_one_mul]
    rw [← Finset.sum_sub_distrib]
    calc
      _ = ∑ i, (if imag then (star (psi i)*(C *ᵥ psi) i).im else
          (star (psi i)*(C *ᵥ psi) i).re) := by
        apply Finset.sum_congr rfl
        intro i _
        simpa only [neg_mul,sub_eq_add_neg] using! paired_readout_scalar (psi i) ((C *ᵥ psi) i) imag
      _ = _ := by
        cases imag <;> simp only [Bool.false_eq_true,if_false,if_true,Qatlib.Foundations.PureStateMath.Inner,dotProduct,
          Complex.re_sum,Complex.im_sum,Pi.star_apply]

open Qatlib.Concepts.FermionAlgebra.CarJordanWigner

theorem fock_card (n : ℕ) : Fintype.card (Reg n) = 2^n := by simp [Reg]

theorem actual_car {n : ℕ} (i j : Fin n) :
    annihilation i * creation j + creation j * annihilation i =
      (if i=j then (1 : Matrix (Reg n) (Reg n) ℂ) else 0) ∧
    annihilation i * annihilation j + annihilation j * annihilation i = 0 ∧
    creation i * creation j + creation j * creation i = 0 := (g1 n).1 i j

theorem actual_jw {n : ℕ} (i : Fin n) :
    annihilation i = jwPauliWord i ∧ creation i = (jwPauliWord i).conjTranspose :=
  (g1 n).2.2.2.2.1 i

noncomputable def occupationZ {n : ℕ} (i : Fin n) : Matrix (Reg n) (Reg n) ℂ :=
  diagonal (fun x => if x i then -1 else 1)

theorem actual_number_half_z {n : ℕ} (i : Fin n) :
    creation i * annihilation i = (1/2 : ℂ) • (1 - occupationZ i) := by
  rw [← numberOp_eq]
  ext y x
  by_cases h : y = x
  · subst y
    cases hx : x i <;> norm_num [num_apply, occupationZ, Matrix.diagonal_apply, hx]
  · simp [num_apply, occupationZ, h, Ne.symm h]

noncomputable def tcMatrix {J : Type*} [Fintype J] [DecidableEq J]
    (H g : Matrix J J ℂ) : Matrix J J ℂ := exp (-g) * H * exp g

theorem actual_tc_pauli_expansion (H g : Matrix (Fin 2) (Fin 2) ℂ) :
    tcMatrix H g = (1/2 : ℂ) •
      (Matrix.trace (tcMatrix H g) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
      ∑ a : Fin 3, Matrix.trace (pauliAxis a * tcMatrix H g) • pauliAxis a) :=
  pauli_axis_expansion (tcMatrix H g)

noncomputable def energy (A : Matrix I I ℂ) (ψ : QState I) : ℂ := Inner ψ (A *ᵥ ψ)

omit [DecidableEq I] in

theorem energy_linear {M : Type*} [Fintype M] (A : M → Matrix I I ℂ)
    (c : M → ℂ) (ψ : QState I) :
    energy (∑ a, c a • A a) ψ = ∑ a, c a * energy (A a) ψ := by
  simp only [energy, Qatlib.Foundations.PureStateMath.Inner, Matrix.sum_mulVec, Matrix.smul_mulVec, dotProduct,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem pauli_energy_real (a : Fin 4) (ψ : QState (Fin 2)) :
    (energy (pauliFin a) ψ).im = 0 :=
  (show (pauliFin a).IsHermitian from pauliFin_adjoint a).im_star_dotProduct_mulVec_self ψ

theorem actual_overlap_readout (U V : Matrix I I ℂ) (ψ : QState I)
    (hU : U ∈ Matrix.unitaryGroup I ℂ) (hV : V ∈ Matrix.unitaryGroup I ℂ)
    (hψ : Normalized ψ) :
    ∀ imag : Bool, MeasureProb
      (Run 1 (gramReadoutCircuit (U.conjTranspose * V) imag) (TensorState (Ket false) ψ)) {x | x.1=false} -
      MeasureProb (Run 1 (gramReadoutCircuit (U.conjTranspose * V) imag) (TensorState (Ket false) ψ)) {x | x.1=true} =
      if imag then (Inner (U *ᵥ ψ) (V *ᵥ ψ)).im else (Inner (U *ᵥ ψ) (V *ᵥ ψ)).re := by
  have hUd : U.conjTranspose ∈ Matrix.unitaryGroup I ℂ := by
    rw [Matrix.mem_unitaryGroup_iff]
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose] using!
      (Matrix.mem_unitaryGroup_iff'.mp hU)
  have hread := (paired_gram_actual_complex_readout (U.conjTranspose * V) ψ
    ((Matrix.unitaryGroup I ℂ).mul_mem hUd hV) hψ).2
  have hinner : Inner (U *ᵥ ψ) (V *ᵥ ψ) = Inner ψ ((U.conjTranspose * V) *ᵥ ψ) := by
    simp only [Qatlib.Foundations.PureStateMath.Inner, Matrix.star_mulVec, Matrix.dotProduct_mulVec,
      Matrix.vecMul_vecMul]
  simpa only [← hinner] using! hread

open scoped Matrix.Norms.L2Operator

noncomputable def standardRotation (P : Matrix I I ℂ) (θ : ℝ) : Matrix I I ℂ :=
  exp (θ • ((-Complex.I / 2 : ℂ) • P))

theorem standardRotation_hasDerivAt (P : Matrix I I ℂ) (θ : ℝ) :
    HasDerivAt (standardRotation P) ((-Complex.I / 2 : ℂ) •
      (P * standardRotation P θ)) θ := by
  simpa only [standardRotation, Matrix.smul_mul] using!
    (hasDerivAt_exp_smul_const' ((-Complex.I / 2 : ℂ) • P) θ)

theorem standardRotation_unitary (P : Matrix I I ℂ) (hP : P.IsHermitian) (θ : ℝ) :
    standardRotation P θ ∈ Matrix.unitaryGroup I ℂ := by
  letI : NormedAlgebra ℚ (Matrix I I ℂ) := NormedAlgebra.restrictScalars ℚ ℝ _
  apply exp_mem_unitary_of_mem_skewAdjoint
  rw [skewAdjoint.mem_iff]
  simp only [star_smul, star_trivial, Matrix.star_eq_conjTranspose, hP.eq]
  have hc : star (-Complex.I / 2 : ℂ) = -(-Complex.I / 2 : ℂ) := by
    simp
    ring
  rw [hc]
  simp only [neg_smul, smul_neg]

theorem rotation_context_hasDerivAt (W T P : Matrix I I ℂ) (θ : ℝ) :
    HasDerivAt (fun t => W * standardRotation P t * T)
      ((-Complex.I / 2 : ℂ) • (W * (P * standardRotation P θ) * T)) θ := by
  simpa only [Matrix.mul_smul, Matrix.smul_mul] using!
    ((standardRotation_hasDerivAt P θ).const_mul W).mul_const T

open Qatlib.Concepts.PauliClifford.PauliBasis

noncomputable def pauliReadout {n : ℕ} (w : Fin n → Fin 4) (ψ : QState (Reg n)) : ℝ :=
  MeasureProb (Run 1 (gramReadoutCircuit (pauliWord w) false) (TensorState (Ket false) ψ))
      {x | x.1=false} -
  MeasureProb (Run 1 (gramReadoutCircuit (pauliWord w) false) (TensorState (Ket false) ψ))
      {x | x.1=true}

theorem word_energy_readout {n : ℕ} (w : Fin n → Fin 4) (ψ : QState (Reg n))
    (hψ : Normalized ψ) : energy (pauliWord w) ψ = (pauliReadout w ψ : ℂ) := by
  apply Complex.ext
  · exact ((paired_gram_actual_complex_readout (pauliWord w) ψ (word_unitary w) hψ).2 false).symm
  · exact (show (pauliWord w).IsHermitian from word_adjoint w).im_star_dotProduct_mulVec_self ψ

theorem actual_tc_finite_pauli_readout {n m : ℕ} (H g : Matrix (Reg n) (Reg n) ℂ)
    (words : Fin m → (Fin n → Fin 4)) (coeff : Fin m → ℂ)
    (hTC : tcMatrix H g = ∑ j, coeff j • pauliWord (words j))
    (ψ : QState (Reg n)) (hψ : Normalized ψ) :
    energy (tcMatrix H g) ψ = ∑ j, coeff j * (pauliReadout (words j) ψ : ℂ) := by
  rw [hTC, energy_linear]
  simp_rw [word_energy_readout _ ψ hψ]

theorem figure1_quadrature (φ y : QState I) (Z : Matrix I I ℂ) (hZ : Z.IsHermitian) :
    2 * (Inner ((-Complex.I / 2 : ℂ) • y) (Z *ᵥ φ)).re =
      (Inner φ (Z *ᵥ y)).im := by
  have hc : Inner y (Z *ᵥ φ) = star (Inner φ (Z *ᵥ y)) := by
    calc
      _ = Inner (Z *ᵥ y) φ := by
        simpa only [hZ.eq] using! (inner_mulVec_left_rect Z y φ).symm
      _ = _ := star_dotProduct _ _
  have hs : Inner ((-Complex.I / 2 : ℂ) • y) (Z *ᵥ φ) =
      star (-Complex.I / 2 : ℂ) * Inner y (Z *ᵥ φ) := by
    simp only [Qatlib.Foundations.PureStateMath.Inner, star_smul,
      smul_dotProduct, smul_eq_mul]
  rw [hs, hc]
  simp [Complex.mul_re]

noncomputable def rxQuarter : Matrix Bool Bool ℂ := testPhase * Hadamard * testPhase

theorem rxQuarter_entries (b c : Bool) :
    rxQuarter b c = (Real.sqrt 2 : ℂ)⁻¹ * (if b=c then 1 else -Complex.I) := by
  cases b <;> cases c <;>
    simp [rxQuarter, testPhase, Hadamard, Matrix.mul_apply]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq]

noncomputable def figure1Circuit (U Y Z : Matrix I I ℂ) : Circuit (Bool × I) :=
  [Step.gate (TensorGate Hadamard (1 : Matrix I I ℂ)),
   Step.gate (controlOracle Y), Step.gate (TensorGate (1 : Matrix Bool Bool ℂ) U),
   Step.gate (controlOracle Z), Step.gate (TensorGate testPhase (1 : Matrix I I ℂ)),
   Step.gate (TensorGate Hadamard (1 : Matrix I I ℂ)),
   Step.gate (TensorGate testPhase (1 : Matrix I I ℂ))]

theorem figure1Circuit_unitary (U Y Z : Matrix I I ℂ)
    (hU : U ∈ Matrix.unitaryGroup I ℂ) (hY : Y ∈ Matrix.unitaryGroup I ℂ)
    (hZ : Z ∈ Matrix.unitaryGroup I ℂ) : IsUnitaryCircuit (figure1Circuit U Y Z) := by
  have hH := tensorGate_unitary hadamard_unitary
    (show (1 : Matrix I I ℂ) ∈ Matrix.unitaryGroup I ℂ by simp)
  have hS := tensorGate_unitary testPhase_unitary
    (show (1 : Matrix I I ℂ) ∈ Matrix.unitaryGroup I ℂ by simp)
  have hsys := tensorGate_unitary
    (show (1 : Matrix Bool Bool ℂ) ∈ Matrix.unitaryGroup Bool ℂ by simp) hU
  simpa only [figure1Circuit, isUnitaryCircuit_gate, isUnitaryCircuit_nil] using!
    ⟨hH, controlOracle_unitary hY, hsys, controlOracle_unitary hZ, hS, hH, hS, trivial⟩
omit [DecidableEq I] in

theorem paired_system_gate (U : Matrix I I ℂ) (v : QState (Bool × I)) (b : Bool) (i : I) :
    (TensorGate (1 : Matrix Bool Bool ℂ) U *ᵥ v) (b,i) =
      (U *ᵥ (fun j => v (b,j))) i := by
  simp [TensorGate, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.one_apply]

theorem figure1_amplitude (U Y Z : Matrix I I ℂ) (ψ : QState I) (b : Bool) (i : I) :
    Run 1 (figure1Circuit U Y Z) (TensorState (Ket false) ψ) (b,i) =
    if b then -Complex.I * ((U *ᵥ ψ) i + Complex.I * (Z *ᵥ (U *ᵥ (Y *ᵥ ψ))) i) / 2
    else ((U *ᵥ ψ) i - Complex.I * (Z *ᵥ (U *ᵥ (Y *ᵥ ψ))) i) / 2 := by
  let a : ℂ := (Real.sqrt 2 : ℂ)⁻¹
  have hs : a^2 = 1/2 := by
    dsimp only [a]
    rw [inv_pow, sqrt2_sq]
    norm_num
  have h1 : TensorGate Hadamard (1 : Matrix I I ℂ) *ᵥ TensorState (Ket false) ψ =
      (fun p : Bool × I => a * ψ p.2) := by
    ext ⟨b,i⟩
    rw [paired_readout_hadamard]
    cases b <;> simp [TensorState, Qatlib.Foundations.PureStateMath.Ket, a]
  have hc (C : Matrix I I ℂ) (v : QState I) :
      C *ᵥ (fun j => a * v j) = a • (C *ᵥ v) := Matrix.mulVec_smul C a v
  have h2 : controlOracle Y *ᵥ (fun p : Bool × I => a * ψ p.2) =
      (fun p : Bool × I => a * (if p.1 then (Y *ᵥ ψ) p.2 else ψ p.2)) := by
    ext ⟨b,i⟩
    rw [paired_readout_control]
    cases b
    · rfl
    · exact congrFun (hc Y ψ) i
  have h3 : TensorGate (1 : Matrix Bool Bool ℂ) U *ᵥ
      (fun p : Bool × I => a * (if p.1 then (Y *ᵥ ψ) p.2 else ψ p.2)) =
      (fun p : Bool × I => a * (if p.1 then (U *ᵥ (Y *ᵥ ψ)) p.2 else (U *ᵥ ψ) p.2)) := by
    ext ⟨b,i⟩
    rw [paired_system_gate]
    cases b <;> exact congrFun (hc U _) i
  have h4 : controlOracle Z *ᵥ
      (fun p : Bool × I => a * (if p.1 then (U *ᵥ (Y *ᵥ ψ)) p.2 else (U *ᵥ ψ) p.2)) =
      (fun p : Bool × I => a * (if p.1 then (Z *ᵥ (U *ᵥ (Y *ᵥ ψ))) p.2 else (U *ᵥ ψ) p.2)) := by
    ext ⟨b,i⟩
    rw [paired_readout_control]
    cases b
    · rfl
    · exact congrFun (hc Z _) i
  simp only [figure1Circuit, run_gate, run_nil, ApplyGate]
  rw [h1, h2, h3, h4, paired_readout_phase]
  cases b <;> simp only [Bool.false_eq_true, if_false, if_true]
  all_goals rw [paired_readout_hadamard]
  all_goals simp only [paired_readout_phase, Bool.false_eq_true, if_false, if_true]
  all_goals dsimp only [a] at hs ⊢
  all_goals ring_nf
  all_goals norm_num [hs, Complex.I_sq]
  all_goals ring

theorem figure1_actual_readout (U Y Z : Matrix I I ℂ) (ψ : QState I) :
    MeasureProb (Run 1 (figure1Circuit U Y Z) (TensorState (Ket false) ψ)) {x | x.1=false} -
    MeasureProb (Run 1 (figure1Circuit U Y Z) (TensorState (Ket false) ψ)) {x | x.1=true} =
    (Inner (U *ᵥ ψ) (Z *ᵥ (U *ᵥ (Y *ᵥ ψ)))).im := by
  simp only [MeasureProb, Finset.sum_filter, Fintype.sum_prod_type, Fintype.sum_bool,
    Bool.false_eq_true, Bool.true_eq_false, if_true, if_false, BornProb, figure1_amplitude]
  simp only [Finset.sum_const_zero, zero_add, add_zero]
  rw [← Finset.sum_sub_distrib]
  calc
    _ = ∑ i, (star ((U *ᵥ ψ) i) * (Z *ᵥ (U *ᵥ (Y *ᵥ ψ))) i).im := by
      apply Finset.sum_congr rfl
      intro i _
      have h := paired_readout_scalar ((U *ᵥ ψ) i) ((Z *ᵥ (U *ᵥ (Y *ᵥ ψ))) i) true
      simpa only [if_true, norm_div, norm_mul, norm_neg, Complex.norm_I, neg_mul,
        one_mul, sub_eq_add_neg, neg_neg] using! h
    _ = _ := by simp only [Qatlib.Foundations.PureStateMath.Inner, dotProduct, Pi.star_apply, Complex.im_sum]

theorem actual_tc_canonical_readout {n : ℕ} (H g : Matrix (Reg n) (Reg n) ℂ)
    (ψ : QState (Reg n)) (hψ : Normalized ψ) :
    energy (tcMatrix H g) ψ = ∑ w, pauliCoefficient (tcMatrix H g) w *
      (pauliReadout w ψ : ℂ) := by
  conv_lhs => rw [word_expansion (tcMatrix H g)]
  rw [energy_linear]
  simp_rw [word_energy_readout _ ψ hψ]

theorem actual_eigenstate_energy (A : Matrix I I ℂ) (ψ : QState I) (E : ℝ)
    (hψ : Normalized ψ) (hE : A *ᵥ ψ = (E : ℂ) • ψ) : energy A ψ = (E : ℂ) := by
  rw [energy, hE]
  change star ψ ⬝ᵥ ((E : ℂ) • ψ) = (E : ℂ)
  rw [dotProduct_smul]
  change (E : ℂ) * Inner ψ ψ = (E : ℂ)
  rw [(normalized_iff_inner_self ψ).mp hψ, mul_one]

theorem standardRotation_commute (P : Matrix I I ℂ) (θ : ℝ) :
    Commute P (standardRotation P θ) := by
  exact (((Commute.refl P).smul_right (-Complex.I / 2 : ℂ)).smul_right θ).exp_right

theorem rotation_context_right_hasDerivAt (W T P : Matrix I I ℂ) (θ : ℝ) :
    HasDerivAt (fun t => W * standardRotation P t * T)
      ((-Complex.I / 2 : ℂ) • (W * (standardRotation P θ * P) * T)) θ := by
  simpa only [(standardRotation_commute P θ).eq] using! rotation_context_hasDerivAt W T P θ

theorem figure1_derivative_readout (U Y Z : Matrix I I ℂ) (ψ : QState I)
    (hZ : Z.IsHermitian) :
    MeasureProb (Run 1 (figure1Circuit U Y Z) (TensorState (Ket false) ψ)) {x | x.1=false} -
    MeasureProb (Run 1 (figure1Circuit U Y Z) (TensorState (Ket false) ψ)) {x | x.1=true} =
    2 * (Inner ((-Complex.I / 2 : ℂ) • (U *ᵥ (Y *ᵥ ψ))) (Z *ᵥ (U *ᵥ ψ))).re := by
  rw [figure1_actual_readout]
  exact (figure1_quadrature (U *ᵥ ψ) (U *ᵥ (Y *ᵥ ψ)) Z hZ).symm

theorem actual_pauli_rotation_figure1 {n : ℕ} (W : Matrix (Reg n) (Reg n) ℂ)
    (hW : W ∈ Matrix.unitaryGroup (Reg n) ℂ) (wy wz : Fin n → Fin 4)
    (ψ : QState (Reg n)) (θ : ℝ) :
    let P := pauliWord wy
    let Z := pauliWord wz
    let U := W * standardRotation P θ
    IsUnitaryCircuit (figure1Circuit U P Z) ∧
    HasDerivAt (fun t => W * standardRotation P t)
      ((-Complex.I / 2 : ℂ) • (W * (standardRotation P θ * P))) θ ∧
    (MeasureProb (Run 1 (figure1Circuit U P Z) (TensorState (Ket false) ψ)) {x | x.1=false} -
     MeasureProb (Run 1 (figure1Circuit U P Z) (TensorState (Ket false) ψ)) {x | x.1=true} =
      2 * (Inner ((-Complex.I / 2 : ℂ) • (U *ᵥ (P *ᵥ ψ))) (Z *ᵥ (U *ᵥ ψ))).re) := by
  (try dsimp only)
  refine ⟨figure1Circuit_unitary _ _ _
    ((Matrix.unitaryGroup (Reg n) ℂ).mul_mem hW
      (standardRotation_unitary _ (word_adjoint wy) θ))
    (word_unitary wy) (word_unitary wz), ?_,
    figure1_derivative_readout _ _ _ ψ (word_adjoint wz)⟩
  simpa only [mul_one] using!
    rotation_context_right_hasDerivAt W (1 : Matrix (Reg n) (Reg n) ℂ) (pauliWord wy) θ

end Qatlib.Papers.TranscorrChem20.MainResults.Encoding
