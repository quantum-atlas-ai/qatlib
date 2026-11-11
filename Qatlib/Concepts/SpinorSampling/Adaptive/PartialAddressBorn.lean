/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.Retained.RetainedSpinInstrument

open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

/-!
# Partial Address Born

Partial Address Born constructions and identities for Spinor Sampling.
-/

open Qatlib.Concepts.SpinorSampling.Model Qatlib.Concepts.SpinorSampling.NativeRecords Qatlib.Concepts.SpinorSampling.Retained

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

set_option autoImplicit false

namespace Qatlib.Concepts.SpinorSampling.Adaptive.PartialAddress
noncomputable section
open scoped BigOperators
open Qatlib ShiftCircuit NativeBridge RetainedSpin

/-- Construction for edge Input in the partial address born model. -/
def edgeInput (u v : Bool → ℂ) : QState (Reg 2) :=
  fun x => (if x 0 then v (x 1) else u (x 1))/(Real.sqrt 2 : ℂ)

/-- Construction for endpoint Word in the partial address born model. -/
def endpointWord (basis : Fin 3) : List (MeasurementGate 2) :=
  if basis=0 then [.native (.h 0)] else
    if basis=1 then [.native (.tdg 0),.native (.tdg 0),.native (.h 0)] else []

/-- Construction for endpoint Program in the partial address born model. -/
def endpointProgram (basis : Fin 3) : Circuit (Reg 2) := measurementProgram (endpointWord basis)

/-- Construction for quarter Phase in the partial address born model. -/
def quarterPhase : ℂ := Complex.exp (((-(Real.pi/4) : ℝ) : ℂ)*Complex.I)

/-- Complete original `native_tadj_at` guarantee for `PartialAddressBorn`; all source hypotheses and output obligations are retained. -/
theorem native_tadj_at (f : QState (Reg 2)) (a b : Bool) :
    ApplyGate (wireGate 2 0 tGateAdj) f (pairReg a b)=
      (if a then quarterPhase else 1)*f (pairReg a b) := by
  let g : Reg 2 → ℂ := fun y => wireGate 2 0 tGateAdj (pairReg a b) y*f y
  change (∑ y : Reg 2,g y)=_
  rw [← Fintype.sum_equiv pairEquiv (fun p => g (pairEquiv p)) g (fun _ => rfl)]
  simp only [Fintype.sum_prod_type,Fintype.sum_bool]
  cases a <;> cases b <;>
    simp [g,pairEquiv,wireGate_apply,tGateAdj,Rz,Matrix.diagonal_apply,quarterPhase]

/-- Complete original `quarter_phase_square` guarantee for `PartialAddressBorn`; all source hypotheses and output obligations are retained. -/
theorem quarter_phase_square : quarterPhase*quarterPhase = -Complex.I := by
  rw [quarterPhase,← Complex.exp_add,
    show (((-(Real.pi/4) : ℝ) : ℂ)*Complex.I)+
      (((-(Real.pi/4) : ℝ) : ℂ)*Complex.I) = -((Real.pi : ℂ)/2*Complex.I) from by
        push_cast
        ring,
    Complex.exp_neg,Complex.exp_pi_div_two_mul_I]
  norm_num

/-- Complete original `endpoint_program_counts` guarantee for `PartialAddressBorn`; all source hypotheses and output obligations are retained. -/
theorem endpoint_program_counts (basis : Fin 3) :
    QueryCount (endpointProgram basis)=0 ∧
      GateCount (endpointProgram basis)=(if basis=0 then 1 else if basis=1 then 3 else 0) := by
  have h := measurement_program_counts (endpointWord basis)
  fin_cases basis <;> simpa [endpointProgram,endpointWord] using h

/-- Complete original `endpoint_x_amplitude` guarantee for `PartialAddressBorn`; all source hypotheses and output obligations are retained. -/
theorem endpoint_x_amplitude (u v : Bool → ℂ) (a b : Bool) :
    Run (1 : Matrix (Reg 2) (Reg 2) ℂ) (endpointProgram 0) (edgeInput u v) (pairReg a b)=
      (u b+(if a then (-1 : ℂ) else 1)*v b)/2 := by
  have hs : (Real.sqrt 2 : ℂ)*(Real.sqrt 2 : ℂ)=2 := by
    norm_cast
    exact Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  change ApplyGate (wireGate 2 0 Hadamard) (edgeInput u v) (pairReg a b)=_
  rw [native_h_at]
  simp only [edgeInput,pair_reg_first,pair_reg_second,Bool.false_eq_true,ite_false,ite_true]
  field_simp
  linear_combination -(u b+(if a then (-1 : ℂ) else 1)*v b)*hs

/-- Complete original `endpoint_y_amplitude` guarantee for `PartialAddressBorn`; all source hypotheses and output obligations are retained. -/
theorem endpoint_y_amplitude (u v : Bool → ℂ) (a b : Bool) :
    Run (1 : Matrix (Reg 2) (Reg 2) ℂ) (endpointProgram 1) (edgeInput u v) (pairReg a b)=
      (u b-(if a then (-1 : ℂ) else 1)*Complex.I*v b)/2 := by
  have hs : (Real.sqrt 2 : ℂ)*(Real.sqrt 2 : ℂ)=2 := by
    norm_cast
    exact Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  change ApplyGate (wireGate 2 0 Hadamard)
    (ApplyGate (wireGate 2 0 tGateAdj) (ApplyGate (wireGate 2 0 tGateAdj) (edgeInput u v)))
      (pairReg a b)=_
  rw [native_h_at,native_tadj_at,native_tadj_at,native_tadj_at,native_tadj_at]
  simp only [Bool.false_eq_true,ite_false,ite_true,one_mul,edgeInput,pair_reg_first,pair_reg_second]
  rw [← mul_assoc quarterPhase quarterPhase,quarter_phase_square]
  field_simp
  linear_combination -(u b-(if a then (-1 : ℂ) else 1)*Complex.I*v b)*hs

/-- Construction for spin Filter in the partial address born model. -/
def spinFilter (spin : Bool) (u : Bool → ℂ) : Bool → ℂ :=
  fun b => if b=spin then u b else 0

/-- Construction for spin Projection in the partial address born model. -/
def spinProjection (spin : Bool) (f : QState (Reg 2)) : QState (Reg 2) :=
  fun x => if x 1=spin then f x else 0

/-- Complete original `edge_spin_filter` guarantee for `PartialAddressBorn`; all source hypotheses and output obligations are retained. -/
theorem edge_spin_filter (u v : Bool → ℂ) (spin : Bool) :
    edgeInput (spinFilter spin u) (spinFilter spin v)=spinProjection spin (edgeInput u v) := by
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases spin <;>
    simp [edgeInput,spinFilter,spinProjection,h0,h1]

/-- Complete original `edge_input_normalized` guarantee for `PartialAddressBorn`; all source hypotheses and output obligations are retained. -/
theorem edge_input_normalized (u v : Bool → ℂ) (hu : qubitMass u=1) (hv : qubitMass v=1) :
    Normalized (edgeInput u v) := by
  unfold Normalized
  rw [← Fintype.sum_equiv pairEquiv
    (fun p => ‖edgeInput u v (pairEquiv p)‖^2) (fun r => ‖edgeInput u v r‖^2) (fun _ => rfl)]
  simp only [Fintype.sum_prod_type,Fintype.sum_bool,Complex.sq_norm]
  dsimp only [pairEquiv,edgeInput,pairReg]
  simp only [Complex.normSq_div,Complex.normSq_ofReal,
    Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  change Complex.normSq (v true)/2+Complex.normSq (v false)/2+
    (Complex.normSq (u true)/2+Complex.normSq (u false)/2)=1
  dsimp [qubitMass] at hu hv
  linarith

/-- Construction for actual Prob in the partial address born model. -/
def actualProb (u v : Bool → ℂ) (spin : Bool) (basis : Fin 3) (outcome : Bool) : ℝ :=
  BornProb (Run (1 : Matrix (Reg 2) (Reg 2) ℂ) (endpointProgram basis)
    (edgeInput (spinFilter spin u) (spinFilter spin v))) (pairReg outcome spin)/3

/-- Construction for bit Sign in the partial address born model. -/
def bitSign (b : Bool) : ℝ := if b then -1 else 1

/-- Construction for sector Mass in the partial address born model. -/
def sectorMass (u v : Bool → ℂ) (spin : Bool) : ℝ :=
  (Complex.normSq (u spin)+Complex.normSq (v spin))/2

/-- Construction for sector Bloch in the partial address born model. -/
def sectorBloch (u v : Bool → ℂ) (spin : Bool) (basis : Fin 3) : ℝ :=
  if basis=0 then (star (u spin)*v spin).re else
    if basis=1 then (star (u spin)*v spin).im else
      (Complex.normSq (u spin)-Complex.normSq (v spin))/2

/-- Construction for signed Prob in the partial address born model. -/
def signedProb (u v : Bool → ℂ) (spin : Bool) (basis : Fin 3) (outcome : Bool) : ℝ :=
  (sectorMass u v spin+bitSign outcome*sectorBloch u v spin basis)/6

/-- Complete original `actual_prob_eq_signed` guarantee for `PartialAddressBorn`; all source hypotheses and output obligations are retained. -/
theorem actual_prob_eq_signed (u v : Bool → ℂ) (spin : Bool)
    (basis : Fin 3) (outcome : Bool) :
    actualProb u v spin basis outcome=signedProb u v spin basis outcome := by
  fin_cases basis
  · change actualProb u v spin 0 outcome=signedProb u v spin 0 outcome
    unfold actualProb BornProb
    rw [endpoint_x_amplitude,Complex.sq_norm,Complex.normSq_div]
    cases outcome <;>
      simp [signedProb,sectorMass,sectorBloch,bitSign,spinFilter,
        Complex.normSq_apply,Complex.mul_re,Complex.add_re,Complex.add_im,
        Complex.conj_re,Complex.conj_im] <;> ring
  · change actualProb u v spin 1 outcome=signedProb u v spin 1 outcome
    unfold actualProb BornProb
    rw [endpoint_y_amplitude,Complex.sq_norm,Complex.normSq_div]
    cases outcome <;>
      simp [signedProb,sectorMass,sectorBloch,bitSign,spinFilter,
        Complex.normSq_apply,Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.add_im,
        Complex.sub_re,Complex.sub_im,Complex.conj_re,Complex.conj_im] <;> ring
  · change actualProb u v spin 2 outcome=signedProb u v spin 2 outcome
    unfold actualProb BornProb
    change ‖edgeInput (spinFilter spin u) (spinFilter spin v) (pairReg outcome spin)‖^2/3=_
    rw [Complex.sq_norm]
    cases outcome <;>
      simp [edgeInput,pairReg,spinFilter,signedProb,sectorMass,sectorBloch,bitSign,
        Complex.normSq_ofReal,Real.mul_self_sqrt] <;> ring

/-- Complete original `actual_prob_nonneg` guarantee for `PartialAddressBorn`; all source hypotheses and output obligations are retained. -/
theorem actual_prob_nonneg (u v : Bool → ℂ) (spin : Bool) (basis : Fin 3) (a : Bool) :
    0 ≤ actualProb u v spin basis a := by
  unfold actualProb BornProb
  positivity

/-- Complete original `actual_prob_sector_sum` guarantee for `PartialAddressBorn`; all source hypotheses and output obligations are retained. -/
theorem actual_prob_sector_sum (u v : Bool → ℂ) (spin : Bool) :
    (∑ basis : Fin 3,∑ a : Bool,actualProb u v spin basis a)=sectorMass u v spin := by
  simp_rw [actual_prob_eq_signed]
  simp only [Fin.sum_univ_succ,Fintype.sum_bool,signedProb,bitSign]
  norm_num
  ring

/-- Complete original `sector_mass_total` guarantee for `PartialAddressBorn`; all source hypotheses and output obligations are retained. -/
theorem sector_mass_total (u v : Bool → ℂ) (hu : qubitMass u=1) (hv : qubitMass v=1) :
    sectorMass u v false+sectorMass u v true=1 := by
  dsimp [sectorMass,qubitMass] at *
  linarith

/-- Abbreviation for Record in the partial address born model. -/
abbrev Record := Bool × Fin 3 × Bool

/-- Construction for record Law in the partial address born model. -/
def recordLaw (u v : Bool → ℂ) (hu : qubitMass u=1) (hv : qubitMass v=1) : FinDist Record where
  prob r := actualProb u v r.1 r.2.1 r.2.2
  nonneg r := actual_prob_nonneg u v r.1 r.2.1 r.2.2
  sum_one := by
    simp only [Fintype.sum_prod_type]
    simp_rw [actual_prob_sector_sum]
    simpa only [Fintype.sum_bool,add_comm] using sector_mass_total u v hu hv

/-- Construction for kernel in the partial address born model. -/
def kernel (r s : Record) : ℝ :=
  if r.1=s.1 then 0 else (1-9*(if r.2.1=s.2.1 then bitSign r.2.2*bitSign s.2.2 else 0))/2

/-- Construction for projection in the partial address born model. -/
def projection (u v : Bool → ℂ) (r : Record) : ℝ :=
  ∑ s : Record,actualProb u v s.1 s.2.1 s.2.2*kernel r s

/-- Complete original `projection_formula` guarantee for `PartialAddressBorn`; all source hypotheses and output obligations are retained. -/
theorem projection_formula (u v : Bool → ℂ) (r : Record) :
    projection u v r=(sectorMass u v (!r.1)-3*bitSign r.2.2*sectorBloch u v (!r.1) r.2.1)/2 := by
  rcases r with ⟨spin,basis,a⟩
  cases spin <;> fin_cases basis <;> cases a <;>
    simp [projection,actual_prob_eq_signed,Fintype.sum_prod_type,
      Fin.sum_univ_succ,kernel,signedProb,bitSign] <;> ring

/-- Construction for kernel Mean in the partial address born model. -/
def kernelMean (u v : Bool → ℂ) : ℝ :=
  ∑ r : Record,actualProb u v r.1 r.2.1 r.2.2*projection u v r

/-- Complete original `kernel_mean_eq_bell` guarantee for `PartialAddressBorn`; all source hypotheses and output obligations are retained. -/
theorem kernel_mean_eq_bell (u v : Bool → ℂ) : kernelMean u v=bellProbability u v := by
  simp only [kernelMean,projection_formula,Fintype.sum_prod_type,Fintype.sum_bool,Fin.sum_univ_succ]
  simp [actual_prob_eq_signed,signedProb,sectorMass,sectorBloch,bitSign,
    bellProbability,determinant,Complex.normSq_apply,Complex.mul_re,Complex.mul_im,
    Complex.sub_re,Complex.sub_im,Complex.conj_re,Complex.conj_im]
  ring

/-- Construction for square Projection in the partial address born model. -/
def squareProjection (u v : Bool → ℂ) (r : Record) : ℝ :=
  ∑ s : Record,actualProb u v s.1 s.2.1 s.2.2*(kernel r s)^2

/-- Complete original `square_projection_formula` guarantee for `PartialAddressBorn`; all source hypotheses and output obligations are retained. -/
theorem square_projection_formula (u v : Bool → ℂ) (r : Record) :
    squareProjection u v r=7*sectorMass u v (!r.1)-
      3*bitSign r.2.2*sectorBloch u v (!r.1) r.2.1/2 := by
  rcases r with ⟨spin,basis,a⟩
  cases spin <;> fin_cases basis <;> cases a <;>
    simp [squareProjection,actual_prob_eq_signed,Fintype.sum_prod_type,
      Fin.sum_univ_succ,kernel,signedProb,bitSign] <;> ring

/-- Construction for sector Product in the partial address born model. -/
def sectorProduct (u v : Bool → ℂ) : ℝ :=sectorMass u v false*sectorMass u v true

/-- Construction for kernel Second in the partial address born model. -/
def kernelSecond (u v : Bool → ℂ) : ℝ :=
  ∑ r : Record,actualProb u v r.1 r.2.1 r.2.2*squareProjection u v r

/-- Complete original `kernel_second_exact` guarantee for `PartialAddressBorn`; all source hypotheses and output obligations are retained. -/
theorem kernel_second_exact (u v : Bool → ℂ) :
    kernelSecond u v=13*sectorProduct u v+bellProbability u v := by
  simp only [kernelSecond,square_projection_formula,Fintype.sum_prod_type,Fintype.sum_bool,Fin.sum_univ_succ]
  simp [actual_prob_eq_signed,signedProb,sectorMass,sectorBloch,bitSign,sectorProduct,
    bellProbability,determinant,Complex.normSq_apply,Complex.mul_re,Complex.mul_im,
    Complex.sub_re,Complex.sub_im,Complex.conj_re,Complex.conj_im]
  ring

/-- Construction for projection Second in the partial address born model. -/
def projectionSecond (u v : Bool → ℂ) : ℝ :=
  ∑ r : Record,actualProb u v r.1 r.2.1 r.2.2*(projection u v r)^2

/-- Complete original `projection_second_homogeneous` guarantee for `PartialAddressBorn`; all source hypotheses and output obligations are retained. -/
theorem projection_second_homogeneous (u v : Bool → ℂ) :
    projectionSecond u v=(sectorMass u v false+sectorMass u v true)*
      (sectorProduct u v+bellProbability u v)/2 := by
  simp only [projectionSecond,projection_formula,Fintype.sum_prod_type,Fintype.sum_bool,Fin.sum_univ_succ]
  simp [actual_prob_eq_signed,signedProb,sectorMass,sectorBloch,bitSign,sectorProduct,
    bellProbability,determinant,Complex.normSq_apply,Complex.mul_re,Complex.mul_im,
    Complex.sub_re,Complex.sub_im,Complex.conj_re,Complex.conj_im]
  ring

/-- Complete original `projection_second_exact` guarantee for `PartialAddressBorn`; all source hypotheses and output obligations are retained. -/
theorem projection_second_exact (u v : Bool → ℂ) (hu : qubitMass u=1) (hv : qubitMass v=1) :
    projectionSecond u v=(sectorProduct u v+bellProbability u v)/2 := by
  rw [projection_second_homogeneous,sector_mass_total u v hu hv,one_mul]

/-- Complete original `kernel_symmetric` guarantee for `PartialAddressBorn`; all source hypotheses and output obligations are retained. -/
theorem kernel_symmetric (r s : Record) : kernel r s=kernel s r := by
  simp [kernel,eq_comm,mul_comm]

/-- Complete original `record_kernel_mean` guarantee for `PartialAddressBorn`; all source hypotheses and output obligations are retained. -/
theorem record_kernel_mean (u v : Bool → ℂ) (hu : qubitMass u=1) (hv : qubitMass v=1) :
    pairKernelMean (recordLaw u v hu hv) kernel=bellProbability u v := by
  change kernelMean u v=bellProbability u v
  exact kernel_mean_eq_bell u v

/-- Complete original `actual_ustatistic_unbiased` guarantee for `PartialAddressBorn`; all source hypotheses and output obligations are retained. -/
theorem actual_ustatistic_unbiased {n : ℕ} (u v : Bool → ℂ)
    (hu : qubitMass u=1) (hv : qubitMass v=1) (hn : 2 ≤ n) :
    (∑ ω : Fin n → Record,(recordLaw u v hu hv).probOf ω*orderedUStatistic kernel ω)=
      bellProbability u v := by
  rw [ordered_ustatistic_unbiased (recordLaw u v hu hv) kernel hn]
  exact record_kernel_mean u v hu hv

/-- Complete original `actual_projection_variance` guarantee for `PartialAddressBorn`; all source hypotheses and output obligations are retained. -/
theorem actual_projection_variance (u v : Bool → ℂ)
    (hu : qubitMass u=1) (hv : qubitMass v=1) :
    (recordLaw u v hu hv).variance (pairKernelProjection (recordLaw u v hu hv) kernel)=
      (sectorProduct u v+bellProbability u v)/2-(bellProbability u v)^2 := by
  rw [finite_variance_identity]
  change projectionSecond u v-(kernelMean u v)^2=_
  rw [projection_second_exact u v hu hv,kernel_mean_eq_bell]

/-- Complete original `actual_pair_variance` guarantee for `PartialAddressBorn`; all source hypotheses and output obligations are retained. -/
theorem actual_pair_variance (u v : Bool → ℂ)
    (hu : qubitMass u=1) (hv : qubitMass v=1) :
    (recordLaw u v hu hv).expect (fun x => (recordLaw u v hu hv).expect
      (fun y => (kernel x y-pairKernelMean (recordLaw u v hu hv) kernel)^2))=
      13*sectorProduct u v+bellProbability u v-(bellProbability u v)^2 := by
  rw [pair_variance_identity]
  change kernelSecond u v-(kernelMean u v)^2=_
  rw [kernel_second_exact,kernel_mean_eq_bell]

/-- Complete original `actual_ustatistic_variance` guarantee for `PartialAddressBorn`; all source hypotheses and output obligations are retained. -/
theorem actual_ustatistic_variance {n : ℕ} (u v : Bool → ℂ)
    (hu : qubitMass u=1) (hv : qubitMass v=1) (hn : 2 ≤ n) :
    (∑ ω : Fin n → Record,(recordLaw u v hu hv).probOf ω*
      (orderedUStatistic kernel ω-bellProbability u v)^2)=
      4*((n : ℝ)-2)/(n*(n-1) : ℕ)*
        ((sectorProduct u v+bellProbability u v)/2-(bellProbability u v)^2)+
      2/(n*(n-1) : ℕ)*(13*sectorProduct u v+bellProbability u v-(bellProbability u v)^2) := by
  have h := ordered_ustatistic_variance (recordLaw u v hu hv) kernel kernel_symmetric hn
  rw [actual_projection_variance,actual_pair_variance,record_kernel_mean] at h
  exact h

/-- Complete original `sector_mass_nonneg` guarantee for `PartialAddressBorn`; all source hypotheses and output obligations are retained. -/
theorem sector_mass_nonneg (u v : Bool → ℂ) (spin : Bool) : 0 ≤ sectorMass u v spin := by
  exact div_nonneg (add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)) (by norm_num)

/-- Complete original `sector_product_nonneg` guarantee for `PartialAddressBorn`; all source hypotheses and output obligations are retained. -/
theorem sector_product_nonneg (u v : Bool → ℂ) : 0 ≤ sectorProduct u v := by
  exact mul_nonneg (sector_mass_nonneg u v false) (sector_mass_nonneg u v true)

/-- Complete original `bell_le_twice_sector_product` guarantee for `PartialAddressBorn`; all source hypotheses and output obligations are retained. -/
theorem bell_le_twice_sector_product (u v : Bool → ℂ) :
    bellProbability u v ≤ 2*sectorProduct u v := by
  have heq : 2*sectorProduct u v-bellProbability u v=
      Complex.normSq (star (u false)*u true+star (v false)*v true)/2 := by
    simp [sectorProduct,sectorMass,bellProbability,determinant,Complex.normSq_apply,
      Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.add_im,Complex.sub_re,Complex.sub_im,
      Complex.conj_re,Complex.conj_im]
    ring
  have hn : 0 ≤ Complex.normSq (star (u false)*u true+star (v false)*v true)/2 := by
    exact div_nonneg (Complex.normSq_nonneg _) (by norm_num)
  linarith

/-- Complete original `sector_product_le_minority` guarantee for `PartialAddressBorn`; all source hypotheses and output obligations are retained. -/
theorem sector_product_le_minority (u v : Bool → ℂ) (hu : qubitMass u=1) (hv : qubitMass v=1) :
    sectorProduct u v ≤ sectorMass u v true := by
  have ht := sector_mass_total u v hu hv
  dsimp [sectorProduct]
  have hm := congrArg (fun x : ℝ => x*sectorMass u v true) ht
  nlinarith [sq_nonneg (sectorMass u v true)]

/-- Complete original `actual_ustatistic_variance_bound` guarantee for `PartialAddressBorn`; all source hypotheses and output obligations are retained. -/
theorem actual_ustatistic_variance_bound {n : ℕ} (u v : Bool → ℂ)
    (hu : qubitMass u=1) (hv : qubitMass v=1) (hn : 2 ≤ n) (q : ℝ)
    (hq : sectorMass u v true ≤ q) :
    (∑ ω : Fin n → Record,(recordLaw u v hu hv).probOf ω*
      (orderedUStatistic kernel ω-bellProbability u v)^2) ≤
      6*q/(n : ℝ)+30*q/(n*(n-1) : ℕ) := by
  have hq0 : 0 ≤ q := (sector_mass_nonneg u v true).trans hq
  have hnu : sectorProduct u v ≤ q := (sector_product_le_minority u v hu hv).trans hq
  have hmu := bell_le_twice_sector_product u v
  have hg : (recordLaw u v hu hv).variance
      (pairKernelProjection (recordLaw u v hu hv) kernel) ≤ 3*q/2 := by
    rw [actual_projection_variance]
    nlinarith [sq_nonneg (bellProbability u v)]
  have hD : (recordLaw u v hu hv).expect (fun r =>
      (recordLaw u v hu hv).expect (fun s => (kernel r s)^2)) ≤ 15*q := by
    change kernelSecond u v ≤ 15*q
    rw [kernel_second_exact]
    linarith
  have h := ordered_ustatistic_variance_bound (recordLaw u v hu hv) kernel
    kernel_symmetric hn (3*q/2) (15*q) (by positivity) hg hD
  rw [record_kernel_mean] at h
  convert h using 1
  ring

#print axioms native_tadj_at
#print axioms quarter_phase_square
#print axioms endpoint_program_counts
#print axioms endpoint_x_amplitude
#print axioms endpoint_y_amplitude
#print axioms edge_spin_filter
#print axioms edge_input_normalized
#print axioms actual_prob_eq_signed
#print axioms actual_prob_sector_sum
#print axioms recordLaw
#print axioms projection_formula
#print axioms kernel_mean_eq_bell
#print axioms square_projection_formula
#print axioms kernel_second_exact
#print axioms projection_second_exact
#print axioms actual_ustatistic_unbiased
#print axioms actual_ustatistic_variance
#print axioms actual_ustatistic_variance_bound
end
end Qatlib.Concepts.SpinorSampling.Adaptive.PartialAddress
