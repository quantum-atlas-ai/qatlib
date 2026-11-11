/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.Adaptive.PartialAddressPilotVector

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

/-!
Chronological H/T/Tdg words, the actual projector-axis recursion, and the
literal nonnegative/squared-overlap acceptance predicate of the reference
compiler. The axis has unit length and acceptance implies its stated overlap
and minority-risk bounds. Actual Frozen H/T matrices on the spin wire run the
same amplitude recursion on both endpoints, preserve their Bell target, and
charge one native gate per word letter. The real acceptance predicate is not
an executable rational checker or a compiler termination/time theorem;
conditioning on random training and the complete trained main remain separate.
-/

open Qatlib.Concepts.SpinorSampling.Matching Qatlib.Concepts.SpinorSampling.Model Qatlib.Concepts.SpinorSampling.NativeRecords Qatlib.Concepts.SpinorSampling.Retained
set_option autoImplicit false
open scoped BigOperators
namespace Qatlib.Concepts.SpinorSampling.Adaptive.PartialAddress.FiniteAxisWord
noncomputable section
open AxisRisk RetainedSpin NativeBridge ShiftCircuit

/-- Constructors for Gate in the partial address finite axis word model. -/
inductive Gate where
  | h | t | tdg
  deriving DecidableEq, Repr

/-- Construction for half Root in the partial address finite axis word model. -/
def halfRoot : ℝ := Real.sqrt 2/2

/-- Complete original `half_square` guarantee for `PartialAddressFiniteAxisWord`; all source hypotheses and output obligations are retained. -/
theorem half_square : halfRoot^2=1/2 := by
  unfold halfRoot
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- Construction for rotate in the partial address finite axis word model. -/
def rotate (g : Gate) (a : Fin 3 → ℝ) : Fin 3 → ℝ :=
  match g with
  | .h => ![a 2,-a 1,a 0]
  | .t => ![halfRoot*(a 0+a 1),halfRoot*(a 1-a 0),a 2]
  | .tdg => ![halfRoot*(a 0-a 1),halfRoot*(a 0+a 1),a 2]

/-- Construction for word Axis in the partial address finite axis word model. -/
def wordAxis : List Gate → Fin 3 → ℝ
  | [] => ![0,0,1]
  | g::gs => rotate g (wordAxis gs)

/-- Complete original `rotate_norm` guarantee for `PartialAddressFiniteAxisWord`; all source hypotheses and output obligations are retained. -/
theorem rotate_norm (g : Gate) (a : Fin 3 → ℝ) : dot (rotate g a) (rotate g a)=dot a a := by
  cases g <;> simp [rotate,dot,Fin.sum_univ_succ]
  · ring
  · linear_combination 2*((a 0)^2+(a 1)^2)*half_square
  · linear_combination 2*((a 0)^2+(a 1)^2)*half_square

/-- Complete original `word_axis_unit` guarantee for `PartialAddressFiniteAxisWord`; all source hypotheses and output obligations are retained. -/
theorem word_axis_unit (gs : List Gate) : dot (wordAxis gs) (wordAxis gs)=1 := by
  induction gs with
  | nil => simp [wordAxis,dot,Fin.sum_univ_succ]
  | cons g gs ih => rw [wordAxis,rotate_norm,ih]

/-- Construction for accepted in the partial address finite axis word model. -/
def accepted (s : Fin 3 → ℝ) (τ : ℝ) (gs : List Gate) : Prop :=
  if length s=0 then wordAxis gs=wordAxis [] else
    0 ≤ dot s (wordAxis gs) ∧ (1-τ/64)^2*dot s s ≤ (dot s (wordAxis gs))^2

/-- Complete original `accepted_overlap` guarantee for `PartialAddressFiniteAxisWord`; all source hypotheses and output obligations are retained. -/
theorem accepted_overlap (s : Fin 3 → ℝ) (τ : ℝ) (gs : List Gate)
    (hτ0 : 0<τ) (hτ1 : τ ≤ 1/2) (hc : accepted s τ gs) :
    1-dot (axis s) (wordAxis gs) ≤ τ/64 := by
  by_cases hL : length s=0
  · have hword : wordAxis gs=wordAxis [] := by simpa only [accepted,ite_eq_left hL] using hc
    have ha : axis s=wordAxis [] := by funext i; fin_cases i <;> simp [axis,hL,wordAxis]
    rw [ha,hword,word_axis_unit]
    linarith
  · have hLp : 0<length s := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hL)
    have hh : 0 ≤ dot s (wordAxis gs) ∧ (1-τ/64)^2*dot s s ≤ (dot s (wordAxis gs))^2 := by
      simpa only [accepted,ite_eq_right hL] using hc
    have ht : 0 ≤ 1-τ/64 := by linarith
    have hscaled : (1-τ/64)*length s ≤ dot s (wordAxis gs) := by
      have hsq : ((1-τ/64)*length s)^2 ≤ (dot s (wordAxis gs))^2 := by
        rw [mul_pow,length_sq]
        exact hh.2
      nlinarith [mul_nonneg ht hLp.le]
    rw [dot_length s (wordAxis gs)] at hscaled
    have hclose : 1-τ/64 ≤ dot (axis s) (wordAxis gs) :=
      le_of_mul_le_mul_left (by simpa only [mul_comm] using hscaled) hLp
    linarith

/-- Complete original `accepted_axis_risk` guarantee for `PartialAddressFiniteAxisWord`; all source hypotheses and output obligations are retained. -/
theorem accepted_axis_risk (r s : Fin 3 → ℝ) (τ : ℝ) (gs : List Gate)
    (hr : length r ≤ 1) (hτ0 : 0<τ) (hτ1 : τ ≤ 1/2) (hc : accepted s τ gs) :
    (1-dot r (wordAxis gs))/2 ≤ 8*((1-length r)/2)+4*distSq s r+τ/32 := by
  apply compiled_axis_risk r s (wordAxis gs) τ hr (word_axis_unit gs)
  have h := accepted_overlap s τ gs hτ0 hτ1 hc
  linarith

/-- Construction for spin Step in the partial address finite axis word model. -/
def spinStep (g : Gate) (u : Bool → ℂ) : Bool → ℂ :=
  match g with
  | .h => fun b => (halfRoot : ℂ)*(u false+(if b then -1 else 1)*u true)
  | .t => fun b => if b then ((halfRoot : ℂ)+(halfRoot : ℂ)*Complex.I)*u true else u false
  | .tdg => fun b => if b then ((halfRoot : ℂ)-(halfRoot : ℂ)*Complex.I)*u true else u false

/-- Construction for run Spin in the partial address finite axis word model. -/
def runSpin : List Gate → (Bool → ℂ) → Bool → ℂ
  | [],u => u
  | g::gs,u => runSpin gs (spinStep g u)

/-- Complete original `spin_step_mass` guarantee for `PartialAddressFiniteAxisWord`; all source hypotheses and output obligations are retained. -/
theorem spin_step_mass (g : Gate) (u : Bool → ℂ) : qubitMass (spinStep g u)=qubitMass u := by
  cases g <;> simp [spinStep,qubitMass,Complex.normSq_apply,Complex.mul_re,Complex.mul_im]
  all_goals ring_nf
  all_goals rw [half_square]
  all_goals ring

/-- Complete original `spin_step_dot` guarantee for `PartialAddressFiniteAxisWord`; all source hypotheses and output obligations are retained. -/
theorem spin_step_dot (g : Gate) (u : Bool → ℂ) (a : Fin 3 → ℝ) :
    dot (qubitBloch (spinStep g u)) a=dot (qubitBloch u) (rotate g a) := by
  cases g <;> simp [dot,qubitBloch,pauliField,spinStep,rotate,Fin.sum_univ_succ,
    Complex.mul_re,Complex.mul_im]
  all_goals ring_nf
  all_goals rw [half_square]
  all_goals ring

/-- Complete original `run_spin_mass` guarantee for `PartialAddressFiniteAxisWord`; all source hypotheses and output obligations are retained. -/
theorem run_spin_mass (gs : List Gate) (u : Bool → ℂ) : qubitMass (runSpin gs u)=qubitMass u := by
  induction gs generalizing u with
  | nil => rfl
  | cons g gs ih => rw [runSpin,ih,spin_step_mass]

/-- Complete original `run_spin_z` guarantee for `PartialAddressFiniteAxisWord`; all source hypotheses and output obligations are retained. -/
theorem run_spin_z (gs : List Gate) (u : Bool → ℂ) :
    qubitBloch (runSpin gs u) 2=dot (qubitBloch u) (wordAxis gs) := by
  induction gs generalizing u with
  | nil => simp [runSpin,wordAxis,dot,Fin.sum_univ_succ]
  | cons g gs ih => rw [runSpin,ih,wordAxis,spin_step_dot]

/-- Complete original `minority_probability` guarantee for `PartialAddressFiniteAxisWord`; all source hypotheses and output obligations are retained. -/
theorem minority_probability (gs : List Gate) (u : Bool → ℂ) (hu : qubitMass u=1) :
    Complex.normSq (runSpin gs u true)=(1-dot (qubitBloch u) (wordAxis gs))/2 := by
  have hm := run_spin_mass gs u
  have hz := run_spin_z gs u
  rw [hu] at hm
  change (runSpin gs u false).re^2+(runSpin gs u false).im^2-
    (runSpin gs u true).re^2-(runSpin gs u true).im^2=dot (qubitBloch u) (wordAxis gs) at hz
  simp only [qubitMass,Complex.normSq_apply] at hm ⊢
  nlinarith

/-- Construction for gate Matrix in the partial address finite axis word model. -/
def gateMatrix : Gate → Matrix Bool Bool ℂ
  | .h => Hadamard
  | .t => tGate
  | .tdg => tGateAdj

/-- Complete original `half_inv` guarantee for `PartialAddressFiniteAxisWord`; all source hypotheses and output obligations are retained. -/
theorem half_inv : (Real.sqrt 2 : ℂ)⁻¹=(halfRoot : ℂ) := by
  have hr : (Real.sqrt 2)⁻¹=halfRoot := by
    have hne : Real.sqrt 2 ≠ 0 := by positivity
    unfold halfRoot
    field_simp
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  exact_mod_cast hr

/-- Complete original `spin_step_matrix` guarantee for `PartialAddressFiniteAxisWord`; all source hypotheses and output obligations are retained. -/
theorem spin_step_matrix (g : Gate) (u : Bool → ℂ) : ApplyGate (gateMatrix g) u=spinStep g u := by
  have hp : Complex.exp (((Real.pi/4 : ℝ) : ℂ)*Complex.I)=
      (halfRoot : ℂ)+(halfRoot : ℂ)*Complex.I := by
    apply Complex.ext <;> simp [halfRoot,Complex.exp_re,Complex.exp_im,
      Complex.mul_re,Complex.mul_im,Real.cos_pi_div_four,Real.sin_pi_div_four]
  have hm : Complex.exp (((-(Real.pi/4) : ℝ) : ℂ)*Complex.I)=
      (halfRoot : ℂ)-(halfRoot : ℂ)*Complex.I := by
    apply Complex.ext <;> simp [halfRoot,Complex.exp_re,Complex.exp_im,
      Complex.mul_re,Complex.mul_im,Real.cos_neg,Real.sin_neg,
      Real.cos_pi_div_four,Real.sin_pi_div_four]
  funext b
  change (∑ a : Bool,gateMatrix g b a*u a)=_
  cases g <;> cases b <;>
    simp [gateMatrix,Hadamard,tGate,tGateAdj,Rz,Matrix.diagonal_apply,
      spinStep,half_inv] <;> ring_nf
  · left
    convert hp using 1 <;> push_cast <;> ring
  · left
    convert hm using 1 <;> push_cast <;> ring

/-- Construction for native Gate in the partial address finite axis word model. -/
def nativeGate (g : Gate) : NativeGate (Fin 2) :=
  match g with
  | .h => .h 1
  | .t => .t 1
  | .tdg => .tdg 1

/-- Construction for program in the partial address finite axis word model. -/
def program (gs : List Gate) : Circuit (Reg 2) :=
  measurementProgram (gs.map (fun g => MeasurementGate.native (nativeGate g)))

/-- Complete original `program_counts` guarantee for `PartialAddressFiniteAxisWord`; all source hypotheses and output obligations are retained. -/
theorem program_counts (gs : List Gate) : QueryCount (program gs)=0 ∧ GateCount (program gs)=gs.length := by
  simpa only [program,List.length_map] using
    measurement_program_counts (gs.map (fun g => MeasurementGate.native (nativeGate g)))

/-- Complete original `wire_spin_edge` guarantee for `PartialAddressFiniteAxisWord`; all source hypotheses and output obligations are retained. -/
theorem wire_spin_edge (U : Matrix Bool Bool ℂ) (u v : Bool → ℂ) :
    ApplyGate (wireGate 2 1 U) (edgeInput u v)=edgeInput (ApplyGate U u) (ApplyGate U v) := by
  funext x
  obtain ⟨⟨a,b⟩,rfl⟩ := pairEquiv.surjective x
  let g : Reg 2 → ℂ := fun y => wireGate 2 1 U (pairReg a b) y*edgeInput u v y
  change (∑ y : Reg 2,g y)=_
  rw [← Fintype.sum_equiv pairEquiv (fun p => g (pairEquiv p)) g (fun _ => rfl)]
  simp only [Fintype.sum_prod_type,Fintype.sum_bool]
  cases a <;> cases b <;>
    simp [g,pairEquiv,wireGate_apply,pairReg,edgeInput,ApplyGate,Matrix.mulVec,dotProduct] <;> ring

/-- Complete original `native_spin_step` guarantee for `PartialAddressFiniteAxisWord`; all source hypotheses and output obligations are retained. -/
theorem native_spin_step (g : Gate) (u v : Bool → ℂ) :
    ApplyGate (reflectionGateMatrix (nativeMatrix (nativeGate g))) (edgeInput u v)=
      edgeInput (spinStep g u) (spinStep g v) := by
  have hmat : reflectionGateMatrix (nativeMatrix (nativeGate g))=wireGate 2 1 (gateMatrix g) := by
    cases g <;> rfl
  rw [hmat,wire_spin_edge,spin_step_matrix,spin_step_matrix]

/-- Complete original `program_edge_run` guarantee for `PartialAddressFiniteAxisWord`; all source hypotheses and output obligations are retained. -/
theorem program_edge_run (gs : List Gate) (u v : Bool → ℂ) :
    Run (1 : Matrix (Reg 2) (Reg 2) ℂ) (program gs) (edgeInput u v)=
      edgeInput (runSpin gs u) (runSpin gs v) := by
  induction gs generalizing u v with
  | nil => simp [program,measurementProgram,reflectionCompile,runSpin]
  | cons g gs ih =>
    change Run (1 : Matrix (Reg 2) (Reg 2) ℂ) (program gs)
      (ApplyGate (reflectionGateMatrix (nativeMatrix (nativeGate g))) (edgeInput u v))=_
    rw [native_spin_step,ih]
    rfl

/-- Construction for determinant Factor in the partial address finite axis word model. -/
def determinantFactor (g : Gate) : ℂ :=
  match g with
  | .h => -1
  | .t => (halfRoot : ℂ)+(halfRoot : ℂ)*Complex.I
  | .tdg => (halfRoot : ℂ)-(halfRoot : ℂ)*Complex.I

/-- Complete original `determinant_step` guarantee for `PartialAddressFiniteAxisWord`; all source hypotheses and output obligations are retained. -/
theorem determinant_step (g : Gate) (u v : Bool → ℂ) :
    determinant (spinStep g u) (spinStep g v)=determinantFactor g*determinant u v := by
  have hc : (halfRoot : ℂ)^2=(1/2 : ℂ) := by
    have h := congrArg Complex.ofReal half_square
    push_cast at h
    exact h
  cases g <;> simp [determinant,spinStep,determinantFactor]
  all_goals ring_nf
  all_goals rw [hc]
  all_goals ring

/-- Complete original `determinant_factor_unit` guarantee for `PartialAddressFiniteAxisWord`; all source hypotheses and output obligations are retained. -/
theorem determinant_factor_unit (g : Gate) : Complex.normSq (determinantFactor g)=1 := by
  cases g <;> simp [determinantFactor,Complex.normSq_apply]
  all_goals nlinarith [half_square]

/-- Complete original `spin_step_bell` guarantee for `PartialAddressFiniteAxisWord`; all source hypotheses and output obligations are retained. -/
theorem spin_step_bell (g : Gate) (u v : Bool → ℂ) :
    bellProbability (spinStep g u) (spinStep g v)=bellProbability u v := by
  unfold bellProbability
  rw [determinant_step,Complex.normSq_mul,determinant_factor_unit,one_mul]

/-- Complete original `run_spin_bell` guarantee for `PartialAddressFiniteAxisWord`; all source hypotheses and output obligations are retained. -/
theorem run_spin_bell (gs : List Gate) (u v : Bool → ℂ) :
    bellProbability (runSpin gs u) (runSpin gs v)=bellProbability u v := by
  induction gs generalizing u v with
  | nil => rfl
  | cons g gs ih => simp only [runSpin,ih,spin_step_bell]

#print axioms half_square
#print axioms rotate_norm
#print axioms word_axis_unit
#print axioms accepted_overlap
#print axioms accepted_axis_risk
#print axioms spin_step_mass
#print axioms spin_step_dot
#print axioms run_spin_mass
#print axioms run_spin_z
#print axioms minority_probability
#print axioms half_inv
#print axioms spin_step_matrix
#print axioms program_counts
#print axioms wire_spin_edge
#print axioms native_spin_step
#print axioms program_edge_run
#print axioms determinant_step
#print axioms determinant_factor_unit
#print axioms spin_step_bell
#print axioms run_spin_bell
end
end Qatlib.Concepts.SpinorSampling.Adaptive.PartialAddress.FiniteAxisWord
