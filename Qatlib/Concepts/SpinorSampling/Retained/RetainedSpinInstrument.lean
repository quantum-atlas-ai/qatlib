/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.NativeRecords.NativeBornBridge

open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

/-!
# Retained Spin Instrument

Reading wire zero from the explicit two-bit pair returns its first bit.
-/

open Qatlib.Concepts.SpinorSampling.Model Qatlib.Concepts.SpinorSampling.NativeRecords

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

set_option autoImplicit false

namespace Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin
noncomputable section
open scoped BigOperators
open Qatlib ShiftCircuit NativeBridge

/-- Construction for pair Reg in the retained spin instrument model. -/
def pairReg (first second : Bool) : Reg 2 := fun i => if i=0 then first else second

/-- Reading wire zero from the explicit two-bit pair returns its first bit. -/
@[simp] theorem pair_reg_first (a b : Bool) : pairReg a b 0=a := by simp [pairReg]
/-- Reading wire one from the explicit two-bit pair returns its second bit. -/
@[simp] theorem pair_reg_second (a b : Bool) : pairReg a b 1=b := by simp [pairReg]

/-- Complete original `pair_reg_eta` guarantee for `RetainedSpinInstrument`; all source hypotheses and output obligations are retained. -/
theorem pair_reg_eta (x : Reg 2) : pairReg (x 0) (x 1)=x := by
  funext i
  fin_cases i <;> simp [pairReg]

/-- Construction for pair Equiv in the retained spin instrument model. -/
def pairEquiv : (Bool × Bool) ≃ Reg 2 where
  toFun p := pairReg p.1 p.2
  invFun x := (x 0,x 1)
  left_inv p := by cases p; simp
  right_inv := pair_reg_eta

/-- Complete original `pair_off_first` guarantee for `RetainedSpinInstrument`; all source hypotheses and output obligations are retained. -/
theorem pair_off_first (a b c d : Bool) :
    (∀ k : Fin 2, k≠0 → pairReg a b k=pairReg c d k) ↔ b=d := by
  constructor
  · intro h
    simpa using h 1 (by decide)
  · intro h k hk
    fin_cases k
    · exact (hk rfl).elim
    · simpa using h

/-- Complete original `pair_update_second` guarantee for `RetainedSpinInstrument`; all source hypotheses and output obligations are retained. -/
theorem pair_update_second (a b c : Bool) :
    Function.update (pairReg a b) 1 c=pairReg a c := by
  funext i
  fin_cases i <;> simp [pairReg]

/-- Construction for pair Input in the retained spin instrument model. -/
def pairInput (u v : Bool → ℂ) : QState (Reg 2) := fun x => u (x 0)*v (x 1)

/-- Construction for bell Word in the retained spin instrument model. -/
def bellWord : List (MeasurementGate 2) := [.native (.cx 0 1),.native (.h 0)]
/-- Construction for bell Program in the retained spin instrument model. -/
def bellProgram : Circuit (Reg 2) := measurementProgram bellWord
/-- Construction for swap Word in the retained spin instrument model. -/
def swapWord : List (MeasurementGate 2) :=
  [.native (.cx 0 1),.native (.cx 1 0),.native (.cx 0 1)]
/-- Construction for swap Program in the retained spin instrument model. -/
def swapProgram : Circuit (Reg 2) := measurementProgram swapWord

/-- Complete original `bell_program_counts` guarantee for `RetainedSpinInstrument`; all source hypotheses and output obligations are retained. -/
theorem bell_program_counts : QueryCount bellProgram=0 ∧ GateCount bellProgram=2 := by
  simpa [bellProgram,bellWord] using measurement_program_counts bellWord

/-- Complete original `swap_program_counts` guarantee for `RetainedSpinInstrument`; all source hypotheses and output obligations are retained. -/
theorem swap_program_counts : QueryCount swapProgram=0 ∧ GateCount swapProgram=3 := by
  simpa [swapProgram,swapWord] using measurement_program_counts swapWord

/-- Complete original `bell_program_unitary` guarantee for `RetainedSpinInstrument`; all source hypotheses and output obligations are retained. -/
theorem bell_program_unitary : IsUnitaryCircuit bellProgram := by
  apply (local_reflection_gate_support_unitarity_counts 2
    (bellWord.map measurementMatrix) ?_).1
  intro g hg
  simp [bellWord,measurementMatrix,nativeMatrix] at hg
  rcases hg with rfl | rfl
  · norm_num [reflectionGateLegal]
  · exact hadamard_unitary

/-- Complete original `swap_program_unitary` guarantee for `RetainedSpinInstrument`; all source hypotheses and output obligations are retained. -/
theorem swap_program_unitary : IsUnitaryCircuit swapProgram := by
  apply (local_reflection_gate_support_unitarity_counts 2
    (swapWord.map measurementMatrix) ?_).1
  intro g hg
  simp [swapWord,measurementMatrix,nativeMatrix] at hg
  rcases hg with rfl | rfl | rfl
  · norm_num [reflectionGateLegal]
  · norm_num [reflectionGateLegal]
  · norm_num [reflectionGateLegal]

/-- Complete original `native_cnot_at` guarantee for `RetainedSpinInstrument`; all source hypotheses and output obligations are retained. -/
theorem native_cnot_at (f : QState (Reg 2)) (a b : Bool) :
    ApplyGate (cnotGate 2 0 1) f (pairReg a b)=f (pairReg a (b ^^ a)) := by
  rw [cnotGate,applyGate_permMatrix (cnotUpdate_involutive 2 0 1 (by decide))]
  simp only [pair_reg_first,pair_reg_second,pair_update_second]

/-- Complete original `native_h_at` guarantee for `RetainedSpinInstrument`; all source hypotheses and output obligations are retained. -/
theorem native_h_at (f : QState (Reg 2)) (a b : Bool) :
    ApplyGate (wireGate 2 0 Hadamard) f (pairReg a b)=
      (f (pairReg false b)+(if a then (-1 : ℂ) else 1)*f (pairReg true b))/
        (Real.sqrt 2 : ℂ) := by
  let g : Reg 2 → ℂ := fun y => wireGate 2 0 Hadamard (pairReg a b) y*f y
  change (∑ y : Reg 2,g y)=_
  rw [← Fintype.sum_equiv pairEquiv (fun p => g (pairEquiv p)) g (fun _ => rfl)]
  simp only [Fintype.sum_prod_type,Fintype.sum_bool]
  cases a <;> cases b <;>
    simp [g,pairEquiv,wireGate_apply,Hadamard,div_eq_mul_inv] <;> ring

/-- Complete original `bell_program_amplitude` guarantee for `RetainedSpinInstrument`; all source hypotheses and output obligations are retained. -/
theorem bell_program_amplitude (u v : Bool → ℂ) (first second : Bool) :
    Run (1 : Matrix (Reg 2) (Reg 2) ℂ) bellProgram (pairInput u v)
        (pairReg first second)=
      (u false*v second+(if first then (-1 : ℂ) else 1)*u true*v (!second))/
        (Real.sqrt 2 : ℂ) := by
  change ApplyGate (wireGate 2 0 Hadamard)
    (ApplyGate (cnotGate 2 0 1) (pairInput u v)) (pairReg first second)=_
  rw [native_h_at,native_cnot_at,native_cnot_at]
  simp [pairInput]

/-- Complete original `swap_program_amplitude` guarantee for `RetainedSpinInstrument`; all source hypotheses and output obligations are retained. -/
theorem swap_program_amplitude (f : QState (Reg 2)) (a b : Bool) :
    Run (1 : Matrix (Reg 2) (Reg 2) ℂ) swapProgram f (pairReg a b)=f (pairReg b a) := by
  change ApplyGate (cnotGate 2 0 1) (ApplyGate (cnotGate 2 1 0)
    (ApplyGate (cnotGate 2 0 1) f)) (pairReg a b)=_
  rw [native_cnot_at]
  rw [cnotGate,applyGate_permMatrix (cnotUpdate_involutive 2 1 0 (by decide))]
  have hupdate : Function.update (pairReg a (b ^^ a)) 0 (a ^^ (b ^^ a))=
      pairReg (a ^^ (b ^^ a)) (b ^^ a) := by
    funext i
    fin_cases i <;> simp [pairReg]
  simp only [pair_reg_first,pair_reg_second,hupdate]
  rw [native_cnot_at]
  cases a <;> cases b <;> rfl

/-- Complete original `swap_empty_memory` guarantee for `RetainedSpinInstrument`; all source hypotheses and output obligations are retained. -/
theorem swap_empty_memory (u : Bool → ℂ) :
    Run (1 : Matrix (Reg 2) (Reg 2) ℂ) swapProgram (pairInput u (Ket false))=
      pairInput (Ket false) u := by
  funext x
  rw [← pair_reg_eta x,swap_program_amplitude]
  simp [pairInput,mul_comm]

/-- Construction for determinant in the retained spin instrument model. -/
def determinant (u v : Bool → ℂ) : ℂ := u false*v true-u true*v false
/-- Construction for overlap in the retained spin instrument model. -/
def overlap (u v : Bool → ℂ) : ℂ :=
  star (u false)*v false+star (u true)*v true
/-- Construction for qubit Mass in the retained spin instrument model. -/
def qubitMass (u : Bool → ℂ) : ℝ := Complex.normSq (u false)+Complex.normSq (u true)
/-- Construction for bell Probability in the retained spin instrument model. -/
def bellProbability (u v : Bool → ℂ) : ℝ := Complex.normSq (determinant u v)/2

/-- Complete original `determinant_overlap_identity` guarantee for `RetainedSpinInstrument`; all source hypotheses and output obligations are retained. -/
theorem determinant_overlap_identity (u v : Bool → ℂ) :
    Complex.normSq (determinant u v)+Complex.normSq (overlap u v)=qubitMass u*qubitMass v := by
  simp [determinant,overlap,qubitMass,Complex.normSq_apply,Complex.mul_re,
    Complex.mul_im,Complex.sub_re,Complex.sub_im,Complex.add_re,Complex.add_im,
    Complex.conj_re,Complex.conj_im]
  ring

/-- Complete original `bell_probability_eq_overlap` guarantee for `RetainedSpinInstrument`; all source hypotheses and output obligations are retained. -/
theorem bell_probability_eq_overlap (u v : Bool → ℂ)
    (hu : qubitMass u=1) (hv : qubitMass v=1) :
    bellProbability u v=(1-Complex.normSq (overlap u v))/2 := by
  have h := determinant_overlap_identity u v
  rw [hu,hv] at h
  dsimp [bellProbability]
  linarith

/-- Complete original `bell_probability_range` guarantee for `RetainedSpinInstrument`; all source hypotheses and output obligations are retained. -/
theorem bell_probability_range (u v : Bool → ℂ)
    (hu : qubitMass u=1) (hv : qubitMass v=1) :
    0≤bellProbability u v ∧ bellProbability u v≤1/2 := by
  constructor
  · exact div_nonneg (Complex.normSq_nonneg _) (by norm_num)
  · rw [bell_probability_eq_overlap u v hu hv]
    linarith [Complex.normSq_nonneg (overlap u v)]

/-- Complete original `bell_program_hit_probability` guarantee for `RetainedSpinInstrument`; all source hypotheses and output obligations are retained. -/
theorem bell_program_hit_probability (u v : Bool → ℂ) :
    BornProb (Run (1 : Matrix (Reg 2) (Reg 2) ℂ) bellProgram (pairInput u v))
      (pairReg true true)=bellProbability u v := by
  unfold BornProb
  rw [bell_program_amplitude,Complex.sq_norm,Complex.normSq_div]
  simp [bellProbability,determinant,Complex.normSq_ofReal,Real.mul_self_sqrt,sub_eq_add_neg]

/-- Complete original `pair_input_normalized` guarantee for `RetainedSpinInstrument`; all source hypotheses and output obligations are retained. -/
theorem pair_input_normalized (u v : Bool → ℂ)
    (hu : qubitMass u=1) (hv : qubitMass v=1) : Normalized (pairInput u v) := by
  unfold Normalized
  rw [← Fintype.sum_equiv pairEquiv
    (fun p => ‖pairInput u v (pairEquiv p)‖^2) (fun r => ‖pairInput u v r‖^2) (fun _ => rfl)]
  simp only [Fintype.sum_prod_type,Fintype.sum_bool,Complex.sq_norm]
  dsimp only [pairEquiv,pairInput,pairReg]
  simp only [Complex.normSq_mul]
  change Complex.normSq (u true)*Complex.normSq (v true)+
    Complex.normSq (u true)*Complex.normSq (v false)+
    (Complex.normSq (u false)*Complex.normSq (v true)+
    Complex.normSq (u false)*Complex.normSq (v false))=1
  calc
    _ = qubitMass u*qubitMass v := by dsimp [qubitMass]; ring
    _ = 1 := by rw [hu,hv]; norm_num

/-- Construction for bell Outcome Law in the retained spin instrument model. -/
def bellOutcomeLaw (u v : Bool → ℂ) (hu : qubitMass u=1) (hv : qubitMass v=1) :
    FinDist (Reg 2) where
  prob r := BornProb (Run (1 : Matrix (Reg 2) (Reg 2) ℂ) bellProgram (pairInput u v)) r
  nonneg r := sq_nonneg _
  sum_one := bell_program_unitary.normalized_run (by simp)
    (pair_input_normalized u v hu hv)

/-- Construction for is Bell Hit in the retained spin instrument model. -/
def isBellHit (r : Reg 2) : Bool := r 0 && r 1

/-- Complete original `is_bell_hit_iff` guarantee for `RetainedSpinInstrument`; all source hypotheses and output obligations are retained. -/
theorem is_bell_hit_iff (r : Reg 2) : isBellHit r=true ↔ r=pairReg true true := by
  constructor
  · intro h
    have hbits : r 0=true ∧ r 1=true := by simpa only [isBellHit,Bool.and_eq_true] using h
    rw [← pair_reg_eta r,hbits.1,hbits.2]
  · rintro rfl
    rfl

/-- This is the actual pushforward of the full normalized native Born law. -/
def bellEventLaw (u v : Bool → ℂ) (hu : qubitMass u=1) (hv : qubitMass v=1) : FinDist Bool where
  prob hit := ∑ r : Reg 2, if isBellHit r=hit then (bellOutcomeLaw u v hu hv).prob r else 0
  nonneg hit := Finset.sum_nonneg fun r _ => by
    split_ifs
    · exact (bellOutcomeLaw u v hu hv).nonneg r
    · exact le_refl _
  sum_one := by
    rw [Finset.sum_comm]
    calc
      _ = ∑ r : Reg 2,(bellOutcomeLaw u v hu hv).prob r := by
        apply Finset.sum_congr rfl
        intro r _
        cases isBellHit r <;> simp
      _ = 1 := (bellOutcomeLaw u v hu hv).sum_one

/-- Complete original `bell_event_law_hit` guarantee for `RetainedSpinInstrument`; all source hypotheses and output obligations are retained. -/
theorem bell_event_law_hit (u v : Bool → ℂ) (hu : qubitMass u=1) (hv : qubitMass v=1) :
    (bellEventLaw u v hu hv).prob true=bellProbability u v := by
  change (∑ r : Reg 2,if isBellHit r=true then (bellOutcomeLaw u v hu hv).prob r else 0)=_
  simp_rw [is_bell_hit_iff]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ,ite_true]
  exact bell_program_hit_probability u v

/-- Construction for qubit Bloch in the retained spin instrument model. -/
def qubitBloch (u : Bool → ℂ) : Fin 3 → ℝ := fun i =>
  pauliField (fun _ : Unit => (u false).re) (fun _ => (u false).im)
    (fun _ => (u true).re) (fun _ => (u true).im) i ()

/-- Complete original `bloch_distance_identity` guarantee for `RetainedSpinInstrument`; all source hypotheses and output obligations are retained. -/
theorem bloch_distance_identity (u v : Bool → ℂ) :
    (∑ i : Fin 3,(qubitBloch u i-qubitBloch v i)^2)=
      (qubitMass u-qubitMass v)^2+4*Complex.normSq (determinant u v) := by
  simp [qubitBloch,pauliField,Fin.sum_univ_succ,qubitMass,determinant,
    Complex.normSq_apply,Complex.mul_re,Complex.mul_im,Complex.sub_re,Complex.sub_im]
  ring

/-- Complete original `bell_probability_eq_bloch_distance` guarantee for `RetainedSpinInstrument`; all source hypotheses and output obligations are retained. -/
theorem bell_probability_eq_bloch_distance (u v : Bool → ℂ)
    (hu : qubitMass u=1) (hv : qubitMass v=1) :
    bellProbability u v=(∑ i : Fin 3,(qubitBloch u i-qubitBloch v i)^2)/8 := by
  rw [bloch_distance_identity,hu,hv]
  simp [bellProbability]
  ring

/-- Construction for project Address in the retained spin instrument model. -/
def projectAddress {S : Type*} [DecidableEq S] (f : Bool → S → ℂ) (x : S) : Bool → S → ℂ :=
  fun spin y => if y=x then f spin y else 0

/-- Complete original `address_projection_selected` guarantee for `RetainedSpinInstrument`; all source hypotheses and output obligations are retained. -/
theorem address_projection_selected {S : Type*} [DecidableEq S]
    (f : Bool → S → ℂ) (x : S) : (fun spin => projectAddress f x spin x)=fun spin => f spin x := by
  funext spin
  simp [projectAddress]

/-- Complete original `projected_spin_mass` guarantee for `RetainedSpinInstrument`; all source hypotheses and output obligations are retained. -/
theorem projected_spin_mass {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    (a b c k : S → ℝ) (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1) (x : S) :
    (∑ y : S, ∑ spin : Bool, Complex.normSq
      (projectAddress (suppliedSpinState a b c k) x spin y))=1/(Fintype.card S : ℝ) := by
  have hsite : qubitMass (complexSpinor a b c k x)=1 := by
    simpa [qubitMass,complexSpinor,Complex.normSq_apply,pow_two,
      add_assoc,add_left_comm,add_comm] using hz x
  rw [Finset.sum_eq_single x]
  · simp only [projectAddress,ite_true,suppliedSpinState,Complex.normSq_div,Complex.normSq_ofReal,
      Real.mul_self_sqrt (Nat.cast_nonneg (Fintype.card S))]
    rw [← Finset.sum_div]
    have hs : (∑ spin : Bool,Complex.normSq (complexSpinor a b c k x spin))=1 := by
      simpa only [Fintype.sum_bool,qubitMass,add_comm] using hsite
    rw [hs]
  · intro y _ hy
    simp [projectAddress,hy]
  · simp

/-- Complete original `retained_spin_amplitude` guarantee for `RetainedSpinInstrument`; all source hypotheses and output obligations are retained. -/
theorem retained_spin_amplitude {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    (a b c k : S → ℝ) (x : S) :
    (fun spin => (Real.sqrt (Fintype.card S : ℝ) : ℂ)*
      projectAddress (suppliedSpinState a b c k) x spin x)=complexSpinor a b c k x := by
  have hM : (Fintype.card S : ℝ)>0 := by exact_mod_cast Fintype.card_pos
  have hroot : (Real.sqrt (Fintype.card S : ℝ) : ℂ)≠0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hM).ne'
  funext spin
  simp only [projectAddress,ite_true,suppliedSpinState]
  field_simp

/-- Complete original `complex_spinor_mass` guarantee for `RetainedSpinInstrument`; all source hypotheses and output obligations are retained. -/
theorem complex_spinor_mass {S : Type*} (a b c k : S → ℝ)
    (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1) (x : S) :
    qubitMass (complexSpinor a b c k x)=1 := by
  simpa [qubitMass,complexSpinor,Complex.normSq_apply,pow_two,
    add_assoc,add_left_comm,add_comm] using hz x

/-- Complete original `complex_spinor_bloch` guarantee for `RetainedSpinInstrument`; all source hypotheses and output obligations are retained. -/
theorem complex_spinor_bloch {S : Type*} (a b c k : S → ℝ) (x : S) :
    qubitBloch (complexSpinor a b c k x)=fun i => pauliField a b c k i x := by
  funext i
  simp [qubitBloch,complexSpinor,pauliField]

/-- Complete original `fresh_captures_joint_hit` guarantee for `RetainedSpinInstrument`; all source hypotheses and output obligations are retained. -/
theorem fresh_captures_joint_hit {S : Type*} [Fintype S] [Nonempty S]
    (a b c k : S → ℝ) (x y : S) :
    BornProb (Run (1 : Matrix (Reg 2) (Reg 2) ℂ) bellProgram
      (pairInput (fun spin => suppliedSpinState a b c k spin x)
        (fun spin => suppliedSpinState a b c k spin y))) (pairReg true true)=
      bellProbability (complexSpinor a b c k x) (complexSpinor a b c k y)/
        (Fintype.card S : ℝ)^2 := by
  rw [bell_program_hit_probability]
  have hM : (Fintype.card S : ℝ)>0 := by exact_mod_cast Fintype.card_pos
  have hs : (Real.sqrt (Fintype.card S : ℝ) : ℂ)^2=(Fintype.card S : ℂ) := by
    exact_mod_cast Real.sq_sqrt hM.le
  have hdet : determinant (fun spin => suppliedSpinState a b c k spin x)
      (fun spin => suppliedSpinState a b c k spin y)=
      determinant (complexSpinor a b c k x) (complexSpinor a b c k y)/
        (Fintype.card S : ℂ) := by
    simp only [determinant,suppliedSpinState]
    rw [div_mul_div_comm,div_mul_div_comm,← sub_div,← pow_two,hs]
  simp only [bellProbability,hdet,Complex.normSq_div,Complex.normSq_natCast]
  ring

end
end Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin

#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.bell_program_counts
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.swap_program_counts
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.bell_program_unitary
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.swap_program_unitary
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.bell_program_amplitude
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.swap_empty_memory
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.bell_program_hit_probability
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.pair_input_normalized
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.bellOutcomeLaw
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.bell_event_law_hit
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.bell_probability_range
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.bell_probability_eq_overlap
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.bell_probability_eq_bloch_distance
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.projected_spin_mass
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.retained_spin_amplitude
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.complex_spinor_bloch
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.fresh_captures_joint_hit
