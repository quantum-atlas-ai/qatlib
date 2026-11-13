/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.QueryLowerBound.ScalarSignalAccess
import Qatlib.Concepts.QsvtCore.QueryLowerBound.ScalarSignalQueryBounds
import Qatlib.Concepts.QsvtCore.QueryLowerBound.SubroutineExpansion
import Qatlib.Concepts.LocalMachine.LocalTransport.ControlledQueryCircuit
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Scalar signal circuits and lower-bound examples

This module constructs explicit Chebyshev query words, their tensor lifts, and controlled
Hadamard readouts. It relates these circuits to scalar response lower bounds in the setting of
[GilyenSuLowWiebe2019].

The examples include a linear query lower bound for opposite responses and a constant-response
circuit illustrating the need for correctly oriented leakage estimates.

## Main statements

* `scalar_signal_chebyshev_actual_word`: Chebyshev response and exact query and gate counts.
* `scalar_signal_chebyshev_phase_readout_and_matching_lower_consumer`: Perfect phase readout and
  a matching linear lower estimate.
* `scalar_signal_printed_leakage_counterexample`: A zero-query constant-response example with a
  positive printed leakage expression.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.BlockEncoding.EncodingCore

open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

namespace Qatlib.Concepts.QsvtCore.QueryLowerBound
open Matrix Qatlib.Concepts.QueryWordCore.AdjointCircuits Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding
open scoped Classical BigOperators Matrix.Norms.L2Operator

/-- The word obtained by repeating a forward scalar-signal query followed by `PauliZ` exactly
`n` times. -/
noncomputable def signalChebyshevWord (n : ℕ) : List (AdjointStep Bool) :=
  repeatAdjointWord [.forward,.gate PauliZ] n

/-- The tensor lift of `signalChebyshevWord` to a trivial auxiliary register. -/
noncomputable def signalChebyshevUnitWord (n : ℕ) : List (AdjointStep (Bool×Unit)) :=
  (signalChebyshevWord n).map (fun c => match c with
    | .gate V => .gate (TensorGate V (1:Matrix Unit Unit ℂ))
    | .forward => .forward
    | .backward => .backward)

/-- The controlled Chebyshev word with Hadamard gates on the control before and after
evaluation. -/
noncomputable def signalChebyshevHadamardWord (n : ℕ) : List (AdjointStep (Bool×Bool)) :=
  [.gate (TensorGate Hadamard (1:Matrix Bool Bool ℂ))] ++
    compileControlled (signalChebyshevWord n) ++
    [.gate (TensorGate Hadamard (1:Matrix Bool Bool ℂ))]

/-- A single fixed gate given by the scalar signal at one half, with no oracle queries. -/
noncomputable def constantHalfSignalWord : List (AdjointStep (Bool×Unit)) :=
  [.gate (scalarSignalLift Unit (1/2))]

/-- The real planar rotation through angle `θ`, viewed as a complex matrix indexed by `Bool`. -/
private noncomputable def scalarRotation (θ : ℝ) : Matrix Bool Bool ℂ :=
  fun a b=>if a=b then (Real.cos θ : ℂ) else if a then (Real.sin θ : ℂ) else -(Real.sin θ : ℂ)

/-- Multiplication of scalar rotation matrices adds their angles. -/
private theorem scalarRotation_add (θ φ : ℝ) : scalarRotation θ*scalarRotation φ=scalarRotation (θ+φ) := by
  ext a b
  cases a <;> cases b <;> apply Complex.ext <;>
    simp [scalarRotation,Matrix.mul_apply,Real.cos_add,Real.sin_add,Complex.mul_re,Complex.mul_im] <;> ring

/-- The `n`th power of a scalar rotation is the rotation through `n * θ`. -/
private theorem scalarRotation_pow (θ : ℝ) (n : ℕ) : scalarRotation θ^n=scalarRotation ((n : ℝ)*θ) := by
  induction n with
  | zero => ext a b; cases a <;> cases b <;> simp [scalarRotation]
  | succ n ih =>
    rw [pow_succ,ih,scalarRotation_add]
    congr 1
    push_cast
    ring

/-- For `x` in `[-1, 1]`, multiplying its scalar signal reflection by `PauliZ` gives rotation
through `arccos x`. -/
private theorem scalarSignal_times_z (x : ℝ) (hx : x∈Set.Icc (-1) 1) :
    scalarSignalReflection x*PauliZ=scalarRotation (Real.arccos x) := by
  ext a b
  cases a <;> cases b <;>
    simp [scalarSignalReflection,PauliZ,Matrix.mul_apply,scalarRotation,
      Real.cos_arccos hx.1 hx.2,Real.sin_arccos]

/-- Evaluation commutes with tensoring every fixed gate of a word with the identity on `Unit`. -/
private theorem scalar_unit_lift_word (x : ℝ) (word : List (AdjointStep Bool)) :
    evaluate (scalarSignalLift Unit x) (word.map (fun c=>match c with
      | .gate V=>.gate (TensorGate V (1 : Matrix Unit Unit ℂ))
      | .forward=>.forward | .backward=>.backward)) =
    TensorGate (evaluate (scalarSignalReflection x) word) (1 : Matrix Unit Unit ℂ) := by
  induction word with
  | nil => simp [evaluate,tensorGate_one]
  | cons c cs ih =>
    simp only [scalarSignalLift] at ih
    cases c <;>
      simp [evaluate,instructionMatrix,ih,scalarSignalLift,tensorGate_mul,tensorGate_conjTranspose]

/-- The repeated signal word is well formed, uses `n` queries and `n` gates, and has top-left
entry `Tₙ(x)` for `x` in `[-1, 1]`. Its evaluation is the corresponding matrix power and
commutes with the trivial tensor lift. -/
theorem scalar_signal_chebyshev_actual_word : ∀ (n : ℕ) (x : ℝ), x ∈ Set.Icc (-1) 1 →
  WellFormedAdjointCircuit (signalChebyshevWord n) ∧
  adjointQueryCount (signalChebyshevWord n)=n ∧ adjointGateCount (signalChebyshevWord n)=n ∧
  evaluate (scalarSignalReflection x) (signalChebyshevWord n)=
    (scalarSignalReflection x*PauliZ)^n ∧
  evaluate (scalarSignalReflection x) (signalChebyshevWord n) false false=
    Complex.ofReal ((Polynomial.Chebyshev.T ℝ (n:ℤ)).eval x) ∧
  evaluate (scalarSignalLift Unit x) (signalChebyshevUnitWord n)=
    TensorGate (evaluate (scalarSignalReflection x) (signalChebyshevWord n))
      (1:Matrix Unit Unit ℂ) := by
  intro n x hx
  have hc := repeat_adjoint_word_semantics_cost (scalarSignalReflection x)
    ([.forward,.gate PauliZ] : List (AdjointStep Bool)) n
  have hbase : WellFormedAdjointCircuit ([.forward,.gate PauliZ] : List (AdjointStep Bool)) := by
    simp [WellFormedAdjointCircuit,pauliZ_unitary]
  have heval : evaluate (scalarSignalReflection x) (signalChebyshevWord n)=(scalarSignalReflection x*PauliZ)^n := by
    simpa only [signalChebyshevWord,evaluate,instructionMatrix,Matrix.mul_one] using hc.1
  refine ⟨hc.2.2.2 hbase,?_,?_,heval,?_,scalar_unit_lift_word x (signalChebyshevWord n)⟩
  · simpa [signalChebyshevWord,adjointQueryCount] using hc.2.1
  · simpa [signalChebyshevWord,adjointGateCount] using hc.2.2.1
  · rw [heval,scalarSignal_times_z x hx,scalarRotation_pow]
    have hT : (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval x=Real.cos ((n : ℝ)*Real.arccos x) := by
      simpa only [Real.cos_arccos hx.1 hx.2,Int.cast_natCast] using
          Polynomial.Chebyshev.T_real_cos (Real.arccos x) (n : ℤ)
    simp only [scalarRotation,if_true,hT]

/-- For `θ` in `[0, π]`, evaluating the Chebyshev word at `cos θ` gives rotation through `n *
θ`. -/
private theorem scalar_chebyshev_angle (n : ℕ) (θ : ℝ) (hθ0 : 0≤θ) (hθπ : θ≤Real.pi) :
    evaluate (scalarSignalReflection (Real.cos θ)) (signalChebyshevWord n)=scalarRotation ((n : ℝ)*θ) := by
  have he :=
      (scalar_signal_chebyshev_actual_word n (Real.cos θ) ⟨Real.neg_one_le_cos θ,Real.cos_le_one θ⟩).2.2.2.1
  have hb : scalarSignalReflection (Real.cos θ)*PauliZ=scalarRotation θ := by
    ext a b
    cases a <;> cases b <;>
      simp [scalarSignalReflection,PauliZ,Matrix.mul_apply,scalarRotation,
        ← Real.sin_eq_sqrt_one_sub_cos_sq hθ0 hθπ]
  rw [he,hb,scalarRotation_pow]

/-- Evaluation of the controlled Chebyshev readout equals the controlled word evaluation
conjugated by Hadamard on the control. -/
private theorem scalar_hadamard_word_matrix (n : ℕ) (U : Matrix Bool Bool ℂ) :
    evaluate (controlOracle U) (signalChebyshevHadamardWord n)=
      TensorGate Hadamard (1 : Matrix Bool Bool ℂ)*controlOracle (evaluate U (signalChebyshevWord n))*
        TensorGate Hadamard (1 : Matrix Bool Bool ℂ) := by
  simp only [signalChebyshevHadamardWord,evaluate_append,evaluate,instructionMatrix,
    Matrix.mul_one,evaluate_compileControlled]

/-- Controlling negative identity gives `PauliZ` on the control tensor the identity on the
target. -/
private theorem scalar_control_neg_one : controlOracle (-(1 : Matrix Bool Bool ℂ))=
    TensorGate PauliZ (1 : Matrix Bool Bool ℂ) := by
  ext ⟨a,i⟩ ⟨b,j⟩
  cases a <;> cases b <;> by_cases hij : i=j <;> simp [controlOracle,select,TensorGate,PauliZ,hij]

/-- Conjugation of `PauliZ` by `Hadamard` gives `PauliX`. -/
private theorem scalar_hadamard_z_hadamard : Hadamard*PauliZ*Hadamard=PauliX := by
  ext i j
  cases i <;> cases j <;> simp
      [Hadamard,PauliZ,PauliX,permMatrix,Matrix.mul_apply] <;> ring_nf <;> norm_num [sqrt2_sq]

/-- The scalar signal distance between `1` and `cos θ` is `2 * sin (θ / 2)` for `θ` in `[0, π]`. -/
private theorem scalar_one_chord (θ : ℝ) (hθ0 : 0≤θ) (hθπ : θ≤Real.pi) :
    scalarSignalDistance 1 (Real.cos θ)=2*Real.sin (θ/2) := by
  have hs : (Real.sqrt (1-(Real.cos θ)^2))^2=1-(Real.cos θ)^2 :=
    Real.sq_sqrt (by nlinarith [Real.neg_one_le_cos θ,Real.cos_le_one θ])
  have hd := scalarSignalDistance_sq 1 (Real.cos θ)
  norm_num only [one_pow,sub_self,Real.sqrt_zero,zero_sub,neg_sq] at hd
  have hc : Real.cos θ=1-2*(Real.sin (θ/2))^2 := by
    have he := Real.cos_two_mul_eq_one_sub (θ/2)
    rw [show 2*(θ/2)=θ by ring] at he
    exact he
  have hsin : 0≤Real.sin (θ/2) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])
  nlinarith only [hd,hs,hc,hsin,scalarSignalDistance_nonneg 1 (Real.cos θ)]

/-- For positive `n`, the Chebyshev readout perfectly distinguishes signals `1` and `cos (π /
n)` using `n` queries and `n + 2` gates. Any fixed well-formed word approximating the
opposite scalar responses at error `eps < 1` requires at least `2 * (1 - eps) * n / π`
queries. -/
theorem scalar_signal_chebyshev_phase_readout_and_matching_lower_consumer : ∀ (n : ℕ), 0<n →
  let x := Real.cos (Real.pi/(n:ℝ));
  evaluate (scalarSignalReflection 1) (signalChebyshevWord n)=1 ∧
  evaluate (scalarSignalReflection x) (signalChebyshevWord n)=-(1:Matrix Bool Bool ℂ) ∧
  WellFormedAdjointCircuit (signalChebyshevHadamardWord n) ∧
  adjointQueryCount (signalChebyshevHadamardWord n)=n ∧
  adjointGateCount (signalChebyshevHadamardWord n)=n+2 ∧
  MeasureProb (evaluate (controlOracle (scalarSignalReflection 1)) (signalChebyshevHadamardWord n)
    *ᵥ Qatlib.Foundations.PureStateMath.Ket (false,false)) {p | p.1=true}=0 ∧
  MeasureProb (evaluate (controlOracle (scalarSignalReflection x)) (signalChebyshevHadamardWord n)
    *ᵥ Qatlib.Foundations.PureStateMath.Ket (false,false)) {p | p.1=true}=1 ∧
  (∀ (word : List (AdjointStep (Bool×Unit))) (eps : ℝ),
    WellFormedAdjointCircuit word → 0≤eps → eps<1 →
    let F := encodingFiber (I:=Unit) false;
    BlockEncoding (1:Matrix Unit Unit ℂ) (evaluate (scalarSignalLift Unit 1) word) F F 1 eps →
    BlockEncoding (-(1:Matrix Unit Unit ℂ)) (evaluate (scalarSignalLift Unit x) word) F F 1 eps →
    (adjointQueryCount word:ℝ) ≥ 2*(1-eps)*(n:ℝ)/Real.pi) := by
  intro n hn
  let θ := Real.pi/(n : ℝ)
  let x := Real.cos θ
  have hnp : 0<(n : ℝ) := Nat.cast_pos.mpr hn
  have hn1 : 1≤(n : ℝ) := by exact_mod_cast hn
  have hθ : 0<θ := div_pos Real.pi_pos hnp
  have hθπ : θ≤Real.pi := by
    apply (div_le_iff₀ hnp).mpr
    nlinarith [Real.pi_pos]
  have hx : x∈Set.Icc (-1) 1 := ⟨Real.neg_one_le_cos θ,Real.cos_le_one θ⟩
  have hone : evaluate (scalarSignalReflection 1) (signalChebyshevWord n)=1 := by
    rw [(scalar_signal_chebyshev_actual_word n 1 (by norm_num)).2.2.2.1]
    have he : scalarSignalReflection 1=PauliZ := by
      ext a b; cases a <;> cases b <;> simp [scalarSignalReflection,PauliZ]
    rw [he,pauliZ_mul_self,one_pow]
  have hneg : evaluate (scalarSignalReflection x) (signalChebyshevWord n)=-(1 : Matrix Bool Bool ℂ) := by
    rw [scalar_chebyshev_angle n θ hθ.le hθπ]
    have he : (n : ℝ)*θ=Real.pi := by dsimp [θ]; field_simp
    rw [he]
    ext a b
    cases a <;> cases b <;> simp [scalarRotation]
  have hc := scalar_signal_chebyshev_actual_word n 1 (by norm_num)
  have hH : WellFormedAdjointCircuit ([.gate (TensorGate Hadamard (1 : Matrix Bool Bool ℂ))] : List (AdjointStep (Bool×Bool))) := by
    simp only [WellFormedAdjointCircuit.gate_cons_iff,WellFormedAdjointCircuit.nil,and_true]
    exact tensorGate_unitary hadamard_unitary (unitaryGroup Bool ℂ).one_mem
  have hw : WellFormedAdjointCircuit (signalChebyshevHadamardWord n) :=
    (hH.append (compileControlled_wellFormed hc.1)).append hH
  have hqueries : adjointQueryCount (signalChebyshevHadamardWord n)=n := by
    simp [signalChebyshevHadamardWord,adjointQueryCount_append,queryCount_compileControlled,hc.2.1,adjointQueryCount]
  have hgates : adjointGateCount (signalChebyshevHadamardWord n)=n+2 := by
    simp [signalChebyshevHadamardWord,adjointGateCount_append,gateCount_compileControlled,hc.2.2.1,adjointGateCount]
  have hstate0 : evaluate (controlOracle (scalarSignalReflection 1)) (signalChebyshevHadamardWord n)*ᵥKet (false,false)=Qatlib.Foundations.PureStateMath.Ket (false,false) := by
    rw [scalar_hadamard_word_matrix,hone,controlOracle_one,Matrix.mul_one,tensorGate_mul,hadamard_mul_self]
    simp [tensorGate_one]
  have hstate1 : evaluate (controlOracle (scalarSignalReflection x)) (signalChebyshevHadamardWord n)*ᵥKet (false,false)=Qatlib.Foundations.PureStateMath.Ket (true,false) := by
    rw [scalar_hadamard_word_matrix,hneg,scalar_control_neg_one,tensorGate_mul,tensorGate_mul,scalar_hadamard_z_hadamard]
    simp only [Matrix.one_mul]
    rw [← tensorState_ket_ket]
    change ApplyGate (TensorGate PauliX (1 : Matrix Bool Bool ℂ))
        (TensorState (Qatlib.Foundations.PureStateMath.Ket false) (Qatlib.Foundations.PureStateMath.Ket false))=Qatlib.Foundations.PureStateMath.Ket (true,false)
    rw [applyGate_tensorGate,applyGate_pauliX_ket,applyGate_one,tensorState_ket_ket]
    rfl
  refine ⟨hone,hneg,hw,hqueries,hgates,?_,?_,?_⟩
  · rw [hstate0]
    simp [MeasureProb,BornProb,Qatlib.Foundations.PureStateMath.Ket,Finset.sum_filter,Fintype.sum_prod_type]
  · rw [hstate1]
    simp [MeasureProb,BornProb,Qatlib.Foundations.PureStateMath.Ket,Finset.sum_filter,Fintype.sum_prod_type]
  · intro word eps hword heps heps1
    (try dsimp only)
    intro hPlus hMinus
    have hchord := scalar_one_chord θ hθ.le hθπ
    have hsin : 0<Real.sin (θ/2) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
    have hdist : 0<scalarSignalDistance 1 x := by rw [hchord]; positivity
    have hne : (1 : ℝ)≠x := by
      intro he
      have hd : scalarSignalDistance 1 x=0 := by rw [← he]; norm_num [scalarSignalDistance]
      linarith
    have hdistθ : scalarSignalDistance 1 x≤θ := by
      rw [hchord]
      nlinarith only [Real.sin_le (by linarith : 0≤θ/2)]
    have hlower := (scalar_signal_actual_response_query_lower_bound Unit Unit (encodingFiber false) (encodingFiber false)
      word 1 x 1 (-1) eps hPlus.left_isometry hPlus.right_isometry hword (by norm_num) hx hne heps
      (by simpa only [Complex.ofReal_one,one_smul] using hPlus.error_le)
      (by simpa only [Complex.ofReal_neg,Complex.ofReal_one,neg_one_smul,one_smul] using hMinus.error_le)).1
    have hnum : max 0 (|1-(-1 : ℝ)|-2*eps)=2*(1-eps) := by
      norm_num
      rw [max_eq_right (by linarith)]
      ring
    rw [hnum] at hlower
    have hh := (div_le_iff₀ hdist).mp hlower
    have hqt :=
        hh.trans (mul_le_mul_of_nonneg_left hdistθ (Nat.cast_nonneg (adjointQueryCount word)))
    have hmul := mul_le_mul_of_nonneg_right hqt hnp.le
    have hθn : θ*(n : ℝ)=Real.pi := div_mul_cancel₀ Real.pi hnp.ne'
    simp only [mul_assoc,hθn] at hmul
    apply (div_le_iff₀ Real.pi_pos).mpr
    simpa only [mul_assoc] using hmul

/-- A well-formed zero-query word encodes the constant response one half within error one tenth,
while the displayed difference of leakage square roots is positive. This tests the leakage
expression associated with [Gilyén et al., Theorem 73][GilyenSuLowWiebe2019]. -/
theorem scalar_signal_printed_leakage_counterexample :
  WellFormedAdjointCircuit constantHalfSignalWord ∧ adjointQueryCount constantHalfSignalWord=0 ∧
  adjointGateCount constantHalfSignalWord=1 ∧
  (∀ x : ℝ, let F := encodingFiber (I:=Unit) false;
    BlockEncoding ((1/2:ℂ) • (1:Matrix Unit Unit ℂ))
      (evaluate (scalarSignalLift Unit x) constantHalfSignalWord) F F 1 (1/10)) ∧
  0 < Real.sqrt (1-(1/2-1/10:ℝ)^2)-Real.sqrt (1-(1/2+1/10:ℝ)^2) := by
  have he := (Qatlib.Concepts.BlockEncoding.ProjectedUnitaryEncoding.toBlockEncoding ((scalar_signal_actual_encoding (1/2) (by norm_num)).2.2.2 Unit)).mono
    (by norm_num : (0 : ℝ)≤1/10)
  refine ⟨?_,rfl,rfl,?_,?_⟩
  · simp only [constantHalfSignalWord,WellFormedAdjointCircuit.gate_cons_iff,WellFormedAdjointCircuit.nil,and_true]
    exact he.unitary
  · intro x
    simpa [constantHalfSignalWord,evaluate,instructionMatrix] using he
  · have hx : (0 : ℝ)≤1-(1/2+1/10 : ℝ)^2 := by norm_num
    have hlt : (1-(1/2+1/10 : ℝ)^2)<1-(1/2-1/10 : ℝ)^2 := by norm_num
    exact sub_pos.mpr (Real.sqrt_lt_sqrt hx hlt)

end Qatlib.Concepts.QsvtCore.QueryLowerBound
