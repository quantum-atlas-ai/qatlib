/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.ScopedOracleWorkspace

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.QueryWordCore.QueryMachinery

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Qatlib.Concepts.GateVocabulary.GateVocab
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement

namespace Qatlib.Concepts.MatrixAccess.CircuitPipeline

open Matrix
open scoped Classical

def reg1Equiv : Reg 1 ≃ Bool where
  toFun x := x 0
  invFun b := fun _ => b
  left_inv := by
    intro x
    funext i
    fin_cases i
    rfl
  right_inv := by
    intro b
    rfl

def reg1Zero : Reg 1 := fun _ => false

def reg1One : Reg 1 := fun _ => true

noncomputable def reg1Relabel (w : QState Bool) : QState (Reg 1) :=
  relabelState reg1Equiv.symm w

/-- Relabeling a Boolean state to a one bit register preserves its amplitude at the
corresponding constant register. -/
theorem reg1Relabel_apply (w : QState Bool) (b : Bool) :
    reg1Relabel w (fun _ => b) = w b := rfl

def reg1Read : Reg 1 → Bool := fun x => x 0

/-- The one bit register equivalence maps a constant register to its Boolean bit. -/
@[simp] theorem reg1Equiv_lam (c : Bool) : reg1Equiv (fun _ => c) = c := rfl

/-- The zero register is the constant false function. -/
@[simp] theorem reg1Zero_eq : reg1Zero = (fun _ => false) := rfl

/-- The one register is the constant true function. -/
@[simp] theorem reg1One_eq : reg1One = (fun _ => true) := rfl

/-- The constant false one bit register differs from the constant true register. -/
@[simp] theorem reg1False_ne_reg1True : (fun _ => false : Reg 1) ≠ fun _ => true := by
  intro h
  have h' := congrArg (fun x : Reg 1 => x 0) h
  simp at h'

/-- The constant true one bit register differs from the constant false register. -/
@[simp] theorem reg1True_ne_reg1False : (fun _ => true : Reg 1) ≠ fun _ => false := by
  intro h
  have h' := congrArg (fun x : Reg 1 => x 0) h
  simp at h'

/-- The false basis state has zero amplitude at the true register. -/
theorem ket_reg1False_at_true : Ket (fun _ => false : Reg 1) (fun _ => true) = 0 := by
  simp [Ket]

/-- The true basis state has unit amplitude at the true register. -/
theorem ket_reg1True_at_true : Ket (fun _ => true : Reg 1) (fun _ => true) = 1 := by
  simp [Ket]

/-- Every one bit register is either `reg1Zero` or `reg1One`. -/
theorem reg1_cases (x : Reg 1) : x = reg1Zero ∨ x = reg1One := by
  by_cases h0 : x 0 = false
  · exact Or.inl (reg1Equiv.injective h0)
  · exact Or.inr (reg1Equiv.injective (Bool.eq_true_of_not_eq_false h0))

/-- The one register differs from the zero register. -/
theorem reg1One_ne_reg1Zero : reg1One ≠ reg1Zero := by
  intro h
  have h' := congrArg (fun x : Reg 1 => x 0) h
  simp [reg1One, reg1Zero] at h'

/-- A sum over one bit registers is the sum of its false and true terms. -/
theorem sum_reg1 (g : Reg 1 → ℂ) :
    (∑ x : Reg 1, g x) = g (fun _ => false) + g (fun _ => true) := by
  rw [Fintype.sum_equiv reg1Equiv g (fun b => g (fun _ => b))]
  · simp [add_comm]
  · intro x
    show g x = g (fun _ => x 0)
    have hx : reg1Equiv x = x 0 := rfl
    rw [← hx]
    congr 1
    funext i
    fin_cases i
    rfl

noncomputable def scopedReg1Hadamard : Matrix (Reg 1) (Reg 1) ℂ :=
  relabelGate reg1Equiv.symm Hadamard

/-- The scoped register Hadamard acts compatibly with relabeling the Boolean Hadamard. -/
theorem applyGate_scopedReg1Hadamard (w : QState Bool) :
    ApplyGate scopedReg1Hadamard (reg1Relabel w) = reg1Relabel (ApplyGate Hadamard w) := by
  show ApplyGate (relabelGate reg1Equiv.symm Hadamard) (relabelState reg1Equiv.symm w)
      = relabelState reg1Equiv.symm (ApplyGate Hadamard w)
  exact applyGate_relabelGate _ _ _

/-- Gives the amplitudes of applying the scoped one bit Hadamard as the normalized sum or
difference of input amplitudes. -/
theorem applyGate_scopedReg1Hadamard_apply (v : QState (Reg 1)) (b : Bool) :
    ApplyGate scopedReg1Hadamard v (fun _ => b)
      = ((Real.sqrt 2 : ℂ)⁻¹)
        * (v (fun _ => false) + (if b then -1 else 1) * v (fun _ => true)) := by
  simp only [ApplyGate, scopedReg1Hadamard, relabelGate, Matrix.reindex_apply,
    Matrix.submatrix_apply, Matrix.mulVec, dotProduct]
  rw [sum_reg1]
  simp only [Hadamard, Matrix.of_apply, Equiv.symm_symm, reg1Equiv_lam]
  by_cases hb : b <;> simp [hb] <;> ring

/-- Gives the coordinates of the scoped one bit Hadamard matrix product as normalized sums and
differences. -/
theorem scopedReg1Hadamard_mulVec_apply (v : QState (Reg 1)) (b : Bool) :
    (scopedReg1Hadamard *ᵥ v) (fun _ => b)
      = ((Real.sqrt 2 : ℂ)⁻¹)
        * (v (fun _ => false) + (if b then -1 else 1) * v (fun _ => true)) := by
  show ApplyGate scopedReg1Hadamard v (fun _ => b) = _
  exact applyGate_scopedReg1Hadamard_apply v b

/-- The scoped one bit Hadamard equals its conjugate transpose. -/
theorem scopedReg1Hadamard_conjTranspose :
    scopedReg1Hadamardᴴ = scopedReg1Hadamard := by
  have h : (relabelGate reg1Equiv.symm Hadamard)ᴴ = relabelGate reg1Equiv.symm Hadamardᴴ := by
    ext x y
    simp only [relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply,
      Matrix.conjTranspose_apply]
  unfold scopedReg1Hadamard
  rw [h, hadamard_conjTranspose]

/-- The scoped one bit Hadamard is unitary. -/
theorem scopedReg1Hadamard_unitary :
    scopedReg1Hadamard ∈ Matrix.unitaryGroup (Reg 1) ℂ :=
  (relabelGate_mem_unitaryGroup (reg1Equiv.symm) Hadamard).2 hadamard_unitary

/-- The prepared marking gate negates amplitudes in the marked set and preserves all others. -/
theorem applyGate_preparedMark {n : ℕ} (S : Finset (Reg n)) (v : QState (Reg n)) (x : Reg n) :
    ApplyGate (preparedMark S) v x = (if x ∈ S then (-1 : ℂ) else 1) * v x := by
  have hone : (1 : Matrix (Reg n) (Reg n) ℂ) *ᵥ v = v := by
    funext y
    show ∑ j, ((1 : Matrix (Reg n) (Reg n) ℂ) y j) * v j = v y
    simp [Matrix.one_apply]
  have hdiag : ∀ d : Reg n → ℂ, (Matrix.diagonal d *ᵥ v) = fun y => d y * v y := by
    intro d
    funext y
    show ∑ j, (Matrix.diagonal d y j) * v j = d y * v y
    simp [Matrix.diagonal_apply]
  show ((1 - (2 : ℂ) • Projector S) *ᵥ v) x = _
  rw [Matrix.sub_mulVec, hone, Matrix.smul_mulVec]
  unfold Projector
  rw [hdiag]
  by_cases hx : x ∈ S
  · simp [hx]
    ring
  · simp [hx]

/-- The inner product with the zero basis state is the zero register amplitude. -/
theorem inner_reg1Zero (v : QState (Reg 1)) : Inner (Ket reg1Zero) v = v reg1Zero := by
  rw [inner_apply, sum_reg1]
  simp [Ket]

/-- Reflection about the zero basis state doubles its zero component and subtracts the original
state. -/
theorem applyGate_reflectionAbout_reg1 (v : QState (Reg 1)) :
    ApplyGate (ReflectionAbout (outerProduct (Ket reg1Zero))) v
      = 2 • (v reg1Zero) • Ket reg1Zero - v := by
  rw [applyGate_reflectionAbout, ApplyGate, outerProduct_mulVec, inner_reg1Zero]
  module

/-- The square of the complex inverse square root of two is one half. -/
theorem invSqrt2_sq : ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) = ((1/2 : ℂ)) := by
  have h : (Real.sqrt 2 : ℂ) ≠ 0 := by
    intro h0
    have h1 : (Real.sqrt 2 : ℂ) ^ 2 = (0 : ℂ) ^ 2 := congrArg (fun z : ℂ => z ^ 2) h0
    rw [sqrt2_sq] at h1
    norm_num at h1
  field_simp
  norm_num [sqrt2_sq]

/-- The complex inverse square root of two is nonzero. -/
theorem invSqrt2_ne_zero : ((Real.sqrt 2 : ℂ)⁻¹ : ℂ) ≠ 0 := by
  intro h0
  have h1 : ((Real.sqrt 2 : ℂ)⁻¹ : ℂ) * ((Real.sqrt 2 : ℂ)⁻¹ : ℂ) = 0 := by
    rw [h0, zero_mul]
  rw [invSqrt2_sq] at h1
  norm_num at h1

/-- The inverse square root of two multiplied by twice itself is one. -/
theorem invSqrt2_dbl :
    ((Real.sqrt 2 : ℂ)⁻¹) * (((Real.sqrt 2 : ℂ)⁻¹) + ((Real.sqrt 2 : ℂ)⁻¹)) = 1 := by
  rw [mul_add]
  norm_num [invSqrt2_sq]

/-- The scoped Hadamard maps the zero basis state to the normalized sum of the two basis states. -/
theorem scopedReg1Hadamard_ketZero :
    scopedReg1Hadamard *ᵥ Ket (fun _ => false : Reg 1)
      = ((Real.sqrt 2 : ℂ)⁻¹) • (Ket (fun _ => false : Reg 1) + Ket (fun _ => true : Reg 1)) := by
  funext x
  rcases reg1_cases x with hx | hx
  · rw [hx]
    simp only [reg1Zero_eq]
    rw [scopedReg1Hadamard_mulVec_apply]
    simp [Ket, smul_eq_mul]
  · rw [hx]
    simp only [reg1One_eq]
    rw [scopedReg1Hadamard_mulVec_apply]
    simp [Ket, smul_eq_mul]

/-- The scoped Hadamard maps the one basis state to the normalized difference of zero and one
basis states. -/
theorem scopedReg1Hadamard_ketOne :
    scopedReg1Hadamard *ᵥ Ket (fun _ => true : Reg 1)
      = ((Real.sqrt 2 : ℂ)⁻¹) • (Ket (fun _ => false : Reg 1) - Ket (fun _ => true : Reg 1)) := by
  funext x
  rcases reg1_cases x with hx | hx
  · rw [hx]
    simp only [reg1Zero_eq]
    rw [scopedReg1Hadamard_mulVec_apply]
    simp [Ket, smul_eq_mul]
  · rw [hx]
    simp only [reg1One_eq]
    rw [scopedReg1Hadamard_mulVec_apply]
    simp [Ket, smul_eq_mul]

/-- The scoped Hadamard maps the normalized zero minus one superposition to the one basis state. -/
theorem scopedReg1Hadamard_signed :
    scopedReg1Hadamard
        *ᵥ (((Real.sqrt 2 : ℂ)⁻¹) • (Ket (fun _ => false : Reg 1) - Ket (fun _ => true : Reg 1)))
      = Ket (fun _ => true : Reg 1) := by
  funext x
  rcases reg1_cases x with hx | hx
  · rw [hx]
    show (scopedReg1Hadamard
        *ᵥ (((Real.sqrt 2 : ℂ)⁻¹) • (Ket (fun _ => false : Reg 1) - Ket (fun _ => true : Reg 1))))
      (fun _ => false : Reg 1) = _
    rw [scopedReg1Hadamard_mulVec_apply]
    simp [Ket, smul_eq_mul]
  · rw [hx]
    show (scopedReg1Hadamard
        *ᵥ (((Real.sqrt 2 : ℂ)⁻¹) • (Ket (fun _ => false : Reg 1) - Ket (fun _ => true : Reg 1))))
      (fun _ => true : Reg 1) = _
    rw [scopedReg1Hadamard_mulVec_apply]
    simp [Ket, smul_eq_mul]
    ring_nf
    norm_num [sqrt2_sq]

/-- The scoped Hadamard maps the negative one basis state to the normalized one minus zero
superposition. -/
theorem scopedReg1Hadamard_negOne :
    scopedReg1Hadamard *ᵥ (-Ket (fun _ => true : Reg 1))
      = ((Real.sqrt 2 : ℂ)⁻¹) • (Ket (fun _ => true : Reg 1) - Ket (fun _ => false : Reg 1)) := by
  funext x
  rcases reg1_cases x with hx | hx
  · rw [hx]
    show (scopedReg1Hadamard *ᵥ (-Ket (fun _ => true : Reg 1))) (fun _ => false : Reg 1) = _
    rw [scopedReg1Hadamard_mulVec_apply]
    simp [Ket, smul_eq_mul]
  · rw [hx]
    show (scopedReg1Hadamard *ᵥ (-Ket (fun _ => true : Reg 1))) (fun _ => true : Reg 1) = _
    rw [scopedReg1Hadamard_mulVec_apply]
    simp [Ket, smul_eq_mul]

/-- The scoped phase gate with phase minus one negates exactly the true register amplitude. -/
theorem reg1_phase_apply (v : QState (Reg 1)) (b : Bool) :
    ApplyGate (scopedPhaseGate reg1Read (-1)) v (fun _ => b)
      = (if b then (-1 : ℂ) else 1) * v (fun _ => b) := by
  show ApplyGate (scopedPhaseGate reg1Read (-1)) v (fun _ => b) = _
  rw [applyGate_scopedPhaseGate]
  simp [reg1Read]

/-- The scoped phase matrix with phase minus one negates exactly the true register coordinate. -/
theorem reg1_phase_mulVec_apply (v : QState (Reg 1)) (b : Bool) :
    (scopedPhaseGate reg1Read (-1) *ᵥ v) (fun _ => b)
      = (if b then (-1 : ℂ) else 1) * v (fun _ => b) :=
  reg1_phase_apply v b

/-- Marking the true register negates its amplitude and preserves the false amplitude. -/
theorem reg1_mark_apply (v : QState (Reg 1)) (b : Bool) :
    ApplyGate (preparedMark {(fun _ => true : Reg 1)}) v (fun _ => b)
      = (if b then (-1 : ℂ) else 1) * v (fun _ => b) := by
  have hmem : ((fun _ => b : Reg 1) ∈ {(fun _ => true : Reg 1)}) ↔ b = true :=
    ⟨fun h => (congrArg (fun x : Reg 1 => x 0) (Finset.mem_singleton.mp h) : b = true),
      fun h => Finset.mem_singleton.mpr (by rw [h])⟩
  show ApplyGate (preparedMark {(fun _ => true : Reg 1)}) v (fun _ => b) = _
  simp only [applyGate_preparedMark, hmem]

/-- The matrix marking the true register negates exactly the true coordinate. -/
theorem reg1_mark_mulVec_apply (v : QState (Reg 1)) (b : Bool) :
    (preparedMark {(fun _ => true : Reg 1)} *ᵥ v) (fun _ => b)
      = (if b then (-1 : ℂ) else 1) * v (fun _ => b) :=
  reg1_mark_apply v b

/-- The scoped phase gate with phase minus one fixes the zero basis state. -/
theorem reg1_phase_ketZero :
    scopedPhaseGate reg1Read (-1) *ᵥ Ket (fun _ => false) = Ket (fun _ => false) := by
  funext x
  rcases reg1_cases x with hx | hx
  · rw [hx]
    simp only [reg1Zero_eq]
    rw [reg1_phase_mulVec_apply]
    simp [Ket]
  · rw [hx]
    simp only [reg1One_eq]
    rw [reg1_phase_mulVec_apply]
    simp [Ket]

/-- The scoped phase gate changes the normalized sum of basis states into their normalized
difference. -/
theorem reg1_phase_on_superposition :
    scopedPhaseGate reg1Read (-1)
      *ᵥ (((Real.sqrt 2 : ℂ)⁻¹) • (Ket (fun _ => false) + Ket (fun _ => true)))
      = ((Real.sqrt 2 : ℂ)⁻¹) • (Ket (fun _ => false) - Ket (fun _ => true)) := by
  funext x
  rcases reg1_cases x with hx | hx
  · rw [hx]
    simp only [reg1Zero_eq]
    rw [reg1_phase_mulVec_apply]
    simp [Ket, smul_eq_mul]
  · rw [hx]
    simp only [reg1One_eq]
    rw [reg1_phase_mulVec_apply]
    simp [Ket, smul_eq_mul]

/-- The prepared true register mark changes the normalized sum of basis states into their
normalized difference. -/
theorem reg1_mark_on_superposition :
    preparedMark {(fun _ => true : Reg 1)}
      *ᵥ (((Real.sqrt 2 : ℂ)⁻¹) • (Ket (fun _ => false) + Ket (fun _ => true)))
      = ((Real.sqrt 2 : ℂ)⁻¹) • (Ket (fun _ => false) - Ket (fun _ => true)) := by
  funext x
  rcases reg1_cases x with hx | hx
  · rw [hx]
    simp only [reg1Zero_eq]
    rw [reg1_mark_mulVec_apply]
    simp [Ket, smul_eq_mul]
  · rw [hx]
    simp only [reg1One_eq]
    rw [reg1_mark_mulVec_apply]
    simp [Ket, smul_eq_mul]

/-- Reflection about the zero basis state negates the one basis state. -/
theorem reg1_reflection_ketOne :
    ReflectionAbout (outerProduct (Ket (fun _ => false : Reg 1))) *ᵥ Ket (fun _ => true : Reg 1)
      = -Ket (fun _ => true : Reg 1) := by
  funext x
  rcases reg1_cases x with hx | hx
  · rw [hx]
    simp only [reg1Zero_eq]
    show ApplyGate (ReflectionAbout (outerProduct (Ket reg1Zero)))
      (Ket (fun _ => true : Reg 1)) reg1Zero = _
    rw [applyGate_reflectionAbout_reg1]
    simp [Ket]
  · rw [hx]
    simp only [reg1One_eq]
    show ApplyGate (ReflectionAbout (outerProduct (Ket reg1Zero)))
      (Ket (fun _ => true : Reg 1)) reg1One = _
    rw [applyGate_reflectionAbout_reg1]
    simp [Ket]

/-- The scoped mark, data gate, mark sequence realizes the corresponding phase sandwich,
restores its ancilla, and uses four queries and three gates. -/
theorem scoped_mark_data_mark_consumer :
    ∀ (n : ℕ) (f : Reg n → Bool) (U : Matrix (Reg n) (Reg n) ℂ) (ψ : QState (Reg n)),
      let w := [ScopedOracleStep.phase (-1), ScopedOracleStep.data U, ScopedOracleStep.phase (-1)]
      scopedLogicalMatrix f w = scopedPhaseGate f (-1) * U * scopedPhaseGate f (-1) ∧
      QueryCount (scopedCompile w) = 4 ∧ GateCount (scopedCompile w) = 3 ∧
      Run (scopedBitOracle f) (scopedCompile w) (TensorState (Ket false) ψ) =
        TensorState (Ket false) (scopedPhaseGate f (-1) *ᵥ (U *ᵥ (scopedPhaseGate f (-1) *ᵥ ψ))) := by
  intro n f U ψ
  have hw : scopedLogicalMatrix f [ScopedOracleStep.phase (-1), ScopedOracleStep.data U,
      ScopedOracleStep.phase (-1)] = scopedPhaseGate f (-1) * U * scopedPhaseGate f (-1) := by
    simp only [scopedLogicalMatrix, scopedStepMatrix, Matrix.one_mul]
  obtain ⟨hpc, hq, hg⟩ := scoped_program_actual_query_and_gate_counts n
    [ScopedOracleStep.phase (-1), ScopedOracleStep.data U, ScopedOracleStep.phase (-1)]
  norm_num [scopedPhaseCount] at hq
  have hrun : Run (scopedBitOracle f)
      (scopedCompile [ScopedOracleStep.phase (-1), ScopedOracleStep.data U,
        ScopedOracleStep.phase (-1)]) (TensorState (Ket false) ψ)
      = TensorState (Ket false) (scopedPhaseGate f (-1) *ᵥ (U *ᵥ (scopedPhaseGate f (-1) *ᵥ ψ))) := by
    rw [scoped_run_clean f _ ψ, hw, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  exact ⟨hw, hq, hg, hrun⟩

/-- The concrete one bit mark, Hadamard, mark circuit produces the signed superposition, with
four queries, three gates, and a maximum wire count of two. -/
theorem scoped_mark_data_mark_reg1_consumer :
    (let f : Reg 1 → Bool := reg1Read
     let U := scopedReg1Hadamard
     let w := [ScopedOracleStep.phase (-1), ScopedOracleStep.data U, ScopedOracleStep.phase (-1)]
     (scopedPhaseGate f (-1) * U * scopedPhaseGate f (-1)) *ᵥ Ket (fun _ => false : Reg 1)
         ≠ (U * scopedPhaseGate f (-1)) *ᵥ Ket (fun _ => false : Reg 1) ∧
     (scopedPhaseGate f (-1) * U * scopedPhaseGate f (-1)) *ᵥ Ket (fun _ => false : Reg 1)
         = ((Real.sqrt 2 : ℂ)⁻¹) • (Ket (fun _ => false : Reg 1) - Ket (fun _ => true : Reg 1)) ∧
     Run (scopedBitOracle f) (scopedCompile w) (TensorState (Ket false) (Ket (fun _ => false : Reg 1)))
       = TensorState (Ket false)
           (((Real.sqrt 2 : ℂ)⁻¹) • (Ket (fun _ => false : Reg 1) - Ket (fun _ => true : Reg 1))) ∧
     QueryCount (scopedCompile w) = 4 ∧ GateCount (scopedCompile w) = 3 ∧
     (scopedWireTrace w).foldl max 0 = 2) := by
  obtain ⟨hw, hq, hg, -⟩ := scoped_mark_data_mark_consumer (1 : ℕ) reg1Read scopedReg1Hadamard
    (Ket (fun _ => false : Reg 1))
  have hPUP : (scopedPhaseGate reg1Read (-1) * scopedReg1Hadamard
      * scopedPhaseGate reg1Read (-1)) *ᵥ Ket (fun _ => false : Reg 1)
      = ((Real.sqrt 2 : ℂ)⁻¹) • (Ket (fun _ => false : Reg 1) - Ket (fun _ => true : Reg 1)) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, reg1_phase_ketZero,
      scopedReg1Hadamard_ketZero, reg1_phase_on_superposition]
  have hUP : (scopedReg1Hadamard * scopedPhaseGate reg1Read (-1)) *ᵥ Ket (fun _ => false : Reg 1)
      = ((Real.sqrt 2 : ℂ)⁻¹) • (Ket (fun _ => false : Reg 1) + Ket (fun _ => true : Reg 1)) := by
    rw [← Matrix.mulVec_mulVec, reg1_phase_ketZero, scopedReg1Hadamard_ketZero]
  have hneq : (scopedPhaseGate reg1Read (-1) * scopedReg1Hadamard
        * scopedPhaseGate reg1Read (-1)) *ᵥ Ket (fun _ => false : Reg 1)
      ≠ (scopedReg1Hadamard * scopedPhaseGate reg1Read (-1)) *ᵥ Ket (fun _ => false : Reg 1) := by
    rw [hPUP, hUP]
    intro h
    have h1 := congrArg (fun v : QState (Reg 1) => v (fun _ => true : Reg 1)) h
    simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply] at h1
    rw [ket_reg1False_at_true, ket_reg1True_at_true] at h1
    simp only [zero_sub, zero_add, mul_neg, mul_one, smul_eq_mul] at h1
    have h3 : ((Real.sqrt 2 : ℂ)⁻¹ : ℂ) + ((Real.sqrt 2 : ℂ)⁻¹ : ℂ) = 0 :=
      neg_eq_iff_add_eq_zero.mp h1
    have h4 : (2 : ℂ) * ((Real.sqrt 2 : ℂ)⁻¹ : ℂ) = 0 := by rw [two_mul]; exact h3
    rcases mul_eq_zero.mp h4 with hz | hz
    · exact absurd hz (by norm_num)
    · exact invSqrt2_ne_zero hz
  have htrace : (scopedWireTrace [ScopedOracleStep.phase (-1), ScopedOracleStep.data
      scopedReg1Hadamard, ScopedOracleStep.phase (-1)]).foldl max 0 = 2 := by
    obtain ⟨-, -, -, h⟩ := scoped_allocation_release_and_peak_trace (1 : ℕ)
      [ScopedOracleStep.phase (-1), ScopedOracleStep.data scopedReg1Hadamard,
        ScopedOracleStep.phase (-1)]
    exact h
  have hrun : Run (scopedBitOracle reg1Read)
      (scopedCompile [ScopedOracleStep.phase (-1), ScopedOracleStep.data scopedReg1Hadamard,
        ScopedOracleStep.phase (-1)]) (TensorState (Ket false) (Ket (fun _ => false : Reg 1)))
      = TensorState (Ket false)
          (((Real.sqrt 2 : ℂ)⁻¹) • (Ket (fun _ => false : Reg 1) - Ket (fun _ => true : Reg 1))) := by
    rw [scoped_run_clean reg1Read _ (Ket (fun _ => false : Reg 1)), hw, hPUP]
  exact ⟨hneq, hPUP, hrun, hq, hg, htrace⟩

/-- Applying the scoped Hadamard to the zero basis state produces the normalized sum of basis
states. -/
theorem scopedReg1Hadamard_ketZero' :
    ApplyGate scopedReg1Hadamard (Ket (fun _ => false : Reg 1))
      = ((Real.sqrt 2 : ℂ)⁻¹) • (Ket (fun _ => false : Reg 1) + Ket (fun _ => true : Reg 1)) := by
  show scopedReg1Hadamard *ᵥ Ket (fun _ => false : Reg 1) = _
  exact scopedReg1Hadamard_ketZero

/-- Applying the scoped Hadamard to the normalized zero minus one superposition produces the one
basis state. -/
theorem scopedReg1Hadamard_signed' :
    ApplyGate scopedReg1Hadamard
      (((Real.sqrt 2 : ℂ)⁻¹) • (Ket (fun _ => false : Reg 1) - Ket (fun _ => true : Reg 1)))
      = Ket (fun _ => true : Reg 1) := by
  show scopedReg1Hadamard
      *ᵥ (((Real.sqrt 2 : ℂ)⁻¹) • (Ket (fun _ => false : Reg 1) - Ket (fun _ => true : Reg 1))) = _
  exact scopedReg1Hadamard_signed

/-- Applying the scoped Hadamard to the negative one basis state produces the normalized one
minus zero superposition. -/
theorem scopedReg1Hadamard_negOne' :
    ApplyGate scopedReg1Hadamard (-Ket (fun _ => true : Reg 1))
      = ((Real.sqrt 2 : ℂ)⁻¹) • (Ket (fun _ => true : Reg 1) - Ket (fun _ => false : Reg 1)) := by
  show scopedReg1Hadamard *ᵥ (-Ket (fun _ => true : Reg 1)) = _
  exact scopedReg1Hadamard_negOne

/-- Applying reflection about the zero basis state negates the one basis state. -/
theorem reg1_reflection_ketOne' :
    ApplyGate (ReflectionAbout (outerProduct (Ket (fun _ => false : Reg 1))))
      (Ket (fun _ => true : Reg 1)) = -Ket (fun _ => true : Reg 1) := by
  show ReflectionAbout (outerProduct (Ket (fun _ => false : Reg 1)))
      *ᵥ Ket (fun _ => true : Reg 1) = _
  exact reg1_reflection_ketOne

/-- Applying the prepared true register mark changes the normalized sum of basis states into
their normalized difference. -/
theorem reg1_mark_on_superposition' :
    ApplyGate (preparedMark {(fun _ => true : Reg 1)})
      (((Real.sqrt 2 : ℂ)⁻¹) • (Ket (fun _ => false : Reg 1) + Ket (fun _ => true : Reg 1)))
      = ((Real.sqrt 2 : ℂ)⁻¹) • (Ket (fun _ => false : Reg 1) - Ket (fun _ => true : Reg 1)) := by
  show preparedMark {(fun _ => true : Reg 1)}
      *ᵥ (((Real.sqrt 2 : ℂ)⁻¹) • (Ket (fun _ => false : Reg 1) + Ket (fun _ => true : Reg 1))) = _
  exact reg1_mark_on_superposition

/-- The scoped phase count is additive under list concatenation. -/
theorem scopedPhaseCount_append {n : ℕ} (l₁ l₂ : List (ScopedOracleStep n)) :
    scopedPhaseCount (l₁ ++ l₂) = scopedPhaseCount l₂ + scopedPhaseCount l₁ := by
  induction l₁ with
  | nil => simp [List.nil_append, scopedPhaseCount]
  | cons s l₁ ih =>
      cases s <;> simp [scopedPhaseCount, ih, Nat.add_comm, Nat.add_left_comm]

/-- The logical matrix of concatenated scoped words is the second logical matrix multiplied by
the first. -/
theorem scopedLogicalMatrix_append {n : ℕ} (f : Reg n → Bool) (l₁ l₂ : List (ScopedOracleStep n)) :
    scopedLogicalMatrix f (l₁ ++ l₂) = scopedLogicalMatrix f l₂ * scopedLogicalMatrix f l₁ := by
  induction l₁ with
  | nil => simp only [List.nil_append, scopedLogicalMatrix, Matrix.mul_one]
  | cons s l₁ ih =>
      rw [List.cons_append, scopedLogicalMatrix, scopedLogicalMatrix, ih, ← Matrix.mul_assoc]

/-- Repeating a scoped word `k` times raises its logical matrix to the power `k`. -/
theorem scopedLogicalMatrix_flatten_replicate {n : ℕ} (f : Reg n → Bool)
    (l : List (ScopedOracleStep n)) (k : ℕ) :
    scopedLogicalMatrix f (List.flatten (List.replicate k l))
      = (scopedLogicalMatrix f l)^k := by
  induction k with
  | zero =>
      simp only [List.replicate_zero, List.flatten_nil, scopedLogicalMatrix, pow_zero]
  | succ k ih =>
      rw [List.replicate_succ, List.flatten_cons, scopedLogicalMatrix_append, ih, pow_succ]

/-- The prepared amplitude amplification circuit acts as the corresponding iterate power after
the preparation matrix. -/
theorem run_preparedAACircuit_shadow {n : ℕ} (A : Matrix (Reg n) (Reg n) ℂ) (j : Reg n)
    (S : Finset (Reg n)) (k : ℕ) :
    Run (preparedMark S) (preparedAACircuit A j k) (Ket j)
      = ((preparedAAIterate A j S)^k * A) *ᵥ Ket j := by
  have hblock : ∀ (M R₀ : Matrix (Reg n) (Reg n) ℂ) (v : QState (Reg n)),
      Run M [Step.query, Step.gate Aᴴ, Step.gate R₀, Step.gate A] v
        = (A * R₀ * Aᴴ * M) *ᵥ v := by
    intro M R₀ v
    show A *ᵥ (R₀ *ᵥ (Aᴴ *ᵥ (M *ᵥ v))) = (A * R₀ * Aᴴ * M) *ᵥ v
    simp only [Matrix.mulVec_mulVec]
    simp only [← Matrix.mul_assoc]
  have hrep : ∀ (m : ℕ) (M R₀ : Matrix (Reg n) (Reg n) ℂ) (v : QState (Reg n)),
      Run M (RepeatCircuit [Step.query, Step.gate Aᴴ, Step.gate R₀, Step.gate A] m) v
        = ((A * R₀ * Aᴴ * M)^m) *ᵥ v := by
    intro m
    induction m with
    | zero => simp [RepeatCircuit]
    | succ m ih =>
        intro M R₀ v
        rw [RepeatCircuit, run_append, hblock, ih, ← Matrix.mulVec_mulVec, pow_succ]
        simp only [← Matrix.mulVec_mulVec]
  unfold preparedAACircuit
  rw [run_append, run_gate, run_nil, hrep]
  simp only [← Matrix.mulVec_mulVec]
  rfl

/-- The scoped bit oracle circuit realizes `k` rounds of prepared amplitude amplification while
restoring its ancilla, using `2*k` queries, `4*k+1` gates, and `n+1` wires. -/
theorem scoped_prepared_aa_actual_bit_query_consumer :
    ∀ (n k : ℕ) (f : Reg n → Bool) (A : Matrix (Reg n) (Reg n) ℂ) (j : Reg n),
      let S := Finset.univ.filter (fun x => f x=true)
      let round :=
          [ScopedOracleStep.phase (-1), .data Aᴴ, .data (ReflectionAbout (outerProduct (Ket j))),
          .data A]
      let w := [ScopedOracleStep.data A] ++ (List.replicate k round).flatten
      Run (scopedBitOracle f) (scopedCompile w) (TensorState (Ket false) (Ket j)) =
        TensorState (Ket false) (Run (preparedMark S) (preparedAACircuit A j k) (Ket j)) ∧
      QueryCount (scopedCompile w) = 2*k ∧ GateCount (scopedCompile w) = 4*k+1 ∧
      (scopedWireTrace w).foldl max 0 = n+1 := by
  intro n k f A j
  set S : Finset (Reg n) := Finset.univ.filter (fun x => f x = true) with hSdef
  set round : List (ScopedOracleStep n) :=
    [ScopedOracleStep.phase (-1), .data Aᴴ, .data (ReflectionAbout (outerProduct (Ket j))),
      .data A] with hrounddef
  set w : List (ScopedOracleStep n) := [ScopedOracleStep.data A] ++ (List.replicate k round).flatten
    with hwdef
  have hS : scopedPhaseGate f (-1) = preparedMark S := by
    rw [hSdef]
    exact scoped_phaseGate_neg_eq_preparedMark f
  have hround : scopedLogicalMatrix f round = preparedAAIterate A j S := by
    simp only [scopedLogicalMatrix, scopedStepMatrix, Matrix.one_mul, hS, preparedAAIterate,
      hrounddef]
  have hw : scopedLogicalMatrix f w = (preparedAAIterate A j S)^k * A := by
    rw [hwdef, scopedLogicalMatrix_append, scopedLogicalMatrix_flatten_replicate, hround,
      scopedLogicalMatrix, scopedLogicalMatrix, Matrix.one_mul, scopedStepMatrix]
  have hrun : Run (scopedBitOracle f) (scopedCompile w) (TensorState (Ket false) (Ket j))
      = TensorState (Ket false) (Run (preparedMark S) (preparedAACircuit A j k) (Ket j)) := by
    rw [scoped_run_clean f w (Ket j), hw, run_preparedAACircuit_shadow A j S k]
  obtain ⟨hpc, hq, hg⟩ := scoped_program_actual_query_and_gate_counts n w
  have hroundc : scopedPhaseCount round = 1 := by
    rw [hrounddef]
    norm_num [scopedPhaseCount]
  have hgen : ∀ (l : List (ScopedOracleStep n)) (m : ℕ),
      scopedPhaseCount (List.flatten (List.replicate m l)) = m * scopedPhaseCount l := by
    intro l m
    induction m with
    | zero => norm_num [List.replicate, List.flatten, scopedPhaseCount]
    | succ m ih =>
        rw [List.replicate_succ, List.flatten_cons, scopedPhaseCount_append, ih]
        simp [Nat.succ_mul]
  have hkey : scopedPhaseCount (List.flatten (List.replicate k round)) = k := by
    rw [hgen round k, hroundc]
    ring
  have hzero : scopedPhaseCount [ScopedOracleStep.data A] = 0 := rfl
  have hpc' : scopedPhaseCount w = k := by
    rw [hwdef, scopedPhaseCount_append, hkey, hzero]
    ring
  have hq' : QueryCount (scopedCompile w) = 2 * k := by
    rw [hq, hpc']
  have hroundlen : round.length = 4 := by
    rw [hrounddef]
    norm_num [List.length_cons, List.length_nil]
  have hg' : GateCount (scopedCompile w) = 4 * k + 1 := by
    rw [hg, hwdef]
    simp [hrounddef]
    ring
  obtain ⟨-, -, -, htrace⟩ := scoped_allocation_release_and_peak_trace n w
  exact ⟨hrun, hq', hg', htrace⟩

/-- The concrete one bit amplitude amplification circuit produces the normalized one minus zero
superposition, using two queries, five gates, and two wires. -/
theorem scoped_prepared_aa_reg1_consumer :
    (let f : Reg 1 → Bool := reg1Read
     let S := Finset.univ.filter (fun x => f x = true)
     let A := scopedReg1Hadamard
     let j := (fun _ => false : Reg 1)
     let w := [ScopedOracleStep.data A] ++ [ScopedOracleStep.phase (-1), .data Aᴴ,
       .data (ReflectionAbout (outerProduct (Ket j))), .data A]
     S = {(fun _ => true : Reg 1)} ∧
     scopedPhaseGate f (-1) = preparedMark S ∧
     A ∈ Matrix.unitaryGroup (Reg 1) ℂ ∧
     Run (scopedBitOracle f) (scopedCompile w) (TensorState (Ket false) (Ket j))
       = TensorState (Ket false)
           (((Real.sqrt 2 : ℂ)⁻¹) • (Ket (fun _ => true : Reg 1) - Ket (fun _ => false : Reg 1))) ∧
     QueryCount (scopedCompile w) = 2 ∧ GateCount (scopedCompile w) = 5 ∧
     (scopedWireTrace w).foldl max 0 = 2) := by
  have hSset : Finset.univ.filter (fun x : Reg 1 => reg1Read x = true)
      = {(fun _ => true : Reg 1)} := by
    ext x
    by_cases h0 : x 0 = true
    · have hx : x = (fun _ => true : Reg 1) := reg1Equiv.injective h0
      rw [hx]
      simp [reg1Read]
    · have h0' : x 0 = false := Bool.eq_false_of_not_eq_true h0
      have hx : x = (fun _ => false : Reg 1) := reg1Equiv.injective h0'
      rw [hx]
      simp [reg1Read]
  have hAA : Run (preparedMark {(fun _ => true : Reg 1)})
      [Step.gate scopedReg1Hadamard, Step.query, Step.gate scopedReg1Hadamardᴴ,
        Step.gate (ReflectionAbout (outerProduct (Ket (fun _ => false : Reg 1)))),
        Step.gate scopedReg1Hadamard] (Ket (fun _ => false : Reg 1))
      = ((Real.sqrt 2 : ℂ)⁻¹) • (Ket (fun _ => true : Reg 1) - Ket (fun _ => false : Reg 1)) := by
    simp only [run_gate, run_query, run_nil, scopedReg1Hadamard_conjTranspose]
    simp only [scopedReg1Hadamard_ketZero', reg1_mark_on_superposition',
      scopedReg1Hadamard_signed', reg1_reflection_ketOne']
    exact scopedReg1Hadamard_negOne'
  obtain ⟨hbridge, hq, hg, htrace⟩ :=
    scoped_prepared_aa_actual_bit_query_consumer (1 : ℕ) (1 : ℕ) reg1Read
      scopedReg1Hadamard (fun _ => false : Reg 1)
  have hrun : Run (scopedBitOracle reg1Read)
      (scopedCompile ([ScopedOracleStep.data scopedReg1Hadamard]
        ++ (List.replicate 1 [ScopedOracleStep.phase (-1), .data scopedReg1Hadamardᴴ,
          .data (ReflectionAbout (outerProduct (Ket (fun _ => false : Reg 1)))),
          .data scopedReg1Hadamard]).flatten))
      (TensorState (Ket false) (Ket (fun _ => false : Reg 1)))
      = TensorState (Ket false)
          (((Real.sqrt 2 : ℂ)⁻¹) • (Ket (fun _ => true : Reg 1) - Ket (fun _ => false : Reg 1))) := by
    rw [hbridge, hSset]
    unfold preparedAACircuit
    exact congrArg (fun v : QState (Reg 1) => TensorState (Ket false) v) hAA
  exact ⟨hSset, scoped_phaseGate_neg_eq_preparedMark reg1Read,
    scopedReg1Hadamard_unitary, hrun, hq, hg, htrace⟩

end Qatlib.Concepts.MatrixAccess.CircuitPipeline
