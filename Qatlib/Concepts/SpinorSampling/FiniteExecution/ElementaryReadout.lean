/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.FiniteExecution.ResourceAccounting

open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

/-!
# Paid elementary readout words

Every S-dagger is expanded to two native T-dagger gates. Exact full-register
execution and actual gate counts are proved from that same chronological word.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace Qatlib.Concepts.SpinorSampling.FiniteExecution.ElementaryReadout
open Qatlib
open Qatlib.Concepts.SpinorSampling.NativeRecords.ShiftCircuit
open Qatlib.Concepts.SpinorSampling.NativeRecords.NativeBridge
open Qatlib.Concepts.SpinorSampling.Model
open Qatlib.Concepts.SpinorSampling.FiniteExecution.Resources

/-- The existing T-dagger primitive implements the S-dagger readout exactly when paid twice. -/
theorem paid_tdag_twice : tGateAdj*tGateAdj=readoutSdgMatrix := by
  unfold tGateAdj Rz readoutSdgMatrix
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext b
  cases b with
  | false => simp
  | true =>
    simp only [ite_true]
    rw [← Complex.exp_add]
    have he : ((-(Real.pi/4) : ℝ) : ℂ)*Complex.I+
        ((-(Real.pi/4) : ℝ) : ℂ)*Complex.I = -((Real.pi : ℂ)/2*Complex.I) := by
      push_cast
      ring
    rw [he, Complex.exp_neg, Complex.exp_pi_div_two_mul_I]
    simp

/-- Expand every readout S-dagger into its two actual elementary T-dagger gates. -/
def paidNativeWord {n : ℕ} : List (MeasurementGate n) → List (NativeGate (Fin n))
  | [] => []
  | .native g::gs => g::paidNativeWord gs
  | .sdg w::gs => .tdg w::.tdg w::paidNativeWord gs

/-- The native expansion of concatenated words is their chronological concatenation. -/
theorem paidNativeWord_append {n : ℕ} (xs ys : List (MeasurementGate n)) :
    paidNativeWord (xs++ys)=paidNativeWord xs++paidNativeWord ys := by
  induction xs with
  | nil => rfl
  | cons g xs ih => cases g <;> simp [paidNativeWord, ih]

/-- A list already made solely of native primitives is preserved exactly. -/
theorem paidNativeWord_native {n : ℕ} (xs : List (NativeGate (Fin n))) :
    paidNativeWord (xs.map MeasurementGate.native)=xs := by
  induction xs with
  | nil => rfl
  | cons g xs ih => simp [paidNativeWord, ih]

/-- The elementary native circuit is constructed from the actual expanded chronological word. -/
def paidNativeProgram {n : ℕ} (xs : List (MeasurementGate n)) : Circuit (Reg n) :=
  measurementProgram ((paidNativeWord xs).map MeasurementGate.native)

/-- On the entire physical register, the expanded elementary program has the exact original Run, with all spectators and phases preserved. -/
theorem paidNativeProgram_run {n : ℕ} (xs : List (MeasurementGate n)) (ψ : QState (Reg n)) :
    Run (1 : Matrix (Reg n) (Reg n) ℂ) (paidNativeProgram xs) ψ =
      Run (1 : Matrix (Reg n) (Reg n) ℂ) (measurementProgram xs) ψ := by
  induction xs generalizing ψ with
  | nil => rfl
  | cons g xs ih =>
    cases g with
    | native g =>
      change Run (1 : Matrix (Reg n) (Reg n) ℂ) (paidNativeProgram xs)
        (ApplyGate (reflectionGateMatrix (nativeMatrix g)) ψ) =
          Run (1 : Matrix (Reg n) (Reg n) ℂ) (measurementProgram xs)
            (ApplyGate (reflectionGateMatrix (nativeMatrix g)) ψ)
      exact ih _
    | sdg w =>
      change Run (1 : Matrix (Reg n) (Reg n) ℂ) (paidNativeProgram xs)
        (ApplyGate (wireGate n w tGateAdj) (ApplyGate (wireGate n w tGateAdj) ψ)) =
          Run (1 : Matrix (Reg n) (Reg n) ℂ) (measurementProgram xs)
            (ApplyGate (wireGate n w readoutSdgMatrix) ψ)
      rw [← applyGate_mul, wireGate_mul, paid_tdag_twice]
      exact ih _

/-- The paid elementary expansion uses exactly its actual word length and no target queries. -/
theorem paidNativeProgram_counts {n : ℕ} (xs : List (MeasurementGate n)) :
    GateCount (paidNativeProgram xs)=(paidNativeWord xs).length ∧
      QueryCount (paidNativeProgram xs)=0 := by
  have h := measurement_program_counts ((paidNativeWord xs).map MeasurementGate.native)
  exact ⟨h.2.trans (List.length_map _),h.1⟩

/-- Exactly one S-dagger in a velocity measurement adds one elementary gate, with no omitted control primitive. -/
theorem paid_velocity_word_length (d r : ℕ) (j : Fin d) (b : Bool) :
    (paidNativeWord (velocityWord d r j b)).length=velocityRecordGates r+1 := by
  have h := spatial_native_length d r j
  cases b <;>
    simp only [velocityWord, paidNativeWord_append, paidNativeWord_native,
      paidNativeWord, Bool.false_eq_true, ite_false, ite_true,
      List.length_append, List.length_cons, List.length_nil, native_reverse_length,
      spatial_native_length, velocityRecordGates] <;> omega

/-- For the original r≥2 domain, every actual native current circuit pays 15(r−1)²+5 elementary gates. -/
theorem paid_velocity_program_counts (d r : ℕ) (j : Fin d) (b : Bool) (hr : 2≤r) :
    GateCount (paidNativeProgram (velocityWord d r j b))=15*(r-1)^2+5 ∧
      QueryCount (paidNativeProgram (velocityWord d r j b))=0 := by
  have h := paidNativeProgram_counts (velocityWord d r j b)
  rw [paid_velocity_word_length, velocityRecordGates, ite_eq_right (by omega : r≠0)] at h
  exact ⟨by omega,h.2⟩

end Qatlib.Concepts.SpinorSampling.FiniteExecution.ElementaryReadout
