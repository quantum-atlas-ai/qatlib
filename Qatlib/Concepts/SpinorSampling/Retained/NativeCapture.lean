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
# Actual capture on selected physical wires

Three native CX gates move the unknown input spin into a chosen clean slot.
The complete-register amplitude identity preserves every spectator, and the
three-wire consumers keep exactly one unknown spin across fresh preparation.
-/

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.SpinorSampling.Retained.NativeCapture
open Qatlib
open Qatlib.Concepts.SpinorSampling.NativeRecords.ShiftCircuit
open Qatlib.Concepts.SpinorSampling.NativeRecords.NativeBridge
open Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin

/-- The actual three-CX capture word acts on chosen physical wires of the complete register; it introduces no SWAP primitive. -/
def captureSwapWord (n : ℕ) (i j : Fin n) : List (MeasurementGate n) :=
  [.native (.cx i j), .native (.cx j i), .native (.cx i j)]

/-- The capture circuit is the existing native compilation of the actual three-CX word. -/
def captureSwapProgram (n : ℕ) (i j : Fin n) : Circuit (Reg n) :=
  measurementProgram (captureSwapWord n i j)

/-- Every capture, including a later address mismatch, has exactly three actual gates and zero target queries. -/
theorem captureSwapProgram_counts (n : ℕ) (i j : Fin n) :
    GateCount (captureSwapProgram n i j)=3 ∧ QueryCount (captureSwapProgram n i j)=0 := by
  have h := measurement_program_counts (captureSwapWord n i j)
  simpa only [captureSwapProgram, captureSwapWord, List.length_cons, List.length_nil] using h.symm

/-- The two-wire specialization is exactly the existing retained-spin SWAP word, not an independently assumed transfer. -/
theorem captureSwapProgram_original : captureSwapProgram 2 0 1=swapProgram := rfl

/-- The actual native CNOT acts by the canonical update of its physical target bit. -/
theorem capture_cnot_amplitude (n : ℕ) (i j : Fin n) (hij : i ≠ j)
    (f : QState (Reg n)) (x : Reg n) :
    ApplyGate (cnotGate n i j) f x = f (Function.update x j (x j ^^ x i)) := by
  rw [cnotGate, applyGate_permMatrix (cnotUpdate_involutive n i j hij)]

/-- Three actual CNOT updates interchange precisely the chosen two physical bits and preserve every other wire. -/
theorem capture_three_updates (n : ℕ) (i j : Fin n) (hij : i ≠ j) (x : Reg n) :
    (let x1 := Function.update x j (x j ^^ x i)
     let x2 := Function.update x1 i (x1 i ^^ x1 j)
     Function.update x2 j (x2 j ^^ x2 i)) =
      (fun k => if k=i then x j else if k=j then x i else x k) := by
  have hxor (a b : Bool) : (a ^^ (b ^^ a)) = b := by
    cases a <;> cases b <;> rfl
  funext k
  by_cases hki : k=i
  · subst k
    simp [Function.update, hij]
    exact hxor (x i) (x j)
  · by_cases hkj : k=j
    · subst k
      simp [Function.update, hij, Ne.symm hij]
    · simp [Function.update, hki, hkj]

/-- The full-register actual native three-CX capture swaps the selected amplitudes while leaving the entire address and all spectators untouched. -/
theorem captureSwapProgram_amplitude (n : ℕ) (i j : Fin n) (hij : i ≠ j)
    (f : QState (Reg n)) (x : Reg n) :
    Run (1 : Matrix (Reg n) (Reg n) ℂ) (captureSwapProgram n i j) f x =
      f (fun k => if k=i then x j else if k=j then x i else x k) := by
  change ApplyGate (cnotGate n i j) (ApplyGate (cnotGate n j i)
    (ApplyGate (cnotGate n i j) f)) x = _
  rw [capture_cnot_amplitude n i j hij,
    capture_cnot_amplitude n j i (Ne.symm hij), capture_cnot_amplitude n i j hij]
  rw [capture_three_updates n i j hij x]

/-- Three physical local wires consist of the current input spin and two distinct storage slots. -/
def captureTriple (live retained fresh : Bool → ℂ) (x : Reg 3) : ℂ :=
  live (x 0)*retained (x 1)*fresh (x 2)

/-- The first actual three-CX capture places the unknown input spin in slot one, with the live and second storage wires still clean. -/
theorem first_capture_clean (u : Bool → ℂ) :
    Run (1 : Matrix (Reg 3) (Reg 3) ℂ) (captureSwapProgram 3 0 1)
      (captureTriple u (Qatlib.Foundations.PureStateMath.Ket false) (Qatlib.Foundations.PureStateMath.Ket false)) =
      captureTriple (Qatlib.Foundations.PureStateMath.Ket false) u (Qatlib.Foundations.PureStateMath.Ket false) := by
  funext x
  rw [captureSwapProgram_amplitude 3 0 1 (by decide)]
  change u (x 1)*(Qatlib.Foundations.PureStateMath.Ket false (x 0))*(Qatlib.Foundations.PureStateMath.Ket false (x 2)) =
    (Qatlib.Foundations.PureStateMath.Ket false (x 0))*u (x 1)*(Qatlib.Foundations.PureStateMath.Ket false (x 2))
  ring

/-- After resetting the clean spectators and preparing the second supplied copy, the second actual three-CX capture preserves the first retained spin and fills slot two. -/
theorem second_capture_preserves_first (u v : Bool → ℂ) :
    Run (1 : Matrix (Reg 3) (Reg 3) ℂ) (captureSwapProgram 3 0 2)
      (captureTriple v u (Qatlib.Foundations.PureStateMath.Ket false)) = captureTriple (Qatlib.Foundations.PureStateMath.Ket false) u v := by
  funext x
  rw [captureSwapProgram_amplitude 3 0 2 (by decide)]
  change v (x 2)*u (x 1)*(Qatlib.Foundations.PureStateMath.Ket false (x 0)) =
    (Qatlib.Foundations.PureStateMath.Ket false (x 0))*u (x 1)*v (x 2)
  ring

/-- The two always-executed native capture words pay all six CX gates even when subsequent addresses do not match. -/
theorem two_captures_paid :
    GateCount (captureSwapProgram 3 0 1)+GateCount (captureSwapProgram 3 0 2)=6 ∧
    QueryCount (captureSwapProgram 3 0 1)+QueryCount (captureSwapProgram 3 0 2)=0 := by
  rw [(captureSwapProgram_counts 3 0 1).1, (captureSwapProgram_counts 3 0 2).1,
    (captureSwapProgram_counts 3 0 1).2, (captureSwapProgram_counts 3 0 2).2]
  norm_num

/-- The explicit local three-wire bit string identifies the live spin and both physical storage slots. -/
def captureReg (live first second : Bool) (i : Fin 3) : Bool :=
  if i=0 then live else if i=1 then first else second

/-- The first bit of the explicit local capture register is the live input bit. -/
@[simp] theorem captureReg_live (a b c : Bool) : captureReg a b c 0=a := rfl
/-- The second bit of the explicit local capture register is the first storage bit. -/
@[simp] theorem captureReg_first (a b c : Bool) : captureReg a b c 1=b := rfl
/-- The third bit of the explicit local capture register is the second storage bit. -/
@[simp] theorem captureReg_second (a b c : Bool) : captureReg a b c 2=c := rfl

/-- The first retained amplitude is obtained by the actual first three-CX circuit, not by an ideal relocation instruction. -/
def firstStoredSpin (u : Bool → ℂ) (s : Bool) : ℂ :=
  Run (1 : Matrix (Reg 3) (Reg 3) ℂ) (captureSwapProgram 3 0 1)
    (captureTriple u (Qatlib.Foundations.PureStateMath.Ket false) (Qatlib.Foundations.PureStateMath.Ket false)) (captureReg false s false)

/-- The actual first capture stores exactly the unknown input amplitude and leaves clean spectators. -/
theorem firstStoredSpin_eq (u : Bool → ℂ) : firstStoredSpin u=u := by
  funext s
  unfold firstStoredSpin
  rw [first_capture_clean]
  simp [captureTriple, Qatlib.Foundations.PureStateMath.Ket]

/-- The second capture really acts on the fresh input, the already retained unknown first spin and a fresh clean slot. -/
def twoCapturedSpins (u v : Bool → ℂ) (r : Reg 2) : ℂ :=
  Run (1 : Matrix (Reg 3) (Reg 3) ℂ) (captureSwapProgram 3 0 2)
    (captureTriple v (firstStoredSpin u) (Qatlib.Foundations.PureStateMath.Ket false)) (captureReg false (r 0) (r 1))

/-- The actual two sequential paid captures produce the correct pair state without copying the first retained spin. -/
theorem twoCapturedSpins_eq (u v : Bool → ℂ) : twoCapturedSpins u v=pairInput u v := by
  funext r
  unfold twoCapturedSpins
  rw [firstStoredSpin_eq, second_capture_preserves_first]
  simp [captureTriple, pairInput, Qatlib.Foundations.PureStateMath.Ket]

end Qatlib.Concepts.SpinorSampling.Retained.NativeCapture
