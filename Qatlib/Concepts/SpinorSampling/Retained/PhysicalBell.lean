/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.Retained.NativeCapture
import Qatlib.Concepts.SpinorSampling.Retained.RetainedBellFlat

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

/-!
# Bell readout on fixed storage wires of the full register

Reuse the actual existing pair transport; every spectator and the literal
Born probability are retained. The conditional native word pays two gates
on a match and zero on a miss, after both captures have already been paid.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
namespace Qatlib.Concepts.SpinorSampling.Retained.PhysicalBell
open Qatlib
open Qatlib.Concepts.SpinorSampling.NativeRecords.ShiftCircuit
open Qatlib.Concepts.SpinorSampling.NativeRecords.NativeBridge
open Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin
open Qatlib.Concepts.SpinorSampling.Retained.NativeCapture
/-- The Bell circuit is actually skipped on an address mismatch, after both capture transfers have already occurred. -/
def postCaptureWord (matched : Bool) : List (MeasurementGate 2) :=
  if matched then bellWord else []

/-- The actual conditional post-capture measurement word uses no new primitive. -/
def postCaptureProgram (matched : Bool) : Circuit (Reg 2) :=
  measurementProgram (postCaptureWord matched)

/-- The actual conditional Bell word pays two gates on a match and zero on a miss; neither branch queries a target. -/
theorem postCaptureProgram_counts (matched : Bool) :
    GateCount (postCaptureProgram matched)=(if matched then 2 else 0) ∧
      QueryCount (postCaptureProgram matched)=0 := by
  constructor
  · calc GateCount (postCaptureProgram matched)=(postCaptureWord matched).length :=
           (measurement_program_counts _).2
         _ = _ := by cases matched <;> rfl
  · exact (measurement_program_counts _).1


/-- The two storage slots are physical wires in one unchanged full register. -/
def physicalStoredPair {n : ℕ} (a b : Fin n) : Unit × Bool → Fin n :=
  fun p => if p.2 then b else a

/-- Distinct storage wires give the existing canonical injection, with no routing instruction. -/
theorem physicalStoredPair_injective {n : ℕ} (a b : Fin n) (hab : a≠b) :
    Function.Injective (physicalStoredPair a b) := by
  intro x y h
  rcases x with ⟨⟨⟩,x⟩
  rcases y with ⟨⟨⟩,y⟩
  cases x <;> cases y <;> simp_all [physicalStoredPair]

/-- The full-register state stores the selected pair and all explicitly given spectator basis bits. -/
def physicalPairState {n : ℕ} (a b : Fin n) (z : Reg n) (φ : QState (Reg 2)) :
    QState (Reg n) :=
  pairedState (physicalStoredPair a b) (fun _ => φ) (fun w => Ket (z w.val))

/-- Rebuild a complete observed register without changing a single spectator wire. -/
def physicalPairRegister {n : ℕ} (a b : Fin n) (z : Reg n) (r : Reg 2) : Reg n :=
  fun k => if k=a then r 0 else if k=b then r 1 else z k

/-- Reading the embedded full-register pair returns its exact local amplitude. -/
theorem physicalPairState_amplitude {n : ℕ} (a b : Fin n) (hab : a≠b)
    (z : Reg n) (φ : QState (Reg 2)) (r : Reg 2) :
    physicalPairState a b z φ (physicalPairRegister a b z r)=φ r := by
  have hp : pairSite (physicalStoredPair a b) (physicalPairRegister a b z r) ()=r := by
    funext i
    fin_cases i <;> simp [pairSite,physicalStoredPair,physicalPairRegister,pairReg,Ne.symm hab]
  have hs (w : unusedWires (physicalStoredPair a b)) :
      physicalPairRegister a b z r w.val=z w.val := by
    have hwa : w.val≠a := by
      intro h
      exact w.property ⟨((),false),by simpa [physicalStoredPair] using h.symm⟩
    have hwb : w.val≠b := by
      intro h
      exact w.property ⟨((),true),by simpa [physicalStoredPair] using h.symm⟩
    simp only [physicalPairRegister,ite_eq_right hwa,ite_eq_right hwb]
  simp only [physicalPairState,pairedState,Fintype.prod_unique,hp,hs,Qatlib.Foundations.PureStateMath.Ket,ite_true,
    Finset.prod_const_one,mul_one]

/-- The actual same-slot conditional native Bell word acts on the full physical register. -/
def physicalBellProgram {n : ℕ} (a b : Fin n) (matched : Bool) : Circuit (Reg n) :=
  pairProgram (physicalStoredPair a b) (if matched then [()] else [])

/-- Exact whole-register execution follows from the existing paid Bell transport, including every spectator. -/
theorem physicalBellProgram_run {n : ℕ} (a b : Fin n) (hab : a≠b)
    (z : Reg n) (φ : QState (Reg 2)) (matched : Bool) :
    Run (1 : Matrix (Reg n) (Reg n) ℂ) (physicalBellProgram a b matched)
      (physicalPairState a b z φ) =
      physicalPairState a b z
        (Run (1 : Matrix (Reg 2) (Reg 2) ℂ) (postCaptureProgram matched) φ) := by
  cases matched with
  | false => rfl
  | true =>
    have h := one_pair_program_transport (physicalStoredPair a b)
      (physicalStoredPair_injective a b hab) () (fun _ => φ) (fun w => Ket (z w.val))
    change _ = pairedState (physicalStoredPair a b)
      (fun _ => Run (1 : Matrix (Reg 2) (Reg 2) ℂ) bellProgram φ) (fun w => Ket (z w.val))
    rw [show (fun _ : Unit => Run (1 : Matrix (Reg 2) (Reg 2) ℂ) bellProgram φ) =
      Function.update (fun _ : Unit => φ) ()
        (Run (1 : Matrix (Reg 2) (Reg 2) ℂ) bellProgram φ) by funext u; cases u; simp]
    exact h

/-- Actual full-register measurement probabilities equal the previously constructed local pair Born law. -/
theorem physicalBellProgram_Born {n : ℕ} (a b : Fin n) (hab : a≠b)
    (z : Reg n) (φ : QState (Reg 2)) (matched : Bool) (r : Reg 2) :
    BornProb (Run (1 : Matrix (Reg n) (Reg n) ℂ) (physicalBellProgram a b matched)
      (physicalPairState a b z φ)) (physicalPairRegister a b z r) =
      BornProb (Run (1 : Matrix (Reg 2) (Reg 2) ℂ) (postCaptureProgram matched) φ) r := by
  rw [physicalBellProgram_run a b hab]
  unfold BornProb
  rw [physicalPairState_amplitude a b hab]

/-- Every actual full-register Bell word has the same paid two-or-zero gate count and zero target queries. -/
theorem physicalBellProgram_counts {n : ℕ} (a b : Fin n) (matched : Bool) :
    GateCount (physicalBellProgram a b matched)=(if matched then 2 else 0) ∧
      QueryCount (physicalBellProgram a b matched)=0 := by
  have h := pair_program_counts (physicalStoredPair a b) (if matched then [()] else [])
  cases matched <;> simpa [physicalBellProgram] using h.symm


end Qatlib.Concepts.SpinorSampling.Retained.PhysicalBell
