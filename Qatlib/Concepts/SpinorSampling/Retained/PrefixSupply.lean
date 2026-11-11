/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.Retained.PhysicalCapture
import Qatlib.Concepts.SpinorSampling.Retained.PhysicalBell

open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

/-!
# Ordinary new-prefix supply preserving fixed unknown storage

On the clean-prefix subspace, a new ordinary input prefix is tensored with
exactly the existing retained-spin amplitudes. The same physical wires,
measured cleanup and native capture/Bell words yield their full-register
Born identities. Canonical address measurement is supplied by consumers.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
namespace Qatlib.Concepts.SpinorSampling.Retained.PrefixSupply
open Qatlib
open Qatlib.Concepts.SpinorSampling.NativeRecords.ShiftCircuit
open Qatlib.Concepts.SpinorSampling.NativeRecords.NativeBridge
open Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin
open Qatlib.Concepts.SpinorSampling.Retained.NativeCapture
open Qatlib.Concepts.SpinorSampling.FiniteExecution.MeasuredReset
open Qatlib.Concepts.SpinorSampling.Retained.PhysicalCapture
open Qatlib.Concepts.SpinorSampling.Retained.PhysicalBell

/-- The coherent state left on one unchanged storage wire after the first measured cleanup. -/
def retainedCleanState {n : ℕ} (b : Fin n) (u : Bool → ℂ) : QState (Reg n) :=
  ∑ s : Bool, u s • Ket (Function.update (fun _ : Fin n => false) b s)

/-- The cleaned storage fibre has exactly the original two unknown amplitudes. -/
theorem retainedCleanState_read {n : ℕ} (b : Fin n) (u : Bool → ℂ) (s : Bool) :
    retainedCleanState b u (Function.update (fun _ : Fin n => false) b s)=u s := by
  have hi : Function.Injective (fun t : Bool => Function.update (fun _ : Fin n => false) b t) := by
    intro t v h
    simpa only [Function.update_self] using congrFun h b
  simp [retainedCleanState,Qatlib.Foundations.PureStateMath.Ket,hi.eq_iff]

/-- One ordinary new-prefix supply branch tensors its supplied spin with the previously stored amplitudes on the same physical wire. -/
def freshPrefixSupply {n : ℕ} (a b c : Fin n) (z : Reg n) (v : Bool → ℂ)
    (stored : QState (Reg n)) : QState (Reg n) :=
  physicalTripleState a b c z (captureTriple v
    (fun s => stored (Function.update (fun _ : Fin n => false) b s)) (Ket false))

/-- A new prefix supply preserves the retained unknown spin without cloning, controlling or inverting its preparation. -/
theorem freshPrefixSupply_retained {n : ℕ} (a b c : Fin n) (z : Reg n)
    (u v : Bool → ℂ) :
    freshPrefixSupply a b c z v (retainedCleanState b u)=
      physicalTripleState a b c z (captureTriple v u (Ket false)) := by
  unfold freshPrefixSupply
  simp_rw [retainedCleanState_read]

/-- The full-register physical fibre retains each local amplitude exactly at its actual embedded record. -/
theorem physicalTripleState_amplitude {n : ℕ} (a b c : Fin n)
    (hab : a≠b) (hac : a≠c) (hbc : b≠c) (z : Reg n)
    (φ : QState (Reg 3)) (t : Reg 3) :
    physicalTripleState a b c z φ (tofEmb a b c t z)=φ t := by
  have hi : Function.Injective (fun u : Reg 3 => tofEmb a b c u z) := by
    intro u v h
    have e := congrArg (tofRestr a b c) h
    simpa only [tofRestr_emb a b c hab hac hbc] using e
  simp [physicalTripleState,Qatlib.Foundations.PureStateMath.Ket,hi.eq_iff]

/-- The actual local Bell word touches only the two stored spins, leaving the live spin clean. -/
def storedBellWord3 : List (Qatlib.Concepts.SpinorSampling.NativeRecords.NativeBridge.MeasurementGate 3) :=
  [.native (.cx 1 2),.native (.h 1)]

/-- The same two actual primitives give exactly the original Bell amplitude on the stored pair. -/
theorem storedBellWord3_amplitude (u v : Bool → ℂ) (r : Reg 2) :
    Run (1 : Matrix (Reg 3) (Reg 3) ℂ)
      (Qatlib.Concepts.SpinorSampling.NativeRecords.NativeBridge.measurementProgram storedBellWord3)
      (captureTriple (Ket false) u v) (captureReg false (r 0) (r 1)) =
    Run (1 : Matrix (Reg 2) (Reg 2) ℂ) bellProgram (pairInput u v) r := by
  change ApplyGate (wireGate 3 1 Hadamard)
    (ApplyGate (cnotGate 3 1 2) (captureTriple (Ket false) u v))
      (captureReg false (r 0) (r 1)) = _
  rw [native_h_update,capture_cnot_amplitude 3 1 2 (by decide),
    capture_cnot_amplitude 3 1 2 (by decide),← pair_reg_eta r,bell_program_amplitude]
  simp [captureTriple,captureReg,Function.update,
    Qatlib.Foundations.PureStateMath.Ket]


/-- The same fixed physical storage word has the exact local three-wire Bell action. -/
theorem physicalBellProgram_triple_run {n : ℕ} (a b c : Fin n)
    (hab : a≠b) (hac : a≠c) (hbc : b≠c) (z : Reg n) (φ : QState (Reg 3)) :
    Run (1 : Matrix (Reg n) (Reg n) ℂ) (physicalBellProgram b c true)
      (physicalTripleState a b c z φ) =
      physicalTripleState a b c z
        (Run (1 : Matrix (Reg 3) (Reg 3) ℂ) (measurementProgram storedBellWord3) φ) := by
  let word : List (MeasurementGate n) := [.native (.cx b c),.native (.h b)]
  have he : physicalBellProgram b c true=measurementProgram word := rfl
  have hl : reflectionLegal (word.map measurementMatrix) := by
    intro g hg
    simp only [word,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,
      or_false,measurementMatrix,nativeMatrix] at hg
    rcases hg with rfl | rfl
    · exact hbc
    · exact hadamard_unitary
  have hw : ∀ g∈word.map measurementMatrix,reflectionGateWires g⊆{a,b,c} := by
    intro g hg
    simp only [word,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,
      or_false,measurementMatrix,nativeMatrix] at hg
    rcases hg with rfl | rfl <;> simp [reflectionGateWires,Finset.subset_iff]
  have hc : (word.map measurementMatrix).map (tofCoreGate a b c)=
      storedBellWord3.map measurementMatrix := by
    simp [word,storedBellWord3,measurementMatrix,nativeMatrix,tofCoreGate,tofCoreWire,
      Ne.symm hab,Ne.symm hac,Ne.symm hbc]
  rw [he]
  exact physicalTripleWord_run a b c hab hac hbc word storedBellWord3 hl hw hc z φ

/-- Every final full-register Bell-or-skip probability equals the actual original pair instrument. -/
theorem physicalBellProgram_triple_Born {n : ℕ} (a b c : Fin n)
    (hab : a≠b) (hac : a≠c) (hbc : b≠c) (z : Reg n)
    (u v : Bool → ℂ) (matched : Bool) (r : Reg 2) :
    BornProb (Run (1 : Matrix (Reg n) (Reg n) ℂ) (physicalBellProgram b c matched)
      (physicalTripleState a b c z (captureTriple (Ket false) u v)))
        (tofEmb a b c (captureReg false (r 0) (r 1)) z) =
      BornProb (Run (1 : Matrix (Reg 2) (Reg 2) ℂ) (postCaptureProgram matched)
        (pairInput u v)) r := by
  cases matched with
  | false =>
    change BornProb (physicalTripleState a b c z (captureTriple (Ket false) u v)) _ =
      BornProb (pairInput u v) r
    unfold BornProb
    rw [physicalTripleState_amplitude a b c hab hac hbc]
    simp [captureTriple,pairInput,Qatlib.Foundations.PureStateMath.Ket]
  | true =>
    rw [physicalBellProgram_triple_run a b c hab hac hbc]
    unfold BornProb
    rw [physicalTripleState_amplitude a b c hab hac hbc,storedBellWord3_amplitude]
    rfl

/-- The actual first capture, measured cleanup, independent prefix supply and second capture occur sequentially on the same fixed wires. -/
def twoFreshPhysicalCaptures {n : ℕ} (a b c : Fin n) (firstAddress secondAddress : Reg n)
    (u v : Bool → ℂ) : QState (Reg n) :=
  let first := Run (1 : Matrix (Reg n) (Reg n) ℂ) (captureSwapProgram n a b)
    (physicalTripleState a b c firstAddress (captureTriple u (Ket false) (Ket false)))
  let clean := Run (1 : Matrix (Reg n) (Reg n) ℂ)
    (measuredClearProgram (retainedCleanupWires b)
      (tofEmb a b c (captureReg false false false) firstAddress)) first
  let next := freshPrefixSupply a b c secondAddress v clean
  Run (1 : Matrix (Reg n) (Reg n) ℂ) (captureSwapProgram n a c) next

/-- No intermediate retained spin is replaced by an assumed ideal pair state. -/
theorem twoFreshPhysicalCaptures_run {n : ℕ} (a b c : Fin n)
    (hab : a≠b) (hac : a≠c) (hbc : b≠c) (firstAddress secondAddress : Reg n)
    (u v : Bool → ℂ) :
    twoFreshPhysicalCaptures a b c firstAddress secondAddress u v =
      physicalTripleState a b c secondAddress (captureTriple (Ket false) u v) := by
  dsimp only [twoFreshPhysicalCaptures]
  rw [physical_first_capture_cleanup a b c hab hac hbc]
  change Run (1 : Matrix (Reg n) (Reg n) ℂ) (captureSwapProgram n a c)
    (freshPrefixSupply a b c secondAddress v (retainedCleanState b u)) = _
  rw [freshPrefixSupply_retained,physical_second_capture a b c hab hac hbc]


/-- An actual boundary state is either a scalar all-zero register or an arbitrary unknown spin on one physical wire with every other wire clean. -/
def AtMostOnePhysicalSpin {n : ℕ} (φ : QState (Reg n)) : Prop :=
  (∃ c : ℂ,φ=c • Ket (fun _ : Fin n => false)) ∨
    ∃ (k : Fin n) (u : Bool → ℂ),φ=retainedCleanState k u

end Qatlib.Concepts.SpinorSampling.Retained.PrefixSupply
