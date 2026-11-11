/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SCWFPrep24.Estimation.NullRisk.PaidMixture
import Qatlib.Concepts.SpinorSampling.FiniteExecution.MeasuredReset
import Qatlib.Concepts.SpinorSampling.Retained.PhysicalBell

open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

/-!
# Actual selected native words and physical resource traces

Supplies and measurement barriers are separate actions. Native gate and
query fees are derived from their existing circuit interpretations;
conditional resets use the same actual measured bits. Full branch selection
and source-instrument coupling are provided by the final consumer.
-/

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.SCWFPrep24.Estimation.NullRisk
open Qatlib
open Qatlib.Concepts.SpinorSampling.NativeRecords.ShiftCircuit
open Qatlib.Concepts.SpinorSampling.NativeRecords.NativeBridge
open Qatlib.Concepts.SpinorSampling.FiniteExecution.ElementaryReadout
open Qatlib.Concepts.SpinorSampling.FiniteExecution.MeasuredReset
open Qatlib.Concepts.SpinorSampling.Retained.NativeCapture
open Qatlib.Concepts.SpinorSampling.Retained.PhysicalBell

/-- Physical actions distinguish supply and measurement barriers from their actual native gate programs. -/
inductive PairPhysicalAction (n : ℕ) where
  | supply
  | native (word : List (MeasurementGate n))
  | capture (live storage : Fin n)
  | bell (first second : Fin n) (matched : Bool)
  | measure (wires : List (Fin n)) (outcome : Reg n)
  | cleanup (wires : List (Fin n)) (outcome : Reg n)

/-- Only actual native operations have a circuit interpretation; a supply or measurement is never silently an identity gate. -/
def PairPhysicalAction.gateProgram {n : ℕ} : PairPhysicalAction n → Option (Circuit (Reg n))
  | .supply => none
  | .native w => some (paidNativeProgram w)
  | .capture a b => some (captureSwapProgram n a b)
  | .bell a b matched => some (physicalBellProgram a b matched)
  | .measure _ _ => none
  | .cleanup ws x => some (measuredClearProgram ws x)

/-- A source request pays exactly one ordinary supplied copy. -/
def PairPhysicalAction.copies {n : ℕ} : PairPhysicalAction n → ℕ
  | .supply => 1
  | _ => 0

/-- The elementary fee is the actual existing circuit's GateCount, not a supplied price field. -/
def PairPhysicalAction.gates {n : ℕ} (a : PairPhysicalAction n) : ℕ :=
  match a.gateProgram with | none => 0 | some C => GateCount C

/-- The target-query fee is computed from the exact same circuit. -/
def PairPhysicalAction.queries {n : ℕ} (a : PairPhysicalAction n) : ℕ :=
  match a.gateProgram with | none => 0 | some C => QueryCount C

/-- Every recorded measurement names each physical measured wire. -/
def PairPhysicalAction.measurements {n : ℕ} : PairPhysicalAction n → ℕ
  | .measure ws _ => ws.length
  | _ => 0

/-- Every reset uses the observed bit and the actual conditional six-gate correction. -/
def PairPhysicalAction.resets {n : ℕ} : PairPhysicalAction n → ℕ
  | .cleanup ws _ => ws.length
  | _ => 0

/-- All physical register wires are explicitly enumerated for measurement and subsequent reuse. -/
def allPhysicalWires (n : ℕ) : List (Fin n) := List.ofFn id

/-- A current execution requests exactly the two selected copies and uses the actual neighbor coins and full measured records. -/
def currentPhysicalTrace (d r : ℕ) (j : Fin d)
    (z : CurrentObservation d r × CurrentObservation d r) : List (PairPhysicalAction (registerWidth d r)) :=
  [.supply,.native (velocityWord d r j z.1.1),
    .measure (allPhysicalWires _) z.1.2,.cleanup (allPhysicalWires _) z.1.2,
    .supply,.native (velocityWord d r j z.2.1),
    .measure (allPhysicalWires _) z.2.2,.cleanup (allPhysicalWires _) z.2.2]

/-- The trace pays both actual current words, all copies, every measurement and every conditional cleanup. -/
theorem currentPhysicalTrace_resources (d r : ℕ) (j : Fin d) (hr : 2≤r)
    (z : CurrentObservation d r × CurrentObservation d r) :
    ((currentPhysicalTrace d r j z).map PairPhysicalAction.copies).sum=2 ∧
    ((currentPhysicalTrace d r j z).map PairPhysicalAction.queries).sum=0 ∧
    ((currentPhysicalTrace d r j z).map PairPhysicalAction.gates).sum≤
      2*(15*(r-1)^2+5)+12*registerWidth d r ∧
    ((currentPhysicalTrace d r j z).map PairPhysicalAction.measurements).sum=2*registerWidth d r ∧
    ((currentPhysicalTrace d r j z).map PairPhysicalAction.resets).sum=2*registerWidth d r := by
  have h1 := paid_velocity_program_counts d r j z.1.1 hr
  have h2 := paid_velocity_program_counts d r j z.2.1 hr
  have c1 := measuredClearProgram_counts (allPhysicalWires (registerWidth d r)) z.1.2
  have c2 := measuredClearProgram_counts (allPhysicalWires (registerWidth d r)) z.2.2
  simp only [allPhysicalWires,List.length_ofFn] at c1 c2
  simp only [currentPhysicalTrace,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    PairPhysicalAction.copies,PairPhysicalAction.queries,PairPhysicalAction.gates,
    PairPhysicalAction.measurements,PairPhysicalAction.resets,PairPhysicalAction.gateProgram,
    h1.1,h1.2,h2.1,h2.2,c1.2,c2.2,allPhysicalWires,List.length_ofFn,add_zero,zero_add]
  exact ⟨trivial,trivial,by omega,by omega,by omega⟩

/-- The Bell trace measures the address before each capture and never measures the retained spin before the second supply. -/
def bellPhysicalTrace {n : ℕ} (a b c : Fin n) (addressWires : List (Fin n))
    (firstAddress secondAddress : Reg n) (matched : Bool) (r : Reg 2) : List (PairPhysicalAction n) :=
  let beforeSecond := Qatlib.Concepts.GateVocabulary.LocalReflectionGates.tofEmb a b c
    (captureReg false false false) firstAddress
  let final := Qatlib.Concepts.GateVocabulary.LocalReflectionGates.tofEmb a b c
    (captureReg false (r 0) (r 1)) secondAddress
  show List (PairPhysicalAction n) from
  [.supply,.measure addressWires firstAddress,.capture a b,
    .measure (retainedCleanupWires b) beforeSecond,
    .cleanup (retainedCleanupWires b) beforeSecond,
    .supply,.measure addressWires secondAddress,.capture a c,.bell b c matched,
    .measure (allPhysicalWires n) final,.cleanup (allPhysicalWires n) final]

/-- The retained-storage cleanup contains exactly the other n−1 physical wires. -/
theorem retainedCleanupWires_length {n : ℕ} (b : Fin n) :
    (retainedCleanupWires b).length=n-1 := by
  rw [retainedCleanupWires,← (List.nodup_finRange n).erase_eq_filter b]
  rw [List.length_erase_of_mem (by simp)]
  simp

/-- Every actual Bell run pays both captures even on a miss, and cleanup fees are derived from the observed corrections. -/
theorem bellPhysicalTrace_resources {n : ℕ} (a b c : Fin n)
    (addressWires : List (Fin n)) (haddr : addressWires.length≤n)
    (firstAddress secondAddress : Reg n) (matched : Bool) (r : Reg 2) :
    ((bellPhysicalTrace a b c addressWires firstAddress secondAddress matched r).map
      PairPhysicalAction.copies).sum=2 ∧
    ((bellPhysicalTrace a b c addressWires firstAddress secondAddress matched r).map
      PairPhysicalAction.queries).sum=0 ∧
    ((bellPhysicalTrace a b c addressWires firstAddress secondAddress matched r).map
      PairPhysicalAction.gates).sum≤6+(if matched then 2 else 0)+12*n ∧
    ((bellPhysicalTrace a b c addressWires firstAddress secondAddress matched r).map
      PairPhysicalAction.measurements).sum≤4*n ∧
    ((bellPhysicalTrace a b c addressWires firstAddress secondAddress matched r).map
      PairPhysicalAction.resets).sum≤2*n := by
  have h1 := captureSwapProgram_counts n a b
  have h2 := captureSwapProgram_counts n a c
  have hb := physicalBellProgram_counts b c matched
  have c1 := measuredClearProgram_counts (retainedCleanupWires b)
    (Qatlib.Concepts.GateVocabulary.LocalReflectionGates.tofEmb a b c
      (captureReg false false false) firstAddress)
  have c2 := measuredClearProgram_counts (allPhysicalWires n)
    (Qatlib.Concepts.GateVocabulary.LocalReflectionGates.tofEmb a b c
      (captureReg false (r 0) (r 1)) secondAddress)
  rw [retainedCleanupWires_length] at c1
  simp only [allPhysicalWires,List.length_ofFn] at c2
  simp only [bellPhysicalTrace,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    PairPhysicalAction.copies,PairPhysicalAction.queries,PairPhysicalAction.gates,
    PairPhysicalAction.measurements,PairPhysicalAction.resets,PairPhysicalAction.gateProgram,
    h1.1,h1.2,h2.1,h2.2,hb.1,hb.2,c1.2,c2.2,allPhysicalWires,List.length_ofFn,
    retainedCleanupWires_length,add_zero,zero_add]
  exact ⟨trivial,trivial,by omega,by omega,by omega⟩

end Qatlib.Papers.SCWFPrep24.Estimation.NullRisk
