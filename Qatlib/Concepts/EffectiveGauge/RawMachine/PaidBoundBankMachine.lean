/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.RawMachine.PaidBoundBankExecution

set_option backward.isDefEq.respectTransparency false

/-!
# Paid Bound Bank Machine

Raw Machine constructions for Effective Gauge.
Defines `readMany`.
Proves `bank_machine`, `readMany_complete`, `bankOutput_encode`.
-/

set_option autoImplicit false
open Turing
namespace Qatlib.Concepts.EffectiveGauge.RawMachine
open Qatlib.Concepts.EffectiveGauge.CodedFloor Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow
open Qatlib.Concepts.BitWordCompiler
open Qatlib.Concepts.BitWordCompiler.WordComposition.PaidMachineSupport
open Qatlib.Concepts.FinitePrecision.ComputableInput.Arithmetic.SignedNatMachine
open CanonicalCodec.TM
namespace PaidBoundBank

/-- The coefficient depends on the fixed called program. This is not yet a
uniform interpreter or the full producer's linear-space theorem. -/
theorem bank_machine {states : ℕ}
    (machine : TM0.Machine CanonicalCodec.TM.Symbol (Fin (states+1))) :
    ∃ (compiledStates : ℕ) (compiled : TM0.Machine CanonicalCodec.TM.Symbol (Fin (compiledStates+1)))
      (coef : ℕ), 0<coef ∧
      ∀ (replies : Fin 9 → CanonicalCodec.Bits) (time space : Fin 9 → ℕ),
        (∀ i, CanonicalCodec.Runs machine (queryBits i) (replies i) (time i) (space i)) →
        CanonicalCodec.Runs compiled [] (bankOutput replies)
          (coef*(1+bankBudget replies time+(1+(bankOutput replies).length)^2))
          (coef*(1+bankBudget replies time+(1+(bankOutput replies).length)^2)) := by
  obtain ⟨compiledStates,compiled,coef,hcoef,hcompile⟩ :=
    Stacks.raw_compiler (program machine) rawSlot outputSlot
  refine ⟨compiledStates,compiled,coef,hcoef,?_⟩
  intro replies time space hrun
  obtain ⟨steps,hsteps,hclock⟩ := bank_execution machine replies time space hrun
  have hh := hcompile [] (bankOutput replies) steps default hsteps
  have hbound : coef*((1+([] : CanonicalCodec.Bits).length)^2+
      Stacks.stackRunClock (program machine) steps (TM2.init rawSlot [])+
      (1+(bankOutput replies).length)^2) ≤
      coef*(1+bankBudget replies time+(1+(bankOutput replies).length)^2) := by
    apply Nat.mul_le_mul_left
    simp only [List.length_nil,Nat.add_zero,Nat.one_pow]
    omega
  exact runs_mono hh hbound hbound

/-- Definition of read Many in the Raw Machine construction. -/
def readMany : ℕ → CanonicalCodec.Bits → Option (List RedundantRational.Frac × CanonicalCodec.Bits)
  | 0,bits => some ([],bits)
  | n+1,bits => do
    let (answer,tail) ← PaidRationalBridge.read bits
    let (rest,tail) ← readMany n tail
    pure (answer::rest,tail)

/-- Original `readMany_complete` guarantee for the `PaidBoundBankMachine` construction; the complete source hypotheses are retained. -/
theorem readMany_complete (answers : List RedundantRational.Frac) (tail : CanonicalCodec.Bits) :
    readMany answers.length (answers.flatMap PaidRationalBridge.encode++tail)=some (answers,tail) := by
  induction answers with
  | nil => rfl
  | cons answer rest ih =>
    simp [readMany,List.append_assoc,PaidRationalBridge.read_complete,ih]

/-- Original `bankOutput_encode` guarantee for the `PaidBoundBankMachine` construction; the complete source hypotheses are retained. -/
theorem bankOutput_encode (answers : Fin 9 → RedundantRational.Frac) :
    bankOutput (fun i => PaidRationalBridge.encode (answers i))=
      (List.ofFn answers).flatMap PaidRationalBridge.encode := by
  simp [bankOutput,emitted,List.ofFn_succ,List.append_assoc]

/-- Original `read_bank` guarantee for the `PaidBoundBankMachine` construction; the complete source hypotheses are retained. -/
theorem read_bank (answers : Fin 9 → RedundantRational.Frac) (tail : CanonicalCodec.Bits) :
    readMany 9 (bankOutput (fun i => PaidRationalBridge.encode (answers i))++tail)=
      some (List.ofFn answers,tail) := by
  rw [bankOutput_encode]
  simpa only [List.length_ofFn] using readMany_complete (List.ofFn answers) tail

/-- One fixed compiled bank runs the original positive-order bound program
nine times. Its returned finite payload contains those same nine answers. -/
theorem original_bounds_bank (v : SpatialPoint → SpatialPoint) {states : ℕ}
    (machine : TM0.Machine CanonicalCodec.TM.Symbol (Fin (states+1)))
    (hb : PaidBoundProtocol.MachinePositiveBounds v machine) :
    ∃ (compiledStates : ℕ) (compiled : TM0.Machine CanonicalCodec.TM.Symbol (Fin (compiledStates+1)))
      (coef : ℕ), 0<coef ∧
      ∃ (answers : Fin 9 → RedundantRational.Frac) (time space : Fin 9 → ℕ),
        (∀ i, CanonicalCodec.Runs machine (CanonicalCodec.natBits (i.val+1))
          (PaidRationalBridge.encode (answers i)) (time i) (space i)) ∧
        CanonicalCodec.Runs compiled [] (bankOutput (fun i => PaidRationalBridge.encode (answers i)))
          (coef*(1+bankBudget (fun i => PaidRationalBridge.encode (answers i)) time+
            (1+(bankOutput (fun i => PaidRationalBridge.encode (answers i))).length)^2))
          (coef*(1+bankBudget (fun i => PaidRationalBridge.encode (answers i)) time+
            (1+(bankOutput (fun i => PaidRationalBridge.encode (answers i))).length)^2)) ∧
        (∀ tail, readMany 9 (bankOutput (fun i => PaidRationalBridge.encode (answers i))++tail)=
          some (List.ofFn answers,tail)) ∧
        ∀ (i : Fin 9) (alpha : Fin 3 → ℕ), (∑ j,alpha j)=i.val+1 →
          ∀ X : SpatialPoint, InFundamentalCube X →
            ‖spatialWordPartial v (List.replicate (alpha 0) 0++List.replicate (alpha 1) 1++List.replicate (alpha 2) 2) X‖ ≤
              (RedundantRational.value (answers i) : ℝ) := by
  have h : ∀ i : Fin 9, ∃ (answer : RedundantRational.Frac) (time space : ℕ),
      CanonicalCodec.Runs machine (queryBits i) (PaidRationalBridge.encode answer) time space ∧
      ∀ alpha : Fin 3 → ℕ, (∑ j,alpha j)=i.val+1 → ∀ X : SpatialPoint, InFundamentalCube X →
        ‖spatialWordPartial v (List.replicate (alpha 0) 0++List.replicate (alpha 1) 1++List.replicate (alpha 2) 2) X‖ ≤
          (RedundantRational.value answer : ℝ) := fun i => hb (i.val+1) (by omega)
  choose answers time space hrun hbound using h
  obtain ⟨compiledStates,compiled,coef,hcoef,hcompiled⟩ := bank_machine machine
  exact ⟨compiledStates,compiled,coef,hcoef,answers,time,space,hrun,
    hcompiled _ _ _ hrun,read_bank answers,hbound⟩

end PaidBoundBank
end Qatlib.Concepts.EffectiveGauge.RawMachine
