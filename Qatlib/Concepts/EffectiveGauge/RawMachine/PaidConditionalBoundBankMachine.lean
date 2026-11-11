/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.RawMachine.PaidConditionalBoundBankExecution

set_option backward.isDefEq.respectTransparency false

/-!
# Paid Conditional Bound Bank Machine

Raw Machine constructions for Effective Gauge.
Defines `readBank`.
Proves `bank_machine`, `output_true`, `output_false`.
-/

set_option autoImplicit false
open Turing
namespace Qatlib.Concepts.EffectiveGauge.RawMachine
open Qatlib.Concepts.EffectiveGauge.CodedFloor Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow
open Qatlib.Concepts.BitWordCompiler
open Qatlib.Concepts.FinitePrecision.ComputableInput.Arithmetic.SignedNatMachine
open CanonicalCodec.TM
namespace PaidConditionalBoundBank

/-- Specialize only to the source program M. The compiled machine precedes
all answer words and run bounds; the runtime flag is not a compiler input. -/
theorem bank_machine {states : ℕ}
    (machine : TM0.Machine CanonicalCodec.TM.Symbol (Fin (states+1))) :
    ∃ (compiledStates : ℕ) (compiled : TM0.Machine CanonicalCodec.TM.Symbol (Fin (compiledStates+1)))
      (coef : ℕ), 0<coef ∧
      ∀ (answers : Fin 9 → RedundantRational.Frac) (time space : Fin 9 → ℕ),
        (∀ i,i.val≤(if decide ((answers 0).num.1=(answers 0).num.2) then (0 : Fin 9) else 8).val →
          CanonicalCodec.Runs machine (PaidBoundBank.queryBits i)
            (PaidRationalBridge.encode (answers i)) (time i) (space i)) →
        let replies := fun i => PaidRationalBridge.encode (answers i)
        let flag := decide ((answers 0).num.1=(answers 0).num.2)
        let output := bankOutput replies (if flag then 0 else 8) flag
        CanonicalCodec.Runs compiled [] output
          (coef*(1+bankBudget replies time flag+(1+output.length)^2))
          (coef*(1+bankBudget replies time flag+(1+output.length)^2)) := by
  obtain ⟨compiledStates,compiled,coef,hcoef,hcompile⟩ := Stacks.raw_compiler (program machine) sourceRaw outputSlot
  refine ⟨compiledStates,compiled,coef,hcoef,?_⟩
  intro answers time space hrun
  obtain ⟨steps,hr,hc⟩ := bank_execution machine answers time space hrun
  have hh := hcompile [] _ steps default hr
  apply runs_mono hh
  all_goals
    apply Nat.mul_le_mul_left
    simp only [List.length_nil,List.reverse_nil,Nat.add_zero,Nat.one_pow]
    omega

/-- Definition of read Bank in the Raw Machine construction. -/
def readBank (bits : CanonicalCodec.Bits) : Option (Bool × List RedundantRational.Frac × CanonicalCodec.Bits) :=
  match bits with
  | [] => none
  | flag::tail => do
    let (answers,rest) ← PaidBoundBank.readMany (if flag then 1 else 9) tail
    pure (flag,answers,rest)

/-- Original `output_true` guarantee for the `PaidConditionalBoundBankMachine` construction; the complete source hypotheses are retained. -/
private theorem output_true (answers : Fin 9 → RedundantRational.Frac) :
    bankOutput (fun i => PaidRationalBridge.encode (answers i)) 0 true=
      true::PaidRationalBridge.encode (answers 0) := by
  simp [bankOutput,PaidBoundBank.emitted,activeReplies]

/-- Original `output_false` guarantee for the `PaidConditionalBoundBankMachine` construction; the complete source hypotheses are retained. -/
private theorem output_false (answers : Fin 9 → RedundantRational.Frac) :
    bankOutput (fun i => PaidRationalBridge.encode (answers i)) 8 false=
      false::(List.ofFn answers).flatMap PaidRationalBridge.encode := by
  have ha : activeReplies (fun i => PaidRationalBridge.encode (answers i)) 8=
      (fun i => PaidRationalBridge.encode (answers i)) := by
    funext j
    exact if_pos (by have hj := j.isLt; omega)
  dsimp only [bankOutput]
  rw [ha]
  change false::PaidBoundBank.bankOutput (fun i => PaidRationalBridge.encode (answers i))=_
  rw [PaidBoundBank.bankOutput_encode]

/-- The same serialized branch bit determines whether exactly one or nine
original raw answers are parsed. This remains proof-side codec correctness. -/
theorem read_bank (answers : Fin 9 → RedundantRational.Frac) (flag : Bool) (tail : CanonicalCodec.Bits) :
    readBank (bankOutput (fun i => PaidRationalBridge.encode (answers i)) (if flag then 0 else 8) flag++tail)=
      some (flag,(List.ofFn answers).take (if flag then 1 else 9),tail) := by
  cases flag with
  | false =>
    have hr := PaidBoundBank.readMany_complete (List.ofFn answers) tail
    simp only [List.length_ofFn] at hr
    have ht : (List.ofFn answers).take 9=List.ofFn answers := by
      apply List.take_of_length_le
      simp
    simp only [Bool.false_eq_true,if_false,output_false,List.cons_append,readBank,hr,ht]
    rfl
  | true =>
    have hr := PaidBoundBank.readMany_complete [answers 0] tail
    have ht : (List.ofFn answers).take 1=[answers 0] := by
      rw [List.ofFn_succ]
      rfl
    simp only [if_true,output_true,List.cons_append,readBank,ht]
    simp only [List.length_singleton,List.flatMap_cons,List.flatMap_nil,List.append_nil] at hr
    rw [hr]
    rfl


end PaidConditionalBoundBank
end Qatlib.Concepts.EffectiveGauge.RawMachine
