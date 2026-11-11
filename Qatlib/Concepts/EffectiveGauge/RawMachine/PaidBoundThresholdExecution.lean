/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.RawMachine.PaidBoundThresholdControl

set_option backward.isDefEq.respectTransparency false

/-!
# Paid Bound Threshold Execution

Raw Machine constructions for Effective Gauge.
Defines `leftInput`, `rightInput`, `preparedInputs`.
Proves `consumed_inputs`, `compare_inputs`, `clear_first`.
-/

set_option autoImplicit false
open Turing
namespace Qatlib.Concepts.EffectiveGauge.RawMachine
open Qatlib.Concepts.EffectiveGauge.CodedFloor Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow
open Qatlib.Concepts.BitWordCompiler
open Qatlib.Concepts.FinitePrecision.ComputableInput.Arithmetic.SignedNatMachine
open CanonicalCodec.TM
namespace PaidBoundCompression.Threshold

/-- Definition of left Input in the Raw Machine construction. -/
def leftInput (q : RedundantRational.Frac) (j : ℕ) :=
  PaidSumProducts.input 256 (positiveDen q).num.1 j (positiveDen q).den.2
/-- Definition of right Input in the Raw Machine construction. -/
def rightInput (q : RedundantRational.Frac) (j : ℕ) :=
  PaidSumProducts.input 256 (positiveDen q).num.2 j (positiveDen q).den.1
/-- Definition of prepared Inputs in the Raw Machine construction. -/
def preparedInputs (q : RedundantRational.Frac) (j : ℕ) (right : Bool) : CanonicalCodec.Bits :=
  if right then (rightInput q j).reverse else (leftInput q j).reverse
/-- Definition of left Word in the Raw Machine construction. -/
def leftWord (q : RedundantRational.Frac) (j : ℕ) := (CanonicalCodec.natBits (leftSum q j)).reverse
/-- Definition of right Word in the Raw Machine construction. -/
def rightWord (q : RedundantRational.Frac) (j : ℕ) := (CanonicalCodec.natBits (rightSum q j)).reverse
/-- Definition of execution Budget in the Raw Machine construction. -/
def executionBudget (q : RedundantRational.Frac) (j : ℕ) :=
  (((((200000*(1+(leftInput q j).length)^3+200000*(1+(rightInput q j).length)^3)+
    100*(1+(leftWord q j).length+(rightWord q j).length)^2)+4)+
    ((leftWord q j).length^2+3*(leftWord q j).length+3))+
    ((rightWord q j).length^2+3*(rightWord q j).length+3))+1

/-- Original `consumed_inputs` guarantee for the `PaidBoundThresholdExecution` construction; the complete source hypotheses are retained. -/
private theorem consumed_inputs (q : RedundantRational.Frac) (j : ℕ) :
    Function.update (Function.update (preparedInputs q j) false []) true []=(fun _ => []) := by
  funext b
  cases b <;> rfl

/-- Original `compare_inputs` guarantee for the `PaidBoundThresholdExecution` construction; the complete source hypotheses are retained. -/
private theorem compare_inputs (left right : CanonicalCodec.Bits) :
    Function.update (Function.update (fun _ => []) (dest false) left) (dest true) right=
      ReadonlyCompare.store left right [] [] [] := by
  funext k
  cases k <;> rfl

/-- Original `clear_first` guarantee for the `PaidBoundThresholdExecution` construction; the complete source hypotheses are retained. -/
private theorem clear_first (left right : CanonicalCodec.Bits) :
    Function.update (ReadonlyCompare.store left right [] [] []) (dest false) []=
      ReadonlyCompare.store [] right [] [] [] := by
  funext k
  cases k <;> rfl

/-- Original `clear_second` guarantee for the `PaidBoundThresholdExecution` construction; the complete source hypotheses are retained. -/
private theorem clear_second (right : CanonicalCodec.Bits) :
    Function.update (ReadonlyCompare.store [] right [] [] []) (dest true) []=(fun _ => []) := by
  funext k
  cases k <;> rfl

/-- Original `output_only` guarantee for the `PaidBoundThresholdExecution` construction; the complete source hypotheses are retained. -/
private theorem output_only (out : CanonicalCodec.Bits) :
    state (fun _ => []) (fun _ => []) out (fun _ => [])=
      Function.update (fun _ => []) Slot.output out := by
  funext k
  cases k <;> rfl

/-- Original `done_step` guarantee for the `PaidBoundThresholdExecution` construction; the complete source hypotheses are retained. -/
private theorem done_step (out : CanonicalCodec.Bits) :
    Stacks.Execution program
      ⟨some .done,default,state (fun _ => []) (fun _ => []) out (fun _ => [])⟩
      ⟨none,default,Function.update (fun _ => []) Slot.output out⟩ 1 := by
  have hs : TM2.step program
      ⟨some .done,default,state (fun _ => []) (fun _ => []) out (fun _ => [])⟩=
      some ⟨none,default,Function.update (fun _ => []) Slot.output out⟩ := by
    simp only [TM2.step,program,TM2.stepAux,output_only]
  refine ⟨1,by rw [Stacks.run_one]; exact hs,?_⟩
  rw [Stacks.stackRunClock,hs]
  exact le_rfl

/-- Both inputs here are already assembled canonical argument words.
The same native execution computes the two sums, writes the threshold bit,
and clears every other stack and local register. It is not yet an original
raw-answer parser or a single-input TM0 implementation. -/
theorem prepared_execution (q : RedundantRational.Frac) (j : ℕ) :
    Stacks.Execution program
      ⟨some default,default,state (preparedInputs q j) (fun _ => []) [] (fun _ => [])⟩
      ⟨none,default,Function.update (fun _ => []) Slot.output [enoughBit q j]⟩
      (executionBudget q j) := by
  have el := sum_call false 256 (positiveDen q).num.1 j (positiveDen q).den.2
    (preparedInputs q j) (fun _ => []) [] rfl rfl
  have er := sum_call true 256 (positiveDen q).num.2 j (positiveDen q).den.1
    (Function.update (preparedInputs q j) false [])
    (Function.update (fun _ => []) (dest false) (leftWord q j)) [] rfl rfl
  have ec := compare_call (leftWord q j) (rightWord q j) []
  have et := choose_step (leftWord q j) (rightWord q j)
  let bit := decide (ReadonlyCompare.order (leftWord q j) (rightWord q j)≠BinaryCompare.Tag.gt)
  have edl := drain_call false (ReadonlyCompare.store (leftWord q j) (rightWord q j) [] [] []) [bit]
  have edr := drain_call true (ReadonlyCompare.store [] (rightWord q j) [] [] []) [bit]
  have ed := done_step [bit]
  change Stacks.Execution program
    ⟨some (.sum false default),default,state (preparedInputs q j) (fun _ => []) [] (fun _ => [])⟩
    _ _ at el
  change Stacks.Execution program _
    ⟨some (.compare default),default,
      state (Function.update (Function.update (preparedInputs q j) false []) true [])
        (Function.update (Function.update (fun _ => []) (dest false) (leftWord q j))
          (dest true) (rightWord q j)) [] (fun _ => [])⟩ _ at er
  rw [consumed_inputs,compare_inputs] at er
  rw [clear_first] at edl
  rw [clear_second] at edr
  have all := (((((el.trans er).trans ec).trans et).trans edl).trans edr).trans ed
  have hb : bit=enoughBit q j := by
    simp only [bit,leftWord,rightWord,threshold_order,enoughBit]
  have hl : (Label.sum false default : Label) = default := rfl
  simpa [hb,hl,executionBudget,leftInput,rightInput,dest,ReadonlyCompare.store] using all

/-- Original `prepared_length` guarantee for the `PaidBoundThresholdExecution` construction; the complete source hypotheses are retained. -/
theorem prepared_length (q : RedundantRational.Frac) (j : ℕ) :
    (leftInput q j).length+(rightInput q j).length=
      38+(PaidRationalBridge.encode q).length+2*(CanonicalCodec.natBits j).length := by
  have hl := positiveDen_length q
  simp only [PaidRationalBridge.encode,PaidFractionInverse.input,List.length_append] at hl
  simp only [leftInput,rightInput,PaidSumProducts.input_length]
  have hc : (CanonicalCodec.natBits 256).length=19 := by decide
  rw [hc]
  simp only [PaidRationalBridge.encode,PaidFractionInverse.input,List.length_append]
  omega

end PaidBoundCompression.Threshold
end Qatlib.Concepts.EffectiveGauge.RawMachine
