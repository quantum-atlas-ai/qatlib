/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.RawMachine.PaidConditionalBoundBankControl

set_option backward.isDefEq.respectTransparency false

/-!
# Paid Conditional Bound Zero Call

Raw Machine constructions for Effective Gauge.
Proves `zero_frame_target`, `zero_call`, `choose_after_first`.
-/

set_option autoImplicit false
open Turing
namespace Qatlib.Concepts.EffectiveGauge.RawMachine
open Qatlib.Concepts.EffectiveGauge.CodedFloor Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow
open Qatlib.Concepts.BitWordCompiler
open Qatlib.Concepts.FinitePrecision.ComputableInput.Arithmetic.SignedNatMachine
open CanonicalCodec.TM
namespace PaidConditionalBoundBank

/-- Original `zero_frame_target` guarantee for the `PaidConditionalBoundZeroCall` construction; the complete source hypotheses are retained. -/
private theorem zero_frame_target (S T : Slot → CanonicalCodec.Bits)
    (data : PaidBoundZeroRetention.Slot → CanonicalCodec.Bits)
    (hi : ∀ k,T (zeroCode k)=data k)
    (ho : ∀ j,(∀ k,zeroCode k≠j) → T j=S j) : StackCall.frame zeroCode S data=T := by
  classical
  funext j
  by_cases hj : ∃ k,zeroCode k=j
  · obtain ⟨k,rfl⟩ := hj
    rw [StackCall.frame_at zeroCode S data zeroCode_injective,hi]
  · rw [WordValidator.frame_outside zeroCode S data j (by simpa using hj)]
    exact (ho j (by simpa using hj)).symm

/-- The parent consumes exactly its saved first answer. The native copy and
zero test preserve all saved answers and use no additional source call. -/
theorem zero_call {states : ℕ}
    (machine : TM0.Machine CanonicalCodec.TM.Symbol (Fin (states+1)))
    (saved : Fin 9 → CanonicalCodec.Bits) (q : RedundantRational.Frac)
    (hfirst : saved 0=PaidRationalBridge.encode q) :
    Stacks.Execution (program machine)
      ⟨some (.zero (.copy .emit)),default,state saved [] [] (fun _ => []) (fun _ => [])⟩
      ⟨some .decide,default,state saved [] [] (fun _ => [])
        (Function.update (fun _ => []) PaidRationalZero.outputSlot [decide (q.num.1=q.num.2)])⟩
      (11026*(1+(PaidRationalBridge.encode q).length)^2) := by
  let S := state saved [] [] (fun _ => []) (fun _ => [])
  let T := state saved [] [] (fun _ => [])
      (Function.update (fun _ => []) PaidRationalZero.outputSlot [decide (q.num.1=q.num.2)])
  let first := PaidBoundZeroRetention.state (PaidRationalBridge.encode q) (fun _ => [])
  let last := PaidBoundZeroRetention.state (PaidRationalBridge.encode q)
      (Function.update (fun _ => []) PaidRationalZero.outputSlot [decide (q.num.1=q.num.2)])
  have hi : StackCall.frame zeroCode S first=S := by
    apply StackCall.frame_same zeroCode S first zeroCode_injective
    intro k
    cases k with
    | inl k => rfl
    | inr k =>
      fin_cases k
      · exact hfirst
      · rfl
  have hf : StackCall.frame zeroCode S last=T := by
    apply zero_frame_target S T last
    · intro k
      cases k with
      | inl k => rfl
      | inr k =>
        fin_cases k
        · exact hfirst
        · rfl
    · intro j hj
      cases j with
      | inl j => rfl
      | inr j =>
        cases j with
        | inl j => exact (hj (.inl j) rfl).elim
        | inr j => rfl
  change StackCall.frame zeroCode S
    (PaidBoundZeroRetention.state (PaidRationalBridge.encode q) (fun _ => []))=S at hi
  change StackCall.frame zeroCode S
    (PaidBoundZeroRetention.state (PaidRationalBridge.encode q)
      (Function.update (fun _ => []) PaidRationalZero.outputSlot [decide (q.num.1=q.num.2)]))=T at hf
  obtain ⟨steps,hr,hc⟩ := PaidBoundZeroRetention.retained_zero_execution q
  obtain ⟨hn,hnc⟩ := StackCall.execution zeroCode Label.zero .decide id (fun _ v => v)
    (StackCall.frame zeroCode S)
    (fun data k => StackCall.frame_at zeroCode S data zeroCode_injective k)
    (fun data k b => StackCall.frame_update zeroCode S data zeroCode_injective k b)
    (fun _ _ => rfl) (fun _ _ _ => rfl) PaidBoundZeroRetention.program (program machine)
    (fun _ => rfl) default steps _ _ hr
  refine ⟨steps,?_,?_⟩
  · simpa only [StackCall.cfg,Option.map_some,Option.getD_some,Option.map_none,Option.getD_none,hi,hf] using hn
  · simpa only [StackCall.cfg,Option.map_some,Option.getD_some,hi] using hnc.trans_le hc

/-- This is the actual tested branch of the parent program, with the same
flag serialized before the one-or-nine answer payload. -/
theorem choose_after_first {states : ℕ}
    (machine : TM0.Machine CanonicalCodec.TM.Symbol (Fin (states+1)))
    (saved : Fin 9 → CanonicalCodec.Bits) (q : RedundantRational.Frac)
    (hfirst : saved 0=PaidRationalBridge.encode q) :
    Stacks.Execution (program machine)
      ⟨some (.zero (.copy .emit)),default,state saved [] [] (fun _ => []) (fun _ => [])⟩
      ⟨some (branchChoice (decide (q.num.1=q.num.2))),default,
        state saved [decide (q.num.1=q.num.2)] [] (fun _ => []) (fun _ => [])⟩
      (11033*(1+(PaidRationalBridge.encode q).length)^2) := by
  have ee := (zero_call machine saved q hfirst).trans
    (decide_step machine saved (decide (q.num.1=q.num.2)))
  apply ee.mono
  have hp : 1≤(1+(PaidRationalBridge.encode q).length)^2 := Nat.one_le_pow 2 _ (by omega)
  omega

end PaidConditionalBoundBank
end Qatlib.Concepts.EffectiveGauge.RawMachine
