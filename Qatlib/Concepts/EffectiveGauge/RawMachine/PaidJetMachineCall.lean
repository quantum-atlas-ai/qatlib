/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.RawMachine.PaidOriginalJetCodec
import Qatlib.Concepts.EffectiveGauge.HopfAtlas.SourceWord
import Qatlib.Concepts.BitWordCompiler.WordComposition.PaidMachineSupport.PaidRawMachineCall

/-!
# Paid Jet Machine Call

Raw Machine constructions for Effective Gauge.
Defines `MachineAccurate`.
Proves `source_call`, `source_call_accurate`.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.RawMachine
open Qatlib.Concepts.EffectiveGauge.CodedFloor Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow
open Qatlib.Concepts.BitWordCompiler
open Qatlib.Concepts.BitWordCompiler.WordComposition.PaidMachineSupport

namespace PaidJetProtocol

/-- Input promise about an actual finite source machine, only on the
canonical encodings of the original rational queries. Arbitrary redundant
query encodings are not silently added to the source's obligations. -/
def MachineAccurate (v : SpatialPoint → SpatialPoint) {states : ℕ}
    (machine : Turing.TM0.Machine CanonicalCodec.TM.Symbol (Fin (states+1))) : Prop :=
  ∀ (X : Fin 3 → ℚ) (alpha : Fin 3 → ℕ) (b : ℕ),
    (∀ i, 0 ≤ (X i : ℝ) ∧ (X i : ℝ) ≤ physicalPeriod) →
    ∃ (reply : Reply) (time space : ℕ),
      CanonicalCodec.Runs machine (encodeQuery (queryOfOriginal ((X,alpha),b))) (encodeReply reply) time space ∧
      ∀ j, |(replyValue reply j : ℝ)-spatialWordPartial v
        (List.replicate (alpha 0) 0++List.replicate (alpha 1) 1++List.replicate (alpha 2) 2)
        (rationalSpatialPoint X) j| ≤ (2^b : ℝ)⁻¹

/-- The actual source machine is simulated on the actual encoded input.
This pays the call from that input stack; query construction and parsing
costs are separate obligations, as is the complete positive solver. -/
theorem source_call {states : ℕ}
    (machine : Turing.TM0.Machine CanonicalCodec.TM.Symbol (Fin (states+1)))
    (query : Query) (reply : Reply) (time space : ℕ)
    (hrun : CanonicalCodec.Runs machine (encodeQuery query) (encodeReply reply) time space) :
    ∃ steps,
      CanonicalCodec.TM.Stacks.stackRun (RawCall.program machine) steps (RawCall.initial (encodeQuery query))=
        some ⟨none,default,Function.update (fun _ => []) RawCall.outputSlot (encodeReply reply).reverse⟩ ∧
      CanonicalCodec.TM.Stacks.stackRunClock (RawCall.program machine) steps (RawCall.initial (encodeQuery query)) ≤
        10050*(1+(encodeQuery query).length+time)^2 ∧
      readReply (encodeReply reply)=some (reply,[]) := by
  obtain ⟨steps,hsteps,hclock⟩ := RawCall.source_exec machine (encodeQuery query) (encodeReply reply) time space hrun
  refine ⟨steps,hsteps,hclock,?_⟩
  simpa only [List.append_nil] using readReply_complete reply []

/-- Literal original Cauchy accuracy and the clock refer to the same
returned reply. There is no value-source function oracle in the program. -/
theorem source_call_accurate (v : SpatialPoint → SpatialPoint) {states : ℕ}
    (machine : Turing.TM0.Machine CanonicalCodec.TM.Symbol (Fin (states+1))) (hs : MachineAccurate v machine)
    (X : Fin 3 → ℚ) (alpha : Fin 3 → ℕ) (b : ℕ)
    (hX : ∀ i, 0 ≤ (X i : ℝ) ∧ (X i : ℝ) ≤ physicalPeriod) :
    ∃ (reply : Reply) (time space steps : ℕ),
      CanonicalCodec.Runs machine (encodeQuery (queryOfOriginal ((X,alpha),b))) (encodeReply reply) time space ∧
      CanonicalCodec.TM.Stacks.stackRun (RawCall.program machine) steps
          (RawCall.initial (encodeQuery (queryOfOriginal ((X,alpha),b))))=
        some ⟨none,default,Function.update (fun _ => []) RawCall.outputSlot (encodeReply reply).reverse⟩ ∧
      CanonicalCodec.TM.Stacks.stackRunClock (RawCall.program machine) steps
          (RawCall.initial (encodeQuery (queryOfOriginal ((X,alpha),b)))) ≤
        10050*(1+(encodeQuery (queryOfOriginal ((X,alpha),b))).length+time)^2 ∧
      readReply (encodeReply reply)=some (reply,[]) ∧
      ∀ j, |(replyValue reply j : ℝ)-spatialWordPartial v
        (List.replicate (alpha 0) 0++List.replicate (alpha 1) 1++List.replicate (alpha 2) 2)
        (rationalSpatialPoint X) j| ≤ (2^b : ℝ)⁻¹ := by
  obtain ⟨reply,time,space,hrun,haccuracy⟩ := hs X alpha b hX
  obtain ⟨steps,hsteps,hclock,hparse⟩ := source_call machine _ reply time space hrun
  exact ⟨reply,time,space,steps,hrun,hsteps,hclock,hparse,haccuracy⟩

end PaidJetProtocol
end Qatlib.Concepts.EffectiveGauge.RawMachine
