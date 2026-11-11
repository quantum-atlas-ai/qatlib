/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.RawMachine.PaidRationalCodec
import Qatlib.Concepts.EffectiveGauge.HopfAtlas.SourceWord
import Qatlib.Concepts.BitWordCompiler.WordComposition.PaidMachineSupport.PaidRawMachineCall

/-!
# Paid Bound Machine Call

Raw Machine constructions for Effective Gauge.
Defines `MachinePositiveBounds`.
Proves `source_call_accurate`.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.RawMachine
open Qatlib.Concepts.EffectiveGauge.CodedFloor Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow
open Qatlib.Concepts.FinitePrecision.ComputableInput.Arithmetic.SignedNatMachine
open Qatlib.Concepts.BitWordCompiler
open Qatlib.Concepts.BitWordCompiler.WordComposition.PaidMachineSupport

namespace PaidBoundProtocol

/-- The original bound program is required only at positive orders. The
mathematical bound and the actual encoded answer come from the same run. -/
def MachinePositiveBounds (v : SpatialPoint → SpatialPoint) {states : ℕ}
    (machine : Turing.TM0.Machine CanonicalCodec.TM.Symbol (Fin (states+1))) : Prop :=
  ∀ order : ℕ, 0<order → ∃ (answer : RedundantRational.Frac) (time space : ℕ),
    CanonicalCodec.Runs machine (CanonicalCodec.natBits order) (PaidRationalBridge.encode answer) time space ∧
    ∀ alpha : Fin 3 → ℕ, (∑ i, alpha i)=order → ∀ X : SpatialPoint, InFundamentalCube X →
      ‖spatialWordPartial v (List.replicate (alpha 0) 0++List.replicate (alpha 1) 1++List.replicate (alpha 2) 2) X‖ ≤
        (RedundantRational.value answer : ℝ)

/-- From one original positive-order bound machine to its same returned
payload and actual simulation clock; finite-cache construction is separate. -/
theorem source_call_accurate (v : SpatialPoint → SpatialPoint) {states : ℕ}
    (machine : Turing.TM0.Machine CanonicalCodec.TM.Symbol (Fin (states+1)))
    (hb : MachinePositiveBounds v machine) (order : ℕ) (ho : 0<order) :
    ∃ (answer : RedundantRational.Frac) (time space steps : ℕ),
      CanonicalCodec.Runs machine (CanonicalCodec.natBits order) (PaidRationalBridge.encode answer) time space ∧
      CanonicalCodec.TM.Stacks.stackRun (RawCall.program machine) steps (RawCall.initial (CanonicalCodec.natBits order))=
        some ⟨none,default,Function.update (fun _ => []) RawCall.outputSlot (PaidRationalBridge.encode answer).reverse⟩ ∧
      CanonicalCodec.TM.Stacks.stackRunClock (RawCall.program machine) steps
          (RawCall.initial (CanonicalCodec.natBits order)) ≤ 10050*(1+(CanonicalCodec.natBits order).length+time)^2 ∧
      PaidRationalBridge.read (PaidRationalBridge.encode answer)=some (answer,[]) ∧
      ∀ alpha : Fin 3 → ℕ, (∑ i, alpha i)=order → ∀ X : SpatialPoint, InFundamentalCube X →
        ‖spatialWordPartial v (List.replicate (alpha 0) 0++List.replicate (alpha 1) 1++List.replicate (alpha 2) 2) X‖ ≤
          (RedundantRational.value answer : ℝ) := by
  obtain ⟨answer,time,space,hrun,hbound⟩ := hb order ho
  obtain ⟨steps,hsteps,hclock⟩ := RawCall.source_exec machine (CanonicalCodec.natBits order)
    (PaidRationalBridge.encode answer) time space hrun
  refine ⟨answer,time,space,steps,hrun,hsteps,hclock,?_,hbound⟩
  simpa only [List.append_nil] using PaidRationalBridge.read_complete answer []

end PaidBoundProtocol
end Qatlib.Concepts.EffectiveGauge.RawMachine
