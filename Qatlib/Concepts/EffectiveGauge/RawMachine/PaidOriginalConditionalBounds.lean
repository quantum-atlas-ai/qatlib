/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.RawMachine.PaidConditionalBoundBankBudget

set_option backward.isDefEq.respectTransparency false

/-!
# Paid Original Conditional Bounds

Raw Machine constructions for Effective Gauge.
Proves `original_bounds_bank`.
-/

set_option autoImplicit false
open Turing
namespace Qatlib.Concepts.EffectiveGauge.RawMachine
open Qatlib.Concepts.EffectiveGauge.CodedFloor Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow
open Qatlib.Concepts.BitWordCompiler
open Qatlib.Concepts.FinitePrecision.ComputableInput.Arithmetic.SignedNatMachine
open CanonicalCodec.TM
namespace PaidConditionalBoundBank

/-- The original positive-order bound promise supplies all needed answers.
The runtime flag is interpreted using its same first answer's derivative
bound, not an additional sign or real-number equality oracle. -/
theorem original_bounds_bank {states : ℕ}
    (machine : TM0.Machine CanonicalCodec.TM.Symbol (Fin (states+1))) :
    ∃ (compiledStates : ℕ) (compiled : TM0.Machine CanonicalCodec.TM.Symbol (Fin (compiledStates+1)))
      (coef : ℕ), 0<coef ∧
      ∀ (v : SpatialPoint → SpatialPoint), PaidBoundProtocol.MachinePositiveBounds v machine →
      ∃ (answers : Fin 9 → RedundantRational.Frac) (time space : Fin 9 → ℕ),
        let replies := fun i => PaidRationalBridge.encode (answers i)
        let flag := decide (sourceMeanCompressedBound (RedundantRational.value (answers 0))=0)
        let stop : Fin 9 := if flag then 0 else 8
        (∀ i,i.val≤stop.val → CanonicalCodec.Runs machine (CanonicalCodec.natBits (i.val+1))
          (replies i) (time i) (space i)) ∧
        CanonicalCodec.Runs compiled [] (bankOutput replies stop flag)
          (coef*(1+bankBudget replies time flag+(1+(bankOutput replies stop flag).length)^2))
          (coef*(1+bankBudget replies time flag+(1+(bankOutput replies stop flag).length)^2)) ∧
        (∀ tail,readBank (bankOutput replies stop flag++tail)=
          some (flag,(List.ofFn answers).take (if flag then 1 else 9),tail)) ∧
        ∀ (i : Fin 9),i.val≤stop.val → ∀ alpha : Fin 3 → ℕ,(∑ j,alpha j)=i.val+1 →
          ∀ X : SpatialPoint,InFundamentalCube X →
            ‖spatialWordPartial v (List.replicate (alpha 0) 0++List.replicate (alpha 1) 1++List.replicate (alpha 2) 2) X‖ ≤
              (RedundantRational.value (answers i) : ℝ) := by
  obtain ⟨compiledStates,compiled,coef,hcoef,hcompiled⟩ := bank_machine machine
  refine ⟨compiledStates,compiled,coef,hcoef,?_⟩
  intro v hb
  have h : ∀ i : Fin 9, ∃ (answer : RedundantRational.Frac) (time space : ℕ),
      CanonicalCodec.Runs machine (PaidBoundBank.queryBits i) (PaidRationalBridge.encode answer) time space ∧
      ∀ alpha : Fin 3 → ℕ,(∑ j,alpha j)=i.val+1 → ∀ X : SpatialPoint,InFundamentalCube X →
        ‖spatialWordPartial v (List.replicate (alpha 0) 0++List.replicate (alpha 1) 1++List.replicate (alpha 2) 2) X‖ ≤
          (RedundantRational.value answer : ℝ) := fun i => hb (i.val+1) (by omega)
  choose answers time space hrun hbound using h
  have hn := PaidRationalZero.bound_nonnegative v 1 (answers 0) (hbound 0)
  have hflag : decide (sourceMeanCompressedBound (RedundantRational.value (answers 0))=0)=
      decide ((answers 0).num.1=(answers 0).num.2) := by
    simp only [PaidRationalZero.compressed_zero (answers 0) hn]
  have hh := hcompiled answers time space (fun i _ => hrun i)
  rw [←hflag] at hh
  refine ⟨answers,time,space,(fun i _ => hrun i),hh,?_,?_⟩
  · exact read_bank answers _
  · exact fun i _ => hbound i

end PaidConditionalBoundBank
end Qatlib.Concepts.EffectiveGauge.RawMachine
