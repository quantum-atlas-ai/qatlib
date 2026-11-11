/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.RawMachine.PaidRationalZeroMachine
import Qatlib.Concepts.EffectiveGauge.RawMachine.PaidBoundMachineCall

set_option backward.isDefEq.respectTransparency false

/-!
# Paid Original Bound Zero

Raw Machine constructions for Effective Gauge.
Proves `bound_nonnegative`, `original_bound_zero_machine`.
-/

set_option autoImplicit false
open Turing
namespace Qatlib.Concepts.EffectiveGauge.RawMachine
open Qatlib.Concepts.EffectiveGauge.CodedFloor Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow
open Qatlib.Concepts.BitWordCompiler
open Qatlib.Concepts.FinitePrecision.ComputableInput.Arithmetic.SignedNatMachine
namespace PaidRationalZero

/-- Nonnegativity is derived from the original derivative-bound promise,
not imposed as a new numerical oracle on the source. -/
theorem bound_nonnegative (v : SpatialPoint → SpatialPoint) (order : ℕ)
    (answer : RedundantRational.Frac)
    (hb : ∀ alpha : Fin 3 → ℕ, (∑ i,alpha i)=order → ∀ X : SpatialPoint, InFundamentalCube X →
      ‖spatialWordPartial v (List.replicate (alpha 0) 0++List.replicate (alpha 1) 1++List.replicate (alpha 2) 2) X‖ ≤
        (RedundantRational.value answer : ℝ)) : 0≤RedundantRational.value answer := by
  let alpha : Fin 3 → ℕ := fun i => if i=0 then order else 0
  have ha : (∑ i,alpha i)=order := by simp [alpha]
  have h0 : InFundamentalCube (0 : SpatialPoint) := fun _ =>
    ⟨by simp, by simpa using physicalPeriod_pos.le⟩
  have h := hb alpha ha 0 h0
  have hn : (0 : ℝ)≤(RedundantRational.value answer : ℝ) := (norm_nonneg _).trans h
  exact_mod_cast hn

/-- One fixed machine tests the exact branch of the original compressed
bound. Its input is only the finite answer word; the derivative promise is
used solely to prove that this branch coincides with numerator cancellation. -/
theorem original_bound_zero_machine :
    ∃ (states coef : ℕ) (machine : TM0.Machine CanonicalCodec.TM.Symbol (Fin (states+1))), 0<coef ∧
      ∀ (v : SpatialPoint → SpatialPoint) (order : ℕ) (answer : RedundantRational.Frac),
        (∀ alpha : Fin 3 → ℕ, (∑ i,alpha i)=order → ∀ X : SpatialPoint, InFundamentalCube X →
          ‖spatialWordPartial v (List.replicate (alpha 0) 0++List.replicate (alpha 1) 1++List.replicate (alpha 2) 2) X‖ ≤
            (RedundantRational.value answer : ℝ)) →
        CanonicalCodec.Runs machine (PaidRationalBridge.encode answer)
          [decide (sourceMeanCompressedBound (RedundantRational.value answer)=0)]
          (coef*(1+(PaidRationalBridge.encode answer).length)^2)
          (coef*(1+(PaidRationalBridge.encode answer).length)^2) := by
  obtain ⟨states,coef,machine,hcoef,hrun⟩ := raw_machine
  refine ⟨states,coef,machine,hcoef,?_⟩
  intro v order answer hb
  simpa only [compressed_zero answer (bound_nonnegative v order answer hb)] using hrun answer

end PaidRationalZero
end Qatlib.Concepts.EffectiveGauge.RawMachine
