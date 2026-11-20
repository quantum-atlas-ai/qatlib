/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.FinitePrecision.ComputableInput.NativeArithmetic.SignedNatMachine.PaidFractionInverse
public import Qatlib.Concepts.FinitePrecision.ComputableInput.NativeArithmetic.SignedNatMachine.RedundantRational
public import Qatlib.Concepts.EffectiveGauge.CodedFloor.FloorRationalCode

@[expose] public section

/-!
# Paid Rational Bridge

Raw Machine constructions for Effective Gauge.
Defines `ofFloorCode`, `encode`.
Proves `ofFloorCode_value`, `inverse_output_codec`, `inverse_machine`.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.RawMachine
open Qatlib.Concepts.EffectiveGauge.CodedFloor

namespace PaidRationalBridge
open Qatlib.Concepts.FinitePrecision.ComputableInput.Arithmetic.SignedNatMachine
open Qatlib.Concepts.BitWordCompiler

/-- Definition of of Floor Code in the Raw Machine construction. -/
def ofFloorCode (q : FloorRationalCode) : RedundantRational.Frac :=
  ⟨q.1,(q.2+1,0),by omega⟩

/-- Definition of encode in the Raw Machine construction. -/
def encode (q : RedundantRational.Frac) : CanonicalCodec.Bits := PaidFractionInverse.input q.num.1 q.num.2 q.den.1 q.den.2

/-- The redundant fraction constructed from a floor rational code represents the same quotient, with the signed numerator over the stored denominator plus one. -/
theorem ofFloorCode_value (q : FloorRationalCode) : RedundantRational.value (ofFloorCode q)=floorRationalCodeValue q := by
  simp only [RedundantRational.value,ofFloorCode,RedundantRational.Pair.value,floorRationalCodeValue,Nat.cast_zero,sub_zero]

/-- The fraction-inversion output on the four natural entries of a redundant fraction is exactly the encoding of its total inverse. -/
theorem inverse_output_codec (q : RedundantRational.Frac) :
    PaidFractionInverse.output q.num.1 q.num.2 q.den.1 q.den.2=encode (RedundantRational.inv q) := by
  by_cases h : q.num.1=q.num.2
  · simp only [PaidFractionInverse.output,ite_eq_left h,RedundantRational.inv,dite_eq_left h,RedundantRational.ofNat,encode,PaidFractionInverse.input,PaidFractionInverse.zeroCodec]
  · simp only [PaidFractionInverse.output,ite_eq_right h,RedundantRational.inv,dite_eq_right h,encode,PaidFractionInverse.input]

/-- One fixed binary TM0, actual framed input/output and measured time/space.
This primitive bridge does not include ABI conversion or the whole solver. -/
theorem inverse_machine :
    ∃ (states coef : ℕ) (machine : Turing.TM0.Machine CanonicalCodec.TM.Symbol (Fin (states+1))),
      0<coef ∧ ∀ q : RedundantRational.Frac,
        CanonicalCodec.Runs machine (encode q) (encode (RedundantRational.inv q))
          (coef*(1+(encode q).length)^2) (coef*(1+(encode q).length)^2) ∧
        RedundantRational.value (RedundantRational.inv q)=(RedundantRational.value q)⁻¹ := by
  obtain ⟨states,coef,machine,hcoef,hrun⟩ := PaidFractionInverse.raw_inverse
  refine ⟨states,coef,machine,hcoef,?_⟩
  intro q
  refine ⟨?_,RedundantRational.value_inv q⟩
  rw [← inverse_output_codec q]
  exact hrun q.num.1 q.num.2 q.den.1 q.den.2

end PaidRationalBridge
end Qatlib.Concepts.EffectiveGauge.RawMachine
