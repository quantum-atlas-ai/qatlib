/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.CodedFloor.FloorNegativeExpBackendCode

/-!
# Floor Full Negative Exp Code

Coded Floor constructions for Effective Gauge.
Defines `floorNegativeExpReducedArguments`, `floorClampScalarResultCode`, `floorRationalNegativeExpCode`.
Proves `floorNegativeExpReducedArguments_value`, `floorClampScalarResultCode_value`, `floorRationalNegativeExpCode_value`.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.CodedFloor
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Definition of floor Negative Exp Reduced Arguments in the Coded Floor construction. -/
def floorNegativeExpReducedArguments (p : FloorExpCodeParameters) : FloorExpCodeParameters :=
  let scale := floorRationalCodePow (floorRationalCodeNat 2) (floorNegativeExpHalvingsCode p.1)
  (floorRationalCodeMul p.1 (floorRationalCodeInv scale),
    floorRationalCodeMul p.2 (floorRationalCodeInv scale))

/-- Definition of floor Clamp Scalar Result Code in the Coded Floor construction. -/
def floorClampScalarResultCode (r : FloorScalarCodeResult) : FloorScalarCodeResult :=
  ((floorScalarClampCode r.1.1,r.1.2),r.2)

/-- Definition of floor Rational Negative Exp Code in the Coded Floor construction. -/
def floorRationalNegativeExpCode (p : FloorExpCodeParameters) : FloorScalarCodeResult :=
  let cutoff := floorRationalCodeArctanFuel p.2
  if floorRationalCodeLE (floorRationalCodeNat cutoff) p.1 then
    ((floorRationalCodeNat 0,
      floorRationalCodeInv (floorRationalCodePow (floorRationalCodeNat 2) cutoff)),0)
  else floorNegativeExpSquaresCode
    (floorClampScalarResultCode (floorReducedNegativeExpCode (floorNegativeExpReducedArguments p)))
    (floorNegativeExpHalvingsCode p.1)

/-- Original `floorNegativeExpReducedArguments_value` guarantee for the `FloorFullNegativeExpCode` construction; the complete source hypotheses are retained. -/
theorem floorNegativeExpReducedArguments_value (p : FloorExpCodeParameters) :
    (floorRationalCodeValue (floorNegativeExpReducedArguments p).1,
      floorRationalCodeValue (floorNegativeExpReducedArguments p).2)=
    (floorRationalCodeValue p.1/(2^negativeExpHalvings (floorRationalCodeValue p.1) : ℚ),
      floorRationalCodeValue p.2/(2^negativeExpHalvings (floorRationalCodeValue p.1) : ℚ)) := by
  simp [floorNegativeExpReducedArguments,floorRationalCodeMul_value,floorRationalCodeInv_value,
    floorRationalCodePow_value,floorRationalCodeNat_value,floorNegativeExpHalvingsCode_value,div_eq_mul_inv]

/-- Original `floorClampScalarResultCode_value` guarantee for the `FloorFullNegativeExpCode` construction; the complete source hypotheses are retained. -/
theorem floorClampScalarResultCode_value (r : FloorScalarCodeResult) :
    floorScalarCodeResultValue (floorClampScalarResultCode r)=
      ⟨scalarClamp (floorScalarCodeResultValue r).value,
        (floorScalarCodeResultValue r).error,(floorScalarCodeResultValue r).terms⟩ := by
  simp [floorClampScalarResultCode,floorScalarCodeResultValue,floorScalarClampCode_value]

/-- Original `floorRationalNegativeExpCode_value` guarantee for the `FloorFullNegativeExpCode` construction; the complete source hypotheses are retained. -/
theorem floorRationalNegativeExpCode_value (p : FloorExpCodeParameters) :
    floorScalarCodeResultValue (floorRationalNegativeExpCode p)=
      rationalNegativeExp (floorRationalCodeValue p.1) (floorRationalCodeValue p.2) := by
  have hg : floorRationalCodeLE (floorRationalCodeNat (floorRationalCodeArctanFuel p.2)) p.1 ↔
      (arctanFuel (floorRationalCodeValue p.2) : ℚ) ≤ floorRationalCodeValue p.1 := by
    rw [floorRationalCodeLE_value,floorRationalCodeNat_value,floorRationalCodeArctanFuel_value]
  unfold floorRationalNegativeExpCode
  by_cases h : floorRationalCodeLE (floorRationalCodeNat (floorRationalCodeArctanFuel p.2)) p.1
  · rw [if_pos h,rationalNegativeExp,if_pos (hg.mp h)]
    simp [floorScalarCodeResultValue,floorRationalCodeNat_value,floorRationalCodeInv_value,
      floorRationalCodePow_value,floorRationalCodeArctanFuel_value]
  · rw [if_neg h,floorNegativeExpSquaresCode_value,floorClampScalarResultCode_value,
      floorReducedNegativeExpCode_value,rationalNegativeExp,if_neg (mt hg.mpr h),
      floorNegativeExpHalvingsCode_value]
    have ha := floorNegativeExpReducedArguments_value p
    have h1 := congrArg Prod.fst ha
    have h2 := congrArg Prod.snd ha
    dsimp only [Prod.fst,Prod.snd] at h1 h2
    rw [h1,h2]

/-- Original `primrec_floorNegativeExpReducedArguments` guarantee for the `FloorFullNegativeExpCode` construction; the complete source hypotheses are retained. -/
theorem primrec_floorNegativeExpReducedArguments : Primrec floorNegativeExpReducedArguments := by
  have hp : Primrec (fun p : FloorExpCodeParameters =>
      floorRationalCodePow (floorRationalCodeNat 2) (floorNegativeExpHalvingsCode p.1)) :=
    primrec_floorRationalCodePow.comp (Primrec.const (floorRationalCodeNat 2))
      (primrec_floorNegativeExpHalvingsCode.comp Primrec.fst)
  exact (primrec_floorRationalCodeMul.comp Primrec.fst (primrec_floorRationalCodeInv.comp hp)).pair
    (primrec_floorRationalCodeMul.comp Primrec.snd (primrec_floorRationalCodeInv.comp hp))

/-- Original `primrec_floorClampScalarResultCode` guarantee for the `FloorFullNegativeExpCode` construction; the complete source hypotheses are retained. -/
theorem primrec_floorClampScalarResultCode : Primrec floorClampScalarResultCode :=
  ((primrec_floorScalarClampCode.comp (Primrec.fst.comp Primrec.fst)).pair
    (Primrec.snd.comp Primrec.fst)).pair Primrec.snd

/-- Original `primrec_floorRationalNegativeExpCode` guarantee for the `FloorFullNegativeExpCode` construction; the complete source hypotheses are retained. -/
theorem primrec_floorRationalNegativeExpCode : Primrec floorRationalNegativeExpCode := by
  have hc : Primrec (fun p : FloorExpCodeParameters => floorRationalCodeArctanFuel p.2) :=
    primrec_floorRationalCodeArctanFuel.comp Primrec.snd
  have hz : Primrec (fun p : FloorExpCodeParameters =>
      ((floorRationalCodeNat 0,
        floorRationalCodeInv (floorRationalCodePow (floorRationalCodeNat 2) (floorRationalCodeArctanFuel p.2))),0)) :=
    ((Primrec.const (floorRationalCodeNat 0)).pair (primrec_floorRationalCodeInv.comp
      (primrec_floorRationalCodePow.comp (Primrec.const (floorRationalCodeNat 2)) hc))).pair (Primrec.const 0)
  have hr : Primrec (fun p : FloorExpCodeParameters => floorNegativeExpSquaresCode
      (floorClampScalarResultCode (floorReducedNegativeExpCode (floorNegativeExpReducedArguments p)))
      (floorNegativeExpHalvingsCode p.1)) :=
    primrec_floorNegativeExpSquaresCode.comp
      (primrec_floorClampScalarResultCode.comp
        (primrec_floorReducedNegativeExpCode.comp primrec_floorNegativeExpReducedArguments))
      (primrec_floorNegativeExpHalvingsCode.comp Primrec.fst)
  have hguard : PrimrecPred (fun p : FloorExpCodeParameters =>
      floorRationalCodeLE (floorRationalCodeNat (floorRationalCodeArctanFuel p.2)) p.1) :=
    primrec_floorRationalCodeLE.comp (primrec_floorRationalCodeNat.comp hc) Primrec.fst
  apply (Primrec.ite hguard hz hr).of_eq
  intro p
  rfl

/-- Original `floorFullMachine_of_primrec` guarantee for the `FloorFullNegativeExpCode` construction; the complete source hypotheses are retained. -/
private theorem floorFullMachine_of_primrec {A B : Type*} [Primcodable A] [Primcodable B]
    (f : A → B) (hf : Primrec f) : ∃ c : Nat.Partrec.Code, ∀ a,
      Nat.Partrec.Code.eval c (Encodable.encode a)=Part.some (Encodable.encode (f a)) := by
  obtain ⟨c,hc⟩ := Nat.Partrec.Code.exists_code.mp hf.to_comp
  exact ⟨c,fun a => by simpa using congrFun hc (Encodable.encode a)⟩

/-- Original `floorRationalNegativeExpCode_encoded` guarantee for the `FloorFullNegativeExpCode` construction; the complete source hypotheses are retained. -/
theorem floorRationalNegativeExpCode_encoded :
    ∃ c : Nat.Partrec.Code, ∀ p : FloorExpCodeParameters,
      Nat.Partrec.Code.eval c (Encodable.encode p)=
        Part.some (Encodable.encode (floorRationalNegativeExpCode p)) :=
  floorFullMachine_of_primrec floorRationalNegativeExpCode primrec_floorRationalNegativeExpCode

end Qatlib.Concepts.EffectiveGauge.CodedFloor
