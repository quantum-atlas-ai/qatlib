/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.CodedFloor.FloorCisLoopCode
import Qatlib.Concepts.EffectiveGauge.CodedFloor.FloorNegativeExpBackendCode

/-!
# Floor Cis Backend Code

Coded Floor constructions for Effective Gauge.
Defines `floorCisSquareStepCode`, `floorCisSquaresCode`, `floorCisHalvingsCode`.
Proves `floorCisSquareStepCode_value`, `floorCisSquaresCode_value`, `floorCisHalvingsCode_value`.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.CodedFloor
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Definition of floor Cis Square Step Code in the Coded Floor construction. -/
def floorCisSquareStepCode (r : FloorCisCodeResult) : FloorCisCodeResult :=
  ((floorComplexCodeSquare r.1.1,
    floorRationalCodeMul r.1.2 (floorRationalCodeAdd (floorRationalCodeNat 2) r.1.2)),r.2)

/-- Definition of floor Cis Squares Code in the Coded Floor construction. -/
def floorCisSquaresCode (r : FloorCisCodeResult) (h : ℕ) : FloorCisCodeResult :=
  floorCisSquareStepCode^[h] r

/-- Definition of floor Cis Halvings Code in the Coded Floor construction. -/
def floorCisHalvingsCode (q : FloorRationalCode) : ℕ :=
  floorNegativeExpHalvingsCode (floorRationalCodeAbs q)

/-- Definition of floor Cis Reduced Arguments in the Coded Floor construction. -/
def floorCisReducedArguments (p : FloorExpCodeParameters) : FloorExpCodeParameters :=
  let scale := floorRationalCodePow (floorRationalCodeNat 2) (floorCisHalvingsCode p.1)
  (floorRationalCodeMul p.1 (floorRationalCodeInv scale),
    floorRationalCodeMul p.2 (floorRationalCodeInv (floorRationalCodeMul (floorRationalCodeNat 8) scale)))

/-- Definition of floor Rational Cis Code in the Coded Floor construction. -/
def floorRationalCisCode (p : FloorExpCodeParameters) : FloorCisCodeResult :=
  floorCisSquaresCode (floorReducedCisCode (floorCisReducedArguments p)) (floorCisHalvingsCode p.1)

/-- Original `floorCisSquareStepCode_value` guarantee for the `FloorCisBackendCode` construction; the complete source hypotheses are retained. -/
theorem floorCisSquareStepCode_value (r : FloorCisCodeResult) :
    floorCisCodeResultValue (floorCisSquareStepCode r)=
      ⟨cisPairSquare (floorCisCodeResultValue r).value,
        (floorCisCodeResultValue r).error*(2+(floorCisCodeResultValue r).error),
        (floorCisCodeResultValue r).terms⟩ := by
  simp [floorCisCodeResultValue,floorCisSquareStepCode,floorComplexCodeSquare_value,
    floorRationalCodeMul_value,floorRationalCodeAdd_value,floorRationalCodeNat_value]

/-- Original `floorCisSquaresCode_value` guarantee for the `FloorCisBackendCode` construction; the complete source hypotheses are retained. -/
theorem floorCisSquaresCode_value (r : FloorCisCodeResult) (h : ℕ) :
    floorCisCodeResultValue (floorCisSquaresCode r h)=cisSquares h (floorCisCodeResultValue r) := by
  induction h with
  | zero => rfl
  | succ h ih =>
    unfold floorCisSquaresCode
    rw [Function.iterate_succ_apply']
    change floorCisCodeResultValue (floorCisSquareStepCode (floorCisSquaresCode r h))=_
    rw [floorCisSquareStepCode_value,ih,cisSquares]

/-- Original `floorCisHalvingsCode_value` guarantee for the `FloorCisBackendCode` construction; the complete source hypotheses are retained. -/
theorem floorCisHalvingsCode_value (q : FloorRationalCode) :
    floorCisHalvingsCode q=cisHalvings (floorRationalCodeValue q) := by
  simp only [floorCisHalvingsCode,floorNegativeExpHalvingsCode_value,
    floorRationalCodeAbs_value,cisHalvings]

/-- Original `floorCisReducedArguments_value` guarantee for the `FloorCisBackendCode` construction; the complete source hypotheses are retained. -/
theorem floorCisReducedArguments_value (p : FloorExpCodeParameters) :
    (floorRationalCodeValue (floorCisReducedArguments p).1,
      floorRationalCodeValue (floorCisReducedArguments p).2)=
    (floorRationalCodeValue p.1/(2^cisHalvings (floorRationalCodeValue p.1) : ℚ),
      floorRationalCodeValue p.2/(8*2^cisHalvings (floorRationalCodeValue p.1) : ℚ)) := by
  simp [floorCisReducedArguments,floorRationalCodeMul_value,floorRationalCodeInv_value,
    floorRationalCodePow_value,floorRationalCodeNat_value,floorCisHalvingsCode_value,div_eq_mul_inv]

/-- Original `floorRationalCisCode_value` guarantee for the `FloorCisBackendCode` construction; the complete source hypotheses are retained. -/
theorem floorRationalCisCode_value (p : FloorExpCodeParameters) :
    floorCisCodeResultValue (floorRationalCisCode p)=
      rationalCis (floorRationalCodeValue p.1) (floorRationalCodeValue p.2) := by
  rw [floorRationalCisCode,floorCisSquaresCode_value,floorReducedCisCode_value,floorCisHalvingsCode_value]
  have ha := floorCisReducedArguments_value p
  have h1 := congrArg Prod.fst ha
  have h2 := congrArg Prod.snd ha
  dsimp only [Prod.fst,Prod.snd] at h1 h2
  rw [h1,h2]
  rfl

/-- Original `primrec_floorCisSquareStepCode` guarantee for the `FloorCisBackendCode` construction; the complete source hypotheses are retained. -/
theorem primrec_floorCisSquareStepCode : Primrec floorCisSquareStepCode :=
  ((primrec_floorComplexCodeSquare.comp (Primrec.fst.comp Primrec.fst)).pair
    (primrec_floorRationalCodeMul.comp (Primrec.snd.comp Primrec.fst)
      (primrec_floorRationalCodeAdd.comp (Primrec.const (floorRationalCodeNat 2))
        (Primrec.snd.comp Primrec.fst)))).pair Primrec.snd

/-- Original `primrec_floorCisSquaresCode` guarantee for the `FloorCisBackendCode` construction; the complete source hypotheses are retained. -/
theorem primrec_floorCisSquaresCode : Primrec₂ floorCisSquaresCode := by
  have hs : Primrec₂ (fun (_ : FloorCisCodeResult × ℕ) (r : FloorCisCodeResult) =>
      floorCisSquareStepCode r) := primrec_floorCisSquareStepCode.comp Primrec.snd
  exact Primrec.nat_iterate Primrec.snd Primrec.fst hs

/-- Original `primrec_floorCisHalvingsCode` guarantee for the `FloorCisBackendCode` construction; the complete source hypotheses are retained. -/
theorem primrec_floorCisHalvingsCode : Primrec floorCisHalvingsCode :=
  primrec_floorNegativeExpHalvingsCode.comp primrec_floorRationalCodeAbs

/-- Original `primrec_floorCisReducedArguments` guarantee for the `FloorCisBackendCode` construction; the complete source hypotheses are retained. -/
theorem primrec_floorCisReducedArguments : Primrec floorCisReducedArguments := by
  have hs : Primrec (fun p : FloorExpCodeParameters =>
      floorRationalCodePow (floorRationalCodeNat 2) (floorCisHalvingsCode p.1)) :=
    primrec_floorRationalCodePow.comp (Primrec.const (floorRationalCodeNat 2))
      (primrec_floorCisHalvingsCode.comp Primrec.fst)
  exact (primrec_floorRationalCodeMul.comp Primrec.fst (primrec_floorRationalCodeInv.comp hs)).pair
    (primrec_floorRationalCodeMul.comp Primrec.snd (primrec_floorRationalCodeInv.comp
      (primrec_floorRationalCodeMul.comp (Primrec.const (floorRationalCodeNat 8)) hs)))

/-- Original `primrec_floorRationalCisCode` guarantee for the `FloorCisBackendCode` construction; the complete source hypotheses are retained. -/
theorem primrec_floorRationalCisCode : Primrec floorRationalCisCode :=
  primrec_floorCisSquaresCode.comp
    (primrec_floorReducedCisCode.comp primrec_floorCisReducedArguments)
    (primrec_floorCisHalvingsCode.comp Primrec.fst)

/-- Original `floorCisMachine_of_primrec` guarantee for the `FloorCisBackendCode` construction; the complete source hypotheses are retained. -/
private theorem floorCisMachine_of_primrec {A B : Type*} [Primcodable A] [Primcodable B]
    (f : A → B) (hf : Primrec f) : ∃ c : Nat.Partrec.Code, ∀ a,
      Nat.Partrec.Code.eval c (Encodable.encode a)=Part.some (Encodable.encode (f a)) := by
  obtain ⟨c,hc⟩ := Nat.Partrec.Code.exists_code.mp hf.to_comp
  exact ⟨c,fun a => by simpa using congrFun hc (Encodable.encode a)⟩

/-- Original `floorRationalCisCode_encoded` guarantee for the `FloorCisBackendCode` construction; the complete source hypotheses are retained. -/
theorem floorRationalCisCode_encoded : ∃ c : Nat.Partrec.Code, ∀ p : FloorExpCodeParameters,
    Nat.Partrec.Code.eval c (Encodable.encode p)=Part.some (Encodable.encode (floorRationalCisCode p)) :=
  floorCisMachine_of_primrec floorRationalCisCode primrec_floorRationalCisCode

end Qatlib.Concepts.EffectiveGauge.CodedFloor
