/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.CodedFloor.FloorComplexCode
import Qatlib.Concepts.EffectiveGauge.CodedFloor.FloorNegativeExpCode

/-!
# Floor Cis Loop Code

Coded Floor constructions for Effective Gauge.
Defines `FloorCisCodeState`, `FloorCisCodeResult`, `floorCisCodeStep`.
Proves `floorCisCodeRun_value`, `floorCisResultPayload_value`, `floorReducedCisCode_value`.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.CodedFloor
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Abbreviation for Floor Cis Code State in the Coded Floor construction. -/
abbrev FloorCisCodeState := ℕ × ((FloorComplexCode × FloorComplexCode) × FloorRationalCode)
/-- Abbreviation for Floor Cis Code Result in the Coded Floor construction. -/
abbrev FloorCisCodeResult := (FloorComplexCode × FloorRationalCode) × ℕ

/-- Definition of floor Cis Code Step in the Coded Floor construction. -/
def floorCisCodeStep (p : FloorExpCodeParameters) (s : FloorCisCodeState) : FloorCisCodeState :=
  if floorRationalCodeLE (floorRationalCodeMul (floorRationalCodeNat 2) s.2.2) p.2 then s else
    (s.1+1,((floorComplexCodeAdd s.2.1.1 s.2.1.2,floorCisTermStepCode p.1 (s.1+1) s.2.1.2),
      floorRationalCodeMul (floorRationalCodeMul s.2.2 (floorRationalCodeAbs p.1))
        (floorRationalCodeInv (floorRationalCodeNat (s.1+1)))))

/-- Definition of floor Cis Code Run in the Coded Floor construction. -/
def floorCisCodeRun (p : FloorExpCodeParameters) (s : FloorCisCodeState) (fuel : ℕ) : FloorCisCodeState :=
  (floorCisCodeStep p)^[fuel] s

/-- Definition of floor Cis Code State Value in the Coded Floor construction. -/
def floorCisCodeStateValue (s : FloorCisCodeState) : RationalCisResult :=
  ⟨floorComplexCodeValue s.2.1.1,2*floorRationalCodeValue s.2.2,s.1⟩

/-- Definition of floor Cis Code Result Value in the Coded Floor construction. -/
def floorCisCodeResultValue (r : FloorCisCodeResult) : RationalCisResult :=
  ⟨floorComplexCodeValue r.1.1,floorRationalCodeValue r.1.2,r.2⟩

/-- Definition of floor Cis Result Payload in the Coded Floor construction. -/
def floorCisResultPayload (s : FloorCisCodeState) : FloorCisCodeResult :=
  ((s.2.1.1,floorRationalCodeMul (floorRationalCodeNat 2) s.2.2),s.1)

/-- Definition of floor Reduced Cis Code in the Coded Floor construction. -/
def floorReducedCisCode (p : FloorExpCodeParameters) : FloorCisCodeResult :=
  floorCisResultPayload (floorCisCodeRun p
    (1,(((floorRationalCodeNat 1,floorRationalCodeNat 0),(floorRationalCodeNat 0,p.1)),floorRationalCodeAbs p.1))
    (floorRationalCodeArctanFuel (floorRationalCodeMul p.2 (floorRationalCodeInv (floorRationalCodeNat 2)))))

/-- Original `floorCisCodeRun_value` guarantee for the `FloorCisLoopCode` construction; the complete source hypotheses are retained. -/
theorem floorCisCodeRun_value (p : FloorExpCodeParameters) (s : FloorCisCodeState) (fuel : ℕ) :
    floorCisCodeStateValue (floorCisCodeRun p s fuel)=
      cisTaylorLoop (floorRationalCodeValue p.1) (floorRationalCodeValue p.2) s.1
        (floorComplexCodeValue s.2.1.1) (floorComplexCodeValue s.2.1.2)
        (floorRationalCodeValue s.2.2) fuel := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
    unfold floorCisCodeRun
    rw [Function.iterate_succ_apply]
    by_cases h : floorRationalCodeLE (floorRationalCodeMul (floorRationalCodeNat 2) s.2.2) p.2
    · have hv : 2*floorRationalCodeValue s.2.2 ≤ floorRationalCodeValue p.2 := by
        simpa only [floorRationalCodeMul_value,floorRationalCodeNat_value,Nat.cast_ofNat] using
          (floorRationalCodeLE_value _ _).mp h
      rw [floorCisCodeStep,if_pos h]
      change floorCisCodeStateValue (floorCisCodeRun p s fuel)=_
      rw [ih]
      cases fuel <;> simp only [cisTaylorLoop,if_pos hv]
    · have hv : ¬2*floorRationalCodeValue s.2.2 ≤ floorRationalCodeValue p.2 := by
        intro hv
        apply h
        exact (floorRationalCodeLE_value _ _).mpr
          (by simpa only [floorRationalCodeMul_value,floorRationalCodeNat_value,Nat.cast_ofNat] using hv)
      rw [floorCisCodeStep,if_neg h]
      change floorCisCodeStateValue (floorCisCodeRun p _ fuel)=_
      rw [ih]
      simp only [floorComplexCodeAdd_value,floorCisTermStepCode_value,floorRationalCodeMul_value,
        floorRationalCodeAbs_value,floorRationalCodeInv_value,floorRationalCodeNat_value,
        cisTaylorLoop,if_neg hv,div_eq_mul_inv]

/-- Original `floorCisResultPayload_value` guarantee for the `FloorCisLoopCode` construction; the complete source hypotheses are retained. -/
theorem floorCisResultPayload_value (s : FloorCisCodeState) :
    floorCisCodeResultValue (floorCisResultPayload s)=floorCisCodeStateValue s := by
  simp [floorCisCodeResultValue,floorCisResultPayload,floorCisCodeStateValue,
    floorRationalCodeMul_value,floorRationalCodeNat_value]

/-- Original `floorReducedCisCode_value` guarantee for the `FloorCisLoopCode` construction; the complete source hypotheses are retained. -/
theorem floorReducedCisCode_value (p : FloorExpCodeParameters) :
    floorCisCodeResultValue (floorReducedCisCode p)=
      reducedCis (floorRationalCodeValue p.1) (floorRationalCodeValue p.2) := by
  rw [floorReducedCisCode,floorCisResultPayload_value,floorCisCodeRun_value]
  simp only [floorRationalCodeArctanFuel_value,floorRationalCodeMul_value,floorRationalCodeInv_value,
    floorRationalCodeNat_value,floorRationalCodeAbs_value,floorComplexCodeValue,
    reducedCis,Nat.cast_one,Nat.cast_zero,Nat.cast_ofNat,div_eq_mul_inv]

/-- Original `primrec_floorCisCodeStep` guarantee for the `FloorCisLoopCode` construction; the complete source hypotheses are retained. -/
theorem primrec_floorCisCodeStep : Primrec₂ floorCisCodeStep := by
  have px : Primrec (fun x : FloorExpCodeParameters × FloorCisCodeState => x.1.1) :=
    Primrec.fst.comp Primrec.fst
  have pt : Primrec (fun x : FloorExpCodeParameters × FloorCisCodeState => x.1.2) :=
    Primrec.snd.comp Primrec.fst
  have sn : Primrec (fun x : FloorExpCodeParameters × FloorCisCodeState => x.2.1) :=
    Primrec.fst.comp Primrec.snd
  have sa : Primrec (fun x : FloorExpCodeParameters × FloorCisCodeState => x.2.2.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
  have st : Primrec (fun x : FloorExpCodeParameters × FloorCisCodeState => x.2.2.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
  have ss : Primrec (fun x : FloorExpCodeParameters × FloorCisCodeState => x.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have sn' := Primrec.nat_add.comp sn (Primrec.const 1)
  have hguard : PrimrecPred (fun x : FloorExpCodeParameters × FloorCisCodeState =>
      floorRationalCodeLE (floorRationalCodeMul (floorRationalCodeNat 2) x.2.2.2) x.1.2) :=
    primrec_floorRationalCodeLE.comp
      (primrec_floorRationalCodeMul.comp (Primrec.const (floorRationalCodeNat 2)) ss) pt
  exact Primrec.ite hguard Primrec.snd
    (sn'.pair (((primrec_floorComplexCodeAdd.comp sa st).pair
      (primrec_floorCisTermStepCode.comp (px.pair sn') st)).pair
      (primrec_floorRationalCodeMul.comp
        (primrec_floorRationalCodeMul.comp ss (primrec_floorRationalCodeAbs.comp px))
        (primrec_floorRationalCodeInv.comp (primrec_floorRationalCodeNat.comp sn')))))

/-- Original `primrec_floorCisCodeRun` guarantee for the `FloorCisLoopCode` construction; the complete source hypotheses are retained. -/
theorem primrec_floorCisCodeRun :
    Primrec (fun x : (FloorExpCodeParameters × FloorCisCodeState) × ℕ => floorCisCodeRun x.1.1 x.1.2 x.2) := by
  have hp : Primrec (fun x : ((FloorExpCodeParameters × FloorCisCodeState) × ℕ) × FloorCisCodeState =>
      x.1.1.1) := Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hs : Primrec₂ (fun (x : (FloorExpCodeParameters × FloorCisCodeState) × ℕ)
      (s : FloorCisCodeState) => floorCisCodeStep x.1.1 s) := primrec_floorCisCodeStep.comp hp Primrec.snd
  exact Primrec.nat_iterate Primrec.snd (Primrec.snd.comp Primrec.fst) hs

/-- Original `primrec_floorCisResultPayload` guarantee for the `FloorCisLoopCode` construction; the complete source hypotheses are retained. -/
theorem primrec_floorCisResultPayload : Primrec floorCisResultPayload :=
  ((Primrec.fst.comp (Primrec.fst.comp Primrec.snd)).pair
    (primrec_floorRationalCodeMul.comp (Primrec.const (floorRationalCodeNat 2))
      (Primrec.snd.comp Primrec.snd))).pair Primrec.fst

/-- Original `primrec_floorReducedCisCode` guarantee for the `FloorCisLoopCode` construction; the complete source hypotheses are retained. -/
theorem primrec_floorReducedCisCode : Primrec floorReducedCisCode := by
  have hi : Primrec (fun p : FloorExpCodeParameters =>
      (1,(((floorRationalCodeNat 1,floorRationalCodeNat 0),(floorRationalCodeNat 0,p.1)),
        floorRationalCodeAbs p.1))) :=
    (Primrec.const 1).pair (((Primrec.const (floorRationalCodeNat 1,floorRationalCodeNat 0)).pair
      ((Primrec.const (floorRationalCodeNat 0)).pair Primrec.fst)).pair
      (primrec_floorRationalCodeAbs.comp Primrec.fst))
  have ht : Primrec (fun p : FloorExpCodeParameters =>
      floorRationalCodeArctanFuel (floorRationalCodeMul p.2 (floorRationalCodeInv (floorRationalCodeNat 2)))) :=
    primrec_floorRationalCodeArctanFuel.comp (primrec_floorRationalCodeMul.comp Primrec.snd
      (Primrec.const (floorRationalCodeInv (floorRationalCodeNat 2))))
  exact primrec_floorCisResultPayload.comp (primrec_floorCisCodeRun.comp ((Primrec.id.pair hi).pair ht))

end Qatlib.Concepts.EffectiveGauge.CodedFloor
