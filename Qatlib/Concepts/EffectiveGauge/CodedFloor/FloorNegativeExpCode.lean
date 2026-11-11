/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.CodedFloor.FloorRationalScalarCode

/-!
# Floor Negative Exp Code

Coded Floor constructions for Effective Gauge.
Defines `FloorExpCodeState`, `FloorExpCodeParameters`, `floorExpCodeStep`.
Proves `floorExpCodeRun_value`, `primrec_floorExpCodeStep`, `primrec_floorExpCodeRun`.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.CodedFloor
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Abbreviation for Floor Exp Code State in the Coded Floor construction. -/
abbrev FloorExpCodeState := ℕ × (FloorRationalCode × FloorRationalCode)
/-- Abbreviation for Floor Exp Code Parameters in the Coded Floor construction. -/
abbrev FloorExpCodeParameters := FloorRationalCode × FloorRationalCode

/-- A stopped state is fixed; consequently a bounded iteration has the exact
early-stop semantics of the existing rational Taylor program. -/
def floorExpCodeStep (p : FloorExpCodeParameters) (s : FloorExpCodeState) : FloorExpCodeState :=
  if floorRationalCodeLE (floorRationalCodeAbs s.2.2) p.2 then s else
    (s.1+1,(floorRationalCodeAdd s.2.1 s.2.2,
      floorRationalCodeMul (floorRationalCodeMul s.2.2 (floorRationalCodeNeg p.1))
        (floorRationalCodeInv (floorRationalCodeNat (s.1+1)))))

/-- Definition of floor Exp Code Run in the Coded Floor construction. -/
def floorExpCodeRun (p : FloorExpCodeParameters) (s : FloorExpCodeState) (fuel : ℕ) : FloorExpCodeState :=
  (floorExpCodeStep p)^[fuel] s

/-- Definition of floor Exp Code Result in the Coded Floor construction. -/
def floorExpCodeResult (s : FloorExpCodeState) : RationalScalarResult :=
  ⟨floorRationalCodeValue s.2.1,|floorRationalCodeValue s.2.2|,s.1⟩

/-- Original `floorExpCodeRun_value` guarantee for the `FloorNegativeExpCode` construction; the complete source hypotheses are retained. -/
theorem floorExpCodeRun_value (p : FloorExpCodeParameters) (s : FloorExpCodeState) (fuel : ℕ) :
    floorExpCodeResult (floorExpCodeRun p s fuel)=
      negativeExpLoop (floorRationalCodeValue p.1) (floorRationalCodeValue p.2) s.1
        (floorRationalCodeValue s.2.1) (floorRationalCodeValue s.2.2) fuel := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
    unfold floorExpCodeRun
    rw [Function.iterate_succ_apply]
    by_cases h : floorRationalCodeLE (floorRationalCodeAbs s.2.2) p.2
    · have hv : |floorRationalCodeValue s.2.2| ≤ floorRationalCodeValue p.2 := by
        simpa only [floorRationalCodeAbs_value] using
          (floorRationalCodeLE_value (floorRationalCodeAbs s.2.2) p.2).mp h
      rw [floorExpCodeStep,if_pos h]
      change floorExpCodeResult (floorExpCodeRun p s fuel)=_
      rw [ih]
      cases fuel <;> simp only [negativeExpLoop,if_pos hv]
    · have hv : ¬|floorRationalCodeValue s.2.2| ≤ floorRationalCodeValue p.2 := by
        intro hv
        apply h
        exact (floorRationalCodeLE_value _ _).mpr (by simpa only [floorRationalCodeAbs_value] using hv)
      rw [floorExpCodeStep,if_neg h]
      change floorExpCodeResult (floorExpCodeRun p _ fuel)=_
      rw [ih]
      simp only [floorRationalCodeAdd_value,floorRationalCodeMul_value,
        floorRationalCodeNeg_value,floorRationalCodeInv_value,floorRationalCodeNat_value,
        negativeExpLoop,if_neg hv,div_eq_mul_inv]

/-- Original `primrec_floorExpCodeStep` guarantee for the `FloorNegativeExpCode` construction; the complete source hypotheses are retained. -/
theorem primrec_floorExpCodeStep : Primrec₂ floorExpCodeStep := by
  have px : Primrec (fun x : FloorExpCodeParameters × FloorExpCodeState => x.1.1) :=
    Primrec.fst.comp Primrec.fst
  have pt : Primrec (fun x : FloorExpCodeParameters × FloorExpCodeState => x.1.2) :=
    Primrec.snd.comp Primrec.fst
  have sn : Primrec (fun x : FloorExpCodeParameters × FloorExpCodeState => x.2.1) :=
    Primrec.fst.comp Primrec.snd
  have sa : Primrec (fun x : FloorExpCodeParameters × FloorExpCodeState => x.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have st : Primrec (fun x : FloorExpCodeParameters × FloorExpCodeState => x.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have sn' := Primrec.nat_add.comp sn (Primrec.const 1)
  exact Primrec.ite (primrec_floorRationalCodeLE.comp (primrec_floorRationalCodeAbs.comp st) pt)
    Primrec.snd
    (sn'.pair ((primrec_floorRationalCodeAdd.comp sa st).pair
      (primrec_floorRationalCodeMul.comp
        (primrec_floorRationalCodeMul.comp st (primrec_floorRationalCodeNeg.comp px))
        (primrec_floorRationalCodeInv.comp (primrec_floorRationalCodeNat.comp sn')))))

/-- Original `primrec_floorExpCodeRun` guarantee for the `FloorNegativeExpCode` construction; the complete source hypotheses are retained. -/
theorem primrec_floorExpCodeRun :
    Primrec (fun x : (FloorExpCodeParameters × FloorExpCodeState) × ℕ =>
      floorExpCodeRun x.1.1 x.1.2 x.2) := by
  have hp : Primrec (fun x : ((FloorExpCodeParameters × FloorExpCodeState) × ℕ) × FloorExpCodeState =>
      x.1.1.1) := Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hs : Primrec₂ (fun (x : (FloorExpCodeParameters × FloorExpCodeState) × ℕ)
      (s : FloorExpCodeState) => floorExpCodeStep x.1.1 s) :=
    primrec_floorExpCodeStep.comp hp Primrec.snd
  exact Primrec.nat_iterate Primrec.snd (Primrec.snd.comp Primrec.fst) hs

/-- Abbreviation for Floor Scalar Code Result in the Coded Floor construction. -/
abbrev FloorScalarCodeResult := (FloorRationalCode × FloorRationalCode) × ℕ

/-- Definition of floor Scalar Code Result Value in the Coded Floor construction. -/
def floorScalarCodeResultValue (s : FloorScalarCodeResult) : RationalScalarResult :=
  ⟨floorRationalCodeValue s.1.1,floorRationalCodeValue s.1.2,s.2⟩

/-- Definition of floor Exp Result Payload in the Coded Floor construction. -/
def floorExpResultPayload (s : FloorExpCodeState) : FloorScalarCodeResult :=
  ((s.2.1,floorRationalCodeAbs s.2.2),s.1)

/-- Definition of floor Reduced Negative Exp Code in the Coded Floor construction. -/
def floorReducedNegativeExpCode (p : FloorExpCodeParameters) : FloorScalarCodeResult :=
  floorExpResultPayload (floorExpCodeRun p
    (1,(floorRationalCodeNat 1,floorRationalCodeNeg p.1)) (floorRationalCodeArctanFuel p.2))

/-- Original `floorExpResultPayload_value` guarantee for the `FloorNegativeExpCode` construction; the complete source hypotheses are retained. -/
theorem floorExpResultPayload_value (s : FloorExpCodeState) :
    floorScalarCodeResultValue (floorExpResultPayload s)=floorExpCodeResult s := by
  simp [floorScalarCodeResultValue,floorExpResultPayload,floorExpCodeResult,floorRationalCodeAbs_value]

/-- Original `floorReducedNegativeExpCode_value` guarantee for the `FloorNegativeExpCode` construction; the complete source hypotheses are retained. -/
theorem floorReducedNegativeExpCode_value (p : FloorExpCodeParameters) :
    floorScalarCodeResultValue (floorReducedNegativeExpCode p)=
      reducedNegativeExp (floorRationalCodeValue p.1) (floorRationalCodeValue p.2) := by
  rw [floorReducedNegativeExpCode,floorExpResultPayload_value,floorExpCodeRun_value]
  simp only [floorRationalCodeArctanFuel_value,floorRationalCodeNat_value,
    floorRationalCodeNeg_value,reducedNegativeExp,Nat.cast_one]

/-- Original `primrec_floorExpResultPayload` guarantee for the `FloorNegativeExpCode` construction; the complete source hypotheses are retained. -/
theorem primrec_floorExpResultPayload : Primrec floorExpResultPayload :=
  ((Primrec.fst.comp Primrec.snd).pair
    (primrec_floorRationalCodeAbs.comp (Primrec.snd.comp Primrec.snd))).pair Primrec.fst

/-- Original `primrec_floorReducedNegativeExpCode` guarantee for the `FloorNegativeExpCode` construction; the complete source hypotheses are retained. -/
theorem primrec_floorReducedNegativeExpCode : Primrec floorReducedNegativeExpCode := by
  have hi : Primrec (fun p : FloorExpCodeParameters =>
      (1,(floorRationalCodeNat 1,floorRationalCodeNeg p.1))) :=
    (Primrec.const 1).pair ((Primrec.const (floorRationalCodeNat 1)).pair
      (primrec_floorRationalCodeNeg.comp Primrec.fst))
  exact primrec_floorExpResultPayload.comp (primrec_floorExpCodeRun.comp
    ((Primrec.id.pair hi).pair (primrec_floorRationalCodeArctanFuel.comp Primrec.snd)))

end Qatlib.Concepts.EffectiveGauge.CodedFloor
