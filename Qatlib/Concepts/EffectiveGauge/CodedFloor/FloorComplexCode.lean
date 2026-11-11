/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.CodedFloor.FloorRationalScalarCode
import Qatlib.Concepts.EffectiveGauge.RationalFlow.CisProgram

/-!
# Floor Complex Code

Coded Floor constructions for Effective Gauge.
Defines `FloorComplexCode`, `floorComplexCodeValue`, `floorComplexCodeAdd`.
Proves `floorComplexCodeAdd_value`, `floorComplexCodeMul_value`, `floorComplexCodeSquare_value`.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.CodedFloor
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Abbreviation for Floor Complex Code in the Coded Floor construction. -/
abbrev FloorComplexCode := FloorRationalCode × FloorRationalCode

/-- Definition of floor Complex Code Value in the Coded Floor construction. -/
def floorComplexCodeValue (a : FloorComplexCode) : RationalCircleSample :=
  (floorRationalCodeValue a.1,floorRationalCodeValue a.2)

/-- Definition of floor Complex Code Add in the Coded Floor construction. -/
def floorComplexCodeAdd (a b : FloorComplexCode) : FloorComplexCode :=
  (floorRationalCodeAdd a.1 b.1,floorRationalCodeAdd a.2 b.2)

/-- Definition of floor Complex Code Mul in the Coded Floor construction. -/
def floorComplexCodeMul (a b : FloorComplexCode) : FloorComplexCode :=
  (floorRationalCodeAdd (floorRationalCodeMul a.1 b.1)
      (floorRationalCodeNeg (floorRationalCodeMul a.2 b.2)),
    floorRationalCodeAdd (floorRationalCodeMul a.1 b.2) (floorRationalCodeMul a.2 b.1))

/-- Definition of floor Complex Code Square in the Coded Floor construction. -/
def floorComplexCodeSquare (a : FloorComplexCode) : FloorComplexCode := floorComplexCodeMul a a

/-- Definition of floor Cis Term Step Code in the Coded Floor construction. -/
def floorCisTermStepCode (x : FloorRationalCode) (n : ℕ) (a : FloorComplexCode) : FloorComplexCode :=
  (floorRationalCodeMul (floorRationalCodeMul (floorRationalCodeNeg a.2) x)
      (floorRationalCodeInv (floorRationalCodeNat n)),
    floorRationalCodeMul (floorRationalCodeMul a.1 x)
      (floorRationalCodeInv (floorRationalCodeNat n)))

/-- Original `floorComplexCodeAdd_value` guarantee for the `FloorComplexCode` construction; the complete source hypotheses are retained. -/
theorem floorComplexCodeAdd_value (a b : FloorComplexCode) :
    floorComplexCodeValue (floorComplexCodeAdd a b)=
      cisPairAdd (floorComplexCodeValue a) (floorComplexCodeValue b) := by
  simp [floorComplexCodeValue,floorComplexCodeAdd,floorRationalCodeAdd_value,cisPairAdd]

/-- Original `floorComplexCodeMul_value` guarantee for the `FloorComplexCode` construction; the complete source hypotheses are retained. -/
theorem floorComplexCodeMul_value (a b : FloorComplexCode) :
    floorComplexCodeValue (floorComplexCodeMul a b)=
      cisPairMul (floorComplexCodeValue a) (floorComplexCodeValue b) := by
  simp [floorComplexCodeValue,floorComplexCodeMul,floorRationalCodeAdd_value,
    floorRationalCodeMul_value,floorRationalCodeNeg_value,cisPairMul,sub_eq_add_neg]

/-- Original `floorComplexCodeSquare_value` guarantee for the `FloorComplexCode` construction; the complete source hypotheses are retained. -/
theorem floorComplexCodeSquare_value (a : FloorComplexCode) :
    floorComplexCodeValue (floorComplexCodeSquare a)=cisPairSquare (floorComplexCodeValue a) := by
  rw [floorComplexCodeSquare,floorComplexCodeMul_value]
  apply Prod.ext <;> dsimp [cisPairMul,cisPairSquare] <;> ring

/-- Original `floorCisTermStepCode_value` guarantee for the `FloorComplexCode` construction; the complete source hypotheses are retained. -/
theorem floorCisTermStepCode_value (x : FloorRationalCode) (n : ℕ) (a : FloorComplexCode) :
    floorComplexCodeValue (floorCisTermStepCode x n a)=
      cisTermStep (floorRationalCodeValue x) n (floorComplexCodeValue a) := by
  simp [floorComplexCodeValue,floorCisTermStepCode,floorRationalCodeMul_value,
    floorRationalCodeNeg_value,floorRationalCodeInv_value,floorRationalCodeNat_value,cisTermStep,
    div_eq_mul_inv]

/-- Original `primrec_floorComplexCodeAdd` guarantee for the `FloorComplexCode` construction; the complete source hypotheses are retained. -/
theorem primrec_floorComplexCodeAdd : Primrec₂ floorComplexCodeAdd :=
  (primrec_floorRationalCodeAdd.comp (Primrec.fst.comp Primrec.fst)
    (Primrec.fst.comp Primrec.snd)).pair
    (primrec_floorRationalCodeAdd.comp (Primrec.snd.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))

/-- Original `primrec_floorComplexCodeMul` guarantee for the `FloorComplexCode` construction; the complete source hypotheses are retained. -/
theorem primrec_floorComplexCodeMul : Primrec₂ floorComplexCodeMul := by
  have ar : Primrec (fun p : FloorComplexCode × FloorComplexCode => p.1.1) := Primrec.fst.comp Primrec.fst
  have ai : Primrec (fun p : FloorComplexCode × FloorComplexCode => p.1.2) := Primrec.snd.comp Primrec.fst
  have br : Primrec (fun p : FloorComplexCode × FloorComplexCode => p.2.1) := Primrec.fst.comp Primrec.snd
  have bi : Primrec (fun p : FloorComplexCode × FloorComplexCode => p.2.2) := Primrec.snd.comp Primrec.snd
  exact (primrec_floorRationalCodeAdd.comp (primrec_floorRationalCodeMul.comp ar br)
    (primrec_floorRationalCodeNeg.comp (primrec_floorRationalCodeMul.comp ai bi))).pair
    (primrec_floorRationalCodeAdd.comp (primrec_floorRationalCodeMul.comp ar bi)
      (primrec_floorRationalCodeMul.comp ai br))

/-- Original `primrec_floorComplexCodeSquare` guarantee for the `FloorComplexCode` construction; the complete source hypotheses are retained. -/
theorem primrec_floorComplexCodeSquare : Primrec floorComplexCodeSquare :=
  primrec_floorComplexCodeMul.comp Primrec.id Primrec.id

/-- Original `primrec_floorCisTermStepCode` guarantee for the `FloorComplexCode` construction; the complete source hypotheses are retained. -/
theorem primrec_floorCisTermStepCode :
    Primrec₂ (fun (p : FloorRationalCode × ℕ) (a : FloorComplexCode) => floorCisTermStepCode p.1 p.2 a) := by
  have x : Primrec (fun p : (FloorRationalCode × ℕ) × FloorComplexCode => p.1.1) :=
    Primrec.fst.comp Primrec.fst
  have d : Primrec (fun p : (FloorRationalCode × ℕ) × FloorComplexCode =>
      floorRationalCodeInv (floorRationalCodeNat p.1.2)) :=
    primrec_floorRationalCodeInv.comp (primrec_floorRationalCodeNat.comp (Primrec.snd.comp Primrec.fst))
  have ar : Primrec (fun p : (FloorRationalCode × ℕ) × FloorComplexCode => p.2.1) :=
    Primrec.fst.comp Primrec.snd
  have ai : Primrec (fun p : (FloorRationalCode × ℕ) × FloorComplexCode => p.2.2) :=
    Primrec.snd.comp Primrec.snd
  exact (primrec_floorRationalCodeMul.comp
    (primrec_floorRationalCodeMul.comp (primrec_floorRationalCodeNeg.comp ai) x) d).pair
    (primrec_floorRationalCodeMul.comp (primrec_floorRationalCodeMul.comp ar x) d)

end Qatlib.Concepts.EffectiveGauge.CodedFloor
