/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.CodedFloor.FloorNegativeExpCode

/-!
# Floor Negative Exp Backend Code

Coded Floor constructions for Effective Gauge.
Defines `floorScalarClampCode`, `floorNegativeExpHalvingsCode`, `floorNegativeExpSquareStep`.
Proves `floorScalarClampCode_value`, `floorNegativeExpHalvingsCode_value`, `floorNegativeExpSquaresCode_value`.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.CodedFloor
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Definition of floor Scalar Clamp Code in the Coded Floor construction. -/
def floorScalarClampCode (q : FloorRationalCode) : FloorRationalCode :=
  floorRationalCodeMin (floorRationalCodeNat 1) (floorRationalCodeMax (floorRationalCodeNat 0) q)

/-- Definition of floor Negative Exp Halvings Code in the Coded Floor construction. -/
def floorNegativeExpHalvingsCode (q : FloorRationalCode) : ℕ :=
  Nat.clog 2 (floorRationalCodeCeil (floorRationalCodeMul (floorRationalCodeNat 2) q))

/-- Definition of floor Negative Exp Square Step in the Coded Floor construction. -/
def floorNegativeExpSquareStep (r : FloorScalarCodeResult) : FloorScalarCodeResult :=
  ((floorRationalCodeMul r.1.1 r.1.1,floorRationalCodeMul (floorRationalCodeNat 2) r.1.2),r.2)

/-- Definition of floor Negative Exp Squares Code in the Coded Floor construction. -/
def floorNegativeExpSquaresCode (r : FloorScalarCodeResult) (h : ℕ) : FloorScalarCodeResult :=
  floorNegativeExpSquareStep^[h] r

/-- Original `floorScalarClampCode_value` guarantee for the `FloorNegativeExpBackendCode` construction; the complete source hypotheses are retained. -/
theorem floorScalarClampCode_value (q : FloorRationalCode) :
    floorRationalCodeValue (floorScalarClampCode q)=scalarClamp (floorRationalCodeValue q) := by
  simp [floorScalarClampCode,floorRationalCodeMin_value,floorRationalCodeMax_value,
    floorRationalCodeNat_value,scalarClamp]

/-- Original `floorNegativeExpHalvingsCode_value` guarantee for the `FloorNegativeExpBackendCode` construction; the complete source hypotheses are retained. -/
theorem floorNegativeExpHalvingsCode_value (q : FloorRationalCode) :
    floorNegativeExpHalvingsCode q=negativeExpHalvings (floorRationalCodeValue q) := by
  simp [floorNegativeExpHalvingsCode,floorRationalCodeCeil_value,floorRationalCodeMul_value,
    floorRationalCodeNat_value,negativeExpHalvings]

/-- Original `floorNegativeExpSquaresCode_value` guarantee for the `FloorNegativeExpBackendCode` construction; the complete source hypotheses are retained. -/
theorem floorNegativeExpSquaresCode_value (r : FloorScalarCodeResult) (h : ℕ) :
    floorScalarCodeResultValue (floorNegativeExpSquaresCode r h)=
      negativeExpSquares h (floorScalarCodeResultValue r) := by
  induction h generalizing r with
  | zero => rfl
  | succ h ih =>
    unfold floorNegativeExpSquaresCode
    rw [Function.iterate_succ_apply]
    change floorScalarCodeResultValue (floorNegativeExpSquaresCode (floorNegativeExpSquareStep r) h)=_
    rw [ih,negativeExpSquares]
    simp [floorScalarCodeResultValue,floorNegativeExpSquareStep,floorRationalCodeMul_value,
      floorRationalCodeNat_value]

/-- Original `primrec_floorScalarClampCode` guarantee for the `FloorNegativeExpBackendCode` construction; the complete source hypotheses are retained. -/
theorem primrec_floorScalarClampCode : Primrec floorScalarClampCode :=
  primrec_floorRationalCodeMin.comp (Primrec.const (floorRationalCodeNat 1))
    (primrec_floorRationalCodeMax.comp (Primrec.const (floorRationalCodeNat 0)) Primrec.id)

/-- Original `primrec_floorNegativeExpHalvingsCode` guarantee for the `FloorNegativeExpBackendCode` construction; the complete source hypotheses are retained. -/
theorem primrec_floorNegativeExpHalvingsCode : Primrec floorNegativeExpHalvingsCode :=
  primrec_floorClogTwo.comp (primrec_floorRationalCodeCeil.comp
    (primrec_floorRationalCodeMul.comp (Primrec.const (floorRationalCodeNat 2)) Primrec.id))

/-- Original `primrec_floorNegativeExpSquareStep` guarantee for the `FloorNegativeExpBackendCode` construction; the complete source hypotheses are retained. -/
theorem primrec_floorNegativeExpSquareStep : Primrec floorNegativeExpSquareStep :=
  ((primrec_floorRationalCodeMul.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.fst)).pair
    (primrec_floorRationalCodeMul.comp (Primrec.const (floorRationalCodeNat 2))
      (Primrec.snd.comp Primrec.fst))).pair Primrec.snd

/-- Original `primrec_floorNegativeExpSquaresCode` guarantee for the `FloorNegativeExpBackendCode` construction; the complete source hypotheses are retained. -/
theorem primrec_floorNegativeExpSquaresCode : Primrec₂ floorNegativeExpSquaresCode := by
  have hs : Primrec₂ (fun (_ : FloorScalarCodeResult × ℕ) (r : FloorScalarCodeResult) =>
      floorNegativeExpSquareStep r) := primrec_floorNegativeExpSquareStep.comp Primrec.snd
  exact Primrec.nat_iterate Primrec.snd Primrec.fst hs

end Qatlib.Concepts.EffectiveGauge.CodedFloor
