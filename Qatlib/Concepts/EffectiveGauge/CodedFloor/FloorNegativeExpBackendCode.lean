/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.EffectiveGauge.CodedFloor.FloorNegativeExpCode

@[expose] public section

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

/-- Decoding the scalar clamp gives the decoded rational input clamped to the interval `[0, 1]`. -/
theorem floorScalarClampCode_value (q : FloorRationalCode) :
    floorRationalCodeValue (floorScalarClampCode q)=scalarClamp (floorRationalCodeValue q) := by
  simp [floorScalarClampCode,floorRationalCodeMin_value,floorRationalCodeMax_value,
    floorRationalCodeNat_value,scalarClamp]

/-- The coded halving count is `negativeExpHalvings` at the represented rational argument. -/
theorem floorNegativeExpHalvingsCode_value (q : FloorRationalCode) :
    floorNegativeExpHalvingsCode q=negativeExpHalvings (floorRationalCodeValue q) := by
  simp [floorNegativeExpHalvingsCode,floorRationalCodeCeil_value,floorRationalCodeMul_value,
    floorRationalCodeNat_value,negativeExpHalvings]

/-- Decoding a sequence of `h` coded squarings gives the rational result of applying
`negativeExpSquares h` to the decoded initial scalar result. -/
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

/-- Clamping a rational code between zero and one is primitive recursive. -/
theorem primrec_floorScalarClampCode : Primrec floorScalarClampCode :=
  primrec_floorRationalCodeMin.comp (Primrec.const (floorRationalCodeNat 1))
    (primrec_floorRationalCodeMax.comp (Primrec.const (floorRationalCodeNat 0)) Primrec.id)

/-- The number of argument halvings for the coded negative-exponential evaluation is primitive
recursive. -/
theorem primrec_floorNegativeExpHalvingsCode : Primrec floorNegativeExpHalvingsCode :=
  primrec_floorClogTwo.comp (primrec_floorRationalCodeCeil.comp
    (primrec_floorRationalCodeMul.comp (Primrec.const (floorRationalCodeNat 2)) Primrec.id))

/-- The coded transition that squares a negative-exponential result and updates its error estimate
is primitive recursive. -/
theorem primrec_floorNegativeExpSquareStep : Primrec floorNegativeExpSquareStep :=
  ((primrec_floorRationalCodeMul.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.fst)).pair
    (primrec_floorRationalCodeMul.comp (Primrec.const (floorRationalCodeNat 2))
      (Primrec.snd.comp Primrec.fst))).pair Primrec.snd

/-- Iterating negative-exponential squaring is primitive recursive jointly in the initial result
code and number of squarings. -/
theorem primrec_floorNegativeExpSquaresCode : Primrec₂ floorNegativeExpSquaresCode := by
  have hs : Primrec₂ (fun (_ : FloorScalarCodeResult × ℕ) (r : FloorScalarCodeResult) =>
      floorNegativeExpSquareStep r) := primrec_floorNegativeExpSquareStep.comp Primrec.snd
  exact Primrec.nat_iterate Primrec.snd Primrec.fst hs

end Qatlib.Concepts.EffectiveGauge.CodedFloor
