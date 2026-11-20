/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.EffectiveGauge.CodedFloor.FloorSourceCodeObstruction

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Floor Source Code Coverage

Coded Floor constructions for Effective Gauge.
Defines `floorRationalCodeOfRat`, `floorPointCodeOfRational`, `floorSourceQueryCodeOfOriginal`.
Proves `floorRationalCodeOfRat_value`, `floorPointCodeOfRational_value`, `floorSourceQueryCodeOfOriginal_multiIndex`.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.CodedFloor
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow Qatlib.Concepts.EffectiveGauge.SpectralH1 Qatlib.Concepts.EffectiveGauge.TorusFourier

/-- The raw input covers every original rational, not a restricted subset of
physical addresses. This is a representation identity, not a runtime oracle. -/
def floorRationalCodeOfRat (q : ℚ) : FloorRationalCode :=
  ((q.num.toNat,(-q.num).toNat),q.den-1)

/-- Encoding a rational in the floor representation and decoding it recovers the original rational
exactly. -/
theorem floorRationalCodeOfRat_value (q : ℚ) :
    floorRationalCodeValue (floorRationalCodeOfRat q)=q := by
  have hz : (q.num.toNat : ℤ)-((-q.num).toNat : ℤ)=q.num := by omega
  have hq : (q.num.toNat : ℚ)-((-q.num).toNat : ℚ)=(q.num : ℚ) := by exact_mod_cast hz
  unfold floorRationalCodeValue floorRationalCodeOfRat
  rw [Nat.sub_add_cancel q.den_pos,hq]
  simpa only [Int.cast_natCast] using
    (Rat.intCast_div_eq_divInt q.num (q.den : ℤ)).trans q.num_divInt_den

/-- Definition of floor Point Code Of Rational in the Coded Floor construction. -/
def floorPointCodeOfRational (X : Fin 3 → ℚ) : FloorPointCode :=
  (floorRationalCodeOfRat (X 0),floorRationalCodeOfRat (X 1),floorRationalCodeOfRat (X 2))

/-- Encoding a rational spatial point coordinatewise and decoding it recovers the original point. -/
theorem floorPointCodeOfRational_value (X : Fin 3 → ℚ) :
    floorPointCodeValue (floorPointCodeOfRational X)=X := by
  funext i
  fin_cases i <;> simp [floorPointCodeValue,floorPointCodeOfRational,floorRationalCodeOfRat_value]

/-- Definition of floor Source Query Code Of Original in the Coded Floor construction. -/
def floorSourceQueryCodeOfOriginal (X : Fin 3 → ℚ) (alpha : Fin 3 → ℕ) (b : ℕ) (j : Fin 3) :
    FloorSourceQueryCode := (floorPointCodeOfRational X,(alpha 0,alpha 1,alpha 2),b,j.val)

/-- Packing an original jet query preserves its multi-index under decoding, regardless of point,
precision, and output coordinate. -/
theorem floorSourceQueryCodeOfOriginal_multiIndex (X : Fin 3 → ℚ) (alpha : Fin 3 → ℕ)
    (b : ℕ) (j : Fin 3) :
    floorSourceQueryMultiIndex (floorSourceQueryCodeOfOriginal X alpha b j)=alpha := by
  funext i
  fin_cases i <;> simp [floorSourceQueryMultiIndex,floorSourceQueryCodeOfOriginal]

/-- Encoding an original point, multi-index, precision, and component as a query and decoding the
resulting answer gives the original program jet source's rational answer. -/
theorem floorEncodedJetSource_original_query (c : Nat.Partrec.Code) (X : Fin 3 → ℚ)
    (alpha : Fin 3 → ℕ) (b : ℕ) (j : Fin 3) :
    floorRationalCodeValue (floorEncodedJetSource c (floorSourceQueryCodeOfOriginal X alpha b j))=
      floorProgramJetSource c ((X,alpha),b) j := by
  rw [floorEncodedJetSource_value,floorSourceQueryCodeOfOriginal_multiIndex]
  simp only [floorSourceQueryCodeOfOriginal,floorPointCodeOfRational_value,floorExprAxis_val]

end Qatlib.Concepts.EffectiveGauge.CodedFloor
